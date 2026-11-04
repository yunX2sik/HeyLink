# =====================================================================
#  HayLink Lite v0.3 - 몽골 조드(Dzud) 대비 공동 건초창고 재고 자동기록 · 구호사료 공동배송 프로토타입
#  모바일 UI + 3개 언어 (ko / en / mn)
#  실행: python Mongolian_app.py  →  브라우저 http://127.0.0.1:5000   (폰: http://노트북IP:5000)
#  필요: pip install flask
#  선택: 환경변수 DATABASE_URL=postgresql://...  → PostgreSQL(Neon)에 저장 (없으면 SQLite 파일). 시연·운영 데이터는 DB 안 demo / live 스키마로 분리
#  선택: 환경변수 HAYLINK_MODE=live → 운영 모드 (가짜 데이터·시연 버튼 없음, DB 파일도 haylink_live.db 로 분리). 기본은 demo
#        단, DATABASE_URL + HAYLINK_ADMIN_PIN 이 모두 있으면 관리자 화면의 '운영 모드 전환' 버튼으로 바꾸고(DB에 저장), 이때 HAYLINK_MODE 는 저장된 값이 없을 때의 처음 값일 뿐
#  선택: 환경변수 HAYLINK_ADMIN_PIN=1234 → 관리자 화면·데모 초기화·대리 신청에 PIN 요구 (미설정 시 열림)
#
#  v0.3 변경점
#   - [핵심] 재고 < 트럭 1대(5t) 창고는 신청·배송 모두 차단 (재보충 전까지)
#   - [핵심] 재고 ≥ 5t 창고도 신청 가능량 = 재고 − 대기 신청량 범위 안에서만 접수
#   - 배송 시점 재고 재검증, 입고(재고 급증) 감지 후 그 이후 데이터만 예측에 사용
#   - 잔량 0% 예측 버그, 시연 반출 ×3 버그, 템플릿 자동 이스케이프(XSS) 수정
#   - 기온 캐시 TTL, 입력 검증, 관리자 PIN, 데모 시드 고정
# =====================================================================
from flask import Flask, request, jsonify, render_template, redirect, g, Response, has_request_context
from jinja2 import DictLoader
from urllib.parse import quote, urlparse
from functools import wraps
import sqlite3, datetime, random, json, urllib.request, os, re, csv, io, time, atexit, threading, hmac
from contextlib import contextmanager

# ─────────────── 설정 ───────────────
APP_MODE         = os.environ.get("HAYLINK_MODE", "demo").strip().lower()   # demo: 시연(가짜 데이터·시연 버튼) | live: 운영(실제 데이터만)
DEMO_MODE        = APP_MODE != "live"
DB_FILE          = "haylink.db" if DEMO_MODE else "haylink_live.db"        # (SQLite 일 때) 시연 DB와 운영 DB 파일을 분리해 섞이지 않게 함
DATABASE_URL     = os.environ.get("DATABASE_URL", "").strip()              # 있으면 PostgreSQL(Neon), 없으면 SQLite 파일
USE_PG           = DATABASE_URL.startswith(("postgres://", "postgresql://"))
PG_URL           = DATABASE_URL.replace("-pooler", "", 1)                   # 연결 풀을 앱이 직접 관리하므로 direct 주소를 씀 (pooled 주소를 넣어도 자동 변환)
PG_SCHEMA        = os.environ.get("HAYLINK_PG_SCHEMA") or ("demo" if DEMO_MODE else "live")   # (PostgreSQL 일 때) 시연·운영 데이터를 한 DB 안에서 분리
if USE_PG and not re.fullmatch(r"[a-z_][a-z0-9_]*", PG_SCHEMA):
    raise SystemExit("HAYLINK_PG_SCHEMA 는 영문 소문자·숫자·밑줄만 쓸 수 있습니다")
TRUCK_CAPACITY_T = 5.0           # 트럭 1대 분량(톤)
LEAD_DAYS        = 3             # 재보충 소요일
HAY_BALE_TON     = 0.35          # 시연용 건초 1묶음
ORDER_MIN_T      = 0.5           # 1회 최소 신청량
REFILL_JUMP_PCT  = 8.0           # 측정 간 재고가 이만큼 이상 늘면 '입고'로 간주
TEMP_TTL_S       = 3600          # 기온 캐시 유효시간(초)
ADMIN_PIN        = os.environ.get("HAYLINK_ADMIN_PIN", "")   # 빈 문자열이면 보호 없음
MODE_SWITCHABLE  = USE_PG and bool(ADMIN_PIN) and not os.environ.get("HAYLINK_PG_SCHEMA")   # 관리자 화면에서 시연/운영 모드를 바꿀 수 있는 조건: Neon 사용 + PIN 설정 (이때 환경변수 HAYLINK_MODE 는 '처음 값'일 뿐)
MODE_TTL_S       = 5             # 다른 서버(워커)가 모드 변경을 알아채는 데 걸리는 최대 시간(초)
GEMINI_MODELS    = os.environ.get("HAYLINK_GEMINI_MODEL", "gemini-3.5-flash-lite,gemini-3-flash-preview,gemini-3.5-flash,gemini-3.1-flash-lite").split(",")   # 앞 모델이 오류·지연이면 다음 모델 시도 (무료 키로 사용 가능)
GEMINI_TOTAL_S   = 25            # 재시도 포함 전체 대기 한도(초). 서버 제한 30초보다 짧게
GEMINI_MAX_OUT  = 2000           # 답변 길이 한도(생각에 쓰는 글자 포함)
GEMINI_TIMEOUT_S = 9          # 모델 하나당 최대 대기 시간(초). 서버가 30초를 넘기면 요청을 끊으므로 짧게 둠
CHAT_MAX_TURNS   = 10            # AI에게 함께 보내는 이전 대화 최대 개수
QUESTION_DB_FILE = "questions.db"   # import_questions.py 가 만드는 자주 묻는 질문 DB (데모 초기화에 지워지지 않도록 따로 둠)
SUGGEST_COUNT    = 6                # 주제 단어만 입력했을 때 보여 줄 질문 버튼 수
TOPIC_KEYWORDS   = {"배송": ("배송", "delivery", "shipping", "хүргэлт"),     # 이 단어만 입력하면 질문 버튼 표시
                    "재고": ("재고", "stock", "нөөц"),
                    "입고": ("입고", "재입고", "재보충", "restock", "restocking", "нөхөх"),
                    "신청": ("신청", "request", "order", "хүсэлт", "захиалга")}
WEATHER_TTL_S    = 1800          # 현재 날씨 캐시 유효시간(초)
FX_TTL_S         = 21600         # 환율 캐시 유효시간(초) = 6시간
FORECAST_HORIZON_D   = 60        # 농가 주문 기반 매진 예측이 내다보는 기간(일)
MIN_ORDERS_FOR_CYCLE = 3         # 농가의 주문 주기를 계산하는 데 필요한 최소 주문 기록 수
BASE_FARE_MNT    = 80000        # 기본 운임(MNT) — 추정치, 공식 요금 아님
PER_KM_FARE_MNT  = 2500          # km당 운임(MNT) — 추정치, 공식 요금 아님
BALES_PER_TON    = 40            # 25kg 묶음 40개 = 1톤
LANGS            = ("ko", "en", "mn")
DEFAULT_LANG     = "ko"
SAFE_BACK        = {"/order", "/admin"}

WAREHOUSES = [
    {"id": "zuunmod_01", "name": {"ko": "준모드 1호 창고", "en": "Zuunmod Warehouse 1", "mn": "Зуунмод 1-р агуулах"},
     "soum": {"ko": "준모드 소움", "en": "Zuunmod soum", "mn": "Зуунмод сум"},
     "lat": 47.707, "lon": 106.953, "d_empty_cm": 300, "d_full_cm": 30, "capacity_ton": 40},
    {"id": "bayan_01", "name": {"ko": "바양 창고", "en": "Bayan Warehouse", "mn": "Баян агуулах"},
     "soum": {"ko": "바양 소움", "en": "Bayan soum", "mn": "Баян сум"},
     "lat": 47.20, "lon": 107.53, "d_empty_cm": 280, "d_full_cm": 30, "capacity_ton": 30},
    {"id": "altanbulag_01", "name": {"ko": "알탄불락 창고", "en": "Altanbulag Warehouse", "mn": "Алтанбулаг агуулах"},
     "soum": {"ko": "알탄불락 소움", "en": "Altanbulag soum", "mn": "Алтанбулаг сум"},
     "lat": 47.72, "lon": 106.38, "d_empty_cm": 320, "d_full_cm": 40, "capacity_ton": 45},
    {"id": "sergelen_01", "name": {"ko": "세르겔렌 창고", "en": "Sergelen Warehouse", "mn": "Сэргэлэн агуулах"},
     "soum": {"ko": "세르겔렌 소움", "en": "Sergelen soum", "mn": "Сэргэлэн сум"},
     "lat": 47.49, "lon": 107.09, "d_empty_cm": 260, "d_full_cm": 30, "capacity_ton": 25},
]
WH_BY_ID = {w["id"]: w for w in WAREHOUSES}

# ─────────────── 챗봇 자주 묻는 질문 ───────────────
# 새 질문을 추가하려면 아래 목록에 {"keywords": [...], "answer": {...}} 한 덩어리를 더하면 됩니다.
FAQS = [
    {"keywords": ["배송", "도착", "택배", "delivery", "shipping", "arrive", "хүргэлт", "ирэх"],
     "answer": {"ko": "현재 배송이 진행 중이며 날씨로 인해 정확한 도착 날짜 측정이 어렵습니다.",
                "en": "Your delivery is in progress, but bad weather makes it hard to give an exact arrival date.",
                "mn": "Хүргэлт явагдаж байна, гэвч цаг агаарын улмаас яг хэзээ ирэхийг тодорхойлоход хэцүү байна."}},
]

# ═══════════════════ 번역 사전 ═══════════════════
T = {
 "tagline":      {"ko": "건초 재고 · 공동배송", "en": "Hay stock · shared delivery", "mn": "Өвсний нөөц · хамтарсан хүргэлт"},
 # 챗봇
 "nav_chat":     {"ko": "챗봇", "en": "Chatbot", "mn": "Чатбот"},
 "chat_title":   {"ko": "무엇이든 물어보세요", "en": "Ask us anything", "mn": "Юу ч асууж болно"},
 "chat_sub":     {"ko": "자주 묻는 질문에 바로 답해 드려요", "en": "Instant answers to common questions", "mn": "Түгээмэл асуултад шууд хариулна"},
 "chat_hello":   {"ko": "무엇을 도와드릴까요?", "en": "How can I help you?", "mn": "Танд юугаар туслах вэ?"},
 "chat_ph":      {"ko": "질문을 입력하세요", "en": "Type your question", "mn": "Асуултаа бичнэ үү"},
 "chat_send":    {"ko": "보내기", "en": "Send", "mn": "Илгээх"},
 "chat_loading": {"ko": "챗봇 답변 생성 중", "en": "Writing an answer", "mn": "Хариулт бэлдэж байна"},
 "chat_pick":    {"ko": "많이 묻는 질문이에요. 궁금한 걸 골라 주세요 👇", "en": "These are frequently asked. Pick one 👇", "mn": "Түгээмэл асуултууд. Сонгоно уу 👇"},
 "chat_fallback":{"ko": "죄송해요, 아직 이 질문은 답을 준비하지 못했어요. 관리자에게 문의해 주세요.", "en": "Sorry, I don't have an answer for that yet. Please contact the administrator.", "mn": "Уучлаарай, энэ асуултад хараахан хариулт бэлдээгүй байна. Удирдлагад хандана уу."},
 "nav_wh":       {"ko": "창고", "en": "Warehouses", "mn": "Агуулах"},
 "nav_order":    {"ko": "배송 신청", "en": "Requests", "mn": "Хүсэлт"},
 "nav_admin":    {"ko": "관리자", "en": "Admin", "mn": "Удирдлага"},
 "footer":       {"ko": "HayLink Lite v0.3 · 프로토타입 · 데모 모드 {m}", "en": "HayLink Lite v0.3 · Prototype · Demo mode {m}", "mn": "HayLink Lite v0.3 · Прототип · Жишээ горим {m}"},
 # 창고 현황
 "idx_title":    {"ko": "소움 건초창고 현황", "en": "Soum hay warehouse status", "mn": "Сумын өвсний агуулахын байдал"},
 "province":     {"ko": "투브(Töv) 아이막", "en": "Töv Province", "mn": "Төв аймаг"},
 "capacity":     {"ko": "용량", "en": "Capacity", "mn": "Багтаамж"},
 "left":         {"ko": "남음", "en": "left", "mn": "үлдсэн"},
 "runs_out":     {"ko": "소진 예상", "en": "Runs out", "mn": "Дуусах хугацаа"},
 "per_day":      {"ko": "하루 소비", "en": "Daily use", "mn": "Өдрийн хэрэглээ"},
 "sensor_off":   {"ko": "센서 12시간 이상 무응답", "en": "Sensor offline >12 h", "mn": "Мэдрэгч 12+ цаг хариугүй"},
 "refilled":     {"ko": "입고 감지 — 입고 이후 데이터로 예측", "en": "Refill detected — forecast uses post-refill data", "mn": "Нөөц нэмэгдсэн — дараах өгөгдлөөр таамагласан"},
 "about_title":  {"ko": "이 화면은?", "en": "About this screen", "mn": "Энэ дэлгэц юу вэ?"},
 "about_body":   {"ko": "각 창고 천장의 초음파 센서(ESP32)가 5분마다 건초 높이를 측정해 재고를 자동 기록합니다. 소진 예상일은 최근 7일 감소 속도(선형회귀)에 한파 예보 가중치를 적용해 계산하며, 입고가 감지되면 입고 이후 데이터만 사용합니다. 사료 신청은 창고 실제 재고 범위 안에서만 받습니다. 또한 농가별 주문 습관(평균 주문량·주기)으로 앞으로의 주문을 예상해 매진일을 계산하고, 센서 추세와 비교해 더 이른 날짜를 보여 줍니다.",
                  "en": "An ultrasonic sensor (ESP32) on each warehouse ceiling measures hay height every 5 minutes and records stock automatically. The depletion date is estimated from the 7-day decline rate (linear regression) weighted by the cold-weather forecast; after a refill only post-refill data is used. Feed requests are accepted only within the warehouse's actual stock. The app also predicts upcoming orders from each herder's ordering habits (average amount and cycle) and shows the earlier of that run-out date and the sensor-trend date.",
                  "mn": "Агуулах бүрийн таазанд байрлуулсан хэт авианы мэдрэгч (ESP32) 5 минут тутамд өвсний өндрийг хэмжиж нөөцийг автоматаар бүртгэнэ. Дуусах хугацааг сүүлийн 7 хоногийн буурах хурд (шугаман регресс) дээр хүйтний урьдчилсан мэдээний жинг нэмж тооцоолно; нөөц нэмэгдсэн бол түүнээс хойшхи өгөгдлийг л ашиглана. Тэжээлийн хүсэлтийг агуулахын бодит нөөцийн хүрээнд л хүлээн авна. Мөн малчин бүрийн захиалгын зуршлаар (дундаж хэмжээ, давтамж) ирэх захиалгыг таамаглаж, мэдрэгчийн хандлагатай харьцуулан эрт дуусах огноог харуулна."},
 # 상세
 "back":         {"ko": "← 창고 목록", "en": "← All warehouses", "mn": "← Агуулахын жагсаалт"},
 "cur_stock":    {"ko": "현재 건초 잔량", "en": "Current hay stock", "mn": "Одоогийн өвсний нөөц"},
 "last_reading": {"ko": "마지막 측정", "en": "Last reading", "mn": "Сүүлийн хэмжилт"},
 "forecast":     {"ko": "소진 예측 (AI v0)", "en": "Depletion forecast (AI v0)", "mn": "Дуусах таамаглал (AI v0)"},
 "base_days":    {"ko": "기본 {a}일 → 한파 반영 {b}일", "en": "Base {a} days → with cold {b} days", "mn": "Үндсэн {a} хоног → хүйтэн тооцвол {b} хоног"},
 "temp_min":     {"ko": "예보 최저기온", "en": "Forecast min. temp", "mn": "Хамгийн бага температурын урьдчилсан мэдээ"},
 "reorder":      {"ko": "재보충 권고일", "en": "Recommended restock date", "mn": "Нөөц нөхөх зөвлөмжийн өдөр"},
 "lead_note":    {"ko": "배송 {n}일 소요 가정", "en": "assuming {n}-day delivery", "mn": "хүргэлт {n} хоног гэж тооцсон"},
 "trend":        {"ko": "최근 7일 재고 추이", "en": "Stock trend (last 7 days)", "mn": "Сүүлийн 7 хоногийн нөөцийн хандлага"},
 "no_data":      {"ko": "데이터 부족", "en": "Not enough data", "mn": "Өгөгдөл хангалтгүй"},
 # 농가 주문 기반 매진 예측
 "src_orders":   {"ko": "농가 주문 기준", "en": "from herder orders", "mn": "малчдын захиалгаар"},
 "src_sensor":   {"ko": "센서 추세 기준", "en": "from sensor trend", "mn": "мэдрэгчийн хандлагаар"},
 "of_title":     {"ko": "농가 주문 기반 매진 예측", "en": "Stockout forecast from herder orders", "mn": "Малчдын захиалгад суурилсан дуусах таамаг"},
 "of_nodata":    {"ko": "농가별 주문 기록이 아직 부족해서 예측할 수 없어요. (농가마다 주문 {n}회 이상 필요)", "en": "Not enough order history yet. (each herder needs {n}+ orders)", "mn": "Захиалгын түүх хангалтгүй байна. (малчин бүр {n}+ захиалгатай байх ёстой)"},
 "of_today":     {"ko": "오늘 매진 예상", "en": "Expected to sell out today", "mn": "Өнөөдөр дуусна гэж таамаглаж байна"},
 "of_stockout":  {"ko": "{d}일 뒤 매진 예상", "en": "Expected to sell out in {d} days", "mn": "{d} хоногийн дараа дуусна гэж таамаглаж байна"},
 "of_none":      {"ko": "{n}일 안에는 매진 예상 없음", "en": "No stockout expected within {n} days", "mn": "{n} хоногт дуусахгүй гэж таамаглаж байна"},
 "of_cause":     {"ko": "매진 시점의 주문", "en": "Orders at that time", "mn": "Тэр үеийн захиалга"},
 "of_block":     {"ko": "신청 차단 예상: {d} (재고가 트럭 1대 {n}t 미만이 됨)", "en": "Requests expected to close: {d} (stock drops below one truck, {n} t)", "mn": "Хүсэлт хаагдах төлөв: {d} (нөөц 1 машин, {n} тн-оос бага болно)"},
 "of_block_now": {"ko": "이미 신청이 막혀 있어요 (재고가 트럭 1대 {n}t 미만)", "en": "Requests are already closed (stock below one truck, {n} t)", "mn": "Хүсэлт аль хэдийн хаалттай (нөөц 1 машин, {n} тн-оос бага)"},
 "of_list":      {"ko": "예상 주문표", "en": "Expected orders", "mn": "Төлөвлөсөн захиалгууд"},
 "of_left":      {"ko": "남는 재고 {x}t", "en": "{x} t left", "mn": "{x} тн үлдэнэ"},
 "of_short":     {"ko": "재고 부족", "en": "short of stock", "mn": "нөөц дутна"},
 "of_habits":    {"ko": "농가별 주문 습관", "en": "Herder ordering habits", "mn": "Малчдын захиалгын зуршил"},
 "of_habit":     {"ko": "평균 {t}t · 약 {d}일마다 · 다음 {nx}", "en": "avg {t} t · every ~{d} days · next {nx}", "mn": "дундаж {t} тн · ~{d} хоног тутам · дараагийнх {nx}"},
 "of_few":       {"ko": "주문 기록 {n}회 (주기를 알기엔 부족)", "en": "{n} orders so far (too few for a cycle)", "mn": "{n} захиалга (мөчлөг тооцоход хангалтгүй)"},
 "of_pending":   {"ko": "대기 중 {t}t", "en": "pending {t} t", "mn": "хүлээгдэж буй {t} тн"},
 "of_used":      {"ko": "농가 {n}곳 중 {m}곳의 주문 주기를 반영했어요", "en": "Used the ordering cycles of {m} of {n} herders", "mn": "{n} малчны {m}-ийн захиалгын мөчлөгийг тооцсон"},
 "of_note":      {"ko": "과거 주문 습관으로 추정한 값이에요. 실제와 다를 수 있어요.", "en": "Estimated from past ordering habits; reality may differ.", "mn": "Өмнөх захиалгын зуршлаас таамагласан утга; бодит байдлаас ялгаатай байж болно."},
 "grp_this":     {"ko": "이 창고 공동배송 신청 현황", "en": "Shared-delivery requests for this warehouse", "mn": "Энэ агуулахын хамтарсан хүргэлтийн хүсэлт"},
 "truck1":       {"ko": "트럭 1대", "en": "1 truck", "mn": "1 ачааны машин"},
 "orders_n":     {"ko": "신청 {n}건", "en": "{n} requests", "mn": "{n} хүсэлт"},
 "join":         {"ko": "사료 신청하기", "en": "Request feed", "mn": "Тэжээл хүсэх"},
 "sensor_info":  {"ko": "센서 정보", "en": "Sensor info", "mn": "Мэдрэгчийн мэдээлэл"},
 "node_id":      {"ko": "노드 ID", "en": "Node ID", "mn": "Зангилааны ID"},
 "d_empty":      {"ko": "천장~바닥 (빈 창고)", "en": "Ceiling to floor (empty)", "mn": "Тааз → шал (хоосон)"},
 "d_full":       {"ko": "천장~가득 찬 건초", "en": "Ceiling to full hay", "mn": "Тааз → дүүрэн өвс"},
 "last_dist":    {"ko": "마지막 거리 측정", "en": "Last distance", "mn": "Сүүлийн зай"},
 "demo_consume": {"ko": "🧪 시연: 건초 1묶음 반출 (−{b}t)", "en": "🧪 Demo: remove 1 bale (−{b} t)", "mn": "🧪 Жишээ: 1 боодол өвс гаргах (−{b} тн)"},
 # 신청 · 재고 제한
 "order_title":  {"ko": "구호사료 공동배송 신청", "en": "Relief feed — shared delivery", "mn": "Тусламжийн тэжээл — хамтарсан хүргэлт"},
 "order_sub":    {"ko": "트럭 1대({n}t)가 차면 함께 배송 · 창고 재고 범위 내에서만 신청 가능", "en": "Delivered together once 1 truck ({n} t) is full · requests limited to warehouse stock", "mn": "1 машин ({n} тн) дүүрэхэд хамт хүргэнэ · агуулахын нөөцийн хүрээнд л хүсэлт гаргана"},
 "stock_in_wh":  {"ko": "창고 재고", "en": "Warehouse stock", "mn": "Агуулахын нөөц"},
 "avail":        {"ko": "신청 가능", "en": "Available", "mn": "Хүсэх боломжтой"},
 "stock_short":  {"ko": "⛔ 창고 재고 부족 — 재보충 후 신청 가능", "en": "⛔ Warehouse stock too low — request after restock", "mn": "⛔ Агуулахын нөөц хүрэлцэхгүй — нөхсөний дараа хүсэлт гаргана уу"},
 "no_truck_stock":{"ko": "⛔ 재고 {s}t < 트럭 {n}t — 창고 재보충 전까지 신청·공동배송 불가", "en": "⛔ Stock {s} t < truck {n} t — no requests or shared delivery until restock", "mn": "⛔ Нөөц {s} тн < машин {n} тн — нөөц нөхөх хүртэл хүсэлт, хамтарсан хүргэлт боломжгүй"},
 "req_closed":   {"ko": "⛔ 신청 불가 (재고 부족)", "en": "⛔ Requests closed (low stock)", "mn": "⛔ Хүсэлт хаалттай (нөөц бага)"},
 "dispatch_btn": {"ko": "🚚 트럭 1대 분량 도달 — 배송 요청", "en": "🚚 Truck full — request delivery", "mn": "🚚 Машин дүүрсэн — хүргэлт хүсэх"},
 "more_needed":  {"ko": "{n}t 더 모이면 배송 가능", "en": "{n} t more to dispatch", "mn": "Дахин {n} тн цуглавал хүргэх боломжтой"},
 "via_app":      {"ko": "📱 ① 앱으로 신청", "en": "📱 ① Request via app", "mn": "📱 ① Аппаар хүсэлт гаргах"},
 "name":         {"ko": "이름", "en": "Name", "mn": "Нэр"},
 "ph_name":      {"ko": "예: Batbayar", "en": "e.g. Batbayar", "mn": "жишээ нь: Батбаяр"},
 "phone":        {"ko": "전화", "en": "Phone", "mn": "Утас"},
 "ph_phone":     {"ko": "예: 9911-1234", "en": "e.g. 9911-1234", "mn": "жишээ нь: 9911-1234"},
 "tons_needed":  {"ko": "필요 건초 (톤)", "en": "Hay needed (tons)", "mn": "Шаардлагатай өвс (тн)"},
 "submit":       {"ko": "신청 등록", "en": "Submit request", "mn": "Хүсэлт өгөх"},
 "offline_note": {"ko": "오프라인이면 폰에 저장 후 신호가 잡힐 때 자동 전송 (실서비스 시 구현 예정)", "en": "If offline, saved on the phone and sent when signal returns (planned for production)", "mn": "Сүлжээгүй бол утсанд хадгалж, сүлжээ орох үед автоматаар илгээнэ (бодит хувилбарт хийгдэнэ)"},
 "via_sms":      {"ko": "✉️ ② SMS 문자로 신청 (시뮬레이션)", "en": "✉️ ② Request via SMS (simulation)", "mn": "✉️ ② Мессежээр хүсэлт гаргах (жишээ)"},
 "sender":       {"ko": "발신 번호", "en": "Sender number", "mn": "Илгээгчийн дугаар"},
 "process_sms":  {"ko": "문자 수신 처리", "en": "Process SMS", "mn": "Мессеж боловсруулах"},
 "sms_note":     {"ko": "형식: <code>HAY 창고 톤수 이름</code> — 2G 신호만 있어도 가능. 실서비스에서는 통신사 SMS 게이트웨이가 이 입력을 대신합니다.",
                  "en": "Format: <code>HAY warehouse tons name</code> — works with 2G signal only. In production a carrier SMS gateway replaces this input.",
                  "mn": "Формат: <code>HAY агуулах тонн нэр</code> — 2G сүлжээтэй ч болно. Бодит үйлчилгээнд операторын SMS gateway энэ оролтыг орлоно."},
 "recent":       {"ko": "최근 신청", "en": "Recent requests", "mn": "Сүүлийн хүсэлтүүд"},
 "pending":      {"ko": "대기", "en": "Pending", "mn": "Хүлээгдэж байна"},
 "dispatched":   {"ko": "배송요청됨", "en": "Dispatched", "mn": "Хүргэлт хүссэн"},
 "ch_app":       {"ko": "📱 앱", "en": "📱 App", "mn": "📱 Апп"},
 "ch_sms":       {"ko": "✉️ SMS", "en": "✉️ SMS", "mn": "✉️ SMS"},
 "ch_proxy":     {"ko": "🧑‍🌾 대리", "en": "🧑‍🌾 Proxy", "mn": "🧑‍🌾 Төлөөлөл"},
 # 관리자
 "admin_title":  {"ko": "관리자 대시보드", "en": "Admin dashboard", "mn": "Удирдлагын самбар"},
 "admin_sub":    {"ko": "NEMA · 소움 정부용", "en": "for NEMA · soum government", "mn": "ОБЕГ · сумын засаг захиргаанд"},
 "priority":     {"ko": "⚠ 부족 예측 우선순위", "en": "⚠ Shortage priority", "mn": "⚠ Хомсдолын эрэмбэ"},
 "stock":        {"ko": "재고", "en": "Stock", "mn": "Нөөц"},
 "pending_orders":{"ko": "대기 신청", "en": "Pending requests", "mn": "Хүлээгдэж буй хүсэлт"},
 "sensor":       {"ko": "센서", "en": "Sensor", "mn": "Мэдрэгч"},
 "online":       {"ko": "🟢 정상", "en": "🟢 Online", "mn": "🟢 Хэвийн"},
 "offline":      {"ko": "🔴 무응답", "en": "🔴 Offline", "mn": "🔴 Хариугүй"},
 "days":         {"ko": "일", "en": "days", "mn": "хоног"},
 "proxy_title":  {"ko": "🧑‍🌾 ③ 대리 신청 등록", "en": "🧑‍🌾 ③ Proxy request", "mn": "🧑‍🌾 ③ Төлөөлөн хүсэлт гаргах"},
 "proxy_who":    {"ko": "바그장 · 창고 관리자", "en": "bagh leader · warehouse manager", "mn": "багийн дарга · агуулахын менежер"},
 "proxy_note":   {"ko": "무신호 지역 목민이 전화·방문으로 요청한 신청을 대신 입력합니다.", "en": "Enter requests made by phone or in person from herders without signal.", "mn": "Сүлжээгүй малчдын утсаар болон биечлэн өгсөн хүсэлтийг төлөөлж оруулна."},
 "herder_name":  {"ko": "목민 이름", "en": "Herder name", "mn": "Малчны нэр"},
 "register":     {"ko": "대리 등록", "en": "Register", "mn": "Бүртгэх"},
 "deliveries":   {"ko": "🚚 배송 기록", "en": "🚚 Delivery log", "mn": "🚚 Хүргэлтийн бүртгэл"},
 "none_yet":     {"ko": "아직 없음", "en": "None yet", "mn": "Одоогоор байхгүй"},
 "households":   {"ko": "{n}가구", "en": "{n} households", "mn": "{n} өрх"},
 "sensor_api":   {"ko": "🔧 센서 API (ESP32)", "en": "🔧 Sensor API (ESP32)", "mn": "🔧 Мэдрэгчийн API (ESP32)"},
 "api_note":     {"ko": "ESP32가 <code>POST /api/reading</code> 로 <code>{\"warehouse_id\":\"zuunmod_01\",\"distance_cm\":152.3}</code> 를 보내면 자동 기록됩니다.",
                  "en": "ESP32 sends <code>POST /api/reading</code> with <code>{\"warehouse_id\":\"zuunmod_01\",\"distance_cm\":152.3}</code> and it is recorded automatically.",
                  "mn": "ESP32 <code>POST /api/reading</code> руу <code>{\"warehouse_id\":\"zuunmod_01\",\"distance_cm\":152.3}</code> илгээхэд автоматаар бүртгэгдэнэ."},
 "dist_test":    {"ko": "거리(cm) 수동 입력 테스트", "en": "Distance (cm) — manual test", "mn": "Зай (см) — гараар оруулах тест"},
 "send_test":    {"ko": "측정값 전송 테스트", "en": "Send test reading", "mn": "Тестийн хэмжилт илгээх"},
 "reset":        {"ko": "데모 데이터 초기화", "en": "Reset demo data", "mn": "Жишээ өгөгдөл шинэчлэх"},
 "pin_title":    {"ko": "관리자 PIN 입력", "en": "Enter admin PIN", "mn": "Удирдлагын PIN оруулах"},
 "pin_ph":       {"ko": "PIN", "en": "PIN", "mn": "PIN"},
 "pin_btn":      {"ko": "확인", "en": "Enter", "mn": "Нэвтрэх"},
 "pin_bad":      {"ko": "PIN이 올바르지 않습니다", "en": "Wrong PIN", "mn": "PIN буруу байна"},
 "ai_deplete":   {"ko": "소진 예측 날짜", "en": "Predicted run-out date", "mn": "Дуусах таамаглал огноо"},
 "logout":       {"ko": "로그아웃 (사용자 화면으로)", "en": "Log out (back to user view)", "mn": "Гарах (хэрэглэгчийн харагдац руу)"},
 "msg_logout":   {"ko": "로그아웃했어요. 지금은 일반 사용자 화면이에요", "en": "Logged out. You are now seeing the user view", "mn": "Гарлаа. Одоо хэрэглэгчийн харагдац байна"},
 # 운영 모드 전환 (관리자)
 "mode_title":   {"ko": "운영 모드 전환", "en": "Switch operating mode", "mn": "Ажиллах горим солих"},
 "mode_now":     {"ko": "지금 모드", "en": "Current mode", "mn": "Одоогийн горим"},
 "mode_demo":    {"ko": "시연 (가짜 데이터)", "en": "Demo (sample data)", "mn": "Жишээ (хуурамч өгөгдөл)"},
 "mode_live":    {"ko": "실제 운영 (실제 데이터)", "en": "Live (real data)", "mn": "Бодит ажиллагаа (бодит өгөгдөл)"},
 "mode_warn":    {"ko": "바꾸면 모든 사용자의 화면이 바로 바뀝니다. 두 모드의 데이터는 따로 보관되어 서로 지워지지 않아요. 실제 농가가 쓰는 중에는 시연으로 돌리지 마세요.",
                  "en": "Switching changes the screen for every user right away. Data of the two modes is kept separately and never erased by switching. Do not switch to demo while real herders are using the app.",
                  "mn": "Солиход бүх хэрэглэгчийн дэлгэц шууд өөрчлөгдөнө. Хоёр горимын өгөгдөл тусдаа хадгалагддаг тул солиход устахгүй. Бодит малчид ашиглаж байх үед жишээ горим руу бүү шилжүүл."},
 "mode_pin_ph":  {"ko": "관리자 PIN 다시 입력", "en": "Enter the admin PIN again", "mn": "Удирдлагын PIN-ийг дахин оруулах"},
 "mode_confirm_ph": {"ko": "확인을 위해 {w} 라고 입력", "en": "Type {w} to confirm", "mn": "Баталгаажуулахын тулд {w} гэж бичнэ үү"},
 "mode_to_live": {"ko": "실제 운영으로 전환", "en": "Switch to Live", "mn": "Бодит горим руу шилжих"},
 "mode_to_demo": {"ko": "시연 모드로 전환", "en": "Switch to Demo", "mn": "Жишээ горим руу шилжих"},
 "mode_off":     {"ko": "이 서버에서는 전환 버튼을 쓸 수 없어요 (Neon DB와 관리자 PIN이 모두 있어야 해요).", "en": "Switching is not available on this server (needs the Neon database and an admin PIN).", "mn": "Энэ сервер дээр солих боломжгүй (Neon өгөгдлийн сан болон удирдлагын PIN хэрэгтэй)."},
 "mode_bad":     {"ko": "잘못된 요청이에요", "en": "Invalid request", "mn": "Буруу хүсэлт"},
 "mode_confirm_bad": {"ko": "확인 글자가 달라서 취소했어요", "en": "Confirmation text did not match — cancelled", "mn": "Баталгаажуулах үг таарахгүй — цуцлагдлаа"},
 "mode_same":    {"ko": "이미 그 모드예요", "en": "Already in that mode", "mn": "Аль хэдийн тэр горимд байна"},
 "msg_mode_set": {"ko": "✅ 모드를 바꿨어요: {m}", "en": "✅ Mode switched: {m}", "mn": "✅ Горим солигдлоо: {m}"},
 # 등급 · 한파
 "lv_ok":        {"ko": "정상", "en": "Normal", "mn": "Хэвийн"},
 "lv_warn":      {"ko": "주의 — 재보충 준비", "en": "Caution — prepare restock", "mn": "Анхаар — нөөц нөхөхөд бэлтгэ"},
 "lv_danger":    {"ko": "위험 — 즉시 재보충", "en": "Critical — restock now", "mn": "Аюултай — нэн даруй нөхөх"},
 "lv_low":       {"ko": "소비 미미", "en": "Low usage", "mn": "Хэрэглээ бага"},
 "lv_nodata":    {"ko": "측정값 없음", "en": "No reading yet", "mn": "Хэмжилт алга"},
 # 신청 통계 (관리자)
 "st_title":     {"ko": "신청 통계", "en": "Request statistics", "mn": "Хүсэлтийн статистик"},
 "st_sub":       {"ko": "신청 시도(성공·실패)를 기간별로 모아 봐요", "en": "Request attempts (success and failure) by period", "mn": "Хүсэлтийн оролдлогыг (амжилттай/амжилтгүй) хугацаагаар"},
 "st_open":      {"ko": "📈 신청 통계 보기", "en": "📈 Request statistics", "mn": "📈 Хүсэлтийн статистик"},
 "st_back":      {"ko": "← 관리자", "en": "← Admin", "mn": "← Удирдлага"},
 "st_day":       {"ko": "일별", "en": "Daily", "mn": "Өдрөөр"},
 "st_week":      {"ko": "주별", "en": "Weekly", "mn": "7 хоногоор"},
 "st_month":     {"ko": "월별", "en": "Monthly", "mn": "Сараар"},
 "st_attempts":  {"ko": "신청 시도", "en": "Attempts", "mn": "Оролдлого"},
 "st_rate":      {"ko": "성공률", "en": "Success rate", "mn": "Амжилтын хувь"},
 "st_tons":      {"ko": "신청량(성공)", "en": "Requested (ok)", "mn": "Хүссэн (амжилттай)"},
 "st_chart":     {"ko": "기간별 신청 시도", "en": "Attempts by period", "mn": "Хугацаагаар оролдлого"},
 "st_ok":        {"ko": "성공", "en": "OK", "mn": "Амжилттай"},
 "st_fail":      {"ko": "실패", "en": "Failed", "mn": "Амжилтгүй"},
 "st_by_period": {"ko": "기간별", "en": "By period", "mn": "Хугацаагаар"},
 "st_by_wh":     {"ko": "창고별", "en": "By warehouse", "mn": "Агуулахаар"},
 "st_by_ch":     {"ko": "신청 경로별", "en": "By channel", "mn": "Сувгаар"},
 "st_reasons":   {"ko": "실패 사유", "en": "Failure reasons", "mn": "Амжилтгүй болсон шалтгаан"},
 "st_none":      {"ko": "아직 기록이 없어요", "en": "No records yet", "mn": "Одоогоор бүртгэл алга"},
 "st_csv_req":   {"ko": "신청 시도 CSV 내려받기", "en": "Download request attempts (CSV)", "mn": "Хүсэлтийн оролдлого (CSV) татах"},
 "st_csv_orders":{"ko": "신청 내역 CSV 내려받기", "en": "Download orders (CSV)", "mn": "Захиалгын жагсаалт (CSV) татах"},
 "rs_bad_input": {"ko": "입력 오류", "en": "Invalid input", "mn": "Оролт буруу"},
 "rs_wh_short":  {"ko": "재고 부족 (트럭 1대 미만)", "en": "Low stock (below one truck)", "mn": "Нөөц бага (1 машинаас доош)"},
 "rs_over_stock":{"ko": "신청 가능량 초과", "en": "Over the available amount", "mn": "Боломжит хэмжээнээс их"},
 "rs_sms_format":{"ko": "문자 형식 오류", "en": "SMS format error", "mn": "SMS формат буруу"},
 "rs_sms_no_warehouse": {"ko": "문자: 창고를 못 찾음", "en": "SMS: warehouse not found", "mn": "SMS: агуулах олдсонгүй"},
 "rs_sms_number":{"ko": "문자: 톤수 오류", "en": "SMS: invalid tons", "mn": "SMS: тонн буруу"},
 "cold_none":    {"ko": "기온 정보 없음 (기본값)", "en": "No temperature data (default)", "mn": "Температурын мэдээлэл алга (анхдагч)"},
 "cold_extreme": {"ko": "극한파 (−35℃ 이하) → 소비 1.5배", "en": "Extreme cold (≤ −35℃) → usage ×1.5", "mn": "Хэт хүйтэн (−35℃-ээс доош) → хэрэглээ 1.5 дахин"},
 "cold_severe":  {"ko": "강한 한파 (−25℃ 이하) → 소비 1.3배", "en": "Severe cold (≤ −25℃) → usage ×1.3", "mn": "Хүчтэй хүйтэн (−25℃-ээс доош) → хэрэглээ 1.3 дахин"},
 "cold_mild":    {"ko": "한파 (−15℃ 이하) → 소비 1.15배", "en": "Cold (≤ −15℃) → usage ×1.15", "mn": "Хүйтэн (−15℃-ээс доош) → хэрэглээ 1.15 дахин"},
 "cold_normal":  {"ko": "평년 수준", "en": "Normal level", "mn": "Хэвийн түвшин"},
 # 메시지
 "msg_order_ok": {"ko": "✅ 신청 등록 완료: {name} {tons}t → {wh} (신청 가능 잔여 {avail}t)", "en": "✅ Request registered: {name} {tons} t → {wh} ({avail} t still available)", "mn": "✅ Хүсэлт бүртгэгдсэн: {name} {tons} тн → {wh} (хүсэх боломжтой {avail} тн үлдсэн)"},
 "msg_wh_short": {"ko": "❌ {wh} 신청 불가: 재고 {stock}t < 트럭 {n}t — 창고 재보충 전까지 신청을 받지 않습니다", "en": "❌ {wh}: requests closed — stock {stock} t < truck {n} t, reopens after restock", "mn": "❌ {wh}: хүсэлт хаалттай — нөөц {stock} тн < машин {n} тн, нөөц нөхсөний дараа дахин нээгдэнэ"},
 "msg_over_stock":{"ko": "❌ {wh} 신청 불가: 요청 {tons}t > 신청 가능 {avail}t (창고 재고 {stock}t, 대기 {pend}t)", "en": "❌ {wh}: cannot request {tons} t — only {avail} t available (stock {stock} t, pending {pend} t)", "mn": "❌ {wh}: {tons} тн хүсэх боломжгүй — {avail} тн л боломжтой (нөөц {stock} тн, хүлээгдэж буй {pend} тн)"},
 "msg_bad_input":{"ko": "❌ 입력 오류: 이름과 {m}t 이상의 톤수를 입력하세요", "en": "❌ Invalid input: enter a name and at least {m} t", "mn": "❌ Оролт буруу: нэр болон {m} тн-оос дээш тонн оруулна уу"},
 "msg_not_enough":{"ko": "❌ 아직 트럭 {n}t 미달", "en": "❌ Still below truck load {n} t", "mn": "❌ {n} тн-д хүрээгүй байна"},
 "msg_dispatch_short":{"ko": "❌ 배송 불가: 대기 {pend}t > 창고 재고 {stock}t — 재보충 후 배송", "en": "❌ Cannot dispatch: pending {pend} t > stock {stock} t — restock first", "mn": "❌ Хүргэх боломжгүй: хүлээгдэж буй {pend} тн > нөөц {stock} тн — эхлээд нөөц нөхнө"},
 "msg_dispatch": {"ko": "🚚 {wh} 공동배송 요청 완료 ({tons}t, {hh})", "en": "🚚 Shared delivery requested for {wh} ({tons} t, {hh})", "mn": "🚚 {wh} хамтарсан хүргэлт хүссэн ({tons} тн, {hh})"},
 "msg_reading":  {"ko": "📡 측정값 기록: {wh} {d}cm → 재고 {p}%", "en": "📡 Reading saved: {wh} {d} cm → stock {p}%", "mn": "📡 Хэмжилт хадгалагдсан: {wh} {d} см → нөөц {p}%"},
 "msg_sms_err":  {"ko": "❌ SMS 오류: {e}", "en": "❌ SMS error: {e}", "mn": "❌ SMS алдаа: {e}"},
 "msg_sms_ok":   {"ko": "✉️ SMS 접수 → 회신(시뮬레이션): \"{reply}\"", "en": "✉️ SMS received → reply (simulated): \"{reply}\"", "mn": "✉️ SMS хүлээн авсан → хариу (жишээ): \"{reply}\""},
 "sms_reply_ok": {"ko": "[HayLink] {name} {tons}t {wh} 접수. 대기 {pend}/{truck}t", "en": "[HayLink] {name} {tons}t {wh} accepted. Pending {pend}/{truck}t", "mn": "[HayLink] {name} {tons}тн {wh} бүртгэсэн. Хүлээгдэж буй {pend}/{truck}тн"},
 "sms_reply_no": {"ko": "[HayLink] {wh} 재고 부족. 신청 가능 {avail}t", "en": "[HayLink] {wh} low stock. Available {avail}t", "mn": "[HayLink] {wh} нөөц хүрэлцэхгүй. Боломжтой {avail}тн"},
 "msg_consume":  {"ko": "건초 반출 → 재고 {p}%", "en": "Hay removed → stock {p}%", "mn": "Өвс гаргасан → нөөц {p}%"},
 "msg_reset":    {"ko": "데모 데이터 초기화 완료", "en": "Demo data reset", "mn": "Жишээ өгөгдөл шинэчлэгдсэн"},
 "sms_fmt":      {"ko": "형식 오류. 예) HAY zuunmod 2 Bold", "en": "Wrong format. e.g. HAY zuunmod 2 Bold", "mn": "Формат буруу. жишээ нь: HAY zuunmod 2 Bold"},
 "sms_nowh":     {"ko": "'{k}' 창고를 찾을 수 없음", "en": "Warehouse '{k}' not found", "mn": "'{k}' агуулах олдсонгүй"},
 "sms_num":      {"ko": "톤수는 숫자여야 함", "en": "Tons must be a number", "mn": "Тонн нь тоо байх ёстой"},
 "sms_herder":   {"ko": "SMS 목민", "en": "SMS herder", "mn": "SMS малчин"},
 # 내 신청 확인 대화 (이름·전화번호·창고를 차례로 물어봄. 이 대화는 AI에게 보내지 않음)
 "oc_intro":    {"ko": "네, 신청 내역을 확인해 드릴게요 😊\n이름, 전화번호, 신청한 창고를 한 번에 알려 주세요.\n(예: 홍길동 9911 2233 준모드)\n창고: {list}", "en": "Sure, let me check your request 😊\nPlease tell me your name, phone number and warehouse in one message.\n(e.g. Bat 9911 2233 Zuunmod)\nWarehouses: {list}", "mn": "За, захиалгыг тань шалгаж өгье 😊\nНэр, утасны дугаар, захиалсан агуулахаа нэг дор хэлнэ үү.\n(жишээ нь: Бат 9911 2233 Зуунмод)\nАгуулах: {list}"},
 "oc_need":     {"ko": "{what}도 알려 주세요 🙏", "en": "Please also tell me your {what} 🙏", "mn": "Мөн {what} хэлнэ үү 🙏"},
 "oc_l_name":   {"ko": "이름", "en": "name", "mn": "нэр"},
 "oc_l_phone":  {"ko": "전화번호", "en": "phone number", "mn": "утасны дугаар"},
 "oc_l_wh":     {"ko": "신청한 창고 ({list})", "en": "warehouse ({list})", "mn": "агуулах ({list})"},
 "oc_found":     {"ko": "확인했어요! {name}님의 {wh} 신청 내역이에요 👇\n{lines}\n\n대기 중인 신청은 같은 창고 신청이 트럭 1대({truck}t)가 되면 함께 배송 요청돼요.", "en": "Found it! Here are {name}'s requests at {wh} 👇\n{lines}\n\nPending requests are sent together once the requests from one warehouse reach one truck ({truck} t).", "mn": "Шалгалаа! {name}-ийн {wh} дахь захиалга 👇\n{lines}\n\nХүлээгдэж буй захиалгууд нэг ачааны машин ({truck}т) болмогц хамт хүргэгдэнэ."},
 "oc_none":      {"ko": "말씀하신 정보로 신청을 찾지 못했어요 😢\n이름, 전화번호, 창고를 다시 한번 확인해 주세요.\n다시 확인하려면 \"내 주문 확인\"이라고 입력해 주세요.", "en": "I couldn't find a request with that information 😢\nPlease double-check the name, phone number and warehouse.\nTo try again, type \"check my order\".", "mn": "Таны хэлсэн мэдээллээр захиалга олдсонгүй 😢\nНэр, утасны дугаар, агуулахаа дахин нягтална уу.\nДахин шалгахын тулд \"миний захиалга шалгах\" гэж бичнэ үү."},
 "oc_cancel":    {"ko": "알겠어요, 확인을 멈출게요. 궁금한 게 있으면 언제든 물어보세요!", "en": "Okay, I'll stop checking. Ask me anything anytime!", "mn": "За, шалгахаа зогсоолоо. Асуух зүйл байвал хэзээ ч асуугаарай!"},
}

def t(key, **kw):
    lang = getattr(g, "lang", DEFAULT_LANG)
    s = T.get(key, {}).get(lang) or T.get(key, {}).get("ko") or key
    return s.format(**kw) if kw else s

def wh_name(wid):
    w = WH_BY_ID.get(wid)
    return w["name"][g.lang] if w else wid

app = Flask(__name__)

@app.before_request
def pick_lang():
    g.lang = request.cookies.get("lang", DEFAULT_LANG)
    if g.lang not in LANGS: g.lang = DEFAULT_LANG
    g.mode = current_mode()                                   # 이 요청 동안 쓸 시연/운영 모드

@app.context_processor
def inject():
    return {"t": t, "lang": g.lang, "wh_name": wh_name, "demo": is_demo(), "privacy": privacy_on(), "pin_on": bool(ADMIN_PIN), "mode_switch": MODE_SWITCHABLE, "truck": TRUCK_CAPACITY_T,
            "lead": LEAD_DAYS, "bale": HAY_BALE_TON, "order_min": ORDER_MIN_T, "warehouses": WAREHOUSES,
            "horizon": FORECAST_HORIZON_D, "min_orders": MIN_ORDERS_FOR_CYCLE}

def msg_url(path, key, kind="ok", **kw):
    return f"{path}?msg={quote(t(key, **kw))}" + ("&kind=err" if kind == "err" else "")

def admin_ok():
    return not ADMIN_PIN or request.cookies.get("admin_pin") == ADMIN_PIN

def admin_required(f):
    @wraps(f)
    def inner(*a, **k):
        if not admin_ok():
            return render_template("pin.html") if request.method == "GET" else redirect("/admin")
        return f(*a, **k)
    return inner

# ═══════════════════ DB ═══════════════════
# DB 는 q(조회)·x(저장)·transaction(여러 개를 한 번에) 세 통로로만 접근. SQL 은 '?' 자리표시자와 SQLite·PostgreSQL 공통 문법으로 쓰고,
# PostgreSQL 일 때는 아래에서 자동으로 바꿔 줌. 조회 결과는 row["열이름"] 으로 읽음.
if USE_PG:
    try:
        import psycopg
        from psycopg.rows import dict_row
        from psycopg_pool import ConnectionPool
    except ImportError as e:
        raise SystemExit('DATABASE_URL 을 쓰려면  pip install "psycopg[binary]" psycopg-pool  이 필요합니다') from e
    _pools = {}                                   # 스키마 이름 → 연결 풀 (시연 demo / 운영 live 각각)
    _pools_lock = threading.Lock()
    _ready = set()                                # 표 준비가 끝난 스키마
    _ready_lock = threading.Lock()

def _pg_sql(sql):
    return sql.replace("?", "%s")

def _pg_ddl(sql):
    """SQLite 식 표 만들기 문장을 PostgreSQL 용으로"""
    return re.sub(r"\bREAL\b", "DOUBLE PRECISION", sql.replace("INTEGER PRIMARY KEY AUTOINCREMENT", "SERIAL PRIMARY KEY"))

def _get_pool(schema):
    """스키마별 연결 풀 (처음 쓸 때 만듦). 연결을 열어 둔 채 재사용 — 요청마다 새로 연결하면 매번 1초 넘게 걸림"""
    pool = _pools.get(schema)
    if pool is None:
        with _pools_lock:
            pool = _pools.get(schema)
            if pool is None:
                with psycopg.connect(PG_URL, connect_timeout=30, autocommit=True) as boot:     # 시연/운영 분리용 스키마 + 모드 설정 표 준비
                    boot.execute("SELECT pg_advisory_lock(727274)")
                    boot.execute(f"CREATE SCHEMA IF NOT EXISTS {schema}")
                    boot.execute("CREATE TABLE IF NOT EXISTS public.haylink_settings(key TEXT PRIMARY KEY, value TEXT NOT NULL, updated_at TEXT)")
                    boot.execute("SELECT pg_advisory_unlock(727274)")
                pool = ConnectionPool(PG_URL, min_size=1, max_size=4, max_idle=120, open=False,
                                      kwargs={"row_factory": dict_row, "connect_timeout": 30, "options": f"-c search_path={schema}"})
                pool.open(wait=True, timeout=60)
                atexit.register(pool.close)                   # 서버가 꺼질 때 연결을 깔끔하게 닫음
                _pools[schema] = pool
    return pool

# ── 시연/운영 모드 ──  PostgreSQL + PIN 이 있으면 관리자 화면 버튼으로 바꿀 수 있고, 선택한 모드는 DB(public.haylink_settings)에 저장됨.
#    그 밖(SQLite, PIN 없음, 시험용 스키마 지정)에서는 환경변수 HAYLINK_MODE 값으로 고정.
_mode_state = {"v": "demo" if DEMO_MODE else "live", "ts": 0.0}

def current_mode():
    """지금 모드 'demo' | 'live'. 전환 가능한 서버에서는 DB 값을 MODE_TTL_S 초마다 확인"""
    if not MODE_SWITCHABLE: return "demo" if DEMO_MODE else "live"
    if time.time() - _mode_state["ts"] > MODE_TTL_S:
        def run():
            with _get_pool(PG_SCHEMA).connection() as con:
                r = con.execute("SELECT value FROM public.haylink_settings WHERE key = 'mode'").fetchone()
                return r["value"] if r else None
        try:
            v = _pg_retry(run)
            _mode_state["v"] = v if v in ("demo", "live") else ("demo" if DEMO_MODE else "live")   # 저장된 값이 없으면 환경변수 값이 처음 값
        except Exception:
            pass                                              # 읽기에 실패하면 마지막으로 알던 값을 유지
        _mode_state["ts"] = time.time()
    return _mode_state["v"]

def set_mode(mode):
    """모드를 DB에 저장하고 바로 적용 (다른 서버는 최대 MODE_TTL_S 초 안에 따라옴)"""
    assert MODE_SWITCHABLE and mode in ("demo", "live")
    def run():
        with _get_pool(PG_SCHEMA).connection() as con:
            con.execute("INSERT INTO public.haylink_settings(key, value, updated_at) VALUES('mode', %s, %s) "
                        "ON CONFLICT (key) DO UPDATE SET value = EXCLUDED.value, updated_at = EXCLUDED.updated_at", (mode, now_iso()))
    _pg_retry(run)
    _ensure_ready(mode)                                       # 새 모드의 표·시연 데이터 준비
    _mode_state["v"], _mode_state["ts"] = mode, time.time()

def _req_mode():
    """이 요청에서 쓰는 모드 (한 요청 안에서 중간에 바뀌지 않게 요청 시작 때 정한 값)"""
    if has_request_context() and hasattr(g, "mode"): return g.mode
    return current_mode()

def is_demo():
    return _req_mode() == "demo"

def _ensure_ready(schema):
    if schema not in _ready:
        with _ready_lock:
            if schema not in _ready:
                _init_schema(schema)
                _ready.add(schema)

def _active_schema():
    """지금 요청이 쓸 PostgreSQL 스키마 (SQLite 이면 None)"""
    if not USE_PG: return None
    sch = ("live" if _req_mode() == "live" else "demo") if MODE_SWITCHABLE else PG_SCHEMA
    _ensure_ready(sch)
    return sch

def _pg_retry(fn):
    try: return fn()
    except (psycopg.OperationalError, psycopg.InterfaceError):    # 끊긴 연결(Neon 대기 상태 등)이면 새 연결로 한 번 더
        return fn()

class _Tx:
    """한 묶음의 DB 작업: 끝나면 저장, 오류가 나면 모두 되돌림"""
    def __init__(self, con): self.con = con
    def execute(self, sql, args=()):
        return self.con.execute(_pg_sql(sql) if USE_PG else sql, args)
    def executemany(self, sql, rows):
        if USE_PG:
            with self.con.cursor() as cur: cur.executemany(_pg_sql(sql), rows)
        else:
            self.con.executemany(sql, rows)
    def script(self, sql):
        if USE_PG: self.con.execute(_pg_ddl(sql))
        else: self.con.executescript(sql)

@contextmanager
def transaction(schema=None):
    if USE_PG:
        with _get_pool(schema or _active_schema()).connection() as con: yield _Tx(con)
    else:
        con = sqlite3.connect(DB_FILE); con.row_factory = sqlite3.Row
        try:
            yield _Tx(con); con.commit()
        except Exception:
            con.rollback(); raise
        finally:
            con.close()

def q(sql, args=(), one=False):
    if USE_PG:
        sch = _active_schema()
        def run():
            with _get_pool(sch).connection() as con:
                cur = con.execute(_pg_sql(sql), args)
                return cur.fetchone() if one else cur.fetchall()
        return _pg_retry(run)
    con = sqlite3.connect(DB_FILE); con.row_factory = sqlite3.Row
    try:
        cur = con.execute(sql, args)
        return cur.fetchone() if one else cur.fetchall()
    finally:
        con.close()

def x(sql, args=()):
    if USE_PG:
        sch = _active_schema()
        def run():
            with _get_pool(sch).connection() as con: con.execute(_pg_sql(sql), args)
        return _pg_retry(run)
    con = sqlite3.connect(DB_FILE)
    try:
        con.execute(sql, args); con.commit()
    finally:
        con.close()

_cache = {}
def cached_rows(sql, ttl=60):
    """거의 안 바뀌는 설정 표(가격·할증)를 잠깐 기억해 DB 왕복을 줄임"""
    key = (_active_schema(), sql)                             # 시연/운영이 서로 다른 스키마라 구분해서 기억
    hit = _cache.get(key)
    if hit and time.time() - hit[1] < ttl: return hit[0]
    rows = q(sql); _cache[key] = (rows, time.time()); return rows

def now_iso():
    return datetime.datetime.now().isoformat(timespec="seconds")

SCHEMA_SQL = """
    CREATE TABLE IF NOT EXISTS readings(id INTEGER PRIMARY KEY AUTOINCREMENT, warehouse_id TEXT, distance_cm REAL, stock_pct REAL, ts TEXT);
    CREATE TABLE IF NOT EXISTS orders(id INTEGER PRIMARY KEY AUTOINCREMENT, warehouse_id TEXT, herder TEXT, phone TEXT, tons REAL, channel TEXT, status TEXT, ts TEXT);
    CREATE TABLE IF NOT EXISTS deliveries(id INTEGER PRIMARY KEY AUTOINCREMENT, warehouse_id TEXT, total_tons REAL, n_orders INTEGER, ts TEXT);
    CREATE INDEX IF NOT EXISTS idx_readings ON readings(warehouse_id, ts);
    CREATE INDEX IF NOT EXISTS idx_orders ON orders(warehouse_id, status);

    -- 사료 기준 단가 (MNT). 조드 시기 시세를 참고한 추정치이며 공식·확정 가격이 아님
    CREATE TABLE IF NOT EXISTS feed_items(
        item_id INTEGER PRIMARY KEY AUTOINCREMENT, item_code TEXT UNIQUE NOT NULL,
        name_ko TEXT NOT NULL, name_mn TEXT NOT NULL, name_en TEXT NOT NULL,
        unit TEXT NOT NULL,                      -- bale(25kg), bag(25kg), block(30kg)
        normal_price_mnt INTEGER NOT NULL,       -- 가을 평시 가격
        dzud_peak_price_mnt INTEGER NOT NULL,    -- 조드 피크 시세
        subsidized_price_mnt INTEGER NOT NULL);  -- 정부·국제기구 구호 단가
    INSERT INTO feed_items (item_code, name_ko, name_mn, name_en, unit, normal_price_mnt, dzud_peak_price_mnt, subsidized_price_mnt) VALUES
        ('HAY_BALE', '천연 건초 (25kg 묶음)', 'Байгалийн өвс (25кг боодол)', 'Natural Hay Bale (25kg)', 'bale', 6000, 18000, 9000),
        ('WHEAT_BRAN', '밀기울 농축사료 (25kg 포대)', 'Хүчит тэжээл / Хивэг (25кг)', 'Wheat Bran Fodder (25kg)', 'bag', 10000, 32000, 15000),
        ('MINERAL_BLOCK', '미네랄 블록 (30kg)', 'Эрдэс долооц (30кг)', 'Mineral Lick Block (30kg)', 'block', 15000, 35000, 18000)
        ON CONFLICT DO NOTHING;

    -- 날씨 단계별 운송비 할증 배율. min_temp: 이 기온보다 따뜻해야 해당 단계, max_snow_cm: 적설이 이보다 적어야 해당 단계
    CREATE TABLE IF NOT EXISTS weather_delivery_rates(
        rate_id INTEGER PRIMARY KEY AUTOINCREMENT, condition_code TEXT UNIQUE NOT NULL, condition_name_ko TEXT NOT NULL,
        min_temp REAL, max_snow_cm REAL, cost_multiplier REAL NOT NULL, description TEXT);
    INSERT INTO weather_delivery_rates (condition_code, condition_name_ko, min_temp, max_snow_cm, cost_multiplier, description) VALUES
        ('NORMAL', '정상 운송', -15.0, 5.0, 1.0, '평시 초원 도로 운행 가능'),
        ('WARNING', '조드 주의 (한파/결빙)', -25.0, 10.0, 1.3, '영하 15~25도 한파, 디젤 결빙 위험 및 원거리 60~70% 운임 상승 반영'),
        ('CRITICAL', '조드 경보 (폭설/고립)', -35.0, 15.0, 1.8, '적설량 10cm 이상, 4WD 특수 트럭 투입 및 도로 통제'),
        ('EMERGENCY', '조드 비상재난 (도로 전면통제)', -50.0, 999.0, 2.5, '제설차량 동반 및 비상 수송 단계')
        ON CONFLICT DO NOTHING;

    -- 신청 시도 기록: 성공·실패 모두. reason = ok / bad_input / wh_short / over_stock / sms_format / sms_no_warehouse / sms_number
    CREATE TABLE IF NOT EXISTS request_log(
        id INTEGER PRIMARY KEY AUTOINCREMENT, ts TEXT NOT NULL, warehouse_id TEXT, herder TEXT, phone TEXT, tons REAL,
        channel TEXT, ok INTEGER NOT NULL, reason TEXT, stock_t REAL, avail_t REAL, pending_t REAL, lang TEXT, raw TEXT);
    CREATE INDEX IF NOT EXISTS idx_request_log ON request_log(ts);
"""

def _init_schema(schema):
    """표 만들기 + (시연 데이터 칸이고 데이터가 비었으면) 시연 데이터 넣기. 서버가 여러 개 동시에 켜져도 한 번만 되도록 PostgreSQL 에서는 잠금을 씀"""
    seed = (schema == "demo") if MODE_SWITCHABLE else DEMO_MODE
    with transaction(schema) as tx:
        if USE_PG: tx.execute("SELECT pg_advisory_xact_lock(727274)")
        tx.script(SCHEMA_SQL)
        if seed and tx.execute("SELECT COUNT(*) AS c FROM readings").fetchone()["c"] == 0:
            seed_demo(tx)

def init_db():
    _init_schema(_active_schema())

def reset_demo_db():
    """시연 데이터를 지우고 다시 만듦. PostgreSQL 에서는 현재 스키마(demo)의 데이터 표만 비워서, 가격·할증 표와 운영(live) 데이터는 그대로 둠"""
    sch = _active_schema()
    if USE_PG:
        with transaction(sch) as tx: tx.execute("TRUNCATE readings, orders, deliveries, request_log RESTART IDENTITY")
    elif os.path.exists(DB_FILE):
        os.remove(DB_FILE)
    _init_schema(sch)

# 시연 시나리오: 창고별 현재 재고(%)와 농가 목록. 날짜는 초기화한 시점 기준으로 만들어져 언제 초기화해도 같은 상황이 재현됨.
# 농가 = (이름, 전화, 1회 주문량 t, 주문 주기 일, 다음 주문까지 남은 일, 지금 대기 중인 신청량 t, 신청 경로)
DEMO_SCENARIOS = {
    "zuunmod_01": {"stock_pct": 30, "herders": [          # 위험: 대기 신청 + Bold·Tsetseg 주문이 겹쳐 이틀 뒤 매진
        ("Batbayar", "9911-0001", 1.5, 9, 0, 1.5, "app"), ("Oyunaa", "9911-0002", 2.0, 11, 0, 2.0, "sms"),
        ("Bold", "9911-0004", 4.0, 12, 1, 0, "app"), ("Tsetseg", "9911-0005", 5.0, 14, 2, 0, "proxy"),
        ("Munkh", "9911-0006", 1.5, 8, 3, 0, "app"), ("Naran", "9911-0007", 2.0, 10, 4, 0, "sms"),
        ("Sarnai", "9911-0008", 1.0, 7, 5, 0, "app"), ("Enkh", "9911-0009", 2.5, 15, 6, 0, "proxy")]},
    "altanbulag_01": {"stock_pct": 40, "herders": [       # 주의: 엿새쯤 뒤 매진
        ("Ganbold", "9911-0020", 6.0, 15, 2, 0, "app"), ("Otgon", "9911-0021", 4.0, 12, 4, 0, "proxy"),
        ("Bayar", "9911-0022", 3.0, 10, 5, 0, "sms"), ("Saran", "9911-0023", 2.0, 8, 1, 0, "app"),
        ("Temuulen", "9911-0024", 1.5, 7, 3, 0, "app"), ("Altan", "9911-0025", 2.5, 9, 6, 0, "sms")]},
    "bayan_01": {"stock_pct": 70, "herders": [            # 안정: 한 달 넘게 여유
        ("Dorj", "9911-0003", 1.0, 12, 0, 1.0, "proxy"), ("Khulan", "9911-0010", 1.5, 14, 5, 0, "app"),
        ("Erdene", "9911-0011", 1.0, 10, 7, 0, "sms"), ("Gerel", "9911-0012", 2.0, 20, 9, 0, "app"),
        ("Lkhagva", "9911-0013", 1.0, 15, 11, 0, "proxy")]},
    "sergelen_01": {"stock_pct": 4, "herders": [          # 이미 부족: 재고가 트럭 1대 미만이라 신청 차단, 오늘 주문도 못 채움
        ("Zorig", "9911-0030", 1.5, 10, 0, 0, "app"), ("Narantuya", "9911-0031", 1.0, 8, 1, 0, "sms"),
        ("Bat-Erdene", "9911-0032", 2.0, 12, 2, 0, "proxy"), ("Solongo", "9911-0033", 1.0, 9, 3, 0, "app"),
        ("Tumur", "9911-0034", 1.5, 14, 5, 0, "app")]},
}

def seed_demo(tx):
    """시연용 가짜 데이터 (시드 고정). 창고마다 다른 상황으로 '농가 주문 기반 매진 예측'을 보여 줌:
       준모드=곧 매진(위험), 알탄불락=며칠 뒤 매진(주의), 바양=여유(안정), 세르겔렌=이미 재고 부족(신청 차단).
       ① 농가별 과거 주문 기록 8회 ② 그 소비 속도에 맞춰 줄어든 14일치 재고 측정값(6시간 간격) ③ 지금 대기 중인 신청"""
    random.seed(42)
    now = datetime.datetime.now(); today = now.date()

    readings, orders, logs = [], [], []                                            # 모아 두었다가 한꺼번에 저장 (외부 DB 왕복을 줄임)

    def seed_log(ts, wid, herder, phone, tons, channel, ok, reason, raw=None):     # 신청 시도 기록 (통계 화면 시연용)
        logs.append((ts, wid, herder, phone, tons, channel, 1 if ok else 0, reason, "ko", raw))

    for w in WAREHOUSES:
        sc = DEMO_SCENARIOS[w["id"]]
        per_day = sum(h[2] / h[3] for h in sc["herders"]) / w["capacity_ton"] * 100   # 농가 주문 속도를 재고 감소율(%/일)로
        for step in range(14 * 4):
            age_days = (14 * 4 - 1 - step) / 4                                      # 마지막 측정값 = 지금
            noise = 0.0 if age_days == 0 else random.uniform(-0.8, 0.8)
            pct = max(2, sc["stock_pct"] + per_day * age_days + noise)
            ts = now - datetime.timedelta(days=age_days)
            readings.append((w["id"], round(pct_to_distance(w, pct), 1), round(pct, 1), ts.isoformat(timespec="seconds")))
        for name, phone, tons, interval, due_in, pending, channel in sc["herders"]:
            # 마지막으로 받아 간 날: 대기 신청이 있으면 한 주기 전, 없으면 '다음 주문일 - 주기'
            d = today - datetime.timedelta(days=interval) if pending else today + datetime.timedelta(days=due_in - interval)
            gaps = [1, -1, 0, 0, 0, 0]; random.shuffle(gaps)                      # 합이 0 → 평균 주기가 정확히 interval
            for k in range(8):
                qty = max(0.5, round(tons * random.uniform(0.85, 1.15), 1))
                order_ts = datetime.datetime.combine(d, datetime.time(9, 0)).isoformat(timespec="seconds")
                orders.append((w["id"], name, phone, qty, channel, "dispatched", order_ts))
                seed_log(order_ts, w["id"], name, phone, qty, channel, True, "ok")
                d -= datetime.timedelta(days=interval + (gaps[k] if k < len(gaps) else 0))
            if pending:
                orders.append((w["id"], name, phone, pending, channel, "pending", now.isoformat(timespec="seconds")))
                seed_log(now.isoformat(timespec="seconds"), w["id"], name, phone, pending, channel, True, "ok")
    # 실패한 신청 시도: 창고 상황에 맞는 사유 (세르겔렌은 재고 부족으로 막힌 시도가 많음)
    fail_plan = {"zuunmod_01": [("over_stock", 6), ("bad_input", 3)], "altanbulag_01": [("over_stock", 4), ("bad_input", 2)],
                 "bayan_01": [("bad_input", 3)], "sergelen_01": [("wh_short", 14), ("over_stock", 2)]}
    for w in WAREHOUSES:
        names = [h[0] for h in DEMO_SCENARIOS[w["id"]]["herders"]]
        for reason, n in fail_plan[w["id"]]:
            for _ in range(n):
                ts = (now - datetime.timedelta(days=random.uniform(0, 45))).isoformat(timespec="seconds")
                seed_log(ts, w["id"], random.choice(names), "", round(random.uniform(0.5, 6.0), 1), random.choice(["app", "app", "sms", "proxy"]), False, reason)
    for _ in range(4):
        seed_log((now - datetime.timedelta(days=random.uniform(0, 45))).isoformat(timespec="seconds"), None, None, "", None, "sms", False, "sms_format", raw="haylink 2 Bold")
    tx.executemany("INSERT INTO readings(warehouse_id, distance_cm, stock_pct, ts) VALUES(?,?,?,?)", readings)
    tx.executemany("INSERT INTO orders(warehouse_id, herder, phone, tons, channel, status, ts) VALUES(?,?,?,?,?,?,?)", orders)
    tx.executemany("INSERT INTO request_log(ts, warehouse_id, herder, phone, tons, channel, ok, reason, lang, raw) VALUES(?,?,?,?,?,?,?,?,?,?)", logs)

# ═══════════════════ 계산 ═══════════════════
def distance_to_pct(w, d):
    return max(0.0, min(100.0, (w["d_empty_cm"] - d) / (w["d_empty_cm"] - w["d_full_cm"]) * 100))

def pct_to_distance(w, pct):
    return w["d_empty_cm"] - pct / 100 * (w["d_empty_cm"] - w["d_full_cm"])

def record_reading(w, dist=None, pct=None):
    """거리(cm) 또는 재고(%) 중 하나로 측정값 기록"""
    if dist is None: dist = pct_to_distance(w, pct)
    if pct is None:  pct = distance_to_pct(w, dist)
    x("INSERT INTO readings(warehouse_id, distance_cm, stock_pct, ts) VALUES(?,?,?,?)", (w["id"], round(dist, 1), round(pct, 1), now_iso()))
    return round(pct, 1)

def latest_reading(wid):
    return q("SELECT * FROM readings WHERE warehouse_id=? ORDER BY ts DESC LIMIT 1", (wid,), one=True)

def readings_last_days(wid, days=7):
    since = (datetime.datetime.now() - datetime.timedelta(days=days)).isoformat()
    return q("SELECT * FROM readings WHERE warehouse_id=? AND ts>=? ORDER BY ts", (wid, since))

def rows_since_last_refill(rows):
    """측정 간 재고가 REFILL_JUMP_PCT 이상 늘어난 지점(입고) 이후만 반환"""
    cut = 0
    for i in range(1, len(rows)):
        if rows[i]["stock_pct"] - rows[i - 1]["stock_pct"] >= REFILL_JUMP_PCT: cut = i
    return rows[cut:], cut > 0

def linear_slope(xs, ys):
    n = len(xs)
    if n < 2: return 0.0
    mx, my = sum(xs) / n, sum(ys) / n
    sxx = sum((x - mx) ** 2 for x in xs)
    return 0.0 if sxx == 0 else sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sxx

_temp_cache = {}   # (lat,lon) → (value, fetched_at)
def fetch_min_temp(lat, lon):
    key = (round(lat, 1), round(lon, 1)); now = datetime.datetime.now()
    hit = _temp_cache.get(key)
    if hit and (now - hit[1]).total_seconds() < TEMP_TTL_S: return hit[0]
    url = (f"https://api.open-meteo.com/v1/forecast?latitude={lat}&longitude={lon}"
           f"&daily=temperature_2m_min&forecast_days=7&timezone=Asia%2FUlaanbaatar")
    try:
        with urllib.request.urlopen(url, timeout=2) as res:
            temps = [v for v in json.loads(res.read())["daily"]["temperature_2m_min"] if v is not None]
        val = round(sum(temps) / len(temps), 1) if temps else None
    except Exception:
        val = None
    _temp_cache[key] = (val, now); return val

_weather_cache = {}   # (lat,lon) → (value, fetched_at)
def fetch_current_weather(lat, lon):
    """Open-Meteo 에서 현재 기온(℃)·적설 깊이(cm)를 가져옴. 모델 계산값이라 실제 초원과 차이 가능.
       실패하면 None (실패도 5분간 기억해서 서버가 느려지지 않게 함)"""
    key = (round(lat, 2), round(lon, 2)); now = datetime.datetime.now()
    hit = _weather_cache.get(key)
    if hit and (now - hit[1]).total_seconds() < (WEATHER_TTL_S if hit[0] else 300): return hit[0]
    url = (f"https://api.open-meteo.com/v1/forecast?latitude={lat}&longitude={lon}"
           f"&current=temperature_2m,snow_depth&timezone=Asia%2FUlaanbaatar")
    try:
        with urllib.request.urlopen(url, timeout=2) as res:
            cur = json.loads(res.read())["current"]
        val = {"temp_c": round(cur["temperature_2m"], 1), "snow_cm": round((cur.get("snow_depth") or 0) * 100, 1), "time": cur["time"]}
    except Exception:
        val = None
    _weather_cache[key] = (val, now); return val

def cold_factor(tm):
    if tm is None:  return 1.0, "cold_none"
    if tm <= -35:   return 1.5, "cold_extreme"
    if tm <= -25:   return 1.3, "cold_severe"
    if tm <= -15:   return 1.15, "cold_mild"
    return 1.0, "cold_normal"

def privacy_on():
    """농가별 신청 내역을 숨기고 예측 날짜만 보여 줄지.
       PIN 이 있는 서버: 관리자(PIN 로그인)가 아닌 모든 사람(시연 모드 포함). PIN 이 없는 서버: 관리자를 가릴 수 없으니 실제 운영 모드에서만"""
    if ADMIN_PIN: return not (has_request_context() and admin_ok())
    return not is_demo()

def herder_cycles(wid):
    """농가별 주문 습관. 농가 구분은 전화번호(없으면 이름). 주문 기록이 MIN_ORDERS_FOR_CYCLE 회 이상이면
       평균 주문량(최근 4회)·평균 주기(최근 6간격, 일)·다음 예상 주문일을 계산"""
    today = datetime.date.today(); groups = {}
    for r in q("SELECT herder, phone, tons, status, ts FROM orders WHERE warehouse_id=? ORDER BY ts", (wid,)):
        key = (r["phone"] or "").strip() or r["herder"].strip().lower()
        g = groups.setdefault(key, {"name": r["herder"].strip(), "orders": []})
        g["orders"].append((datetime.datetime.fromisoformat(r["ts"]).date(), float(r["tons"]), r["status"]))
    out = []
    for g in groups.values():
        orders = g["orders"]; dates = [o[0] for o in orders]
        pending = round(sum(o[1] for o in orders if o[2] == "pending"), 1)
        gaps = [(b - a).days for a, b in zip(dates, dates[1:]) if (b - a).days > 0][-6:]
        h = {"name": g["name"], "n_orders": len(orders), "pending_t": pending, "avg_t": None, "interval_d": None, "next_date": None}
        if len(orders) >= MIN_ORDERS_FOR_CYCLE and gaps:
            h["interval_d"] = max(1, round(sum(gaps) / len(gaps)))
            h["avg_t"] = round(sum(o[1] for o in orders[-4:]) / len(orders[-4:]), 1)
            # 대기 신청이 있으면 그게 이번 주문 → 다음은 한 주기 뒤. 예정일이 지났으면 '오늘'로 봄
            step = datetime.timedelta(days=h["interval_d"])
            h["next_date"] = today + step if pending else max(today, dates[-1] + step)
        out.append(h)
    return out

def order_forecast(w, stock_t):
    """[핵심] 농가별 주문 습관으로 앞으로 FORECAST_HORIZON_D 일의 예상 주문표를 만들고,
       현재 재고에서 날짜순으로 빼 가며 '재고 0 도달(매진)'과 '트럭 1대 미만(신청 차단)' 시점을 찾음.
       대기 중인 신청은 오늘 나갈 양으로 봄. 날짜는 화면용 'MM/DD' 문자열로 반환"""
    today = datetime.date.today(); end = today + datetime.timedelta(days=FORECAST_HORIZON_D)
    herders = herder_cycles(w["id"]); events = []
    for h in herders:
        if h["pending_t"]: events.append((today, h["name"], h["pending_t"]))
        if h["interval_d"]:
            d = h["next_date"]
            while d <= end:
                events.append((d, h["name"], h["avg_t"])); d += datetime.timedelta(days=h["interval_d"])
    events.sort(key=lambda e: (e[0], e[1]))
    left = stock_t; stockout = None; timeline = []
    blocked_now = stock_t < TRUCK_CAPACITY_T
    block = today if blocked_now else None
    for d, name, tons in events:
        if stockout is not None and d > stockout: break
        left -= tons
        if block is None and left < TRUCK_CAPACITY_T: block = d
        if stockout is None and left <= 1e-9: stockout = d
        timeline.append({"d": d, "name": name, "tons": tons, "left": round(max(left, 0.0), 1), "short": left <= 1e-9})
    fmt = lambda d: d.strftime("%m/%d") if d else None
    herders.sort(key=lambda h: (h["next_date"] is None, h["next_date"] or today, h["name"]))
    hide = privacy_on()          # 실제 운영 모드의 일반 사용자에게는 누가 언제 얼마를 신청했는지(개인별 내역)를 주지 않고, 예측 결과(매진·차단 날짜)만 줌
    return {
        "n_herders": len(herders), "n_used": sum(1 for h in herders if h["interval_d"]),
        "has_data": any(h["interval_d"] for h in herders),          # 주기를 아는 농가가 한 곳도 없으면 예측 근거 없음
        "stockout_date": fmt(stockout), "days": (stockout - today).days if stockout else None,
        "cause": [] if hide else [e["name"] for e in timeline if e["d"] == stockout],
        "block_date": fmt(block), "blocked_now": blocked_now,
        "timeline": [] if hide else [{"date": fmt(e["d"]), "name": e["name"], "tons": e["tons"], "left": e["left"], "short": e["short"]} for e in timeline[:10]],
        "herders": [] if hide else [{"name": h["name"], "avg_t": h["avg_t"], "interval_d": h["interval_d"], "next": fmt(h["next_date"]) or "-",
                                     "n_orders": h["n_orders"], "pending_t": h["pending_t"]} for h in herders],
    }

def empty_forecast():
    """측정값이 없어 예측할 수 없을 때의 빈 결과 (order_forecast 와 같은 모양)"""
    return {"n_herders": 0, "n_used": 0, "has_data": False, "stockout_date": None, "days": None, "cause": [],
            "block_date": None, "blocked_now": False, "timeline": [], "herders": []}

def predict(w):
    rows, refilled = rows_since_last_refill(readings_last_days(w["id"], 7))
    last = latest_reading(w["id"])
    cur_pct = float(last["stock_pct"]) if last else 0.0
    if len(rows) >= 2:
        t0 = datetime.datetime.fromisoformat(rows[0]["ts"])
        xs = [(datetime.datetime.fromisoformat(r["ts"]) - t0).total_seconds() / 86400 for r in rows]
        slope = linear_slope(xs, [r["stock_pct"] for r in rows])
    else:
        slope = 0.0
    per_day = max(0.0, -slope)
    temp = fetch_min_temp(w["lat"], w["lon"]); factor, factor_key = cold_factor(temp)
    days_base = cur_pct / per_day if per_day > 0.05 else None
    days_cold = days_base / factor if days_base is not None else None
    days_use = days_cold
    source = "sensor" if days_use is not None else None
    fc = order_forecast(w, cur_pct / 100 * w["capacity_ton"]) if last else empty_forecast()
    if fc["days"] is not None and (days_use is None or fc["days"] < days_use):   # 센서 추세·농가 주문 중 빠른 날짜 하나만 사용
        days_use, source = float(fc["days"]), "orders"
    if days_use is None:            level, level_key = "ok", "lv_low"
    elif days_use <= LEAD_DAYS:     level, level_key = "danger", "lv_danger"
    elif days_use <= LEAD_DAYS + 4: level, level_key = "warn", "lv_warn"
    else:                           level, level_key = "ok", "lv_ok"
    if cur_pct <= 5 and level != "danger":  # 잔량 자체가 바닥이면 소비 속도와 무관하게 위험
        level, level_key = "danger", "lv_danger"
    if last is None:  # 센서 측정값이 아직 없음 (운영 시작 직후) → 재고 0% 위험으로 오해하지 않게
        level, level_key = "ok", "lv_nodata"
    today = datetime.date.today(); has = days_use is not None
    return {
        "cur_pct": round(cur_pct, 1), "cur_ton": round(cur_pct / 100 * w["capacity_ton"], 1),
        "per_day": round(per_day, 2), "temp_min": temp, "factor": factor, "factor_key": factor_key, "refilled": refilled,
        "days_base": round(days_base, 1) if days_base is not None else None,
        "days_cold": round(days_cold, 1) if days_cold is not None else None,
        "days_use": round(days_use, 1) if has else None,
        "deplete_date": (today + datetime.timedelta(days=days_use)).strftime("%m/%d") if has else "-",
        "reorder_date": (today + datetime.timedelta(days=max(0, days_use - LEAD_DAYS))).strftime("%m/%d") if has else "-",
        "level": level, "level_key": level_key, "stockout_source": source, "order_fc": fc,
        "last_ts": last["ts"].replace("T", " ") if last else "-",
        "sensor_ok": bool(last) and (datetime.datetime.now() - datetime.datetime.fromisoformat(last["ts"])) < datetime.timedelta(hours=12),
    }

def pending_tons(wid):
    r = q("SELECT COALESCE(SUM(tons),0) s, COUNT(*) n FROM orders WHERE warehouse_id=? AND status='pending'", (wid,), one=True)
    return float(r["s"]), int(r["n"])

def availability(w, p=None):
    """[핵심] 창고 재고 대비 신청/배송 가능 여부
       truck_possible = 재고 ≥ 트럭 1대          → 아니면 신청·배송 모두 불가
       avail          = 재고(t) − 대기 신청(t)   → 이 범위 안에서만 새 신청 허용
       can_dispatch   = 대기 ≥ 트럭 1대 AND 대기 ≤ 재고"""
    p = p or predict(w)
    pend, n = pending_tons(w["id"])
    stock = p["cur_ton"]
    truck_possible = stock >= TRUCK_CAPACITY_T
    # 재고가 트럭 1대 분량 미만이면 배송 자체가 불가 → 신청도 0t (재보충 전까지 차단)
    avail = max(0.0, stock - pend) if truck_possible else 0.0
    return {"stock": stock, "pend": round(pend, 1), "n": n, "avail": round(avail, 1),
            "truck_possible": truck_possible,
            "can_dispatch": truck_possible and pend >= TRUCK_CAPACITY_T and pend <= stock + 1e-9}

def weather_level(temp_celsius, snow_depth_cm=None):
    """기온·적설량으로 날씨 단계와 운송비 할증 배율을 구함 (기준은 weather_delivery_rates 표).
       '기온이 min_temp 보다 높고 적설이 max_snow_cm 보다 적은' 첫 단계. 모두 넘으면 가장 높은 단계. 값이 None 이면 그 조건은 무시."""
    rows = cached_rows("SELECT condition_code, min_temp, max_snow_cm, cost_multiplier FROM weather_delivery_rates ORDER BY cost_multiplier")
    if not rows: return "NORMAL", 1.0
    for r in rows:
        if ((temp_celsius is None or r["min_temp"] is None or temp_celsius > r["min_temp"])
                and (snow_depth_cm is None or r["max_snow_cm"] is None or snow_depth_cm < r["max_snow_cm"])):
            return r["condition_code"], r["cost_multiplier"]
    return rows[-1]["condition_code"], rows[-1]["cost_multiplier"]

def delivery_weather(w, p=None):
    """창고 지역의 배송 날씨 단계. 현재 기온·적설(실시간)을 우선 쓰고, 못 가져오면 7일 예보 최저기온으로 대체"""
    cur = fetch_current_weather(w["lat"], w["lon"])
    if cur:
        cond, mult = weather_level(cur["temp_c"], cur["snow_cm"])
        return {"condition": cond, "multiplier": mult, "temp_c": cur["temp_c"], "snow_cm": cur["snow_cm"], "source": "current"}
    p = p or predict(w)
    cond, mult = weather_level(p["temp_min"])
    return {"condition": cond, "multiplier": mult, "temp_c": p["temp_min"], "snow_cm": None, "source": "forecast"}

def calculate_delivery_cost(distance_km, temp_celsius, snow_depth_cm, herder_count=1):
    """거리·기온·적설량·공동배송 가구 수로 배송비(MNT)와 가구당 분담금을 계산 (모두 추정치).
       총액 = (기본 운임 + 거리 × km당 운임) × 날씨 할증 배율,  가구당 = 총액 ÷ 가구 수"""
    condition, multiplier = weather_level(temp_celsius, snow_depth_cm)
    raw_total_cost = (BASE_FARE_MNT + max(0.0, float(distance_km)) * PER_KM_FARE_MNT) * multiplier
    per_herder_cost = raw_total_cost / max(1, int(herder_count))
    return {
        "condition": condition,
        "multiplier": multiplier,
        "total_delivery_cost_mnt": round(raw_total_cost),
        "per_herder_cost_mnt": round(per_herder_cost),
        "savings_per_herder_mnt": round(raw_total_cost - per_herder_cost),
    }

def log_request(ok, reason, wid=None, herder=None, phone=None, tons=None, channel=None, stock=None, avail=None, pend=None, raw=None):
    """신청 시도(성공·실패 모두)를 request_log 에 기록. 기록이 실패해도 신청 처리는 막지 않음"""
    try:
        x("INSERT INTO request_log(ts, warehouse_id, herder, phone, tons, channel, ok, reason, stock_t, avail_t, pending_t, lang, raw) "
          "VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?)",
          (now_iso(), (str(wid)[:40] if wid else None), (herder or None) and str(herder)[:60], (phone or None) and str(phone)[:30], tons,
           channel, 1 if ok else 0, reason, stock, avail, pend, getattr(g, "lang", None), (raw or None) and str(raw)[:300]))
    except Exception as e:
        print("request_log error:", e)

def try_add_order(wid, herder, phone, tons, channel):
    """검증 후 신청 등록. (ok, msg_key, kwargs) 반환. 앱·SMS·대리 3채널이 모두 이 함수를 거침. 성공·실패 모두 request_log 에 남김."""
    w = WH_BY_ID.get(wid)
    herder = (herder or "").strip()[:60]
    phone = (phone or "").strip()[:30]
    try: tons = round(float(tons), 1)
    except (TypeError, ValueError): tons = 0.0
    if not w or not herder or tons < ORDER_MIN_T:
        log_request(False, "bad_input", wid, herder, phone, tons, channel)
        return False, "msg_bad_input", {"m": ORDER_MIN_T}
    a = availability(w)
    seen = {"stock": a["stock"], "avail": a["avail"], "pend": a["pend"]}
    if not a["truck_possible"]:
        log_request(False, "wh_short", wid, herder, phone, tons, channel, **seen)
        return False, "msg_wh_short", {"wh": wh_name(wid), "stock": a["stock"], "n": TRUCK_CAPACITY_T, "avail": 0.0}
    if tons > a["avail"] + 1e-9:
        log_request(False, "over_stock", wid, herder, phone, tons, channel, **seen)
        return False, "msg_over_stock", {"wh": wh_name(wid), "tons": tons, "avail": a["avail"], "stock": a["stock"], "pend": a["pend"]}
    x("INSERT INTO orders(warehouse_id, herder, phone, tons, channel, status, ts) VALUES(?,?,?,?,?,?,?)", (wid, herder, phone, tons, channel, "pending", now_iso()))
    log_request(True, "ok", wid, herder, phone, tons, channel, **seen)
    return True, "msg_order_ok", {"name": herder, "tons": tons, "wh": wh_name(wid), "avail": round(a["avail"] - tons, 1)}

def request_stats(period="day"):
    """신청 시도(request_log)를 일(30일)·주(12주)·월(12개월) 단위로 모아 시도·성공·실패·신청량(성공 건)과
       창고별·경로별·실패 사유별 합계를 계산. 날짜 묶기는 파이썬에서 해서 DB 종류와 무관하게 동작"""
    today = datetime.date.today()
    if period == "week":
        monday = today - datetime.timedelta(days=today.weekday())
        keys = [(monday - datetime.timedelta(weeks=i)).isoformat() for i in range(11, -1, -1)]
    elif period == "month":
        keys = []
        for i in range(11, -1, -1):
            m = today.month - i; keys.append(f"{today.year + (m - 1) // 12:04d}-{(m - 1) % 12 + 1:02d}")
    else:
        period = "day"; keys = [(today - datetime.timedelta(days=i)).isoformat() for i in range(29, -1, -1)]

    def bucket(ts):
        if period == "month": return ts[:7]
        if period == "day": return ts[:10]
        d = datetime.date.fromisoformat(ts[:10]); return (d - datetime.timedelta(days=d.weekday())).isoformat()

    def label(k):
        return k if period == "month" else k[5:].replace("-", "/") + ("~" if period == "week" else "")

    rows = q("SELECT ts, warehouse_id, tons, channel, ok, reason FROM request_log WHERE ts>=? ORDER BY ts",
             (keys[0] + ("-01" if period == "month" else ""),))
    new = lambda: {"attempts": 0, "ok": 0, "fail": 0, "tons": 0.0}
    buckets = {k: {"label": label(k), **new()} for k in keys}; total = new()
    by_wh, by_ch, reasons = {}, {}, {}
    for r in rows:
        b = buckets.get(bucket(r["ts"]))
        if b is None: continue
        ok = bool(r["ok"]); tons = float(r["tons"] or 0) if ok else 0.0
        for acc in (b, total, by_wh.setdefault(r["warehouse_id"] or "-", new()), by_ch.setdefault(r["channel"] or "-", new())):
            acc["attempts"] += 1; acc["ok" if ok else "fail"] += 1; acc["tons"] = round(acc["tons"] + tons, 1)
        if not ok: reasons[r["reason"] or "-"] = reasons.get(r["reason"] or "-", 0) + 1
    ch_label = {"app": "ch_app", "sms": "ch_sms", "proxy": "ch_proxy"}
    return {
        "period": period, "buckets": list(buckets.values()), "total": total,
        "rate": round(total["ok"] / total["attempts"] * 100) if total["attempts"] else 0,
        "by_wh": sorted(({"key": k, **v} for k, v in by_wh.items()), key=lambda r: -r["attempts"]),
        "by_ch": sorted(({"key": k, "label_key": ch_label.get(k, k), **v} for k, v in by_ch.items()), key=lambda r: -r["attempts"]),
        "reasons": sorted(({"key": k, "n": n} for k, n in reasons.items()), key=lambda r: -r["n"]),
    }

def svg_bars(buckets, width=440, height=160):
    """기간별 신청 시도 막대 그래프 (초록=성공, 빨강=실패)"""
    pad = 24; n = len(buckets); top = max(1, max(b["attempts"] for b in buckets))
    slot = (width - 2 * pad) / n; bw = slot * 0.7; base = height - pad; scale = (height - 2 * pad) / top; bars = ""
    for i, b in enumerate(buckets):
        xx = pad + i * slot + (slot - bw) / 2; h_ok = b["ok"] * scale; h_fail = b["fail"] * scale
        bars += f'<rect x="{xx:.1f}" y="{base - h_ok:.1f}" width="{bw:.1f}" height="{h_ok:.1f}" fill="#43a047"/>'
        bars += f'<rect x="{xx:.1f}" y="{base - h_ok - h_fail:.1f}" width="{bw:.1f}" height="{h_fail:.1f}" fill="#e53935"/>'
    return (f'<svg viewBox="0 0 {width} {height}" style="width:100%;display:block">'
            f'<line x1="{pad}" y1="{base}" x2="{width - pad}" y2="{base}" stroke="#d5dad3"/>'
            f'<text x="2" y="{pad - 8}" font-size="10" fill="#8a958c">{top}</text>{bars}'
            f'<text x="{pad}" y="{height - 6}" font-size="10" fill="#8a958c">{buckets[0]["label"]}</text>'
            f'<text x="{width - pad - 40}" y="{height - 6}" font-size="10" fill="#8a958c">{buckets[-1]["label"]}</text></svg>')

def csv_safe(v):
    """엑셀에서 열 때 '=' '+' '-' '@' 로 시작하는 글자가 수식으로 실행되지 않게 앞에 작은따옴표를 붙임"""
    return "'" + v if isinstance(v, str) and v[:1] in ("=", "+", "-", "@") else v

def csv_response(filename, header, rows):
    buf = io.StringIO(); buf.write("﻿")        # 엑셀에서 한글이 깨지지 않게 BOM
    wr = csv.writer(buf); wr.writerow(header)
    for r in rows: wr.writerow([csv_safe(v) for v in r])
    return Response(buf.getvalue(), mimetype="text/csv", headers={"Content-Disposition": f"attachment; filename={filename}"})

def svg_chart(rows, width=440, height=180):
    if len(rows) < 2: return f"<p class='muted'>{t('no_data')}</p>"
    t0 = datetime.datetime.fromisoformat(rows[0]["ts"]); t1 = datetime.datetime.fromisoformat(rows[-1]["ts"])
    span = max((t1 - t0).total_seconds(), 1); pad = 28; pts = []
    for r in rows:
        xx = pad + ((datetime.datetime.fromisoformat(r["ts"]) - t0).total_seconds() / span) * (width - 2 * pad)
        yy = pad + (1 - r["stock_pct"] / 100) * (height - 2 * pad); pts.append(f"{xx:.1f},{yy:.1f}")
    grid = "".join(f'<line x1="{pad}" y1="{pad+(1-p/100)*(height-2*pad):.1f}" x2="{width-pad}" y2="{pad+(1-p/100)*(height-2*pad):.1f}" stroke="#eef1ed"/>'
                   f'<text x="2" y="{pad+(1-p/100)*(height-2*pad)+4:.1f}" font-size="10" fill="#8a958c">{p}%</text>' for p in (0, 25, 50, 75, 100))
    return (f'<svg viewBox="0 0 {width} {height}" style="width:100%;display:block">{grid}'
            f'<polyline fill="none" stroke="#2e7d32" stroke-width="2.5" stroke-linejoin="round" points="{" ".join(pts)}"/>'
            f'<text x="{pad}" y="{height-6}" font-size="10" fill="#8a958c">{t0.strftime("%m/%d")}</text>'
            f'<text x="{width-pad-28}" y="{height-6}" font-size="10" fill="#8a958c">{t1.strftime("%m/%d")}</text></svg>')

def parse_sms(text):
    parts = (text or "").strip().split()
    if len(parts) < 3 or parts[0].upper() != "HAY": return None, t("sms_fmt"), "sms_format"
    key = parts[1].lower()
    w = next((w for w in WAREHOUSES if key in w["id"].lower() or any(key in s.lower() for s in w["soum"].values())), None)
    if not w: return None, t("sms_nowh", k=parts[1]), "sms_no_warehouse"
    try: tons = float(parts[2])
    except ValueError: return None, t("sms_num"), "sms_number"
    return {"warehouse_id": w["id"], "tons": tons, "herder": " ".join(parts[3:]) or t("sms_herder")}, "OK", None

def answer_faq(text):
    text = (text or "").lower()
    best, best_score = None, 0
    for faq in FAQS:
        score = sum(1 for k in faq["keywords"] if k.lower() in text)
        if score > best_score: best, best_score = faq, score
    return best["answer"][g.lang] if best else t("chat_fallback")

def suggest_questions(text):
    """'배송'처럼 주제 단어만 입력하면, 그 주제에서 가장 많이 나온 질문을 종류(날짜·비용 등)별 1개씩 많이 나온 순으로 반환"""
    word = re.sub(r"[\s.,?!~]+", "", text or "").lower()
    topic = next((k for k, ws in TOPIC_KEYWORDS.items() if word in ws), None)
    if not topic or not os.path.exists(QUESTION_DB_FILE): return []
    con = sqlite3.connect(QUESTION_DB_FILE)
    try:
        col = {"en": "question_en", "mn": "question_mn"}.get(g.lang)   # 번역이 없으면 한국어 질문 사용
        shown = f"COALESCE(NULLIF({col}, ''), question)" if col else "question"
        rows = con.execute(f"SELECT {shown} FROM faq_questions WHERE topic=? AND pick>0 ORDER BY pick LIMIT ?",
                           (topic, SUGGEST_COUNT)).fetchall()
    except sqlite3.Error:
        return []
    finally:
        con.close()
    return [r[0] for r in rows]

LANG_NAME = {"ko": "Korean", "en": "English", "mn": "Mongolian"}

_fx = {"data": None, "ts": 0.0, "fail": 0.0}

def fetch_fx():
    """투그릭(MNT)·원(KRW)·달러(USD) 환율. 무료·키 불필요(open.er-api.com), 6시간 기억. 실패하면 5분 뒤 다시 시도하고 그동안은 이전 값(없으면 None)"""
    now = time.time()
    if _fx["data"] and now - _fx["ts"] < FX_TTL_S: return _fx["data"]
    if now - _fx["fail"] < 300: return _fx["data"]
    try:
        req = urllib.request.Request("https://open.er-api.com/v6/latest/USD", headers={"User-Agent": "HayLinkLite"})
        with urllib.request.urlopen(req, timeout=4) as r: d = json.load(r)
        mnt, krw = float(d["rates"]["MNT"]), float(d["rates"]["KRW"])
        if not (mnt > 0 and krw > 0): raise ValueError("bad rate")
        _fx["data"] = {"mnt_per_usd": mnt, "mnt_per_100krw": mnt / krw * 100, "krw_per_1000mnt": krw / mnt * 1000,
                       "krw_per_usd": krw, "date": (d.get("time_last_update_utc") or "")[5:16]}
        _fx["ts"] = now
    except Exception:
        _fx["fail"] = now
    return _fx["data"]

def fx_context():
    d = fetch_fx()
    if not d: return "Exchange rates: not available right now (say you cannot check the rate at the moment; do not guess a number)."
    return (f"Exchange rates (reference only, market mid-rate, may differ from bank rates; updated {d['date']} UTC): "
            f"1 USD = about {d['mnt_per_usd']:,.0f} MNT; 100 KRW (Korean won) = about {d['mnt_per_100krw']:,.0f} MNT; "
            f"1,000 MNT = about {d['krw_per_1000mnt']:,.0f} KRW; 1 USD = about {d['krw_per_usd']:,.0f} KRW.")

# 챗봇에게 알려 줄 날씨 단계 이름: 코드(NORMAL)나 배율(x1.3) 대신 사람이 쓰는 말로
WEATHER_LABELS = {
    "NORMAL":    {"ko": "맑음·평소 날씨", "en": "clear / normal weather", "mn": "цэлмэг, ердийн цаг агаар"},
    "WARNING":   {"ko": "한파·길 얼음", "en": "cold snap / icy roads", "mn": "хүйтний давалгаа, мөстсөн зам"},
    "CRITICAL":  {"ko": "폭설", "en": "heavy snow", "mn": "их хэмжээний цас"},
    "EMERGENCY": {"ko": "폭설로 길이 막힌 비상 상황", "en": "blizzard, roads closed (emergency)", "mn": "шуурганы улмаас зам хаагдсан онцгой байдал"},
}

def weather_label(code):
    return WEATHER_LABELS.get(code, {}).get(g.lang) or WEATHER_LABELS.get(code, {}).get("en") or "unknown weather"

def extra_fee_txt(mult):
    pct = round((float(mult) - 1) * 100)
    return f"about {pct}% extra delivery fee" if pct > 0 else "no extra weather fee"

def warehouse_context():
    """AI에게 알려 줄 현재 창고 상황 (재고·소진 예상·신청 가능량)"""
    lines = []
    for w in WAREHOUSES:
        p = predict(w); a = availability(w, p)
        dw = delivery_weather(w, p)
        weather_txt = (f"right now {dw['temp_c']} C, snow depth {dw['snow_cm']} cm - model estimate, may differ on the ground" if dw["source"] == "current"
                       else f"forecast min temp {dw['temp_c'] if dw['temp_c'] is not None else 'unknown'} C, snow depth unknown")
        of = p["order_fc"]
        if of["stockout_date"]:
            fc_txt = f"order-based forecast: stock runs out {of['stockout_date']} (in {of['days']} days)"
            if of["cause"]: fc_txt += f" when orders from {', '.join(of['cause'])} come"
        elif of["has_data"]:
            fc_txt = f"order-based forecast: no stockout expected within {FORECAST_HORIZON_D} days"
        else:
            fc_txt = "order-based forecast: not enough order history"
        if of["blocked_now"]: fc_txt += "; requests already closed (stock below one truck)"
        elif of["block_date"]: fc_txt += f"; requests expected to close around {of['block_date']} (stock below one truck)"
        upcoming = "; ".join(f"{e['date']} {e['name']} {e['tons']}t" for e in of["timeline"][:5])
        if upcoming: fc_txt += f"; next expected orders: {upcoming}"
        if of["herders"]: fc_txt += f"; based on {of['n_used']} of {of['n_herders']} herders' ordering cycles"
        lines.append(f"- {w['name']['en']} (id {w['id']}): stock {p['cur_pct']}% (~{p['cur_ton']}t of {w['capacity_ton']}t), "
                     f"daily use {p['per_day']}%, runs out {p['deplete_date']}, status {p['level']}, "
                     f"pending requests {a['pend']}t, available to request {a['avail']}t, "
                     f"requests {'open' if a['truck_possible'] else 'closed (stock below one truck)'}, "
                     f"delivery weather now: {weather_label(dw['condition'])} ({extra_fee_txt(dw['multiplier'])}; {weather_txt}), "
                     f"displayed run-out date {p['deplete_date']} ({p['stockout_source'] or 'none'}-based), {fc_txt}")
    return "\n".join(lines)

def cost_context():
    """AI에게 알려 줄 사료 가격·배송비 추정치 (조드 시세 기준 참고값, 공식·확정 가격 아님)"""
    lines = []
    for i in cached_rows("SELECT item_code, name_en, unit, normal_price_mnt, dzud_peak_price_mnt, subsidized_price_mnt FROM feed_items"):
        lines.append(f"- {i['name_en']} per {i['unit']}: normal-season {i['normal_price_mnt']:,} MNT, dzud-peak market {i['dzud_peak_price_mnt']:,} MNT, "
                     f"relief (subsidized) {i['subsidized_price_mnt']:,} MNT")
        if i["item_code"] == "HAY_BALE":
            lines.append(f"- Natural hay per ton (= {BALES_PER_TON} bales of 25 kg): normal-season about {i['normal_price_mnt'] * BALES_PER_TON:,} MNT, "
                         f"dzud-peak market about {i['dzud_peak_price_mnt'] * BALES_PER_TON:,} MNT, relief about {i['subsidized_price_mnt'] * BALES_PER_TON:,} MNT")
    lines.append(f"Delivery fee estimate = base {BASE_FARE_MNT:,} MNT + {PER_KM_FARE_MNT:,} MNT per km, plus an extra for bad weather; the truck fee is split among the households sharing the delivery.")
    for r in cached_rows("SELECT condition_code, condition_name_ko, cost_multiplier FROM weather_delivery_rates ORDER BY cost_multiplier"):
        total = round((BASE_FARE_MNT + 100 * PER_KM_FARE_MNT) * r["cost_multiplier"])
        lines.append(f"  - if the weather is {weather_label(r['condition_code'])} ({extra_fee_txt(r['cost_multiplier'])}): for 100 km about {total:,} MNT per truck, about {round(total / 4):,} MNT per household if 4 households share")
    return "\n".join(lines)

def ask_llm(text, history):
    """Gemini API로 답변 생성. 키가 없거나 오류면 None → 호출한 쪽이 FAQ로 대체"""
    key = os.environ.get("GEMINI_API_KEY")
    if not key: return None
    system = (
        "You are the help assistant of HayLink Lite, an app for shared hay warehouses and relief-feed delivery "
        "during Mongolian dzud (severe winter). Users are herders and soum officials, mostly non-technical. "
        f"Always reply in {LANG_NAME[g.lang]}, in short, simple sentences. "
        "Rules of the app: a truck carries 5 t; requests are accepted only if warehouse stock is at least one truck; "
        "a request cannot exceed stock minus pending requests; delivery takes about 3 days; weather can delay delivery. "
        "A request can be made in 3 ways: in the app (Requests tab, minimum 0.5 t), by SMS in the format 'HAY warehouse tons name' "
        "(works with 2G signal), or by the bagh leader / warehouse manager on behalf of a herder without signal. "
        "Requests from one warehouse are delivered together once pending requests reach one truck (5 t). "
        "Use only the data below for stock questions; if you don't know, say so and suggest contacting the administrator. "
        "How stock is measured: an ultrasonic sensor mounted on the ceiling of each warehouse measures the distance down to the hay pile "
        "(the closer the hay is to the ceiling, the fuller the warehouse); the app converts that distance into remaining stock (% and tons) "
        "and saves it automatically in the app's database, which is also how the run-out forecast follows real consumption. "
        "The real sensors are not installed yet: for now the stock figures come from sample data or are entered by the administrator, "
        "and the sensor connection is being prepared. If asked how stock is known, explain the ceiling sensor; if asked whether the sensors are already working, "
        "say honestly that they are being prepared. Do not claim a figure is a live sensor reading. "
        "Each warehouse has a run-out forecast: the app learns each herder's usual order amount and cycle, predicts upcoming orders, "
        "and subtracts them from the current stock; the displayed run-out date is the earlier of this order-based date and the sensor-trend date. "
        "When asked when a warehouse will run out or sell out, give that date, name the herders whose expected orders cause it, "
        "mention when requests are expected to close (stock below one truck), and say it is an estimate from past ordering habits. "
        "Privacy: if someone asks whether a specific named person has ordered or requested, or asks for a person's order details, phone number or history, "
        "never confirm or deny it and never say 'no record' or 'not in the data'; say that individual order information is private and only the administrator can check it. "
        "This does not apply to the run-out forecast explanation above. "
        "For price or cost questions use only the estimates below, and make the answer SHORT and easy to take in at a glance: "
        "2 to 3 short lines, at most about 40 words, no lists, no formulas, no background unless the user asks for it. "
        "Line 1 starts with 💰 and gives the main amount first, e.g. '💰 About 330,000 MNT per truck (100 km), about 82,500 MNT per household if 4 share.' "
        "Give only one comparison, and only if useful (for example the amount in clear weather versus in heavy snow). "
        "Then one short sentence: it is a rough estimate and the administrator confirms the final amount before delivery. "
        "Always say 'about' and never present a price as official or fixed. If asked about hay, give the dzud-peak market price and mention in a few words that relief supply may be cheaper. "
        "Mention a shared delivery only in a few words (the truck fee is divided among the households). "
        "Describe weather in plain words such as clear, cold snap, heavy snow, blizzard, and the extra fee as a percent; "
        "NEVER write level codes (NORMAL, WARNING, CRITICAL, EMERGENCY) or multipliers like x1.3. "
        "Each warehouse below shows its current delivery weather; when asked about weather or extra fees, say it in one short sentence "
        "(for example 'Now it is heavy snow, so about 80% extra delivery fee') and add that conditions can change before delivery. "
        "Never say for certain that hay or delivery is free or must be paid for; say it depends (relief supply may be cheaper or supported) and the administrator confirms. "
        "For a 'free?' question, do not begin with 'yes' or 'no': begin with 'it depends'. "
        "Write dzud as 조드 in Korean and as зуд in Mongolian, using only that one word (never add another language in parentheses). "
        "Do not invent prices or distances that are not given below. "
        "For currency or exchange-rate questions (MNT, KRW, USD) use only the exchange rates below: answer with the rate in one short line, say 'about', "
        "and add that the bank rate may differ and the rate changes daily. Convert amounts only when asked, using those rates. "
        "If the rates are not available, say you cannot check the rate right now; never guess a rate.\n\n"
        "Current warehouse data:\n" + warehouse_context() + "\n\nPrice and delivery cost estimates (reference only):\n" + cost_context() + "\n\n" + fx_context()
    )
    msgs = [{"role": "user" if h["role"] == "user" else "model", "parts": [{"text": str(h["content"])[:1000]}]}
            for h in history[-CHAT_MAX_TURNS:]
            if isinstance(h, dict) and h.get("role") in ("user", "assistant") and h.get("content")]
    while msgs and msgs[0]["role"] != "user": msgs.pop(0)
    msgs.append({"role": "user", "parts": [{"text": text[:1000]}]})
    deadline = time.time() + GEMINI_TOTAL_S
    for model in GEMINI_MODELS:
        model = model.strip()
        cfg = {"maxOutputTokens": GEMINI_MAX_OUT}
        if "lite" not in model: cfg["thinkingConfig"] = {"thinkingLevel": "low"}   # 속으로 오래 생각하느라 답이 잘리는 것을 막음
        body = json.dumps({"system_instruction": {"parts": [{"text": system}]}, "contents": msgs,
                           "generationConfig": cfg}).encode("utf-8")
        for attempt in range(2):   # 모델이 "바빠요"(500·503)라고 바로 거절하면 잠깐 뒤 한 번 더 시도
            left = deadline - time.time()
            if left < 3: return None
            req = urllib.request.Request(
                f"https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent",
                data=body, headers={"Content-Type": "application/json", "x-goog-api-key": key})
            try:
                with urllib.request.urlopen(req, timeout=min(GEMINI_TIMEOUT_S, left)) as res:
                    cand = json.loads(res.read())["candidates"][0]
                answer = "".join(p.get("text", "") for p in cand["content"]["parts"]).strip()
                if answer and cand.get("finishReason") != "MAX_TOKENS": return answer   # 중간에 잘린 답은 쓰지 않고 다음 모델로
                print(f"Gemini answer unusable ({model}): finish={cand.get('finishReason')}")
                break
            except urllib.error.HTTPError as e:
                print(f"Gemini API error ({model}, try {attempt + 1}):", e)
                if e.code in (500, 503) and attempt == 0:   # 429(하루 한도 초과)는 다시 물어도 소용없어 바로 다음 모델로
                    time.sleep(1.5); continue
                break
            except Exception as e:   # 시간 초과 등: 같은 모델을 또 기다리지 않고 다음 모델로
                print(f"Gemini API error ({model}):", e)
                break
    return None

# ═══════════════════ 화면 (모바일 UI) ═══════════════════
# 템플릿 이름에 .html 을 붙여야 Jinja 자동 이스케이프가 켜짐 (v0.2는 꺼져 있어 XSS 가능했음)
BASE = """<!doctype html><html lang="{{ lang }}"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover"><title>HayLink Lite</title>
<style>
*{box-sizing:border-box} html,body{margin:0;background:#dfe3dc}
body{font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,"Malgun Gothic","Noto Sans",sans-serif;color:#1f2a22;font-size:16px;-webkit-text-size-adjust:100%}
.phone{max-width:480px;margin:0 auto;min-height:100vh;background:#f4f6f3;position:relative;padding-bottom:88px;box-shadow:0 0 24px rgba(0,0,0,.08)}
header{position:sticky;top:0;z-index:10;background:#2e5d34;color:#fff;padding:12px 16px;display:flex;justify-content:space-between;align-items:center}
.logo{color:#fff;text-decoration:none;font-weight:700;font-size:1.15rem;line-height:1.1}
.logo small{display:block;font-size:.7rem;font-weight:400;opacity:.8;margin-top:2px}
.lang{display:flex;background:rgba(255,255,255,.15);border-radius:999px;padding:3px}
.lang a{color:#dfe9dc;text-decoration:none;font-size:.75rem;font-weight:700;padding:6px 10px;border-radius:999px}
.lang a.on{background:#fff;color:#2e5d34}
main{padding:14px 14px 0}
h1{font-size:1.25rem;margin:4px 0 12px;line-height:1.3} h2{font-size:1rem;margin:0 0 10px}
.sub{display:block;color:#6b7a6e;font-size:.85rem;font-weight:400;margin-top:2px}
.card{background:#fff;border-radius:16px;padding:16px;margin-bottom:12px;box-shadow:0 1px 3px rgba(0,0,0,.06)}
a.card-link{text-decoration:none;color:inherit;display:block} a.card-link .card:active{transform:scale(.99)}
.top{display:flex;justify-content:space-between;align-items:flex-start;gap:8px}
.gauge{background:#e8ebe7;border-radius:999px;height:14px;overflow:hidden;margin:8px 0} .gauge>div{height:100%;border-radius:999px}
.ok{background:#43a047}.warn{background:#fb8c00}.danger{background:#e53935}
.badge{display:inline-block;padding:4px 10px;border-radius:999px;font-size:.72rem;font-weight:600;color:#fff;white-space:nowrap}
.muted{color:#6b7a6e;font-size:.85rem} .big{font-size:2.2rem;font-weight:700;line-height:1.1}
.kv{display:flex;justify-content:space-between;padding:9px 0;border-bottom:1px solid #eef1ed;font-size:.9rem;gap:8px} .kv:last-child{border-bottom:none} .kv b{text-align:right}
input,select,button{font:inherit;font-size:1rem;width:100%;padding:13px 14px;border:1px solid #d5dad3;border-radius:12px;margin:5px 0;background:#fff;min-height:48px}
button{background:#2e5d34;color:#fff;border:none;font-weight:600;cursor:pointer} button:active{opacity:.85}
button:disabled,input:disabled{opacity:.5;cursor:not-allowed}
button.secondary{background:#607d8b} button.danger{background:#e53935} button.outline{background:#fff;color:#2e5d34;border:1.5px solid #2e5d34}
.msg{background:#e8f5e9;border-left:4px solid #43a047;padding:12px;border-radius:12px;margin-bottom:12px;font-size:.9rem;word-break:break-word}
.msg.err{background:#fdecea;border-color:#e53935}
.warnbox{background:#fdecea;border-left:4px solid #e53935;padding:10px 12px;border-radius:12px;font-size:.88rem;margin-top:8px}
.infobox{margin-top:10px;padding:10px 12px;background:#f0f6f1;border-radius:12px}
.item{display:flex;justify-content:space-between;align-items:center;padding:10px 0;border-bottom:1px solid #eef1ed;font-size:.9rem;gap:8px} .item:last-child{border-bottom:none}
.rank{width:28px;height:28px;border-radius:50%;background:#2e5d34;color:#fff;display:inline-flex;align-items:center;justify-content:center;font-size:.8rem;font-weight:700;flex-shrink:0}
.tabs{position:fixed;bottom:0;left:50%;transform:translateX(-50%);width:100%;max-width:480px;background:#fff;border-top:1px solid #e0e4de;display:flex;padding:6px 0 calc(8px + env(safe-area-inset-bottom));z-index:10}
.tabs a{flex:1;text-align:center;text-decoration:none;color:#8a958c;font-size:.72rem;font-weight:600;display:flex;flex-direction:column;align-items:center;gap:2px}
.tabs a span{font-size:1.35rem} .tabs a.on{color:#2e5d34}
code{background:#f0f2ee;padding:2px 6px;border-radius:6px;font-size:.85em;word-break:break-all}
footer{text-align:center;color:#9aa49c;font-size:.75rem;padding:8px 0 4px}
.chatlog{display:flex;flex-direction:column;gap:8px;min-height:260px}
.bubble{max-width:85%;padding:10px 14px;border-radius:16px;font-size:.92rem;line-height:1.45;white-space:pre-wrap}
.bubble.bot{background:#e8f5e9;align-self:flex-start;border-bottom-left-radius:4px}
.bubble.me{background:#2e5d34;color:#fff;align-self:flex-end;border-bottom-right-radius:4px}
.chatform{display:flex;gap:8px} .chatform input{flex:1;margin:0} .chatform button{width:auto;margin:0;padding:0 18px}
</style></head><body><div class="phone">
<header><a class="logo" href="/">🌾 HayLink Lite<small>{{ t('tagline') }}</small></a>
<div class="lang">{% for c,l in [('ko','KO'),('en','EN'),('mn','MN')] %}<a href="/lang/{{ c }}" class="{{ 'on' if c==lang else '' }}">{{ l }}</a>{% endfor %}</div></header>
<main>{% if request.args.get('msg') %}<div class="msg {{ 'err' if request.args.get('kind')=='err' else '' }}">{{ request.args.get('msg') }}</div>{% endif %}
{% block content %}{% endblock %}
<footer>{{ t('footer', m='ON' if demo else 'OFF') }}</footer></main>
<nav class="tabs">
<a href="/" class="{{ 'on' if request.path=='/' or request.path.startswith('/warehouse') else '' }}"><span>🏠</span>{{ t('nav_wh') }}</a>
<a href="/order" class="{{ 'on' if request.path.startswith('/order') else '' }}"><span>🚚</span>{{ t('nav_order') }}</a>
<a href="/chat" class="{{ 'on' if request.path.startswith('/chat') else '' }}"><span>💬</span>{{ t('nav_chat') }}</a>
<a href="/admin" class="{{ 'on' if request.path.startswith('/admin') else '' }}"><span>📊</span>{{ t('nav_admin') }}</a>
</nav></div>
<script>
/* 선택한 창고의 신청 가능량에 맞춰 톤수 입력 max·버튼 잠금 (서버 검증이 최종) */
document.querySelectorAll('form[data-avail]').forEach(function(f){
  var s=f.querySelector('select'),i=f.querySelector('input[name=tons]'),h=f.querySelector('.avail-hint'),b=f.querySelector('button[type=submit]');
  function u(){var o=s.options[s.selectedIndex],a=parseFloat(o.dataset.avail||'0');i.max=a;if(h)h.textContent=o.dataset.hint||'';var no=a<{{ order_min }};i.disabled=no;b.disabled=no;}
  s.addEventListener('change',u);u();});
</script></body></html>"""

INDEX = """{% extends "base.html" %}{% block content %}
<h1>{{ t('idx_title') }}<span class="sub">{{ t('province') }}</span></h1>
{% for w, p, a in items %}
<a class="card-link" href="/warehouse/{{ w.id }}"><div class="card">
 <div class="top"><div><h2 style="margin:0">{{ w.name[lang] }}</h2><div class="muted">{{ w.soum[lang] }} · {{ t('capacity') }} {{ w.capacity_ton }}t</div></div>
  <span class="badge {{ p.level }}">{{ t(p.level_key) }}</span></div>
 <div class="gauge"><div class="{{ p.level }}" style="width:{{ p.cur_pct }}%"></div></div>
 <div style="display:flex;justify-content:space-between;align-items:baseline;flex-wrap:wrap;gap:4px">
  <span><b style="font-size:1.4rem">{{ p.cur_pct }}%</b> <span class="muted">≈ {{ p.cur_ton }}t {{ t('left') }}</span></span>
  <span class="muted">{{ t('runs_out') }} <b>{{ p.deplete_date }}</b></span></div>
 <div class="muted">{{ t('per_day') }} {{ p.per_day }}% · {% if a.truck_possible %}{{ t('avail') }} <b>{{ a.avail }}t</b>{% else %}<span style="color:#e53935">{{ t('req_closed') }}</span>{% endif %}{% if not p.sensor_ok %} · <span style="color:#e53935">⚠ {{ t('sensor_off') }}</span>{% endif %}</div>
</div></a>
{% endfor %}
<div class="card"><h2>ℹ️ {{ t('about_title') }}</h2><p class="muted" style="margin:0">{{ t('about_body') }}</p></div>
{% endblock %}"""

DETAIL = """{% extends "base.html" %}{% block content %}
<a href="/" class="muted" style="text-decoration:none">{{ t('back') }}</a>
<h1 style="margin-top:8px">{{ w.name[lang] }}<span class="sub">{{ w.soum[lang] }} · <span class="badge {{ p.level }}">{{ t(p.level_key) }}</span></span></h1>
<div class="card"><div class="muted">{{ t('cur_stock') }}</div>
 <div style="display:flex;align-items:baseline;gap:10px"><span class="big">{{ p.cur_pct }}%</span><span class="muted">≈ {{ p.cur_ton }}t / {{ w.capacity_ton }}t</span></div>
 <div class="gauge"><div class="{{ p.level }}" style="width:{{ p.cur_pct }}%"></div></div>
 <div class="muted">{{ t('last_reading') }}: {{ p.last_ts }}</div></div>
{% if privacy %}<div class="card"><div class="muted">{{ t('ai_deplete') }}</div><span class="big">{{ p.deplete_date }}</span></div>
{% else %}<div class="card"><div class="muted">{{ t('forecast') }}</div>
 <div style="display:flex;align-items:baseline;gap:10px;flex-wrap:wrap"><span class="big">{{ p.deplete_date }}</span>
  {% if p.stockout_source %}<span class="badge {{ p.level }}">{{ t('src_' ~ p.stockout_source) }}</span>{% endif %}</div>
 {% if p.days_base is not none %}<div class="muted">{{ t('src_sensor') }}: {{ t('base_days', a=p.days_base, b=p.days_cold) }}</div>{% endif %}
 <div class="muted">🌡 {{ t('temp_min') }}: {{ p.temp_min if p.temp_min is not none else '?' }}℃ · {{ t(p.factor_key) }}</div>
 {% if p.refilled %}<div class="muted">📥 {{ t('refilled') }}</div>{% endif %}
 <div class="infobox">📦 {{ t('reorder') }}: <b>{{ p.reorder_date }}</b> <span class="muted">({{ t('lead_note', n=lead) }})</span></div></div>
{% set f = p.order_fc %}
<div class="card"><h2>🔮 {{ t('of_title') }}</h2>
{% if not f.has_data %}<p class="muted" style="margin:0">{{ t('of_nodata', n=min_orders) }}</p>
{% else %}
 <div style="display:flex;align-items:baseline;gap:10px;flex-wrap:wrap">
 {% if f.stockout_date %}<span class="big">{{ f.stockout_date }}</span><span class="muted">{{ t('of_today') if f.days == 0 else t('of_stockout', d=f.days) }}</span>
 {% else %}<b style="font-size:1.1rem">{{ t('of_none', n=horizon) }}</b>{% endif %}</div>
 {% if f.cause %}<div>{{ t('of_cause') }}: <b>{{ f.cause|join(', ') }}</b></div>{% endif %}
 {% if f.blocked_now %}<div class="warnbox">⛔ {{ t('of_block_now', n=truck) }}</div>
 {% elif f.block_date %}<div class="warnbox">⛔ {{ t('of_block', d=f.block_date, n=truck) }}</div>{% endif %}
 {% if f.timeline %}<h2 style="margin:14px 0 4px">{{ t('of_list') }}</h2>
 {% for e in f.timeline %}<div class="item"{% if e.short %} style="color:#e53935;font-weight:700"{% endif %}><span>{{ e.date }} · {{ e.name }}</span>
  <span>−{{ e.tons }}t → {{ t('of_short') if e.short else t('of_left', x=e.left) }}</span></div>{% endfor %}{% endif %}
 {% if f.herders %}<h2 style="margin:14px 0 4px">{{ t('of_habits') }}</h2>
 {% for h in f.herders %}<div class="item"><span>{{ h.name }}{% if h.pending_t %} <span class="badge warn">{{ t('of_pending', t=h.pending_t) }}</span>{% endif %}</span>
  <span class="muted">{% if h.interval_d %}{{ t('of_habit', t=h.avg_t, d=h.interval_d, nx=h.next) }}{% else %}{{ t('of_few', n=h.n_orders) }}{% endif %}</span></div>{% endfor %}{% endif %}
 <div class="muted" style="margin-top:8px">{% if not privacy %}{{ t('of_used', m=f.n_used, n=f.n_herders) }} · {% endif %}{{ t('of_note') }}</div>
{% endif %}</div>{% endif %}
<div class="card"><h2>{{ t('trend') }}</h2>{{ chart|safe }}</div>
<div class="card"><h2>{{ t('grp_this') }}</h2>
 <div class="gauge"><div class="ok" style="width:{{ (a.pend/truck*100)|round|int if a.pend<truck else 100 }}%"></div></div>
 <div><b>{{ a.pend }}t</b> / {{ t('truck1') }} {{ truck }}t · {{ t('orders_n', n=a.n) }}</div>
 <div class="muted">{{ t('stock_in_wh') }} {{ a.stock }}t · {{ t('avail') }} <b>{{ a.avail }}t</b></div>
 {% if not a.truck_possible %}<div class="warnbox">{{ t('no_truck_stock', s=a.stock, n=truck) }}</div>
 {% elif a.avail < order_min %}<div class="warnbox">{{ t('stock_short') }}</div>
 {% else %}<a href="/order?w={{ w.id }}"><button style="margin-top:10px">{{ t('join') }}</button></a>{% endif %}</div>
<div class="card"><h2>{{ t('sensor_info') }}</h2>
 <div class="kv"><span>{{ t('node_id') }}</span><b><code>{{ w.id }}</code></b></div>
 <div class="kv"><span>{{ t('d_empty') }}</span><b>{{ w.d_empty_cm }} cm</b></div>
 <div class="kv"><span>{{ t('d_full') }}</span><b>{{ w.d_full_cm }} cm</b></div>
 <div class="kv"><span>{{ t('last_dist') }}</span><b>{{ last_dist }} cm</b></div>
 {% if demo %}<form method="post" action="/api/demo/consume/{{ w.id }}"><button class="secondary" type="submit">{{ t('demo_consume', b=bale) }}</button></form>{% endif %}</div>
{% endblock %}"""

WH_SELECT = """<select name="warehouse_id">{% for w in warehouses %}{% set a = av[w.id] %}
<option value="{{ w.id }}" data-avail="{{ a.avail }}" data-hint="{% if not a.truck_possible %}{{ t('no_truck_stock', s=a.stock, n=truck) }}{% else %}{{ t('avail') }} {{ a.avail }}t · {{ t('stock_in_wh') }} {{ a.stock }}t · {{ t('pending') }} {{ a.pend }}t{% endif %}" {% if w.id==sel %}selected{% endif %}>{{ w.name[lang] }} — {% if not a.truck_possible %}{{ t('req_closed') }}{% else %}{{ t('avail') }} {{ a.avail }}t{% endif %}</option>{% endfor %}</select>
<div class="muted avail-hint" style="margin:0 0 4px 4px"></div>"""

ORDER = """{% extends "base.html" %}{% block content %}
<h1>{{ t('order_title') }}<span class="sub">{{ t('order_sub', n=truck) }}</span></h1>
{% for w, a in stats %}
<div class="card"><div class="top"><div><h2 style="margin:0">{{ w.name[lang] }}</h2><div class="muted">{{ w.soum[lang] }} · {{ t('stock_in_wh') }} {{ a.stock }}t</div></div><b>{{ a.pend }}t / {{ truck }}t</b></div>
 <div class="gauge"><div class="{{ 'ok' if a.can_dispatch else ('danger' if not a.truck_possible else 'warn') }}" style="width:{{ (a.pend/truck*100)|round|int if a.pend<truck else 100 }}%"></div></div>
 <div class="muted">{{ t('orders_n', n=a.n) }} · {{ t('avail') }} <b>{{ a.avail }}t</b></div>
 {% if not a.truck_possible %}<div class="warnbox">{{ t('no_truck_stock', s=a.stock, n=truck) }}</div>
 {% elif a.can_dispatch %}<form method="post" action="/dispatch/{{ w.id }}"><button>{{ t('dispatch_btn') }}</button></form>
 {% elif a.pend >= truck %}<div class="warnbox">{{ t('msg_dispatch_short', pend=a.pend, stock=a.stock) }}</div>
 {% else %}<div class="muted" style="margin-top:4px">{{ t('more_needed', n=(truck-a.pend)|round(1)) }}</div>{% endif %}</div>
{% endfor %}
<div class="card"><h2>{{ t('via_app') }}</h2>
 <form method="post" action="/order" data-avail>
  """ + WH_SELECT + """
  <input name="herder" placeholder="{{ t('name') }} ({{ t('ph_name') }})" required maxlength="60">
  <input name="phone" placeholder="{{ t('phone') }} ({{ t('ph_phone') }})" maxlength="30">
  <input name="tons" type="number" step="0.5" min="{{ order_min }}" placeholder="{{ t('tons_needed') }}" required>
  <button type="submit">{{ t('submit') }}</button></form>
 <p class="muted" style="margin:6px 0 0">{{ t('offline_note') }}</p></div>
<div class="card"><h2>{{ t('via_sms') }}</h2>
 <form method="post" action="/api/sms">
  <input name="phone" placeholder="{{ t('sender') }}" value="9900-0000">
  <input name="text" placeholder="HAY zuunmod 2 Bold" required>
  <button type="submit" class="secondary">{{ t('process_sms') }}</button></form>
 <p class="muted" style="margin:6px 0 0">{{ t('sms_note')|safe }}</p></div>
{% if not privacy %}<div class="card"><h2>{{ t('recent') }}</h2>
{% set ch = {'app':'ch_app','sms':'ch_sms','proxy':'ch_proxy'} %}
{% for o in orders %}<div class="item"><div><b>{{ o.herder }}</b> · {{ o.tons }}t<div class="muted">{{ wh_name(o.warehouse_id) }} · {{ o.ts[5:16].replace('T',' ') }}</div></div>
 <div style="text-align:right"><div>{{ t(ch.get(o.channel, 'ch_app')) }}</div><div class="muted">{{ t('pending') if o.status=='pending' else t('dispatched') }}</div></div></div>{% endfor %}
{% if not orders %}<div class="muted">{{ t('none_yet') }}</div>{% endif %}</div>{% endif %}
{% endblock %}"""

ADMIN = """{% extends "base.html" %}{% block content %}
<h1>{{ t('admin_title') }}<span class="sub">{{ t('admin_sub') }}</span></h1>
<a href="/admin/stats"><button type="button" class="outline" style="margin-bottom:12px">{{ t('st_open') }}</button></a>
{% if pin_on %}<form method="post" action="/admin/logout" style="margin-bottom:12px"><button type="submit" class="secondary">{{ t('logout') }}</button></form>{% endif %}
<div class="card"><h2>{{ t('priority') }}</h2>
{% for w, p, a in rows %}
<a class="card-link" href="/warehouse/{{ w.id }}"><div class="item">
 <span class="rank">{{ loop.index }}</span>
 <div style="flex:1"><b>{{ w.name[lang] }}</b> <span class="badge {{ p.level }}">{{ t(p.level_key) }}</span>
  <div class="muted">{{ t('stock') }} {{ p.cur_pct }}% ({{ p.cur_ton }}t) · {{ t('runs_out') }} {{ p.deplete_date }}{% if p.days_use is not none %} ({{ p.days_use }} {{ t('days') }}){% endif %}</div>
  <div class="muted">{{ t('reorder') }} {{ p.reorder_date }} · {{ t('pending_orders') }} {{ a.pend }}t/{{ a.n }} · {{ t('avail') }} {{ a.avail }}t · {{ t('sensor') }} {{ t('online') if p.sensor_ok else t('offline') }}</div>
  {% if not a.truck_possible %}<div class="muted" style="color:#e53935">{{ t('no_truck_stock', s=a.stock, n=truck) }}</div>{% endif %}</div>
</div></a>{% endfor %}</div>
<div class="card"><h2>{{ t('proxy_title') }}<span class="sub">{{ t('proxy_who') }}</span></h2>
 <p class="muted" style="margin:0 0 6px">{{ t('proxy_note') }}</p>
 <form method="post" action="/order" data-avail>
  """ + WH_SELECT + """
  <input name="herder" placeholder="{{ t('herder_name') }}" required maxlength="60"><input name="phone" placeholder="{{ t('phone') }}" maxlength="30">
  <input name="tons" type="number" step="0.5" min="{{ order_min }}" placeholder="{{ t('tons_needed') }}" required>
  <input type="hidden" name="channel" value="proxy"><input type="hidden" name="back" value="/admin">
  <button type="submit">{{ t('register') }}</button></form></div>
<div class="card"><h2>{{ t('deliveries') }}</h2>
{% for d in deliveries %}<div class="item"><div><b>{{ wh_name(d.warehouse_id) }}</b><div class="muted">{{ d.ts[5:16].replace('T',' ') }}</div></div><div style="text-align:right"><b>{{ d.total_tons }}t</b><div class="muted">{{ t('households', n=d.n_orders) }}</div></div></div>{% endfor %}
{% if not deliveries %}<div class="muted">{{ t('none_yet') }}</div>{% endif %}</div>
<div class="card"><h2>{{ t('sensor_api') }}</h2><p class="muted" style="margin:0 0 6px">{{ t('api_note')|safe }}</p>
 <form method="post" action="/api/reading">
  <select name="warehouse_id">{% for w in warehouses %}<option value="{{ w.id }}">{{ w.id }}</option>{% endfor %}</select>
  <input name="distance_cm" type="number" step="0.1" min="0" placeholder="{{ t('dist_test') }}" required>
  <button class="secondary" type="submit">{{ t('send_test') }}</button></form>
 {% if demo %}<form method="post" action="/api/demo/reset" style="margin-top:6px"><button class="danger" type="submit">{{ t('reset') }}</button></form>{% endif %}</div>
<div class="card"><h2>{{ t('mode_title') }}</h2>
 <p style="margin:0 0 6px">{{ t('mode_now') }}: <b>{{ t('mode_demo') if demo else t('mode_live') }}</b></p>
 {% if mode_switch %}
 <p class="muted" style="margin:0 0 6px">{{ t('mode_warn') }}</p>
 <form method="post" action="/admin/mode">
  <input type="hidden" name="target" value="{{ 'live' if demo else 'demo' }}">
  <input name="pin" type="password" placeholder="{{ t('mode_pin_ph') }}" required autocomplete="off">
  <input name="confirm" placeholder="{{ t('mode_confirm_ph', w='LIVE' if demo else 'DEMO') }}" required autocomplete="off">
  <button class="danger" type="submit">{{ t('mode_to_live') if demo else t('mode_to_demo') }}</button></form>
 {% else %}<p class="muted" style="margin:0">{{ t('mode_off') }}</p>{% endif %}</div>
{% endblock %}"""

PIN = """{% extends "base.html" %}{% block content %}
<h1>{{ t('pin_title') }}</h1>
<div class="card"><form method="post" action="/admin/login">
 <input name="pin" type="password" placeholder="{{ t('pin_ph') }}" required autocomplete="off">
 <button type="submit">{{ t('pin_btn') }}</button></form></div>
{% endblock %}"""

CHAT = """{% extends "base.html" %}{% block content %}
<h1>{{ t('chat_title') }}<span class="sub">{{ t('chat_sub') }}</span></h1>
<style>
/* 입력창은 하단 메뉴 바로 위에 고정, 대화만 스크롤 (카카오톡 방식) */
.chatform{position:fixed;left:50%;transform:translateX(-50%);width:100%;max-width:480px;background:#f4f6f3;border-top:1px solid #e0e4de;padding:8px 14px;z-index:9}
#chatspace{height:76px} footer{display:none}
.chips{display:flex;flex-direction:column;gap:6px;align-self:flex-start;max-width:90%}
.bubble.loading{color:#4a6b4e}
.bubble.loading::after{content:'...';display:inline-block;vertical-align:bottom;overflow:hidden;width:0;animation:dots 1.2s steps(4,end) infinite}
@keyframes dots{to{width:1.1em}}
.chip{width:auto;margin:0;min-height:0;padding:9px 14px;text-align:left;background:#fff;color:#2e5d34;border:1.5px solid #2e5d34;border-radius:16px;font-size:.9rem;font-weight:600}
</style>
<div class="card"><div class="chatlog" id="log"><div class="bubble bot">{{ t('chat_hello') }}</div></div></div>
<div id="chatspace"></div>
<form class="chatform" id="chatform">
 <input id="q" placeholder="{{ t('chat_ph') }}" autocomplete="off" required>
 <button type="submit">{{ t('chat_send') }}</button></form>
<script>
const log = document.getElementById('log'), form = document.getElementById('chatform'), q = document.getElementById('q');
const chatHistory = [];
let orderFlow = null;   // '내 신청 확인' 대화 진행 상태 (이름·전화번호는 AI 대화 기록에 넣지 않음)
function layout(){ const tabs = document.querySelector('.tabs'); form.style.bottom = tabs.offsetHeight + 'px'; document.getElementById('chatspace').style.height = (form.offsetHeight + 12) + 'px'; }
function toBottom(){ window.scrollTo({top: document.documentElement.scrollHeight, behavior: 'smooth'}); }
window.addEventListener('load', layout); window.addEventListener('resize', layout);
function add(cls, text){ const d = document.createElement('div'); d.className = 'bubble ' + cls; d.textContent = text; log.appendChild(d); toBottom(); }
function addChips(list){
  const box = document.createElement('div'); box.className = 'chips';
  list.forEach(function(s){ const b = document.createElement('button'); b.type = 'button'; b.className = 'chip'; b.textContent = s;
    b.addEventListener('click', function(){ box.remove(); send(s); }); box.appendChild(b); });
  log.appendChild(box); toBottom();
}
async function send(text){
  add('me', text);
  add('bot loading', {{ t('chat_loading')|tojson }});
  const wait = log.lastElementChild;
  try {
    const res = await fetch('/api/chat', {method:'POST', headers:{'Content-Type':'application/json'}, body: JSON.stringify({text: text, history: chatHistory, flow: orderFlow})});
    const data = await res.json(); wait.remove(); add('bot', data.answer);
    orderFlow = data.flow || null;
    if (data.private) return;
    if (data.suggestions) { addChips(data.suggestions); return; }
    chatHistory.push({role:'user', content:text}, {role:'assistant', content:data.answer});
  } catch(err) { wait.remove(); add('bot', '...'); }
}
form.addEventListener('submit', function(e){
  e.preventDefault();
  const text = q.value.trim(); if(!text) return;
  q.value = ''; send(text);
});
</script>
{% endblock %}"""

STATS = """{% extends "base.html" %}{% block content %}
<a href="/admin" class="muted" style="text-decoration:none">{{ t('st_back') }}</a>
<h1 style="margin-top:8px">📈 {{ t('st_title') }}<span class="sub">{{ t('st_sub') }}</span></h1>
<div style="display:flex;gap:6px;margin-bottom:12px">
{% for key in ['day', 'week', 'month'] %}<a href="/admin/stats?period={{ key }}" style="flex:1"><button type="button" class="{{ '' if key == period else 'outline' }}">{{ t('st_' ~ key) }}</button></a>{% endfor %}</div>
<div class="card"><div style="display:flex;justify-content:space-around;text-align:center">
 <div><div class="big">{{ s.total.attempts }}</div><div class="muted">{{ t('st_attempts') }}</div></div>
 <div><div class="big">{{ s.rate }}%</div><div class="muted">{{ t('st_rate') }}</div></div>
 <div><div class="big">{{ s.total.tons }}t</div><div class="muted">{{ t('st_tons') }}</div></div></div></div>
<div class="card"><h2>{{ t('st_chart') }}</h2>{{ chart|safe }}<div class="muted">🟩 {{ t('st_ok') }} · 🟥 {{ t('st_fail') }}</div></div>
<div class="card"><h2>{{ t('st_by_period') }}</h2>
{% for b in s.buckets|reverse %}{% if b.attempts %}<div class="item"><span>{{ b.label }}</span><span><b>{{ b.attempts }}</b> <span class="muted">({{ t('st_ok') }} {{ b.ok }} · {{ t('st_fail') }} {{ b.fail }}) · {{ b.tons }}t</span></span></div>{% endif %}{% endfor %}
{% if not s.total.attempts %}<div class="muted">{{ t('st_none') }}</div>{% endif %}</div>
<div class="card"><h2>{{ t('st_by_wh') }}</h2>
{% for r in s.by_wh %}<div class="item"><span>{{ wh_name(r.key) }}</span><span><b>{{ r.attempts }}</b> <span class="muted">({{ t('st_ok') }} {{ r.ok }} · {{ t('st_fail') }} {{ r.fail }}) · {{ r.tons }}t</span></span></div>{% endfor %}
{% if not s.by_wh %}<div class="muted">{{ t('st_none') }}</div>{% endif %}</div>
<div class="card"><h2>{{ t('st_by_ch') }}</h2>
{% for r in s.by_ch %}<div class="item"><span>{{ t(r.label_key) }}</span><span><b>{{ r.attempts }}</b> <span class="muted">({{ t('st_ok') }} {{ r.ok }} · {{ t('st_fail') }} {{ r.fail }}) · {{ r.tons }}t</span></span></div>{% endfor %}
{% if not s.by_ch %}<div class="muted">{{ t('st_none') }}</div>{% endif %}</div>
<div class="card"><h2>{{ t('st_reasons') }}</h2>
{% for r in s.reasons %}<div class="item"><span>{{ t('rs_' ~ r.key) }}</span><b>{{ r.n }}</b></div>{% endfor %}
{% if not s.reasons %}<div class="muted">{{ t('st_none') }}</div>{% endif %}</div>
<a href="/admin/export/requests.csv"><button type="button" class="secondary">⬇ {{ t('st_csv_req') }}</button></a>
<a href="/admin/export/orders.csv"><button type="button" class="secondary">⬇ {{ t('st_csv_orders') }}</button></a>
{% endblock %}"""

app.jinja_loader = DictLoader({"base.html": BASE, "index.html": INDEX, "detail.html": DETAIL, "stats.html": STATS,
                               "order.html": ORDER, "admin.html": ADMIN, "pin.html": PIN, "chat.html": CHAT})

def avail_map():
    return {w["id"]: availability(w) for w in WAREHOUSES}

# ═══════════════════ 라우트 ═══════════════════
@app.route("/lang/<code>")
def set_lang(code):
    if code not in LANGS: code = DEFAULT_LANG
    back = urlparse(request.referrer).path if request.referrer else "/"
    resp = redirect(back or "/")
    resp.set_cookie("lang", code, max_age=60 * 60 * 24 * 365, samesite="Lax")
    return resp

@app.route("/")
def index():
    items = []
    for w in WAREHOUSES:
        p = predict(w); items.append((w, p, availability(w, p)))
    return render_template("index.html", items=items)

@app.route("/warehouse/<wid>")
def detail(wid):
    w = WH_BY_ID.get(wid)
    if not w: return "not found", 404
    p = predict(w); last = latest_reading(wid)
    return render_template("detail.html", w=w, p=p, a=availability(w, p), chart=svg_chart(readings_last_days(wid, 7)),
                           last_dist=last["distance_cm"] if last else "-")

@app.route("/order", methods=["GET", "POST"])
def order():
    if request.method == "POST":
        f = request.form
        channel = f.get("channel", "app")
        if channel not in ("app", "proxy"): channel = "app"
        if channel == "proxy" and not admin_ok(): return "forbidden", 403
        back = f.get("back", "/order")
        if back not in SAFE_BACK: back = "/order"
        ok, key, kw = try_add_order(f.get("warehouse_id"), f.get("herder"), f.get("phone"), f.get("tons"), channel)
        return redirect(msg_url(back, key, kind="ok" if ok else "err", **kw))
    av = avail_map()
    stats = [(w, av[w["id"]]) for w in WAREHOUSES]
    orders = [] if privacy_on() else q("SELECT * FROM orders ORDER BY ts DESC, id DESC LIMIT 15")   # 실제 운영의 일반 사용자에게는 신청 내역을 보여 주지 않음
    sel = request.args.get("w", WAREHOUSES[0]["id"])
    return render_template("order.html", stats=stats, av=av, orders=orders, sel=sel if sel in WH_BY_ID else WAREHOUSES[0]["id"])

@app.route("/dispatch/<wid>", methods=["POST"])
def dispatch(wid):
    w = WH_BY_ID.get(wid)
    if not w: return "not found", 404
    p = predict(w); a = availability(w, p)
    # [핵심] 재고 < 트럭 1대 → 불가 / 대기 < 트럭 1대 → 불가 / 대기 > 재고(센서로 소비 확인) → 불가
    if not a["truck_possible"]:
        return redirect(msg_url("/order", "msg_wh_short", kind="err", wh=wh_name(wid), stock=a["stock"], n=TRUCK_CAPACITY_T))
    if a["pend"] < TRUCK_CAPACITY_T:
        return redirect(msg_url("/order", "msg_not_enough", kind="err", n=TRUCK_CAPACITY_T))
    if not a["can_dispatch"]:
        return redirect(msg_url("/order", "msg_dispatch_short", kind="err", pend=a["pend"], stock=a["stock"]))
    with transaction() as tx:
        tx.execute("UPDATE orders SET status='dispatched' WHERE warehouse_id=? AND status='pending'", (wid,))
        tx.execute("INSERT INTO deliveries(warehouse_id, total_tons, n_orders, ts) VALUES(?,?,?,?)", (wid, a["pend"], a["n"], now_iso()))
    if is_demo():
        # 실서비스에선 센서가 반출을 감지함. 데모에선 반출 후 측정값을 직접 기록해 재고를 맞춘다.
        record_reading(w, pct=max(0.0, p["cur_pct"] - a["pend"] / w["capacity_ton"] * 100))
    return redirect(msg_url("/order", "msg_dispatch", wh=wh_name(wid), tons=f"{a['pend']:.1f}", hh=t("households", n=a["n"])))

@app.route("/admin")
@admin_required
def admin():
    rows = []
    for w in WAREHOUSES:
        p = predict(w); rows.append((w, p, availability(w, p)))
    rows.sort(key=lambda r: (r[1]["days_use"] if r[1]["days_use"] is not None else 9999, r[1]["cur_pct"]))
    deliveries = q("SELECT * FROM deliveries ORDER BY ts DESC, id DESC LIMIT 10")
    return render_template("admin.html", rows=rows, av=avail_map(), sel=WAREHOUSES[0]["id"], deliveries=deliveries)

@app.route("/admin/stats")
@admin_required
def admin_stats():
    s = request_stats(request.args.get("period", "day"))
    return render_template("stats.html", s=s, period=s["period"], chart=svg_bars(s["buckets"]))

@app.route("/admin/export/requests.csv")
@admin_required
def export_requests():
    cols = ["id", "ts", "warehouse_id", "herder", "phone", "tons", "channel", "ok", "reason", "stock_t", "avail_t", "pending_t", "lang", "raw"]
    rows = q(f"SELECT {', '.join(cols)} FROM request_log ORDER BY ts DESC, id DESC")
    return csv_response("haylink_requests.csv", cols, [[r[c] for c in cols] for r in rows])

@app.route("/admin/export/orders.csv")
@admin_required
def export_orders():
    cols = ["id", "ts", "warehouse_id", "herder", "phone", "tons", "channel", "status"]
    rows = q(f"SELECT {', '.join(cols)} FROM orders ORDER BY ts DESC, id DESC")
    return csv_response("haylink_orders.csv", cols, [[r[c] for c in cols] for r in rows])

@app.route("/admin/login", methods=["POST"])
def admin_login():
    pin = request.form.get("pin", "")
    if ADMIN_PIN and pin != ADMIN_PIN:
        return redirect(msg_url("/admin", "pin_bad", kind="err"))
    resp = redirect("/admin")
    resp.set_cookie("admin_pin", pin, max_age=60 * 60 * 12, httponly=True, samesite="Lax")
    return resp

@app.route("/admin/logout", methods=["POST"])
def admin_logout():
    resp = redirect(msg_url("/", "msg_logout"))
    resp.delete_cookie("admin_pin", path="/")
    return resp

@app.route("/api/reading", methods=["POST"])
def api_reading():
    data = request.get_json(silent=True) or request.form
    w = WH_BY_ID.get(data.get("warehouse_id", ""))
    if not w: return jsonify({"ok": False, "error": "unknown warehouse_id"}), 400
    try: dist = float(data.get("distance_cm"))
    except (TypeError, ValueError): return jsonify({"ok": False, "error": "distance_cm required"}), 400
    if not (0 <= dist <= w["d_empty_cm"] * 1.5):
        return jsonify({"ok": False, "error": "distance_cm out of range"}), 400
    pct = record_reading(w, dist=dist)
    if request.is_json: return jsonify({"ok": True, "warehouse_id": w["id"], "distance_cm": dist, "stock_pct": pct})
    return redirect(msg_url("/admin", "msg_reading", wh=w["id"], d=dist, p=f"{pct:.1f}"))

@app.route("/api/sms", methods=["POST"])
def api_sms():
    src = request.get_json(silent=True) or request.form
    parsed, err, err_code = parse_sms(src.get("text", ""))
    if not parsed:
        log_request(False, err_code, phone=src.get("phone", ""), channel="sms", raw=src.get("text", ""))
        return redirect(msg_url("/order", "msg_sms_err", kind="err", e=err))
    ok, key, kw = try_add_order(parsed["warehouse_id"], parsed["herder"], src.get("phone", ""), parsed["tons"], "sms")
    if ok:
        pend, _ = pending_tons(parsed["warehouse_id"])
        reply = t("sms_reply_ok", name=kw["name"], tons=kw["tons"], wh=kw["wh"], pend=round(pend, 1), truck=TRUCK_CAPACITY_T)
        return redirect(msg_url("/order", "msg_sms_ok", reply=reply))
    if key in ("msg_over_stock", "msg_wh_short"):
        reply = t("sms_reply_no", wh=kw["wh"], avail=kw.get("avail", 0.0))
        return redirect(msg_url("/order", "msg_sms_ok", kind="err", reply=reply))
    return redirect(msg_url("/order", "msg_sms_err", kind="err", e=t(key, **kw)))

_OC_ORDER_W = ("주문", "신청", "order", "request", "захиал", "хүсэлт")
_OC_CHECK_W = ("확인", "들어갔", "들어 갔", "들어왔", "접수", "됐", "됬", "되었", "되어", "내역", "조회", "check", "status", "went through",
               "go through", "receiv", "confirm", "my order", "my request", "шалга", "орсон", "бүртгэ", "миний")
_OC_SKIP_W  = ("방법", "어떻게", "how to", "how do", "яаж")
_OC_CANCEL_W = ("취소", "그만", "cancel", "stop", "болих", "зогс")

def wants_order_check(text):
    """'내 주문 들어갔는지 확인하고 싶어'처럼 본인 신청 확인을 원하는 말인지"""
    s = (text or "").lower()
    return any(w in s for w in _OC_ORDER_W) and any(w in s for w in _OC_CHECK_W) and not any(w in s for w in _OC_SKIP_W)

_OC_FILLER_PREFIX = ("이름", "전화", "번호", "창고", "신청", "주문", "확인", "저는", "제가", "입니다", "이에요", "예요", "이고", "그리고",
                     "name", "phone", "number", "warehouse", "нэр", "утас", "дугаар", "агуулах")
_OC_FILLER_EXACT = ("my", "is", "and", "the", "of")

def match_warehouse(text):
    """말 속에서 창고 이름(첫 낱말)을 찾아 (창고 id, 찾은 낱말)을 돌려줌"""
    s = (text or "").lower()
    for w in WAREHOUSES:
        for nm in w["name"].values():
            first = nm.split()[0].lower()   # '준모드 1호 창고' → '준모드'
            if first and first in s: return w["id"], first
    return None, None

def find_phone(text):
    """말 속에서 전화번호(숫자 7개 이상)를 찾음. 여러 개면 마지막 것"""
    best = ""
    for m in re.finditer(r"\+?\d[\d\s\-]{5,}\d", text or ""):
        if len(re.sub(r"\D", "", m.group())) >= 7: best = m.group()
    return best

def has_name_word(text, phone, wh_word):
    """전화번호·창고 이름·'이름은/입니다' 같은 군더더기를 빼고도 이름처럼 보이는 글자가 남아 있는지"""
    rest = (text or "").replace(phone, " ").lower().replace(wh_word or "\0", " ")
    for tok in re.split(r"[\s,./:;()]+", rest):
        if re.search(r"[a-zа-яөүё가-힣]{2,}", tok) and tok not in _OC_FILLER_EXACT and not tok.startswith(_OC_FILLER_PREFIX): return True
    return False

def find_my_orders(said, phone, wid):
    """말 속에 신청자 이름이 들어 있고 전화번호(끝 8자리)도 같은 신청만 찾음 ('윤준식이고' 같은 조사가 붙어도 찾도록 포함 여부로 비교)"""
    key = lambda s: re.sub(r"\s+", "", s or "").lower()
    p8 = lambda s: re.sub(r"\D", "", s or "")[-8:]
    rows = q("SELECT herder, phone, tons, status, ts FROM orders WHERE warehouse_id=? ORDER BY ts DESC LIMIT 500", (wid,))
    return [r for r in rows if key(r["herder"]) and key(r["herder"]) in key(said) and p8(r["phone"]) == p8(phone)]

def order_check_step(text, flow):
    """내 신청 확인 대화. 이름·전화번호·창고를 한 번에 받고, 빠진 것만 다시 물은 뒤 모두 맞으면 본인 신청 내역만 알려 줌.
       이름·전화번호는 AI(구글)에게 보내지 않고 여기서만 처리하며, 지금까지 받은 말은 화면(브라우저)이 들고 있다가 다시 보내 줌"""
    wh_list = ", ".join(w["name"][g.lang] for w in WAREHOUSES)
    reply = lambda key, flow=None, **kw: {"answer": t(key, **kw), "flow": flow, "private": True}
    if flow is None:
        if not find_phone(text): return reply("oc_intro", {"step": "info", "text": ""}, list=wh_list)   # 처음 말에 번호가 없으면 안내부터
        said = text[:300]
    else:
        if any(w in text.lower() for w in _OC_CANCEL_W): return reply("oc_cancel")
        said = ((str(flow.get("text", ""))[:300] + " " + text)[-300:])
    phone = find_phone(said); wid, wh_word = match_warehouse(said)
    need = ([t("oc_l_name")] if not has_name_word(said, phone, wh_word) else []) + ([t("oc_l_phone")] if not phone else []) \
         + ([t("oc_l_wh", list=wh_list)] if not wid else [])
    if need: return reply("oc_need", {"step": "info", "text": said}, what=", ".join(need))
    mine = find_my_orders(said, phone, wid)
    if not mine: return reply("oc_none")
    lines = "\n".join(f"• {str(r['ts'])[:10]} · {r['tons']}t · {t('pending') if r['status'] == 'pending' else t('dispatched')}" for r in mine[:5])
    return reply("oc_found", name=mine[0]["herder"], wh=wh_name(wid), lines=lines, truck=TRUCK_CAPACITY_T)


@app.route("/chat")
def chat():
    return render_template("chat.html")

@app.route("/api/chat", methods=["POST"])
def api_chat():
    data = request.get_json(silent=True) or request.form
    text = (data.get("text", "") or "").strip()
    if not text: return jsonify({"answer": t("chat_fallback")})
    flow = data.get("flow") if request.is_json else None
    if isinstance(flow, dict) and "?" not in text and "？" not in text: return jsonify(order_check_step(text, flow))   # 확인 대화 중이면 AI로 보내지 않음
    suggestions = suggest_questions(text)
    if suggestions: return jsonify({"answer": t("chat_pick"), "suggestions": suggestions})
    if wants_order_check(text) or len(re.sub(r"\D", "", find_phone(text))) >= 8: return jsonify(order_check_step(text, None))   # 전화번호가 든 말은 AI로 보내지 않고 신청 확인으로 연결
    history = data.get("history", []) if request.is_json else []
    return jsonify({"answer": ask_llm(text, history if isinstance(history, list) else []) or answer_faq(text)})

@app.route("/api/warehouses")
def api_warehouses():
    out = []
    for w in WAREHOUSES:
        p = predict(w); out.append({**w, **p, "availability": availability(w, p)})
    return jsonify(out)

@app.route("/api/demo/consume/<wid>", methods=["POST"])
def demo_consume(wid):
    w = WH_BY_ID.get(wid)
    if not w or not is_demo(): return "not found", 404
    last = latest_reading(wid)
    cur = float(last["stock_pct"]) if last else 50.0
    new_pct = record_reading(w, pct=max(0.0, cur - HAY_BALE_TON / w["capacity_ton"] * 100))  # v0.2의 ×3 버그 제거
    return redirect(msg_url(f"/warehouse/{wid}", "msg_consume", p=f"{new_pct:.1f}"))

@app.route("/api/demo/reset", methods=["POST"])
@admin_required
def demo_reset():
    if not is_demo(): return "not found", 404
    reset_demo_db()
    return redirect(msg_url("/admin", "msg_reset"))

@app.route("/admin/mode", methods=["POST"])
@admin_required
def admin_mode():
    """시연 ↔ 운영 전환. PIN 다시 입력 + 확인 글자(LIVE/DEMO) 입력이 모두 맞아야 바뀜"""
    if not MODE_SWITCHABLE: return "not found", 404
    f = request.form
    target = f.get("target", "")
    if target not in ("demo", "live"): return redirect(msg_url("/admin", "mode_bad", kind="err"))
    if not hmac.compare_digest(f.get("pin", "").encode(), ADMIN_PIN.encode()):
        return redirect(msg_url("/admin", "pin_bad", kind="err"))
    if f.get("confirm", "").strip().upper() != target.upper():
        return redirect(msg_url("/admin", "mode_confirm_bad", kind="err"))
    if target == current_mode(): return redirect(msg_url("/admin", "mode_same", kind="err"))
    set_mode(target)
    return redirect(msg_url("/admin", "msg_mode_set", m=t("mode_" + target)))

init_db()

if __name__ == "__main__":
    print("HayLink Lite v0.3 → http://127.0.0.1:5000")
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)), debug=False)
