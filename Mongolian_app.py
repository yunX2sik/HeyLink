# =====================================================================
#  HayLink Lite v0.2 - 몽골 조드(Dzud) 대비 건초창고 재고 자동기록 · 공동배송 프로토타입
#  모바일 UI + 3개 언어 (ko / en / mn)
#  실행: python app.py  →  브라우저 http://127.0.0.1:5000   (폰: http://노트북IP:5000)
#  필요: pip install flask
# =====================================================================
from flask import Flask, request, jsonify, render_template, redirect, g
from jinja2 import DictLoader
from urllib.parse import quote, urlparse
import sqlite3, datetime, random, json, urllib.request, os

# ─────────────── 설정 ───────────────
DB_FILE          = "haylink.db"
DEMO_MODE        = True          # 센서 없이 14일치 가짜 데이터 자동 생성
TRUCK_CAPACITY_T = 5.0           # 트럭 1대 분량(톤)
LEAD_DAYS        = 3             # 재보충 소요일
HAY_BALE_TON     = 0.35          # 시연용 건초 1묶음
LANGS            = ("ko", "en", "mn")
DEFAULT_LANG     = "ko"

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

# ═══════════════════ 번역 사전 ═══════════════════
T = {
 "tagline":      {"ko": "건초 재고 · 공동배송", "en": "Hay stock · shared delivery", "mn": "Өвсний нөөц · хамтарсан хүргэлт"},
 "nav_wh":       {"ko": "창고", "en": "Warehouses", "mn": "Агуулах"},
 "nav_order":    {"ko": "공동주문", "en": "Group order", "mn": "Захиалга"},
 "nav_admin":    {"ko": "관리자", "en": "Admin", "mn": "Удирдлага"},
 "footer":       {"ko": "HayLink Lite v0.2 · 프로토타입 · 데모 모드 {m}", "en": "HayLink Lite v0.2 · Prototype · Demo mode {m}", "mn": "HayLink Lite v0.2 · Прототип · Жишээ горим {m}"},
 # 창고 현황
 "idx_title":    {"ko": "소움 건초창고 현황", "en": "Soum hay warehouse status", "mn": "Сумын өвсний агуулахын байдал"},
 "province":     {"ko": "투브(Töv) 아이막", "en": "Töv Province", "mn": "Төв аймаг"},
 "capacity":     {"ko": "용량", "en": "Capacity", "mn": "Багтаамж"},
 "left":         {"ko": "남음", "en": "left", "mn": "үлдсэн"},
 "runs_out":     {"ko": "소진 예상", "en": "Runs out", "mn": "Дуусах хугацаа"},
 "per_day":      {"ko": "하루 소비", "en": "Daily use", "mn": "Өдрийн хэрэглээ"},
 "sensor_off":   {"ko": "센서 12시간 이상 무응답", "en": "Sensor offline >12 h", "mn": "Мэдрэгч 12+ цаг хариугүй"},
 "about_title":  {"ko": "이 화면은?", "en": "About this screen", "mn": "Энэ дэлгэц юу вэ?"},
 "about_body":   {"ko": "각 창고 천장의 초음파 센서(ESP32)가 5분마다 건초 높이를 측정해 재고를 자동 기록합니다. 소진 예상일은 최근 7일 감소 속도(선형회귀)에 한파 예보 가중치를 적용해 계산합니다.",
                  "en": "An ultrasonic sensor (ESP32) on each warehouse ceiling measures hay height every 5 minutes and records stock automatically. The depletion date is estimated from the 7-day decline rate (linear regression) weighted by the cold-weather forecast.",
                  "mn": "Агуулах бүрийн таазанд байрлуулсан хэт авианы мэдрэгч (ESP32) 5 минут тутамд өвсний өндрийг хэмжиж нөөцийг автоматаар бүртгэнэ. Дуусах хугацааг сүүлийн 7 хоногийн буурах хурд (шугаман регресс) дээр хүйтний урьдчилсан мэдээний жинг нэмж тооцоолно."},
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
 "grp_this":     {"ko": "이 창고 공동주문 현황", "en": "Group order for this warehouse", "mn": "Энэ агуулахын хамтарсан захиалга"},
 "truck1":       {"ko": "트럭 1대", "en": "1 truck", "mn": "1 ачааны машин"},
 "orders_n":     {"ko": "주문 {n}건", "en": "{n} orders", "mn": "{n} захиалга"},
 "join":         {"ko": "주문 참여하기", "en": "Join the order", "mn": "Захиалгад нэгдэх"},
 "sensor_info":  {"ko": "센서 정보", "en": "Sensor info", "mn": "Мэдрэгчийн мэдээлэл"},
 "node_id":      {"ko": "노드 ID", "en": "Node ID", "mn": "Зангилааны ID"},
 "d_empty":      {"ko": "천장~바닥 (빈 창고)", "en": "Ceiling to floor (empty)", "mn": "Тааз → шал (хоосон)"},
 "d_full":       {"ko": "천장~가득 찬 건초", "en": "Ceiling to full hay", "mn": "Тааз → дүүрэн өвс"},
 "last_dist":    {"ko": "마지막 거리 측정", "en": "Last distance", "mn": "Сүүлийн зай"},
 "demo_consume": {"ko": "🧪 시연: 건초 1묶음 반출 (−{b}t)", "en": "🧪 Demo: remove 1 bale (−{b} t)", "mn": "🧪 Жишээ: 1 боодол өвс гаргах (−{b} тн)"},
 # 주문
 "order_title":  {"ko": "사료 공동주문", "en": "Group feed order", "mn": "Тэжээлийн хамтарсан захиалга"},
 "order_sub":    {"ko": "트럭 1대({n}t)가 차면 함께 배송", "en": "Delivered together once 1 truck ({n} t) is full", "mn": "1 машин ({n} тн) дүүрэхэд хамт хүргэнэ"},
 "dispatch_btn": {"ko": "🚚 트럭 1대 분량 도달 — 배송 요청", "en": "🚚 Truck full — request delivery", "mn": "🚚 Машин дүүрсэн — хүргэлт хүсэх"},
 "more_needed":  {"ko": "{n}t 더 모이면 배송 가능", "en": "{n} t more to dispatch", "mn": "Дахин {n} тн цуглавал хүргэх боломжтой"},
 "via_app":      {"ko": "📱 ① 앱으로 주문", "en": "📱 ① Order via app", "mn": "📱 ① Аппаар захиалах"},
 "name":         {"ko": "이름", "en": "Name", "mn": "Нэр"},
 "ph_name":      {"ko": "예: Batbayar", "en": "e.g. Batbayar", "mn": "жишээ нь: Батбаяр"},
 "phone":        {"ko": "전화", "en": "Phone", "mn": "Утас"},
 "ph_phone":     {"ko": "예: 9911-1234", "en": "e.g. 9911-1234", "mn": "жишээ нь: 9911-1234"},
 "tons_needed":  {"ko": "필요 건초 (톤)", "en": "Hay needed (tons)", "mn": "Шаардлагатай өвс (тн)"},
 "submit":       {"ko": "주문 등록", "en": "Submit order", "mn": "Захиалга өгөх"},
 "offline_note": {"ko": "오프라인이면 폰에 저장 후 신호가 잡힐 때 자동 전송 (실서비스 시 구현)", "en": "If offline, saved on the phone and sent when signal returns (production feature)", "mn": "Сүлжээгүй бол утсанд хадгалж, сүлжээ орох үед автоматаар илгээнэ (бодит хувилбарт)"},
 "via_sms":      {"ko": "✉️ ② SMS 문자로 주문 (시뮬레이션)", "en": "✉️ ② Order via SMS (simulation)", "mn": "✉️ ② Мессежээр захиалах (жишээ)"},
 "sender":       {"ko": "발신 번호", "en": "Sender number", "mn": "Илгээгчийн дугаар"},
 "process_sms":  {"ko": "문자 수신 처리", "en": "Process SMS", "mn": "Мессеж боловсруулах"},
 "sms_note":     {"ko": "형식: <code>HAY 창고 톤수 이름</code> — 2G 신호만 있어도 가능. 실서비스에서는 통신사 SMS 게이트웨이가 이 입력을 대신합니다.",
                  "en": "Format: <code>HAY warehouse tons name</code> — works with 2G signal only. In production a carrier SMS gateway replaces this input.",
                  "mn": "Формат: <code>HAY агуулах тонн нэр</code> — 2G сүлжээтэй ч болно. Бодит үйлчилгээнд операторын SMS gateway энэ оролтыг орлоно."},
 "recent":       {"ko": "최근 주문", "en": "Recent orders", "mn": "Сүүлийн захиалгууд"},
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
 "pending_orders":{"ko": "대기 주문", "en": "Pending orders", "mn": "Хүлээгдэж буй захиалга"},
 "sensor":       {"ko": "센서", "en": "Sensor", "mn": "Мэдрэгч"},
 "online":       {"ko": "🟢 정상", "en": "🟢 Online", "mn": "🟢 Хэвийн"},
 "offline":      {"ko": "🔴 무응답", "en": "🔴 Offline", "mn": "🔴 Хариугүй"},
 "days":         {"ko": "일", "en": "days", "mn": "хоног"},
 "proxy_title":  {"ko": "🧑‍🌾 ③ 대리 주문 등록", "en": "🧑‍🌾 ③ Proxy order", "mn": "🧑‍🌾 ③ Төлөөлөн захиалах"},
 "proxy_who":    {"ko": "바그장 · 창고 관리자", "en": "bagh leader · warehouse manager", "mn": "багийн дарга · агуулахын менежер"},
 "proxy_note":   {"ko": "무신호 지역 목민이 전화·방문으로 요청한 주문을 대신 입력합니다.", "en": "Enter orders requested by phone or in person from herders without signal.", "mn": "Сүлжээгүй малчдын утсаар болон биечлэн өгсөн захиалгыг төлөөлж оруулна."},
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
 # 등급 · 한파
 "lv_ok":        {"ko": "정상", "en": "Normal", "mn": "Хэвийн"},
 "lv_warn":      {"ko": "주의 — 재보충 준비", "en": "Caution — prepare restock", "mn": "Анхаар — нөөц нөхөхөд бэлтгэ"},
 "lv_danger":    {"ko": "위험 — 즉시 재보충", "en": "Critical — restock now", "mn": "Аюултай — нэн даруй нөхөх"},
 "lv_low":       {"ko": "소비 미미", "en": "Low usage", "mn": "Хэрэглээ бага"},
 "cold_none":    {"ko": "기온 정보 없음 (기본값)", "en": "No temperature data (default)", "mn": "Температурын мэдээлэл алга (анхдагч)"},
 "cold_extreme": {"ko": "극한파 (−35℃ 이하) → 소비 1.5배", "en": "Extreme cold (≤ −35℃) → usage ×1.5", "mn": "Хэт хүйтэн (−35℃-ээс доош) → хэрэглээ 1.5 дахин"},
 "cold_severe":  {"ko": "강한 한파 (−25℃ 이하) → 소비 1.3배", "en": "Severe cold (≤ −25℃) → usage ×1.3", "mn": "Хүчтэй хүйтэн (−25℃-ээс доош) → хэрэглээ 1.3 дахин"},
 "cold_mild":    {"ko": "한파 (−15℃ 이하) → 소비 1.15배", "en": "Cold (≤ −15℃) → usage ×1.15", "mn": "Хүйтэн (−15℃-ээс доош) → хэрэглээ 1.15 дахин"},
 "cold_normal":  {"ko": "평년 수준", "en": "Normal level", "mn": "Хэвийн түвшин"},
 # 메시지
 "msg_order_ok": {"ko": "✅ 주문 등록 완료: {name} {tons}t", "en": "✅ Order registered: {name} {tons} t", "mn": "✅ Захиалга бүртгэгдсэн: {name} {tons} тн"},
 "msg_not_enough":{"ko": "아직 {n}t 미달", "en": "Still below {n} t", "mn": "{n} тн-д хүрээгүй байна"},
 "msg_dispatch": {"ko": "🚚 {wh} 공동배송 요청 완료 ({tons}t, {hh})", "en": "🚚 Shared delivery requested for {wh} ({tons} t, {hh})", "mn": "🚚 {wh} хамтарсан хүргэлт хүссэн ({tons} тн, {hh})"},
 "msg_reading":  {"ko": "📡 측정값 기록: {wh} {d}cm → 재고 {p}%", "en": "📡 Reading saved: {wh} {d} cm → stock {p}%", "mn": "📡 Хэмжилт хадгалагдсан: {wh} {d} см → нөөц {p}%"},
 "msg_sms_err":  {"ko": "SMS 오류: {e}", "en": "SMS error: {e}", "mn": "SMS алдаа: {e}"},
 "msg_sms_ok":   {"ko": "✉️ SMS 주문 접수: {name} {tons}t → {wh} (회신 문자 발송됨)", "en": "✉️ SMS order received: {name} {tons} t → {wh} (reply sent)", "mn": "✉️ SMS захиалга хүлээн авсан: {name} {tons} тн → {wh} (хариу мессеж илгээсэн)"},
 "msg_consume":  {"ko": "건초 반출 → 재고 {p}%", "en": "Hay removed → stock {p}%", "mn": "Өвс гаргасан → нөөц {p}%"},
 "msg_reset":    {"ko": "데모 데이터 초기화 완료", "en": "Demo data reset", "mn": "Жишээ өгөгдөл шинэчлэгдсэн"},
 "sms_fmt":      {"ko": "형식 오류. 예) HAY zuunmod 2 Bold", "en": "Wrong format. e.g. HAY zuunmod 2 Bold", "mn": "Формат буруу. жишээ нь: HAY zuunmod 2 Bold"},
 "sms_nowh":     {"ko": "'{k}' 창고를 찾을 수 없음", "en": "Warehouse '{k}' not found", "mn": "'{k}' агуулах олдсонгүй"},
 "sms_num":      {"ko": "톤수는 숫자여야 함", "en": "Tons must be a number", "mn": "Тонн нь тоо байх ёстой"},
 "sms_herder":   {"ko": "SMS 목민", "en": "SMS herder", "mn": "SMS малчин"},
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

@app.context_processor
def inject():
    return {"t": t, "lang": g.lang, "wh_name": wh_name, "demo": DEMO_MODE, "truck": TRUCK_CAPACITY_T,
            "lead": LEAD_DAYS, "bale": HAY_BALE_TON, "warehouses": WAREHOUSES}

def msg_url(path, key, **kw):
    return f"{path}?msg={quote(t(key, **kw))}"

# ═══════════════════ DB ═══════════════════
def db():
    con = sqlite3.connect(DB_FILE); con.row_factory = sqlite3.Row; return con

def init_db():
    con = db(); cur = con.cursor()
    cur.executescript("""
    CREATE TABLE IF NOT EXISTS readings(id INTEGER PRIMARY KEY AUTOINCREMENT, warehouse_id TEXT, distance_cm REAL, stock_pct REAL, ts TEXT);
    CREATE TABLE IF NOT EXISTS orders(id INTEGER PRIMARY KEY AUTOINCREMENT, warehouse_id TEXT, herder TEXT, phone TEXT, tons REAL, channel TEXT, status TEXT, ts TEXT);
    CREATE TABLE IF NOT EXISTS deliveries(id INTEGER PRIMARY KEY AUTOINCREMENT, warehouse_id TEXT, total_tons REAL, n_orders INTEGER, ts TEXT);
    """)
    con.commit()
    if DEMO_MODE and cur.execute("SELECT COUNT(*) FROM readings").fetchone()[0] == 0:
        seed_demo(cur); con.commit()
    con.close()

def seed_demo(cur):
    now = datetime.datetime.now()
    profile = {"zuunmod_01": (88, 2.2), "bayan_01": (70, 4.5), "altanbulag_01": (95, 1.4), "sergelen_01": (55, 3.8)}
    for w in WAREHOUSES:
        start, per_day = profile[w["id"]]
        for step in range(14 * 4):
            ts = now - datetime.timedelta(hours=(14 * 4 - step) * 6)
            pct = max(2, start - per_day * (step / 4) + random.uniform(-1.5, 1.5))
            cur.execute("INSERT INTO readings VALUES(NULL,?,?,?,?)",
                        (w["id"], round(pct_to_distance(w, pct), 1), round(pct, 1), ts.isoformat(timespec="seconds")))
    for o in [("zuunmod_01", "Batbayar", "9911-0001", 1.5, "app"), ("zuunmod_01", "Oyunaa", "9911-0002", 2.0, "sms"),
              ("bayan_01", "Dorj", "9911-0003", 1.0, "proxy")]:
        cur.execute("INSERT INTO orders VALUES(NULL,?,?,?,?,?,?,?)", (*o, "pending", now.isoformat(timespec="seconds")))

# ═══════════════════ 계산 ═══════════════════
def distance_to_pct(w, d):
    return max(0.0, min(100.0, (w["d_empty_cm"] - d) / (w["d_empty_cm"] - w["d_full_cm"]) * 100))

def pct_to_distance(w, pct):
    return w["d_empty_cm"] - pct / 100 * (w["d_empty_cm"] - w["d_full_cm"])

def latest_reading(wid):
    con = db(); r = con.execute("SELECT * FROM readings WHERE warehouse_id=? ORDER BY ts DESC LIMIT 1", (wid,)).fetchone(); con.close(); return r

def readings_last_days(wid, days=7):
    since = (datetime.datetime.now() - datetime.timedelta(days=days)).isoformat()
    con = db(); rows = con.execute("SELECT * FROM readings WHERE warehouse_id=? AND ts>=? ORDER BY ts", (wid, since)).fetchall(); con.close(); return rows

def linear_slope(xs, ys):
    n = len(xs)
    if n < 2: return 0.0
    mx, my = sum(xs) / n, sum(ys) / n
    sxx = sum((x - mx) ** 2 for x in xs)
    return 0.0 if sxx == 0 else sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sxx

_temp_cache = {}
def fetch_min_temp(lat, lon):
    key = (round(lat, 1), round(lon, 1))
    if key in _temp_cache: return _temp_cache[key]
    url = (f"https://api.open-meteo.com/v1/forecast?latitude={lat}&longitude={lon}"
           f"&daily=temperature_2m_min&forecast_days=7&timezone=Asia%2FUlaanbaatar")
    try:
        with urllib.request.urlopen(url, timeout=3) as res:
            temps = json.loads(res.read())["daily"]["temperature_2m_min"]
        val = round(sum(temps) / len(temps), 1)
    except Exception:
        val = None
    _temp_cache[key] = val; return val

def cold_factor(tm):
    if tm is None:  return 1.0, "cold_none"
    if tm <= -35:   return 1.5, "cold_extreme"
    if tm <= -25:   return 1.3, "cold_severe"
    if tm <= -15:   return 1.15, "cold_mild"
    return 1.0, "cold_normal"

def predict(w):
    rows = readings_last_days(w["id"], 7); last = latest_reading(w["id"])
    cur_pct = last["stock_pct"] if last else 0
    if len(rows) >= 2:
        t0 = datetime.datetime.fromisoformat(rows[0]["ts"])
        xs = [(datetime.datetime.fromisoformat(r["ts"]) - t0).total_seconds() / 86400 for r in rows]
        slope = linear_slope(xs, [r["stock_pct"] for r in rows])
    else:
        slope = 0.0
    per_day = -slope
    temp = fetch_min_temp(w["lat"], w["lon"]); factor, factor_key = cold_factor(temp)
    days_base = cur_pct / per_day if per_day > 0.05 else None
    days_cold = days_base / factor if days_base else None
    days_use = days_cold if days_cold is not None else days_base
    if days_use is None:            level, level_key = "ok", "lv_low"
    elif days_use <= LEAD_DAYS:     level, level_key = "danger", "lv_danger"
    elif days_use <= LEAD_DAYS + 4: level, level_key = "warn", "lv_warn"
    else:                           level, level_key = "ok", "lv_ok"
    today = datetime.date.today()
    return {
        "cur_pct": round(cur_pct, 1), "cur_ton": round(cur_pct / 100 * w["capacity_ton"], 1),
        "per_day": round(per_day, 2), "temp_min": temp, "factor": factor, "factor_key": factor_key,
        "days_base": round(days_base, 1) if days_base else None, "days_cold": round(days_cold, 1) if days_cold else None,
        "days_use": round(days_use, 1) if days_use else None,
        "deplete_date": (today + datetime.timedelta(days=days_use)).strftime("%m/%d") if days_use else "-",
        "reorder_date": (today + datetime.timedelta(days=max(0, days_use - LEAD_DAYS))).strftime("%m/%d") if days_use else "-",
        "level": level, "level_key": level_key,
        "last_ts": last["ts"].replace("T", " ") if last else "-",
        "sensor_ok": bool(last) and (datetime.datetime.now() - datetime.datetime.fromisoformat(last["ts"])) < datetime.timedelta(hours=12),
    }

def pending_tons(wid):
    con = db(); r = con.execute("SELECT COALESCE(SUM(tons),0) s, COUNT(*) n FROM orders WHERE warehouse_id=? AND status='pending'", (wid,)).fetchone(); con.close()
    return r["s"], r["n"]

def svg_chart(rows, width=440, height=180):
    if len(rows) < 2: return f"<p class='muted'>{t('no_data')}</p>"
    t0 = datetime.datetime.fromisoformat(rows[0]["ts"]); t1 = datetime.datetime.fromisoformat(rows[-1]["ts"])
    span = max((t1 - t0).total_seconds(), 1); pad = 28; pts = []
    for r in rows:
        x = pad + ((datetime.datetime.fromisoformat(r["ts"]) - t0).total_seconds() / span) * (width - 2 * pad)
        y = pad + (1 - r["stock_pct"] / 100) * (height - 2 * pad); pts.append(f"{x:.1f},{y:.1f}")
    grid = "".join(f'<line x1="{pad}" y1="{pad+(1-p/100)*(height-2*pad):.1f}" x2="{width-pad}" y2="{pad+(1-p/100)*(height-2*pad):.1f}" stroke="#eef1ed"/>'
                   f'<text x="2" y="{pad+(1-p/100)*(height-2*pad)+4:.1f}" font-size="10" fill="#8a958c">{p}%</text>' for p in (0, 25, 50, 75, 100))
    return (f'<svg viewBox="0 0 {width} {height}" style="width:100%;display:block">{grid}'
            f'<polyline fill="none" stroke="#2e7d32" stroke-width="2.5" stroke-linejoin="round" points="{" ".join(pts)}"/>'
            f'<text x="{pad}" y="{height-6}" font-size="10" fill="#8a958c">{t0.strftime("%m/%d")}</text>'
            f'<text x="{width-pad-28}" y="{height-6}" font-size="10" fill="#8a958c">{t1.strftime("%m/%d")}</text></svg>')

def parse_sms(text):
    parts = text.strip().split()
    if len(parts) < 3 or parts[0].upper() != "HAY": return None, t("sms_fmt")
    key = parts[1].lower()
    w = next((w for w in WAREHOUSES if key in w["id"].lower() or any(key in s.lower() for s in w["soum"].values())), None)
    if not w: return None, t("sms_nowh", k=parts[1])
    try: tons = float(parts[2])
    except ValueError: return None, t("sms_num")
    return {"warehouse_id": w["id"], "tons": tons, "herder": " ".join(parts[3:]) or t("sms_herder")}, "OK"

def add_order(wid, herder, phone, tons, channel):
    con = db()
    con.execute("INSERT INTO orders VALUES(NULL,?,?,?,?,?,?,?)", (wid, herder, phone, tons, channel, "pending", datetime.datetime.now().isoformat(timespec="seconds")))
    con.commit(); con.close()

# ═══════════════════ 화면 (모바일 UI) ═══════════════════
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
button.secondary{background:#607d8b} button.danger{background:#e53935} button.outline{background:#fff;color:#2e5d34;border:1.5px solid #2e5d34}
.msg{background:#e8f5e9;border-left:4px solid #43a047;padding:12px;border-radius:12px;margin-bottom:12px;font-size:.9rem}
.item{display:flex;justify-content:space-between;align-items:center;padding:10px 0;border-bottom:1px solid #eef1ed;font-size:.9rem;gap:8px} .item:last-child{border-bottom:none}
.rank{width:28px;height:28px;border-radius:50%;background:#2e5d34;color:#fff;display:inline-flex;align-items:center;justify-content:center;font-size:.8rem;font-weight:700;flex-shrink:0}
.tabs{position:fixed;bottom:0;left:50%;transform:translateX(-50%);width:100%;max-width:480px;background:#fff;border-top:1px solid #e0e4de;display:flex;padding:6px 0 calc(8px + env(safe-area-inset-bottom));z-index:10}
.tabs a{flex:1;text-align:center;text-decoration:none;color:#8a958c;font-size:.72rem;font-weight:600;display:flex;flex-direction:column;align-items:center;gap:2px}
.tabs a span{font-size:1.35rem} .tabs a.on{color:#2e5d34}
code{background:#f0f2ee;padding:2px 6px;border-radius:6px;font-size:.85em;word-break:break-all}
.two{display:grid;grid-template-columns:1fr 1fr;gap:10px}
footer{text-align:center;color:#9aa49c;font-size:.75rem;padding:8px 0 4px}
</style></head><body><div class="phone">
<header><a class="logo" href="/">🌾 HayLink Lite<small>{{ t('tagline') }}</small></a>
<div class="lang">{% for c,l in [('ko','KO'),('en','EN'),('mn','MN')] %}<a href="/lang/{{ c }}" class="{{ 'on' if c==lang else '' }}">{{ l }}</a>{% endfor %}</div></header>
<main>{% if request.args.get('msg') %}<div class="msg">{{ request.args.get('msg') }}</div>{% endif %}
{% block content %}{% endblock %}
<footer>{{ t('footer', m='ON' if demo else 'OFF') }}</footer></main>
<nav class="tabs">
<a href="/" class="{{ 'on' if request.path=='/' or request.path.startswith('/warehouse') else '' }}"><span>🏠</span>{{ t('nav_wh') }}</a>
<a href="/order" class="{{ 'on' if request.path.startswith('/order') else '' }}"><span>🚚</span>{{ t('nav_order') }}</a>
<a href="/admin" class="{{ 'on' if request.path.startswith('/admin') else '' }}"><span>📊</span>{{ t('nav_admin') }}</a>
</nav></div></body></html>"""

INDEX = """{% extends "base" %}{% block content %}
<h1>{{ t('idx_title') }}<span class="sub">{{ t('province') }}</span></h1>
{% for w, p in items %}
<a class="card-link" href="/warehouse/{{ w.id }}"><div class="card">
 <div class="top"><div><h2 style="margin:0">{{ w.name[lang] }}</h2><div class="muted">{{ w.soum[lang] }} · {{ t('capacity') }} {{ w.capacity_ton }}t</div></div>
  <span class="badge {{ p.level }}">{{ t(p.level_key) }}</span></div>
 <div class="gauge"><div class="{{ p.level }}" style="width:{{ p.cur_pct }}%"></div></div>
 <div style="display:flex;justify-content:space-between;align-items:baseline;flex-wrap:wrap;gap:4px">
  <span><b style="font-size:1.4rem">{{ p.cur_pct }}%</b> <span class="muted">≈ {{ p.cur_ton }}t {{ t('left') }}</span></span>
  <span class="muted">{{ t('runs_out') }} <b>{{ p.deplete_date }}</b></span></div>
 <div class="muted">{{ t('per_day') }} {{ p.per_day }}%{% if not p.sensor_ok %} · <span style="color:#e53935">⚠ {{ t('sensor_off') }}</span>{% endif %}</div>
</div></a>
{% endfor %}
<div class="card"><h2>ℹ️ {{ t('about_title') }}</h2><p class="muted" style="margin:0">{{ t('about_body') }}</p></div>
{% endblock %}"""

DETAIL = """{% extends "base" %}{% block content %}
<a href="/" class="muted" style="text-decoration:none">{{ t('back') }}</a>
<h1 style="margin-top:8px">{{ w.name[lang] }}<span class="sub">{{ w.soum[lang] }} · <span class="badge {{ p.level }}">{{ t(p.level_key) }}</span></span></h1>
<div class="card"><div class="muted">{{ t('cur_stock') }}</div>
 <div style="display:flex;align-items:baseline;gap:10px"><span class="big">{{ p.cur_pct }}%</span><span class="muted">≈ {{ p.cur_ton }}t / {{ w.capacity_ton }}t</span></div>
 <div class="gauge"><div class="{{ p.level }}" style="width:{{ p.cur_pct }}%"></div></div>
 <div class="muted">{{ t('last_reading') }}: {{ p.last_ts }}</div></div>
<div class="card"><div class="muted">{{ t('forecast') }}</div>
 <div style="display:flex;align-items:baseline;gap:10px"><span class="big">{{ p.deplete_date }}</span>
  {% if p.days_base %}<span class="muted">{{ t('base_days', a=p.days_base, b=p.days_cold) }}</span>{% endif %}</div>
 <div class="muted">🌡 {{ t('temp_min') }}: {{ p.temp_min if p.temp_min is not none else '?' }}℃ · {{ t(p.factor_key) }}</div>
 <div style="margin-top:10px;padding:10px 12px;background:#f0f6f1;border-radius:12px">📦 {{ t('reorder') }}: <b>{{ p.reorder_date }}</b> <span class="muted">({{ t('lead_note', n=lead) }})</span></div></div>
<div class="card"><h2>{{ t('trend') }}</h2>{{ chart|safe }}</div>
<div class="card"><h2>{{ t('grp_this') }}</h2>
 <div class="gauge"><div class="ok" style="width:{{ (pend/truck*100)|round|int if pend<truck else 100 }}%"></div></div>
 <div><b>{{ pend }}t</b> / {{ t('truck1') }} {{ truck }}t · {{ t('orders_n', n=n) }}</div>
 <a href="/order?w={{ w.id }}"><button style="margin-top:10px">{{ t('join') }}</button></a></div>
<div class="card"><h2>{{ t('sensor_info') }}</h2>
 <div class="kv"><span>{{ t('node_id') }}</span><b><code>{{ w.id }}</code></b></div>
 <div class="kv"><span>{{ t('d_empty') }}</span><b>{{ w.d_empty_cm }} cm</b></div>
 <div class="kv"><span>{{ t('d_full') }}</span><b>{{ w.d_full_cm }} cm</b></div>
 <div class="kv"><span>{{ t('last_dist') }}</span><b>{{ last_dist }} cm</b></div>
 <form method="post" action="/api/demo/consume/{{ w.id }}"><button class="secondary" type="submit">{{ t('demo_consume', b=bale) }}</button></form></div>
{% endblock %}"""

ORDER = """{% extends "base" %}{% block content %}
<h1>{{ t('order_title') }}<span class="sub">{{ t('order_sub', n=truck) }}</span></h1>
{% for w, pend, n in stats %}
<div class="card"><div class="top"><div><h2 style="margin:0">{{ w.name[lang] }}</h2><div class="muted">{{ w.soum[lang] }}</div></div><b>{{ pend }}t / {{ truck }}t</b></div>
 <div class="gauge"><div class="{{ 'ok' if pend>=truck else 'warn' }}" style="width:{{ (pend/truck*100)|round|int if pend<truck else 100 }}%"></div></div>
 <div class="muted">{{ t('orders_n', n=n) }}</div>
 {% if pend >= truck %}<form method="post" action="/dispatch/{{ w.id }}"><button>{{ t('dispatch_btn') }}</button></form>
 {% else %}<div class="muted" style="margin-top:4px">{{ t('more_needed', n=(truck-pend)|round(1)) }}</div>{% endif %}</div>
{% endfor %}
<div class="card"><h2>{{ t('via_app') }}</h2>
 <form method="post" action="/order">
  <select name="warehouse_id">{% for w in warehouses %}<option value="{{ w.id }}" {% if w.id==sel %}selected{% endif %}>{{ w.name[lang] }}</option>{% endfor %}</select>
  <input name="herder" placeholder="{{ t('name') }} ({{ t('ph_name') }})" required>
  <input name="phone" placeholder="{{ t('phone') }} ({{ t('ph_phone') }})">
  <input name="tons" type="number" step="0.5" min="0.5" placeholder="{{ t('tons_needed') }}" required>
  <button type="submit">{{ t('submit') }}</button></form>
 <p class="muted" style="margin:6px 0 0">{{ t('offline_note') }}</p></div>
<div class="card"><h2>{{ t('via_sms') }}</h2>
 <form method="post" action="/api/sms">
  <input name="phone" placeholder="{{ t('sender') }}" value="9900-0000">
  <input name="text" placeholder="HAY zuunmod 2 Bold" required>
  <button type="submit" class="secondary">{{ t('process_sms') }}</button></form>
 <p class="muted" style="margin:6px 0 0">{{ t('sms_note')|safe }}</p></div>
<div class="card"><h2>{{ t('recent') }}</h2>
{% set ch = {'app':'ch_app','sms':'ch_sms','proxy':'ch_proxy'} %}
{% for o in orders %}<div class="item"><div><b>{{ o.herder }}</b> · {{ o.tons }}t<div class="muted">{{ wh_name(o.warehouse_id) }} · {{ o.ts[5:16].replace('T',' ') }}</div></div>
 <div style="text-align:right"><div>{{ t(ch[o.channel]) }}</div><div class="muted">{{ t('pending') if o.status=='pending' else t('dispatched') }}</div></div></div>{% endfor %}
{% if not orders %}<div class="muted">{{ t('none_yet') }}</div>{% endif %}</div>
{% endblock %}"""

ADMIN = """{% extends "base" %}{% block content %}
<h1>{{ t('admin_title') }}<span class="sub">{{ t('admin_sub') }}</span></h1>
<div class="card"><h2>{{ t('priority') }}</h2>
{% for w, p, pend, n in rows %}
<a class="card-link" href="/warehouse/{{ w.id }}"><div class="item">
 <span class="rank">{{ loop.index }}</span>
 <div style="flex:1"><b>{{ w.name[lang] }}</b> <span class="badge {{ p.level }}">{{ t(p.level_key) }}</span>
  <div class="muted">{{ t('stock') }} {{ p.cur_pct }}% ({{ p.cur_ton }}t) · {{ t('runs_out') }} {{ p.deplete_date }}{% if p.days_use %} ({{ p.days_use }} {{ t('days') }}){% endif %}</div>
  <div class="muted">{{ t('reorder') }} {{ p.reorder_date }} · {{ t('pending_orders') }} {{ pend }}t/{{ n }} · {{ t('sensor') }} {{ t('online') if p.sensor_ok else t('offline') }}</div></div>
</div></a>{% endfor %}</div>
<div class="card"><h2>{{ t('proxy_title') }}<span class="sub">{{ t('proxy_who') }}</span></h2>
 <p class="muted" style="margin:0 0 6px">{{ t('proxy_note') }}</p>
 <form method="post" action="/order">
  <select name="warehouse_id">{% for w in warehouses %}<option value="{{ w.id }}">{{ w.name[lang] }}</option>{% endfor %}</select>
  <input name="herder" placeholder="{{ t('herder_name') }}" required><input name="phone" placeholder="{{ t('phone') }}">
  <input name="tons" type="number" step="0.5" min="0.5" placeholder="{{ t('tons_needed') }}" required>
  <input type="hidden" name="channel" value="proxy"><input type="hidden" name="back" value="/admin">
  <button type="submit">{{ t('register') }}</button></form></div>
<div class="card"><h2>{{ t('deliveries') }}</h2>
{% for d in deliveries %}<div class="item"><div><b>{{ wh_name(d.warehouse_id) }}</b><div class="muted">{{ d.ts[5:16].replace('T',' ') }}</div></div><div style="text-align:right"><b>{{ d.total_tons }}t</b><div class="muted">{{ t('households', n=d.n_orders) }}</div></div></div>{% endfor %}
{% if not deliveries %}<div class="muted">{{ t('none_yet') }}</div>{% endif %}</div>
<div class="card"><h2>{{ t('sensor_api') }}</h2><p class="muted" style="margin:0 0 6px">{{ t('api_note')|safe }}</p>
 <form method="post" action="/api/reading">
  <select name="warehouse_id">{% for w in warehouses %}<option value="{{ w.id }}">{{ w.id }}</option>{% endfor %}</select>
  <input name="distance_cm" type="number" step="0.1" placeholder="{{ t('dist_test') }}">
  <button class="secondary" type="submit">{{ t('send_test') }}</button></form>
 <form method="post" action="/api/demo/reset" style="margin-top:6px"><button class="danger" type="submit">{{ t('reset') }}</button></form></div>
{% endblock %}"""

app.jinja_loader = DictLoader({"base": BASE, "index": INDEX, "detail": DETAIL, "order": ORDER, "admin": ADMIN})

# ═══════════════════ 라우트 ═══════════════════
@app.route("/lang/<code>")
def set_lang(code):
    if code not in LANGS: code = DEFAULT_LANG
    back = urlparse(request.referrer).path if request.referrer else "/"
    resp = redirect(back or "/")
    resp.set_cookie("lang", code, max_age=60 * 60 * 24 * 365)
    return resp

@app.route("/")
def index():
    return render_template("index", items=[(w, predict(w)) for w in WAREHOUSES])

@app.route("/warehouse/<wid>")
def detail(wid):
    w = WH_BY_ID.get(wid)
    if not w: return "not found", 404
    p = predict(w); last = latest_reading(wid); pend, n = pending_tons(wid)
    return render_template("detail", w=w, p=p, chart=svg_chart(readings_last_days(wid, 7)),
                           pend=round(pend, 1), n=n, last_dist=last["distance_cm"] if last else "-")

@app.route("/order", methods=["GET", "POST"])
def order():
    if request.method == "POST":
        f = request.form
        add_order(f["warehouse_id"], f["herder"], f.get("phone", ""), float(f["tons"]), f.get("channel", "app"))
        return redirect(msg_url(f.get("back", "/order"), "msg_order_ok", name=f["herder"], tons=f["tons"]))
    stats = []
    for w in WAREHOUSES:
        pend, n = pending_tons(w["id"]); stats.append((w, round(pend, 1), n))
    con = db(); orders = con.execute("SELECT * FROM orders ORDER BY ts DESC LIMIT 15").fetchall(); con.close()
    return render_template("order", stats=stats, orders=orders, sel=request.args.get("w", WAREHOUSES[0]["id"]))

@app.route("/dispatch/<wid>", methods=["POST"])
def dispatch(wid):
    pend, n = pending_tons(wid)
    if pend < TRUCK_CAPACITY_T: return redirect(msg_url("/order", "msg_not_enough", n=TRUCK_CAPACITY_T))
    con = db()
    con.execute("UPDATE orders SET status='dispatched' WHERE warehouse_id=? AND status='pending'", (wid,))
    con.execute("INSERT INTO deliveries VALUES(NULL,?,?,?,?)", (wid, round(pend, 1), n, datetime.datetime.now().isoformat(timespec="seconds")))
    con.commit(); con.close()
    return redirect(msg_url("/order", "msg_dispatch", wh=wh_name(wid), tons=f"{pend:.1f}", hh=t("households", n=n)))

@app.route("/admin")
def admin():
    rows = []
    for w in WAREHOUSES:
        p = predict(w); pend, n = pending_tons(w["id"]); rows.append((w, p, round(pend, 1), n))
    rows.sort(key=lambda r: (r[1]["days_use"] or 9999))
    con = db(); deliveries = con.execute("SELECT * FROM deliveries ORDER BY ts DESC LIMIT 10").fetchall(); con.close()
    return render_template("admin", rows=rows, deliveries=deliveries)

@app.route("/api/reading", methods=["POST"])
def api_reading():
    data = request.get_json(silent=True) or request.form
    w = WH_BY_ID.get(data.get("warehouse_id", ""))
    if not w: return jsonify({"ok": False, "error": "unknown warehouse_id"}), 400
    try: dist = float(data.get("distance_cm"))
    except (TypeError, ValueError): return jsonify({"ok": False, "error": "distance_cm required"}), 400
    pct = distance_to_pct(w, dist)
    con = db()
    con.execute("INSERT INTO readings VALUES(NULL,?,?,?,?)", (w["id"], dist, round(pct, 1), datetime.datetime.now().isoformat(timespec="seconds")))
    con.commit(); con.close()
    if request.is_json: return jsonify({"ok": True, "warehouse_id": w["id"], "distance_cm": dist, "stock_pct": round(pct, 1)})
    return redirect(msg_url("/admin", "msg_reading", wh=w["id"], d=dist, p=f"{pct:.1f}"))

@app.route("/api/sms", methods=["POST"])
def api_sms():
    src = request.get_json(silent=True) or request.form
    parsed, err = parse_sms(src.get("text", ""))
    if not parsed: return redirect(msg_url("/order", "msg_sms_err", e=err))
    add_order(parsed["warehouse_id"], parsed["herder"], src.get("phone", ""), parsed["tons"], "sms")
    return redirect(msg_url("/order", "msg_sms_ok", name=parsed["herder"], tons=parsed["tons"], wh=wh_name(parsed["warehouse_id"])))

@app.route("/api/warehouses")
def api_warehouses():
    return jsonify([{**w, **predict(w)} for w in WAREHOUSES])

@app.route("/api/demo/consume/<wid>", methods=["POST"])
def demo_consume(wid):
    w = WH_BY_ID[wid]; last = latest_reading(wid)
    cur = last["stock_pct"] if last else 50
    new_pct = max(0, cur - HAY_BALE_TON / w["capacity_ton"] * 100 * 3)
    con = db()
    con.execute("INSERT INTO readings VALUES(NULL,?,?,?,?)", (wid, round(pct_to_distance(w, new_pct), 1), round(new_pct, 1), datetime.datetime.now().isoformat(timespec="seconds")))
    con.commit(); con.close()
    return redirect(msg_url(f"/warehouse/{wid}", "msg_consume", p=f"{new_pct:.1f}"))

@app.route("/api/demo/reset", methods=["POST"])
def demo_reset():
    if os.path.exists(DB_FILE): os.remove(DB_FILE)
    init_db()
    return redirect(msg_url("/admin", "msg_reset"))

init_db()

if __name__ == "__main__":
    print("HayLink Lite v0.2 → http://127.0.0.1:5000")
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)), debug=False)
