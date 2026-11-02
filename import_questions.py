# =====================================================================
#  AI-Hub '소상공인 고객 주문 질의-응답' 데이터에서 손님 질문을 뽑아 questions.db 에 저장
#  실행: python import_questions.py   (한 번만 실행하면 됨. 다시 실행하면 questions.db 의 질문표만 새로 만듦)
#  - data_extracted 폴더의 라벨링데이터 zip(train, validation)을 읽음
#  - 손님(c)이 한 질문(q) 중 인텐트가 '<주제>_<종류>_질문' 인 것만 사용
#  - 띄어쓰기·문장부호만 다른 질문은 같은 질문으로 합쳐 횟수를 셈
# =====================================================================
import csv, glob, io, os, re, sqlite3, zipfile, collections

HERE       = os.path.dirname(os.path.abspath(__file__))
SRC_GLOB   = os.path.join(HERE, "data_extracted", "*.zip")
OUT_DB     = os.path.join(HERE, "questions.db")
# 앱 주제 → (인텐트 앞 단어, 인텐트 종류). 종류가 None 이면 그 앞 단어의 모든 종류를 사용
TOPIC_SOURCES = {"배송": ("배송", None), "재고": ("제품", "재고"), "입고": ("제품", "입고")}
SOURCE = "AI-Hub 소상공인 고객 주문 질의-응답"
AUTO_PICK_TOPICS = ("배송",)  # 종류(날짜·비용 등)별로 가장 많이 나온 질문 1개씩을 버튼으로
# 데이터에서 많이 나온 질문 중 골라 쓰는 버튼 (표시 순서대로). 데이터에 없으면 횟수 0 으로 추가됨
CURATED = {
    "재고": ["재고 있나요?", "재고가 없나요?", "품절인가요?", "구매 가능한가요?", "주문 가능한가요?"],
    "입고": ["재입고 언제 되나요?", "언제 입고되나요?", "재입고 안 되나요?", "품절 언제 풀리나요?"],
}
# 데이터가 없어서 직접 만든 질문 (이 앱의 신청 규칙에 맞춤)
HANDWRITTEN = {
    "신청": ["사료는 어떻게 신청하나요?", "몇 톤까지 신청할 수 있나요?", "문자로도 신청할 수 있나요?",
             "신청이 안 되는 이유가 뭔가요?", "신청하면 언제 배송되나요?"],
}
KEEP_PER_SUBTYPE = 30        # 종류별로 저장할 질문 수
MIN_LEN, MAX_LEN = 5, 35     # 너무 짧거나 긴 질문 제외
SKIP_SUBTYPES = ("일반",)    # 다른 종류와 내용이 겹치는 종류
SKIP_PATTERN  = re.compile(r"^어(떻|찌)|제주")   # 앞뒤 설명 없이는 뜻을 알 수 없는 질문 / 한국 택배에만 해당하는 질문

# 버튼으로 보여 줄 질문의 영어·몽골어 번역 (한국어 질문 → (영어, 몽골어)). 여기에 없는 질문은 한국어로 표시됨
TRANSLATIONS = {
    "언제 배송되나요?":      ("When will it be delivered?",                 "Хэзээ хүргэх вэ?"),
    "택배사가 어디인가요?":  ("Which delivery company is it?",              "Ямар хүргэлтийн компани вэ?"),
    "해외 배송 가능한가요?": ("Do you deliver overseas?",                   "Гадаадад хүргэх боломжтой юу?"),
    "묶음배송 안 되나요?":   ("Can orders be bundled into one delivery?",   "Захиалгыг нэг дор нэгтгэж хүргэх боломжтой юу?"),
    "무료 배송인가요?":      ("Is delivery free?",                          "Хүргэлт үнэгүй юу?"),
    "누락된 건가요?":        ("Is something missing?",                      "Ямар нэг зүйл дутуу байна уу?"),
    "재고 있나요?":          ("Is it in stock?",                            "Нөөцөд байгаа юу?"),
    "재고가 없나요?":        ("Is it out of stock?",                        "Нөөц дууссан уу?"),
    "품절인가요?":           ("Is it sold out?",                            "Дууссан уу?"),
    "구매 가능한가요?":      ("Is it available?",                           "Авах боломжтой юу?"),
    "주문 가능한가요?":      ("Can I order it?",                            "Захиалж болох уу?"),
    "재입고 언제 되나요?":   ("When will it be restocked?",                 "Хэзээ дахин нөөцөлнө вэ?"),
    "언제 입고되나요?":      ("When will new stock arrive?",                "Шинэ нөөц хэзээ ирэх вэ?"),
    "재입고 안 되나요?":     ("Won't it be restocked?",                     "Дахин нөөцлөхгүй юу?"),
    "품절 언제 풀리나요?":   ("When will it be back in stock?",             "Хэзээ дахин нөөцөд орох вэ?"),
    "사료는 어떻게 신청하나요?":   ("How do I request feed?",                "Тэжээлийг яаж хүсэх вэ?"),
    "몇 톤까지 신청할 수 있나요?": ("How many tons can I request?",          "Хэдэн тонн хүртэл хүсэж болох вэ?"),
    "문자로도 신청할 수 있나요?":  ("Can I request by SMS?",                 "Мессежээр хүсэлт гаргаж болох уу?"),
    "신청이 안 되는 이유가 뭔가요?": ("Why can't I submit a request?",       "Яагаад хүсэлт өгч болохгүй байна вэ?"),
    "신청하면 언제 배송되나요?":   ("When is it delivered after I request?", "Хүсэлт өгсний дараа хэзээ хүргэх вэ?"),
}

csv.field_size_limit(10 ** 9)
norm = lambda s: re.sub(r"[\s.,?!~]+", "", s).lower()

counts   = collections.defaultdict(collections.Counter)   # (topic, subtype) → {정규화 질문: 횟수}
variants = collections.defaultdict(collections.Counter)   # 정규화 질문 → {원문: 횟수}

for zpath in glob.glob(SRC_GLOB):
    with zipfile.ZipFile(zpath) as zf:
        for name in zf.namelist():
            if not name.endswith(".csv"): continue
            with zf.open(name) as f:
                for row in csv.DictReader(io.TextIOWrapper(f, encoding="utf-8-sig", errors="replace", newline="")):
                    if row["발화자"] != "c" or row["QA여부"] != "q": continue
                    parts = row["인텐트"].split("_")
                    if len(parts) != 3 or parts[2] != "질문" or parts[1] in SKIP_SUBTYPES: continue
                    topic = next((t for t, (a, b) in TOPIC_SOURCES.items() if parts[0] == a and b in (None, parts[1])), None)
                    if not topic: continue
                    text = row["발화문"].strip()
                    if not (MIN_LEN <= len(text) <= MAX_LEN) or SKIP_PATTERN.search(text): continue
                    key = norm(text)
                    counts[(topic, parts[1])][key] += 1
                    variants[key][text] += 1
    print("읽기 완료:", os.path.basename(zpath))

# pick: 챗봇 버튼으로 보여 줄 순서 (1부터, 0 이면 버튼 아님)
rows = []
for (topic, subtype), c in counts.items():
    for key, n in c.most_common(KEEP_PER_SUBTYPE):
        rows.append({"topic": topic, "subtype": subtype, "question": variants[key].most_common(1)[0][0],
                     "count": n, "source": SOURCE, "pick": 0, "key": key})
for topic in AUTO_PICK_TOPICS:
    best = {}
    for r in rows:
        if r["topic"] == topic and r["count"] > best.get(r["subtype"], {"count": -1})["count"]: best[r["subtype"]] = r
    for i, r in enumerate(sorted(best.values(), key=lambda r: -r["count"]), 1): r["pick"] = i
for topic, questions in CURATED.items():
    for i, q in enumerate(questions, 1):
        r = next((r for r in rows if r["topic"] == topic and r["key"] == norm(q)), None)
        if r: r["question"], r["pick"] = q, i
        else:
            print(f"  ※ 데이터에 없어 횟수 0 으로 추가: [{topic}] {q}")
            rows.append({"topic": topic, "subtype": "직접 선택", "question": q, "count": 0, "source": SOURCE, "pick": i, "key": norm(q)})
for topic, questions in HANDWRITTEN.items():
    for i, q in enumerate(questions, 1):
        rows.append({"topic": topic, "subtype": "직접 작성", "question": q, "count": 0, "source": "직접 작성", "pick": i, "key": norm(q)})

con = sqlite3.connect(OUT_DB)
con.executescript("""
DROP TABLE IF EXISTS faq_questions;
CREATE TABLE faq_questions(id INTEGER PRIMARY KEY AUTOINCREMENT, topic TEXT, subtype TEXT, question TEXT, count INTEGER, source TEXT,
                           question_en TEXT, question_mn TEXT, pick INTEGER DEFAULT 0);
CREATE INDEX idx_faq_topic ON faq_questions(topic, pick);
""")
for r in rows:
    en, mn = TRANSLATIONS.get(r["question"], (None, None))
    con.execute("INSERT INTO faq_questions VALUES(NULL,?,?,?,?,?,?,?,?)",
                (r["topic"], r["subtype"], r["question"], r["count"], r["source"], en, mn, r["pick"]))
con.commit()

print("\n저장된 질문 수:", con.execute("SELECT COUNT(*) FROM faq_questions").fetchone()[0])
for topic, q, n, en in con.execute("SELECT topic, question, count, question_en FROM faq_questions WHERE pick>0 ORDER BY topic, pick"):
    print(f"  [{topic}] {q}  ({n:,}번)  | {en or '번역 없음'}")
con.close()
