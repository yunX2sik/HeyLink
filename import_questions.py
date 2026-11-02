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
TOPICS     = ("배송",)       # 저장할 주제 (인텐트 앞부분). 다른 주제를 추가하려면 여기에 더하면 됨
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
                    if len(parts) != 3 or parts[0] not in TOPICS or parts[2] != "질문" or parts[1] in SKIP_SUBTYPES: continue
                    text = row["발화문"].strip()
                    if not (MIN_LEN <= len(text) <= MAX_LEN) or SKIP_PATTERN.search(text): continue
                    key = norm(text)
                    counts[(parts[0], parts[1])][key] += 1
                    variants[key][text] += 1
    print("읽기 완료:", os.path.basename(zpath))

con = sqlite3.connect(OUT_DB)
con.executescript("""
DROP TABLE IF EXISTS faq_questions;
CREATE TABLE faq_questions(id INTEGER PRIMARY KEY AUTOINCREMENT, topic TEXT, subtype TEXT, question TEXT, count INTEGER, source TEXT,
                           question_en TEXT, question_mn TEXT);
CREATE INDEX idx_faq_topic ON faq_questions(topic, subtype, count DESC);
""")
for (topic, subtype), c in counts.items():
    for key, n in c.most_common(KEEP_PER_SUBTYPE):
        text = variants[key].most_common(1)[0][0]
        en, mn = TRANSLATIONS.get(text, (None, None))
        con.execute("INSERT INTO faq_questions VALUES(NULL,?,?,?,?,?,?,?)",
                    (topic, subtype, text, n, "AI-Hub 소상공인 고객 주문 질의-응답", en, mn))
con.commit()

print("\n저장된 질문 수:", con.execute("SELECT COUNT(*) FROM faq_questions").fetchone()[0])
for r in con.execute("SELECT subtype, question, count FROM faq_questions WHERE id IN "
                     "(SELECT id FROM faq_questions f WHERE count = (SELECT MAX(count) FROM faq_questions WHERE topic=f.topic AND subtype=f.subtype)) "
                     "ORDER BY count DESC"):
    print(f"  [{r[0]}] {r[1]}  ({r[2]:,}번)")
con.close()
