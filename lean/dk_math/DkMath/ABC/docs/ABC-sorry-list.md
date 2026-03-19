# ABC: `sorry` / `admit` 再調査メモ

最終更新: 2026-03-19

対象: `lean/dk_math/DkMath/ABC/**/*.lean`

- 調査コマンド: `rg -n '\\bsorry\\b|\\badmit\\b' lean/dk_math/DkMath/ABC/**/*.lean`
- 備考: 本リストは実際の `sorry/admit` トークンのみを集計（コメント文字列は除外）。

---

## 0件（確認済み）

- `ABC025.lean`
- `ABC025_allX.lean`
- `ABC029.lean`
- `ABC016.lean`
- `ABC030.lean`
- `ABC008.lean`
- `ABC009.lean`
- `ABC031.lean`
- `ABC038.lean`
- `ABCMGFTwoTailLog.lean`
- `ABCFinalRealExpFactorizationLog.lean`

---

## 残件一覧（実測）

| file | hits | lines | メモ |
|---|---:|---|---|
| `ABC021.lean` | 16 | 187,192,201,207,219,227,246,254,258,263,277,283,308,313,317,323 | Janson/期待値系。重い本丸。 |
| `ABCQualityLeOfNotBad.lean` | 8 | 71,79,85,102,255,261,263,279 | 型変換＋log分解＋補助不等式。中～重。 |
| `ABC039.lean` | 2 | 61,180 | 設計不一致の可能性あり（先にstatement確認）。 |
| `ABCWorking.lean` | 1 | 351 | 作業用ファイル。削除/保留判断対象。 |
| `ABC#Research.lean` | 1 | 105 | 研究用（モジュール運用対象外なら除外可）。 |

---

## 着手優先度（いま潰しやすい順）

### A. すぐ潰せる可能性が高い（局所穴）

1. `ABCQualityLeOfNotBad.lean:261,263`（`admit` 2件）
2. `ABC039.lean:61,180`

### B. 次点（局所だが文脈確認が必要）

1. `ABCQualityLeOfNotBad.lean:71,79,85,102,255,279`
2. `ABC021.lean:246,254,258,263`（局所補題だが依存が重い）

### C. 先に設計確認を推奨

1. `ABCWorking.lean`, `ABC#Research.lean`（運用対象かどうかを先に決定）

### D. 最後にまとめて攻める本丸

1. `ABC021.lean`（16件、期待値/分散/Janson の連鎖）

---

## 次の実作業チェックリスト

- [x] `ABC008.lean:1981` を解消
- [x] `ABC025_allX.lean:66` を解消
- [x] `ABC031.lean:315,423` を解消
- [x] `ABC038.lean:221,242,270` を解消
- [ ] `ABCWorking.lean`, `ABC#Research.lean` を「対象に含めるか」決定
