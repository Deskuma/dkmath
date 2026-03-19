# ABC: `sorry` / `admit` 再調査メモ

最終更新: 2026-03-19

対象: `lean/dk_math/DkMath/ABC/**/*.lean`

- 調査コマンド: `rg -n '\\bsorry\\b|\\badmit\\b' lean/dk_math/DkMath/ABC/**/*.lean`
- 注意: `ABC025_allX.lean` の 3 件中 2 件は本文中の文字列（`\`sorry\``）で、実際の穴は 1 件。

---

## 0件（確認済み）

- `ABC025.lean`
- `ABCMGFTwoTailLog.lean`
- `ABCFinalRealExpFactorizationLog.lean`

---

## 残件一覧（実測）

| file | hits | lines | メモ |
|---|---:|---|---|
| `ABC021.lean` | 16 | 187,192,201,207,219,227,246,254,258,263,277,283,308,313,317,323 | Janson/期待値系。重い本丸。 |
| `ABCQualityLeOfNotBad.lean` | 8 | 71,79,85,102,255,260,262,278 | 型変換＋log分解＋補助不等式。中～重。 |
| `ABC038.lean` | 3 | 221,242,270 | 文脈依存。statement整合チェック要。 |
| `ABC025_allX.lean` | 3 | 32,45,66 | 実穴は 66 の 1 件（32,45 は文中参照）。 |
| `ABC039.lean` | 2 | 61,180 | 設計不一致の可能性あり（先にstatement確認）。 |
| `ABC031.lean` | 2 | 309,411 | 密度/ε-δ。中程度。 |
| `ABC030.lean` | 2 | 376,386 | 小規模 admit。着手しやすい。 |
| `ABC029.lean` | 1 | 135 | 小規模 admit。最優先候補。 |
| `ABC016.lean` | 1 | 740 | 小規模 admit。最優先候補。 |
| `ABC008.lean` | 1 | 1981 | 単発 admit。着手可。 |
| `ABCWorking.lean` | 1 | 351 | 作業用ファイル。削除/保留判断対象。 |
| `ABC#Research.lean` | 1 | 105 | 研究用（モジュール運用対象外なら除外可）。 |

---

## 着手優先度（いま潰しやすい順）

### A. すぐ潰せる可能性が高い（局所穴）

1. `ABC029.lean:135`
2. `ABC016.lean:740`
3. `ABC030.lean:376,386`
4. `ABC008.lean:1981`

### B. 次点（局所だが文脈確認が必要）

1. `ABC031.lean:309,411`
2. `ABC038.lean:221,242,270`
3. `ABC025_allX.lean:66`

### C. 先に設計確認を推奨

1. `ABC039.lean`（valuation の対象定義がズレる可能性）
2. `ABCQualityLeOfNotBad.lean`（補助補題の棚卸しが先）

### D. 最後にまとめて攻める本丸

1. `ABC021.lean`（16件、期待値/分散/Janson の連鎖）

---

## 次の実作業チェックリスト

- [ ] `ABC029.lean:135` を解消
- [ ] `ABC016.lean:740` を解消
- [ ] `ABC030.lean:376,386` を解消
- [ ] `ABC008.lean:1981` を解消
- [ ] `ABC025_allX.lean` は文中参照と実穴を分離して整理
- [ ] `ABCWorking.lean`, `ABC#Research.lean` を「対象に含めるか」決定
