# ABC: `sorry` 一覧（チェックリスト）

このドキュメントは、`lean/dk_math/DkMath/ABC/ABC0*.lean` に残る `sorry` を一覧化し、
どこで何が詰まっているのかを可視化するためのチェックリストです。

**Note:** 本ファイルは `dev/ABC-260318-v1` ブランチに対応しています。

---

## ✅ 進行中（現状確認済み）

### `ABC025.lean`（Telescoping系）

- **行 1087**: `sorry -- KNOWN ISSUE: Claim is false; proof needs restructuring`  
  - **内容**: `3^(-1/2)` を `1/2` 未満とする不正確な評価に依存している。
  - **対応方針**: 既に追加済みの `three_pow_neg_log2_div_log3_eq_half` 補題を活用し、`x/(1-x) ≤ 3` 型のシンプル評価に書き換える。
  - [ ] 目標：`sorry` を削除し、`norm_num` などで完結させる。

### `ABC021.lean`（Janson / 2次モーメント系）

このファイルには複数の `sorry` が残っており、いずれも **確率期待値／分散／Janson不等式** に関する証明の穴です。

- **行 246**: `sorry -- This is a general property of indicator expectations`
- **行 254**: `sorry -- Need to show mu ≠ 0 implies mu > 0` (定義からの正値性)
- **行 258**: `sorry -- This should follow from the definition of mu in ABC.lean`
- **行 263**: `sorry -- Sum of indicators is nonnegative`
- **行 277**: `sorry -- Combine second moment method with variance formula`
- **行 283**: `sorry -- This is the key analytic inequality (uses convexity/Taylor)`
- **行 308**: `sorry -- Product is 1 iff all ¬ω v are true iff X = 0`
- **行 313**: `sorry -- Apply PMF.expect_mono with h_prod_to_sum`
- **行 317**: `sorry -- Apply janson_core_inequality and algebraic manipulation`
- **行 323**: `sorry -- When Δ̄ = 0, events are independent; use simpler bound`

> これらは「証明の骨格は見えているが、確率論的な細部（期待値操作や不等式の組み合わせ）を形式化していない」パターンと見られる。

### `ABC031.lean`（密度 / ε-δ 系）

- **行 309**: `sorry  -- TODO: fill from twoTail_log_bound_adjacent_density_one (deferred)`
- **行 411**: `sorry  -- TODO: Refine ε ≤ δ case via parameter optimization or limiting argument`

### `ABC038.lean`（不明：コメントなし）

- **行 221**: `sorry`
- **行 242**: `sorry`
- **行 270**: `sorry`

### `ABC039.lean`（不明：コメントなし）

- **行 61**: `sorry`
- **行 180**: `sorry`

---

## 🔍 使い方（進め方の例）

1. **優先度をつける**
   - 1st: `ABC025.lean` の `sorry`（「数学的に間違っている」ため）
   - 2nd: `ABC021.lean` の `sorry`（主要な不等式 / Janson 連鎖）
   - 3rd: `ABC031/ABC038/ABC039` の `sorry`（内容がコメント無しのため、調査が必要）

2. **該当箇所の “正解候補” を用意する**
   - `ABC025.lean` なら `three_pow_neg_log2_div_log3_eq_half` を使う形で書き換え
   - `ABC021.lean` なら `PMF.expect_mono` や `Real.exp` の基本不等式を使う形で証明を埋める

3. **作業を記録する**
   - 直した `sorry` には `[dev/ABC-260318-v1]` のようにタグを残す（既にその模式を追加済み）
   - 変更が完了したら、このドキュメントにチェックボックスを追加して完了状態にする

---

## 🔧 次のアクション提案

- ✅ **まずは `ABC025.lean` の `sorry`** を 1 つ潰す（`three_pow_neg_log2_div_log3_eq_half` で置換する、など）。
- 🔎 **次に `ABC021.lean` の `sorry`** をひとつずつ「どんな補題で潰すか」を整理する。

必要なら、`ABC021.lean` の該当行だけを深堀りして「どの Mathlib 補題で埋められるか」を具体的に提案できます。

---

🧠 **補足**: `ABC026.lean` や `ABC027〜ABC024` などには `sorry` は見当たらないため、今回の「チェックリスト対象」は上記のファイルに絞られます。
