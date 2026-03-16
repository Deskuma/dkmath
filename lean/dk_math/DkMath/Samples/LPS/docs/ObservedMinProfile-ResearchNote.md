# Observed Minimum Profile Research Note

## 1. 目的

`DkMath.Samples.LPS.BigFamilyExamples` で観測している

- same Big
- different Body
- different observed minimum profiles

の再現状況を、実験段階の事実確認として逐次記録する。

## 2. 現在の固定結果（Lean）

参照ファイル:

- `DkMath/Samples/LPS/BigFamilyExamples.lean`

主要総括定理:

- `cube_observed_min_split_reproduced_three_samples`

この定理は、`d = 3` において、same Big に対する residual の
observed minimum profile 分岐 (`ObservedMinTwo`, `ObservedMinOne`) が、
少なくとも 3 つの独立標本で再現することを束ねる。

1. `candidateBig = 216`:
   - `216 - 125 = 91` (`ObservedMinTwo 3 91`)
   - `216 - 152 = 64` (`ObservedMinOne 3 64`)
2. `candidateBigCube₂ = 64`:
   - `64 - 29 = 35` (`ObservedMinTwo 3 35`)
   - `64 - 37 = 27` (`ObservedMinOne 3 27`)
3. `candidateBigCube₃ = 125`:
   - `125 - 60 = 65` (`ObservedMinTwo 3 65`)
   - `125 - 61 = 64` (`ObservedMinOne 3 64`)

補足（平方側）:

- `d = 2` でも `candidate_sq_same_big_observed_min_split_profile` により、
   same Big での profile 分岐の実例を 1 標本確認済み。

## 3. 標本生成の原理（短メモ）

立方世界で same Big の profile 分岐標本を作る基本手順は次の通り。

1. Big を固定する。
2. Body を 2 通り選び、residual を `r₂ = a^3 + b^3` 型と `r₁ = c^3` 型へ振り分ける。
3. `r₂` 側で `ObservedMinTwo`（1項不可・2項可）を示し、`r₁` 側で `ObservedMinOne` を示す。
4. これにより same Big の中で observed minimum profile の分岐を観測する。

## 4. 研究メモ（実験段階方針）

- 現段階では `ObservedMinOne/Two` は局所定義のまま維持する。
- 汎用 API (`GapFillRank.lean` への昇格) は、再利用箇所が増えてから判断する。
- 先に標本数を増やし、観測再現性を優先する。

## 5. 現状分析（2026-03-17）

### 5.1. 現在地

- `Samples/LPS` は LPS 本体の証明ではなく、Big-family 語彙で現象を観測する実験層として機能している。
- `BigFamily` / `BigFamilyInt` / `PowerSwap` / `GapFillRank` / `BigFamilyExamples` の役割分担は明確で、相互接続も安定している。

### 5.2. 重要な観測事実

- 立方次数 `d = 3` で、same Big に対する residual の observed minimum profile 分岐
   (`ObservedMinTwo`, `ObservedMinOne`) が独立 3 標本で再現した。
- この事実は `cube_observed_min_split_reproduced_three_samples` で Lean 上に固定されている。
- 平方次数 `d = 2` でも 1 標本の分岐が確認され、現象が立方世界だけの偶然ではない可能性を示す。

### 5.3. 強み

- 語彙統一（Big / Body / Gap / Core / Beam / ObservedMin）により、設計書と実装の対応が追跡しやすい。
- `ℕ` 版と `ℤ` 版の併置により、差分観測の記述自由度が高い。
- `ObservedMinOne/Two` を局所定義に留めたことで、実験段階の仕様変更に耐えやすい。

### 5.4. 未確定点

- `ObservedMin` は現状 `1` と `2` のみで、一般 `r` への拡張方針は未固定。
- 標本は hand-crafted が中心で、系統生成の一般条件はまだ定式化途上。
- LPS 本体予想への論理橋（一般定理レベル）は未整備。

### 5.5. 次の分岐

1. 生成原理を短文化して標本設計の再利用性を上げる。
2. 立方標本を増やして再現性の厚みを上げる。

現時点では、生成原理の短文化を先に行う方が研究ノートとしての密度が高い。

## 6. 追記テンプレート

### yyyy-mm-dd: new sample

- degree:
- Big:
- Body pair:
- residual pair:
- Lean theorem name:
- note:
