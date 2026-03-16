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

## 5. 追記テンプレート

### yyyy-mm-dd: new sample

- degree:
- Big:
- Body pair:
- residual pair:
- Lean theorem name:
- note:
