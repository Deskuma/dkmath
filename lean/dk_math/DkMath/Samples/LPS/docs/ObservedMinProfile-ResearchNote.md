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

この定理は、`d = 3` において次の 3 標本で
`ObservedMinTwo` と `ObservedMinOne` の分岐が再現することを束ねる。

1. `candidateBig = 216`:
   - `216 - 125 = 91` (`ObservedMinTwo 3 91`)
   - `216 - 152 = 64` (`ObservedMinOne 3 64`)
2. `candidateBigCube₂ = 64`:
   - `64 - 29 = 35` (`ObservedMinTwo 3 35`)
   - `64 - 37 = 27` (`ObservedMinOne 3 27`)
3. `candidateBigCube₃ = 125`:
   - `125 - 60 = 65` (`ObservedMinTwo 3 65`)
   - `125 - 61 = 64` (`ObservedMinOne 3 64`)

## 3. 研究メモ（実験段階方針）

- 現段階では `ObservedMinOne/Two` は局所定義のまま維持する。
- 汎用 API (`GapFillRank.lean` への昇格) は、再利用箇所が増えてから判断する。
- 先に標本数を増やし、観測再現性を優先する。

## 4. 追記テンプレート

### yyyy-mm-dd: new sample

- degree:
- Big:
- Body pair:
- residual pair:
- Lean theorem name:
- note:
