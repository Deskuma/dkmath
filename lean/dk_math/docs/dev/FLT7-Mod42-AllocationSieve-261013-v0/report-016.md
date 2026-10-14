# report-016 — 実装・検証結果

2026-10-14。instruction-016 の Outcome A。

## 実装

`DkMath/FLT/Seven/SevenRamifiedFusionPermutationPrimeSupport.lean` に5公開宣言を追加した。

- `centeredSevenSextic_cast_difference`: 任意 CommRing R で natural cast した actual sextic の七乗差恒等式。
- `zmod_seventh_power_injective`: ℓ 素数、Nat.Coprime 7 (ℓ−1) のもとで全 ZMod ℓ の7乗写像が単射。
- `centeredSevenSextic_not_dvd_of_seven_power_permutation`: 上記条件にℓ≠2とℓ∤Dを加えた arbitrary-natural-input 非零性。
- `nestedAllocation_excluded_of_permutation_prime_support`: ℓ≠7、ℓ∤r、ℓ∣M/rを加え、同じ chosen divisor の両 exact receiver を排除。
- `sixthPowerSieved_smallCoefficient_permutation_prime_excluded`: c≤343,n>0 と上記素数条件による full-sieve 排除の optional schema。

Mathlib の群冪写像の全単射性と単元群の位数を使い、零を含む全有限体の単射性に接続した。既存 receiver と以前の production ファイルは変更していない。imports は gate 015 support と Mathlib finite-field / order-of-element modules。license と file print を既存様式に合わせた。

同名の DkMathTest module に任意 ring identity、法11単射性、法11・法13の任意自然数非零性、M=11,r=1 の receiver 排除、両法の coefficient schema 適用、法29・法2の countermodel、法7の fixed-gap diagnostic、公理監査を保存した。scratch は DkMathTest で校正した後に昇格した。

## 検証

作業 cwd は `lean/dk_math`。

| 実行 / 監査 | 結果 |
|---|---|
| calibration 初回 / 第2回 | 各 exit 1、零分岐の等式向きの問題 |
| calibration 修正後 | exit 0、警告なし |
| `lake build DkMath.FLT.Seven.SevenRamifiedFusionPermutationPrimeSupport` | exit 0、9090 jobs |
| `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionPermutationPrimeSupport.lean` | exit 0、警告なし |
| 全5公開宣言と3 named test の `#print axioms` | 標準公理のみ、sorryAx なし |
| 新規 Lean の禁止構文検索 | sorry/admit/axiom/unsafe/native_decide 一致なし |
| `git diff --check` と新規5ファイルの whitespace 検査 | 成功 |

公理の内訳、source hash、実際の exit status を [evidence/016-verification-summary.md](evidence/016-verification-summary.md) に記録した。数学的 Python precheck は実行していない。raw logs は既存 ignore 規則の `logs/__016-*.txt` にある一時ファイル。

## 結果と研究範囲

七乗差と冪写像の単射性により法13の機構を一般化できた。法11は新しい成立例、法29は permutation 条件を落とした命題の反例である。modular zero と exact receiver witness を区別した。次は source 側の同一 packet bridge を優先する判断を findings に記載し、この gate では着手せず終了した。
