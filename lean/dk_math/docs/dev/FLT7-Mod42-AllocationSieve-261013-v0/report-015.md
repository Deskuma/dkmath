# report-015 — 実装結果

2026-10-14。instruction-015 の Outcome A。

## 追加した API

`DkMath/FLT/Seven/SevenRamifiedFusionSmallCoefficientPrimeSupport.lean` に3公開定理を追加した。

```lean
eligible_primitive_divisor_smallCoefficient_prime_not_dvd
  {c p n r : ℕ} (hp : Nat.Prime p) (hc : c ≤ 7 ^ 3)
  (hmem : r ∈ (c * p ^ n).divisors)
  (hcop : Nat.Coprime r ((c * p ^ n) / r))
  (hsize : 7 ^ 3 * r ^ 7 < c * p ^ n) : ¬ p ∣ r

eligible_smallCoefficient_prime_in_complement
  {c p n r : ℕ} (hp : Nat.Prime p) (hc : c ≤ 7 ^ 3) (hn : 0 < n)
  (hmem : r ∈ (c * p ^ n).divisors)
  (hcop : Nat.Coprime r ((c * p ^ n) / r))
  (hsize : 7 ^ 3 * r ^ 7 < c * p ^ n) :
  ¬ p ∣ r ∧ p ∣ (c * p ^ n) / r

sixthPowerSieved_smallCoefficient_thirteen_pow_excluded
  {c n : ℕ} (hc : c ≤ 7 ^ 3) (hn : 0 < n) :
  ¬ SixthPowerSievedNestedCondition (c * 13 ^ n)
```

production は gate 013 module のみを import する。gate 014 の矛盾分岐を standalone 証明として抽出し、r∣c からの不正な推論や c,p の互いに素という追加条件を使っていない。以前の production ファイル・receiver 定義は変更していない。

同名の DkMathTest module に任意入力での API 適用、c=1,3,13,343,0 の任意正指数 regression、3*13^12 の旧 filter passage と whole-core exclusion、整除推論の countermodel、実際に eligible な c=13,n=2,r=1 の support、c=0/n=0 の avoidance 適用を保存した。DkMathTest の import は test 側だけに置いた。calibration は DkMathTest で試し、最終モジュールへ昇格した。

## 実行した検証

cwd は `lean/dk_math`。

| Command / check | Actual result |
|---|---|
| `lake env lean DkMathTest/FLT/Seven/SmallCoefficientSupportCalibration.lean` (昇格前) | exit 0、警告なし |
| `lake build DkMath.FLT.Seven.SevenRamifiedFusionSmallCoefficientPrimeSupport DkMathTest.FLT.Seven.SevenRamifiedFusionCenteredThirteenSupport` | exit 0、9093 jobs |
| `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionSmallCoefficientPrimeSupport.lean` | exit 0、警告なし |
| 3公開定理と3 named test 定理の `#print axioms` | propext、Classical.choice、Quot.sound のみ、sorryAx なし |
| 新規 Lean の禁止構文検索 | sorry/admit/axiom/unsafe/native_decide 一致なし |
| `git diff --check`、新規5ファイルの whitespace | 成功 |

[evidence/015-verification-summary.md](evidence/015-verification-summary.md) に検証結果と source hash を記録した。raw logs は既存 ignore 規則に従う `logs/__015-*.txt` の一時ファイルであり、evidence へ転記していない。

## 成立範囲

全 c≤343、n>0 の c*13^n を扱い、c=13 も含む。指数の上限、係数の合同条件、c と13の coprimality は必要ない。結論は抽象 full-sieve 排除であり、source core の分類や unconditional FLT7 へは拡張していない。
