# report-014 — 実装・検証結果

2026-10-14。instruction-014 の Outcome A。

## 実装

`DkMath/FLT/Seven/SevenRamifiedFusionSmallCoefficientPrimePowerOwnership.lean` を追加し、次の4公開定理を実装した。

```lean
eligible_primitive_divisor_smallCoefficient_prime_pow
  {c p n r : ℕ} (hp : Nat.Prime p) (hc : c ≤ 7 ^ 3)
  (hmem : r ∈ (c * p ^ n).divisors)
  (hcop : Nat.Coprime r ((c * p ^ n) / r))
  (hsize : 7 ^ 3 * r ^ 7 < c * p ^ n) : r ∣ c

sixthPowerSieved_three_thirteen_pow_excluded {n : ℕ} (hn : 0 < n) :
  ¬ SixthPowerSievedNestedCondition (3 * 13 ^ n)

threeThirteenPowerCore_injective :
  Function.Injective (fun k : ℕ => 3 * 13 ^ (k + 1))

sixthPowerSieved_three_thirteen_power_family_excluded (k : ℕ) :
  ¬ SixthPowerSievedNestedCondition (3 * 13 ^ (k + 1))
```

一般所有則は prime/coprimality と strict size の証明で、指数や M の上限を使わない。production imports は既存法42 consumer と gate 013 consumer の2モジュール。既存 receiver・sieve・以前のモジュールは変更していない。ヘッダと file print は `DkMath.Basic` の様式に合わせた。

同名の `DkMathTest/FLT/Seven/` モジュールに generic API、c=0・n=0 境界の適用、全正指数と全 index の適用、単射性、n=12 と n=1 の回帰、coefficient bound を外した偽命題の countermodel を保存した。scratch は DkMathTest 配下で試した後、この2モジュールへ昇格した。

## 検証

作業 cwd: `lean/dk_math`。

| 実行 | 結果 |
|---|---|
| `lake env lean DkMathTest/FLT/Seven/SmallCoefficientCalibration.lean` (昇格前) | exit 0、unused simp argument 警告1件。最終コードで除去 |
| `lake build DkMath.FLT.Seven.SevenRamifiedFusionSmallCoefficientPrimePowerOwnership` | exit 0、9091 jobs、対象を build |
| `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionSmallCoefficientPrimePowerOwnership.lean` | exit 0、回帰と公理監査成功、出力に警告なし |
| 4公開定理・countermodel の `#print axioms` | propext、Classical.choice、Quot.sound のみ、sorryAx なし |
| 新規 Lean 2ファイルの禁止構文検索 | sorry/admit/axiom/unsafe/native_decide の一致なし |
| `git diff --check` と新規ファイルの whitespace 検査 | 成功 |

必要な証拠を [evidence/014-verification-summary.md](evidence/014-verification-summary.md) に要約した。raw logs は既存の `__*` ignore 規則に合わせた一時ファイル名に置いた。

## 結果の意味

この gate は r=3 だけの排除を、全 eligible divisor を扱う無限族の full-sieve 排除へ拡張した。必要な条件 c≤343 と n>0 を各定理で保持した。結果は抽象 core の full-sieve に関するもので、source packet や FLT7 の定理へ拡張していない。
