# NumberGeometry-TwoPointGauge NGEO-008 実装報告

## 1. 結果

Outcome A。`MassScalesBy` の real-valued gauge relation に、明示的な
`Nat.Prime` label を持つ `PrimeScaleStep` と、有限 prime-labelled chain を
追加した。

この checkpoint は NumberGeometry 内の離散 prime-scale layer に限定した。
`DkMath.NumberTheory.StructuralArithmetic.PrimeScaleGeneratedBy` は import せず、
Units、UnitCycle、DHNT、logarithms、cyclotomic theory、FLT も追加していない。

## 2. 変更ファイル

追加:

- `DkMath/NumberGeometry/PrimeScale.lean`
- `DkMathTest/NumberGeometry/PrimeScaleAxiomAudit.lean`
- `docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-008.md`

変更:

- `DkMath/NumberGeometry.lean`
  - `DkMath.NumberGeometry.PrimeScale` を public facade へ追加。

既存の `Basic`、`Gauge`、`GaugeTransition`、および NGEO-006 calibration modules は
変更していない。

## 3. PrimeScaleStep

最終定義は次のとおり。

```lean
def PrimeScaleStep
    (p : ℕ) (K1 K2 : TwoPointKernel) : Prop :=
  Nat.Prime p ∧ MassScalesBy (p : ℝ) K1 K2
```

label は existential に隠さず、chain の list label と同じ明示引数にした。
読み出し用に次も追加した。

- `PrimeScaleStep.prime`
- `PrimeScaleStep.massScalesBy`

## 4. Prime label uniqueness

```lean
PrimeScaleStep.label_unique
```

は `K1.Active`、同一 transition に対する二つの prime-labelled step を仮定し、
`p = q` を返す。`MassScalesBy.factor_unique` と real cast の exact recovery
だけを使用し、gauge cancellation を再証明していない。

## 5. Activity propagation

```lean
PrimeScaleStep.target_active
```

は `PrimeScaleStep p K1 K2` と `K1.Active` から `K2.Active` を導く。証明は
`Nat.Prime.pos` と `massGauge_pos_iff_active` による positive mass-gauge product
である。degenerate source からの activity は主張していない。

## 6. Prime-shell retarget

```lean
primeScaleStep_retarget_of_onNatShell
```

は activity 仮定なしに、次を形式化する。

```text
Nat.Prime p
P ∈ OnNatShell K p
  -> PrimeScaleStep p K (K.retarget P)
```

NGEO-007 の `massScalesBy_retarget_of_onNatShell` をそのまま利用している。

## 7. Prime irreducibility

```lean
PrimeScaleStep.irreducible
```

の仮定は次のとおり。

```text
hp13 : PrimeScaleStep p K1 K3
h12  : MassScalesBy (a : ℝ) K1 K2
h23  : MassScalesBy (b : ℝ) K2 K3
hK1  : K1.Active
```

結論は `a = 1 ∨ b = 1` である。

証明では `MassScalesBy.trans` と active source の factor uniqueness により
`p = a * b` を natural equality へ戻し、canonical Mathlib theorem
`Nat.prime_mul_iff` を使用した。

この結果は natural-labelled transition の irreducibility だけを示す。
任意の positive real factor、intermediate kernel の uniqueness、任意の環での
algebraic primalityは主張していない。

## 8. Composite-factor converse

未実装で deferred とした。

`n = a * b` のときに `sqrt a` similarity から intermediate kernel を構成する
converse は、今回の required prime irreducibility に不要であり、新しい similarity
hierarchy を導入しない bounded proof としての利用価値もまだ確定していない。

## 9. PrimeScaleChain representation

次の endpoint relation を採用した。

```lean
inductive PrimeScaleChain :
    TwoPointKernel → TwoPointKernel → List ℕ → Prop
  | nil (K) : PrimeScaleChain K K []
  | cons
      (hStep : PrimeScaleStep p K1 K2)
      (hTail : PrimeScaleChain K2 K3 ps) :
      PrimeScaleChain K1 K3 (p :: ps)
```

中間 kernel は constructor history に存在し、別個の vector、category、graph
structure は導入していない。

## 10. Chain product / activity / prime power

次を実装した。

```lean
PrimeScaleChain.massScalesBy_prod
PrimeScaleChain.target_active
PrimeScaleChain.massScalesBy_pow
```

`massScalesBy_prod` は induction により

```text
PrimeScaleChain K1 K2 ps
  -> MassScalesBy ((ps.prod : ℕ) : ℝ) K1 K2
```

を証明する。空 list は `massScalesBy_refl`、cons は
`MassScalesBy.trans` を利用する。

`target_active` は active source から chain endpoint までの activity propagation
である。

`massScalesBy_pow` は

```text
PrimeScaleChain K1 K2 (List.replicate k p)
  -> MassScalesBy ((p ^ k : ℕ) : ℝ) K1 K2
```

を `List.prod_replicate` から導く。

## 11. Distance interpretation

薄い corollary として次も追加した。

```lean
PrimeScaleStep.dist_sq_eq_prime_mul_dist_sq
```

内容は

```text
dist K2.source K2.target ^ 2
  = (p : ℝ) * dist K1.source K1.target ^ 2
```

であり、`massScalesBy_iff_dist_sq` の corollary である。unsquared distance と
`sqrt p` は導入していない。

## 12. 意図的に主張していないこと

- `PrimeScaleStep` が NumberTheory の既存 `PrimeScaleGeneratedBy` と同一であること。
- prime scale の Units / UnitCycle / DHNT / logarithmic interpretation。
- arbitrary positive real factors に対する irreducibility。
- composite natural factorization に対する geometric intermediate の存在。
- chain の intermediate kernel の uniqueness。
- prime distribution、prime existence、FLT、cyclotomic theory。

## 13. 検証

成功した build:

```text
lake build DkMath.NumberGeometry.PrimeScale
Build completed successfully (2427 jobs)

lake build DkMath.NumberGeometry
Build completed successfully (8935 jobs)

lake build DkMathTest.NumberGeometry.PrimeScaleAxiomAudit
Build completed successfully (8936 jobs)

lake build DkMath
Build completed successfully (10276 jobs)
```

`PrimeScaleAxiomAudit.lean` の substantive declarations の `#print axioms` は
すべて既存 logical infrastructure の
`[propext, Classical.choice, Quot.sound]` のみである。

## 14. NGEO-009 proposed scope

NGEO-009 では、今回の prime-labelled chain を `DkMath.Units.*`、
`DkMath.UnitCycle.*`、`DkMath.DHNT.*` へ接続するかを、依存方向と theorem
ownership を確認したうえで bounded に検討する。

対象は prime-scale chain と既存 Unit API の最小 bridge に限定し、logarithmic
coordinates は NGEO-010 へ延期する。cyclotomic theory、FLT、prime distribution
は含めない。

NGEO-008 はここで終了する。
