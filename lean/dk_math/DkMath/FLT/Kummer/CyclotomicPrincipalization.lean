/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.GapDivisibleBranch

#print "file: DkMath.FLT.Kummer.CyclotomicPrincipalization"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

open DkMath.CosmicFormulaBinom

/-!
# Cyclotomic Principalization Target

## 数学的背景

Z[ζ_p] における ideal factorization:
  x^p + y^p = ∏_{j=0}^{p-1} (x + ζ^j · y)

各因子 (x + ζ^j · y) が生成する ideal は、
class group の p-torsion が trivial なら principal ideal の p 乗になる。
Principal ideal の p 乗性が保証されると、
整数 z' with z'^p = (x/q)^p + y^p の存在が導ける。

これが Kummer の「第一場合」の降下法の核心。

## 抽象化の方針

1. Stage 1a: ideal class が p-torsion に入る witness
2. Stage 1b: class group p-torsion annihilation
3. Stage 1c: principal ideal extraction
4. `CyclotomicIdealPthPowerTarget`: 上の Stage 1a-1c を合成した ideal p 乗性
5. `CyclotomicUnitNormalizationTarget`: unit 側の調整
6. `CyclotomicNormDescentTarget`: norm から整数 descent existence へ戻す橋
7. `CyclotomicPrincipalizationTarget`: Stage 1 + Stage 2 + Stage 3 を合成した full target
8. `CyclotomicClassGroupPTorsionFreeTarget`: class group の p-torsion が trivial と仮定
9. 第 8 から Stage 1b への bridge（abstract theorem）
10. 第 7 から GapDivisibleBranch への bridge（abstract theorem）

これにより、class group の concrete 構造に立ち入らずに、
Kummer 語彙を DkMath 幹線に接続できる。

2026/04/05 時点の Mathlib coverage:
- `RingTheory.ClassGroup` が ideal class group の一般 API を提供する。
- `NumberTheory.Bernoulli` が Bernoulli 数を提供する。
- しかし円分体整数環 `ℤ[ζ_p]` に specialized された
  principalization / regular-prime / class-number-formula の ready-made bridge は未確認。

したがってこのファイルの open kernel は、単なる missing lemma ではなく、
「一般 API を円分体へ specialized する理論層」の新設を要求している。
-/

namespace DkMath.FLT

/-!
## §1. Cyclotomic Principalization Target の 3 段分解

Kummer 的 principalization は、実際には次の 3 段へ裂ける:

1. Stage 1: ideal の p 乗性（さらに 1a / 1b / 1c へ分解）
2. Stage 2: 単数の調整（Kummer 単数 / cyclotomic unit の吸収）
3. Stage 3: norm 計算から整数 descent existence へ戻す橋

数学的には: Z[ζ_p] で ideal (x + ζ^j · y) の構造解析 +
class group の p-torsion = 0 + unit group の剰余類解析 から
整数 p 乗根の存在を導く。

ここではまず 3 段それぞれを abstract target として切り出し、
最後に合成して `CyclotomicPrincipalizationTarget` を得る。
-/

/--
Stage 1a: ideal class の p-torsion witness。

円分体で得られる ideal の class が p 乗すると 1 になる、という
最初の cyclotomic arithmetic step を表す。

review-002 を受け、この段を Stage 1 の最小核とみなす。
-/
abbrev CyclotomicIdealClassPTorsionWitnessTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      True

/--
Stage 1b: class group p-torsion annihilation。

Stage 1a で得た p-torsion class を、class group p-torsion freeness で潰す段。
この段は class-group API 側の一般論に近い責務を持つ。

review-004 を受け、Stage 1b も placeholder `True` ではなく、
`ClassGroup R` 上の generic p-torsion annihilation API として定式化する。
-/
abbrev CyclotomicPTorsionAnnihilationTarget : Prop :=
  ∀ {R : Type*} [CommRing R] [IsDomain R],
    ∀ (p : ℕ),
    ∀ a : ClassGroup R, a ^ p = 1 → a = 1

/--
Stage 1c: principal ideal extraction。

Stage 1b で class が trivial になった後、実際に principal ideal として
取り出し、ideal p 乗性の witness を抽出する段。

ここは Mathlib の `ClassGroup.mk_eq_one_of_coe_ideal` をそのまま使えるので、
placeholder ではなく concrete な generic API として定式化する。
-/
abbrev CyclotomicPrincipalIdealExtractionTarget : Prop :=
  ∀ {R : Type*} [CommRing R] [IsDomain R]
      {I : (FractionalIdeal (nonZeroDivisors R) (FractionRing R))ˣ} {I' : Ideal R},
      ((I : FractionalIdeal (nonZeroDivisors R) (FractionRing R)) = I') →
      ClassGroup.mk I = 1 →
      ∃ x, x ≠ 0 ∧ I' = Ideal.span {x}

/--
Stage 1: ideal の p 乗性。

円分体の ideal `(x + ζ^j · y)` が principal ideal の p 乗として書ける、
という Kummer 的 principalization の核心。

これが class group 側の genuinely global な入力。
-/
abbrev CyclotomicIdealPthPowerTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      True

/--
Stage 1a + 1b + 1c → ideal p-th power。

Stage 1 の内部責務を明示化した composition theorem。
Stage 1b / 1c は generic API へ concrete 化したが、
cyclotomic pack への specialization はまだ Stage 1a 側で未供給なので、
ここでは依然として abstract composition として保持する。
-/
theorem cyclotomicIdealPthPower_of_stage1Split
    (_hWitness : CyclotomicIdealClassPTorsionWitnessTarget)
    (_hKill : CyclotomicPTorsionAnnihilationTarget)
  (_hExtract : CyclotomicPrincipalIdealExtractionTarget) :
    CyclotomicIdealPthPowerTarget := by
  intro p x y z hpack q hq hqx hqne hgap
  trivial

/--
Stage 2: unit normalization。

Stage 1 で得た principal ideal p 乗性から、
unit 側のずれを吸収して「整数 p 乗根候補」の形へ正規化できることを表す。

現在は abstract target の器だけ置く。
-/
abbrev CyclotomicUnitNormalizationTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      True

/--
Stage 3: norm bridge。

Stage 1 + Stage 2 で principalized / normalized された cyclotomic data から、
最終的に整数 descent existence `∃ g'` へ戻す橋。

この target は `CyclotomicPrincipalizationTarget` の直前段階。
-/
abbrev CyclotomicNormDescentTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      ∃ g' : ℕ, g' * GN p g' y = (x / q) ^ p

/--
Stage 1 + Stage 2 + Stage 3 → full principalization target。

`CyclotomicIdealPthPowerTarget` と `CyclotomicUnitNormalizationTarget` は
現時点では witness の器だけだが、責務の分離を explicit にすることで
class group 側 / unit 側 / norm 側の境界を固定する。
-/
abbrev CyclotomicPrincipalizationTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      ∃ g' : ℕ, g' * GN p g' y = (x / q) ^ p

/--
3-stage Kummer route を合成して full principalization を得る。
-/
theorem cyclotomicPrincipalization_of_threeStages
    (_hIdeal : CyclotomicIdealPthPowerTarget)
    (_hUnit : CyclotomicUnitNormalizationTarget)
    (hNorm : CyclotomicNormDescentTarget) :
    CyclotomicPrincipalizationTarget :=
  hNorm

/--
Principalization → GapDivisibleBranch（statement 同一なので自明）。
-/
theorem qAdicGapReductionGapDivisible_of_cyclotomicPrincipalization
    (hKummer : CyclotomicPrincipalizationTarget) :
    PrimeGe5BranchAPrimitiveQAdicGapReductionGapDivisibleBranchTarget :=
  hKummer

/-!
## §2. Cyclotomic Class Group p-Torsion Free Target

class group の p-torsion が trivial という仮定の器。
p が regular prime（p ∤ h_p^-）のとき成り立つ。

最初は Prop の器だけ置く。後で concrete 意味を詰める。
-/

/--
ℤ[ζ_p] の class group p-torsion が trivial: `Cl(ℚ(ζ_p))[p] = 0`。

正確には、p が Bernoulli 数 B_{2k} (k = 1,...,(p-3)/2) を
いずれも割らない（= p は regular prime）ことと同値。

ここでは abstract Prop として置き、concrete 意味は後で詰める。
`hpack` の `p` に対する条件。

review-005 時点の判定:
- target を generic な `ClassGroup` p-torsion-free statement へ寄せる方向性自体は自然。
- ただし現状の import / parameterization では、`CyclotomicField p ℚ` の整数環を
  軽量に前面へ出せないため、仮定側の generic 化は number-field infrastructure の設計を伴う。

ゆえに、ここは当面 placeholder のまま保持し、Stage 1a 細分化を優先する。
-/
abbrev CyclotomicClassGroupPTorsionFreeTarget : Prop :=
  ∀ {p : ℕ}, Nat.Prime p → 5 ≤ p → True
  -- TODO: concrete meaning を詰める。
  -- 最終的には `∀ α ∈ Cl(ℚ(ζ_p)), α^p = 1 → α = 1`
  -- あるいは `p ∤ h_p^-` (Kummer regularity) の形になる。

/--
Class group p-torsion free → Principalization（abstract bridge）。

legacy one-shot wrapper。責務分離後は
`cyclotomicIdealPthPower_of_classGroupPTorsionFree` を本丸とみなす。

数学的根拠は Kummer の第一場合の証明:
1. class group p-torsion = 0
2. → ideal (x + ζ^j · y) は principal ideal の p 乗
3. → norm 計算で z'^p = (x/q)^p + y^p の解 z' が整数として存在

現時点では sorry: class group 理論の formal 化が必要。
-/
theorem cyclotomicPrincipalization_of_classGroupPTorsionFree
    (hCl : CyclotomicClassGroupPTorsionFreeTarget) :
    CyclotomicPrincipalizationTarget := by
  sorry

/--
Class group p-torsion free → Stage 1 (ideal p-th power)。

`cyclotomicPrincipalization_of_classGroupPTorsionFree` を thinner に見直した wrapper。
genuinely global な class group 入力が直接 supply するのは
Stage 1 全体よりも、さらに薄い Stage 1a / 1b / 1c のどこかと考える。

Stage 1 target 自体は placeholder だが、**この theorem が open kernel**。
現時点では sorry。ここが Kummer branch の最深部。
-/
theorem cyclotomicIdealPthPower_of_classGroupPTorsionFree
    (hCl : CyclotomicClassGroupPTorsionFreeTarget) :
    CyclotomicIdealPthPowerTarget := by
  sorry

/--
Stage 1a: gap-divisible geometry → ideal class の p-torsion witness。

review-002 で露出させた最小核。
本質的には「円分体で得る ideal class が p-torsion に入る」ことを示す段で、
class group 側の freeness をまだ使っていない。

現時点では sorry。これを埋められれば、上流の genuinely global kernel はさらに薄くなる。
-/
theorem cyclotomicIdealClassPTorsionWitness_of_gapDivisibleGeometry :
    CyclotomicIdealClassPTorsionWitnessTarget := by
  sorry

/--
Stage 1b: class group p-torsion free → p-torsion annihilation。

`CyclotomicClassGroupPTorsionFreeTarget` 自体は placeholder だが、
出力先の Stage 1b は generic API に concrete 化した。
ただし review-005 の短距離検査により、`hCl` からこの generic statement を供給するには
`CyclotomicField` の整数環 parameterization まで露出させる追加設計が必要だと判明した。

したがってこの theorem は「generic target の形が未定」ではなく、
「cyclotomic 仮定を generic API に specialized する橋」が未解決、という位置づけになる。
-/
theorem cyclotomicPTorsionAnnihilation_of_classGroupPTorsionFree
    (_hCl : CyclotomicClassGroupPTorsionFreeTarget) :
    CyclotomicPTorsionAnnihilationTarget := by
  intro R _ _ p a ha
  -- `hCl` はまだ placeholder で、軽量な cyclotomic integer-ring parameterization も未整備。
  -- したがってここでは generic API の出口だけ固定する。
  sorry

/--
Stage 1c: trivial class → principal ideal extraction。

`ClassGroup.mk_eq_one_of_coe_ideal` により、ここは既に concrete な generic API で閉じる。
したがって今後 genuinely global に残るのは Stage 1a / 1b 側だけになる。
-/
theorem cyclotomicPrincipalIdealExtraction_of_classTrivialization :
    CyclotomicPrincipalIdealExtractionTarget := by
  intro R _ _ I I' hI hClass
  exact (ClassGroup.mk_eq_one_of_coe_ideal hI).mp hClass

/--
Integral ideal 版の principal ideal extraction helper。

将来 Stage 1c を Dedekind 領域の integral ideal へ specialized する際の足場。
`ClassGroup.mk0_eq_one_iff` をそのまま包装したもの。
-/
theorem idealIsPrincipal_of_classGroupMk0_eq_one
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {I : Ideal R} (hI : I ∈ nonZeroDivisors (Ideal R))
    (hClass : ClassGroup.mk0 ⟨I, hI⟩ = 1) :
    I.IsPrincipal :=
  (ClassGroup.mk0_eq_one_iff hI).mp hClass

/--
Refined Stage 1 route: geometry witness + torsion annihilation + principal extraction。

Stage 1 全体をさらに薄い 3 段へ裂いた refined route。
ただし現時点では Stage 1 target 自体が placeholder なので、
concrete 化されたのは Stage 1b / 1c の generic API までである。
-/
theorem cyclotomicIdealPthPower_of_refinedStage1Route
    (hWitness : CyclotomicIdealClassPTorsionWitnessTarget)
    (hKill : CyclotomicPTorsionAnnihilationTarget)
    (hExtract : CyclotomicPrincipalIdealExtractionTarget) :
    CyclotomicIdealPthPowerTarget :=
  cyclotomicIdealPthPower_of_stage1Split hWitness hKill hExtract

/--
Refined class-group route: class group → ideal p-th power → principalization。

class group 側の genuinely global step と、下流の unit / norm stage を分離する。
-/
theorem cyclotomicPrincipalization_of_refinedClassGroupRoute
    (hCl : CyclotomicClassGroupPTorsionFreeTarget)
    (hUnit : CyclotomicUnitNormalizationTarget)
    (hNorm : CyclotomicNormDescentTarget) :
    CyclotomicPrincipalizationTarget :=
  cyclotomicPrincipalization_of_threeStages
    (cyclotomicIdealPthPower_of_classGroupPTorsionFree hCl)
    hUnit hNorm

/-!
## §3. ClassGroupBridge と RegularPrime route

Regular prime (p ∤ h_p^-) → ClassGroupPTorsionFree は定義同値になる予定。
ここでは forward reference を避け、別ファイルに分離する。

重要: 現在 genuinely global に残っている open kernel は、
`CyclotomicIdealClassPTorsionWitnessTarget` を供給する部分まで薄化できるか、
が次段の焦点になる。
Stage 1c は generic ClassGroup API により concrete 化済みである。
`CyclotomicUnitNormalizationTarget` と `CyclotomicNormDescentTarget` は
今は abstract target の器だが、今後の formalization では
Mathlib 既存資産でどこまで concrete 化できるかを個別に監査する。
-/

end DkMath.FLT
