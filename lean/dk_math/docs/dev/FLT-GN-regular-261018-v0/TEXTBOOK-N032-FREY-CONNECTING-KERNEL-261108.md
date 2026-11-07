# NOTE-032 教科書 — 同じ連結準同型の単射性・係数核の同型・位数 p の巡回核

日付: 2026-11-08。最新レビューの不変剰余類と核の同型の提案を、実際の Mathlib API で5ステップ実装した。
この文書の5つの Lean ブロックは、対応する5 production ソースの全文である。
各 import 群直後の正確な `#print "file: モジュール名"` を保持する。
既存 DkMath の Lake 環境で、それぞれ別ファイルへコピペして検査できる。

## 同じ係数と同じ写像を使う

同じ Frey 曲線 E、巡回段 T、上位捩れ商 Q=E[p^(n+2)]/T、慣性群 I と固定部分群 F=Q^I を使う。
元の実際の包含が誘導する通常の H¹ 写像を

    ι_* : H¹(I,F) → H¹(I,Q)
    K = ker ι_*

とする。F の作用は固定性に対応する自明作用、Q の作用は元の実際の慣性作用である。
今回の K は、この同じ Mathlib の H¹ 写像の **実際の整数部分加群としての核**。
単に濃度の等しい別の群へ置き換えない。

## 1. Q/F 全体は慣性固定になる

元の有限捩れ群の局所的な差分積零性から、任意の同じ有限捩れ点 x の作用差の Q での像は F に入る。
前回の不変剰余類の構成は、特定の障害点だけでなく全ての x に適用できる。
Q の商写像と Q/F の商写像の全射性を使うと、任意の Q/F の元がそのような点で表せる。
従って、同じ q≠p の悪い住所の局所条件の下で

    (Q/F)^I = Q/F

という内容を、元をそのまま保つ整数線形同型として構成できる。
これは **Q/F の作用自明性** であり、元の Q の作用自明性ではない。

## 2. H⁰ 射影が零なので連結準同型は単射

同じ短完全列 0→F→Q→Q/F→0 に対する実際の連結準同型を

    δ : H⁰(I,Q/F) → H¹(I,F)

とする。F=Q^I なので、Q の不変元は全て元の F に属し、Q/F での像は零になる。
標準 H⁰ 同型の自然性により、実際の写像 H⁰(I,Q)→H⁰(I,Q/F) は零写像である。
H⁰(I,Q) そのものが零であるとは仮定も証明もしない。

Mathlib の実際の長完全系列の正確性を使うと

    ker δ = im(H⁰(I,Q)→H⁰(I,Q/F)) = 0

となり、δ の単射性が従う。この部分は元の固定部分群の定義と短完全列だけを使い、
hclass、Cofixed、局所節点幾何や q の条件を要求しない。

## 3. 不変剰余類と実際の係数核の同型

長完全系列の次の箇所の正確性は

    im δ = ker ι_* = K

を与える。同じ δ を K へ値域制限し、その単射性と正確性による全射性から

    H⁰(I,Q/F) ≃ₗ[ℤ] K
    (Q/F)^I ≃ₗ[ℤ] K

を構成した。写像の順方向は元の同じ δ である。
局所条件の下では第1段階の同型を合成できるので

    Q/F ≃ₗ[ℤ] K

まで得られる。これらは型だけの宣言ではなく、実際の線形同型の構成である。

## 4. 同じ剰余類と核元の厳密位数 p

元の同じ障害点 y は p•y∈T を満たすので、Q の元 u=[y] は p•u=0 を満たす。
Q/F への同じ射影で ū=u+F も p で消える。
以前の同じ非自明な差分値による ū≠0 と p の素数性を合わせ、

    addOrderOf ū = p

を不変部分加群の元として証明した。標準の H⁰ 同型でも同じ厳密位数を保つ。
さらに構成した同型で同じ ū を K へ写した元 k について、

    k.val = α_I
    addOrderOf k = p
    |zmultiples k| = p

を証明した。k.val は以前の同じ慣性固定係数類であり、別の核元を選んだものではない。
濃度 p と確定したのは、この同じ k が生成する巡回部分群である。

## 5. 核全体の濃度と元の算術証明書

同じ Q/F と K の実際の同型、元の部分群 F の濃度公式、以前の Q の正確な濃度から

    |K| · |F| = |Q| = p^(n+3)

を証明した。従って |K| は p^(n+3) を割り、

    |K| = p^s,  0≤s≤n+3

となる。元の障害証明書から得た同じ厳密位数 p の核元により K は自明ではないので、

    1≤s≤n+3

も得られる。新しい有限性・核濃度・同型を provider にしていない。
核全体の濃度が p と主張するわけではない。

最終定理 `residual_exists_prime_cyclic_coefficient_kernel` は従来の正確な hclass と同じ Cofixed 候補から、
元の n,T,q,A,τ,y と同じ障害証明書 h を取得する。
同じ ū、同じ H⁰ 元、同じ核元 k の厳密位数 p、その実際の巡回部分群の濃度 p、
k.val=α_I、核全体の正の p 冪濃度を一緒に出力する。

## 数学的な境界

同じ非零連結像が実際の係数核に属すること、さらにその核と Q/F が同型であることは、
完全系列に沿う整合した構造である。それ自体は算術的矛盾ではない。
Q/F 全体が慣性固定でも、それが零になることは証明していない。
K も零ではなく、同じ障害証明書の下で正の p 冪濃度を持つ。

今回の H⁰/H¹ は Mathlib の **通常の群コホモロジー**。
連続 H¹ との比較、大域の円分類群への同定、Frey 固有の両共鳴分岐の算術的排除、hclass の供給は残る。
**無条件の一般 hno は引き続き未完成。**

## 模範解答と Mathlib の照合

ローカル模範解答の `S_groupCohomology_deltaCochain0_mem_coboundaries1_iff.lean` で、
不変元の持ち上げと連結 cochain の coboundary の関係を照合した。
`S_groupCohomology_map_delta_eq_delta_map.lean` の短完全列と連結写像の自然性も確認した。
今回は外部の独自 cochain や provider を移植せず、Mathlib の実際の短完全列の長完全系列を使用する。
`mapShortComplex₃_exact`、`mapShortComplex₁_exact` と H⁰ 同型の自然性を参照した。
P2M/P2MW や外部の theorem/provider は import しない。
参照 HEAD と SHA-256 は `evidence/note032-frey-connecting-kernel-reference-audit.json` に保存した。

## 1. 同じ Q/F の全慣性固定性

二つの元の商写像の全射性から、全剰余類の固定性と元を保つ線形同型を構成する。

ソース: `DkMath/FLT/FreyFixedQuotientTrivial.lean`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFixedH1PrimeOrder

#print "file: DkMath.FLT.FreyFixedQuotientTrivial"

/-!
# 同じ Q/F 全体の慣性固定性

F=Q^I。元の有限捩れにおける差分積零性から、全ての Q の作用差は F に入る。
Q/F の自明作用と、元の Q の作用を区別する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 元の同じ Q/F の全ての元は、同じ実際の慣性作用で固定される。 -/
theorem ResidualCyclicStage.fixedQuotient_all_invariant (z : T.fixedQuotientCoefficient A) :
    z ∈ (T.fixedQuotientCoefficient A).ρ.invariants := by
  obtain ⟨u, rfl⟩ := (T.fixedCoefficientSubmodule A).mkQ_surjective z
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective u
  exact (T.fixedCosetInvariant hp5 hq hqp haddr A hA x).property

/-- 同じ Q/F の作用そのものが自明。元の Q の作用自明性は主張しない。 -/
theorem ResidualCyclicStage.fixedQuotient_action_trivial (σ : inertiaSubgroupIn A ℚ)
    (z : T.fixedQuotientCoefficient A) : (T.fixedQuotientCoefficient A).ρ σ z = z :=
  T.fixedQuotient_all_invariant hp5 hq hqp haddr A hA z σ

/-- 同じ全ての剰余類を保つ、不変部分加群と Q/F の整数線形同型。 -/
def ResidualCyclicStage.fixedQuotientInvariantEquiv :
    (T.fixedQuotientCoefficient A).ρ.invariants ≃ₗ[ℤ] T.fixedQuotientCoefficient A where
  toFun z := z.val
  invFun z := ⟨z, T.fixedQuotient_all_invariant hp5 hq hqp haddr A hA z⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end
end DkMath.FLT.Frey.Source
```

## 2. 実際の連結準同型の単射性

H⁰ 射影の零性と、実際の長完全系列の正確性を使う。

ソース: `DkMath/FLT/FreyFixedConnectingInjective.lean`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFixedH1PrimeOrder

#print "file: DkMath.FLT.FreyFixedConnectingInjective"

/-!
# 同じ固定係数の連結準同型の単射性

F=Q^I なので H⁰(Q)→H⁰(Q/F) は零。実際の長完全系列の正確性から δ は単射。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))

/-- 同じ係数射影が誘導する実際の通常の H⁰ 写像。 -/
abbrev ResidualCyclicStage.fixedH0Projection :=
  groupCohomology.map (A := T.fullInertiaCoefficient A) (B := T.fixedQuotientCoefficient A) (MonoidHom.id (inertiaSubgroupIn A ℚ)) (T.fixedCoefficientProjection A) 0

/-- Q の不変元は元の F に属するので、この同じ H⁰ 射影は零。 -/
theorem ResidualCyclicStage.fixedH0Projection_zero : T.fixedH0Projection A = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply (CategoryTheory.Iso.toLinearEquiv (groupCohomology.H0Iso (T.fixedQuotientCoefficient A))).injective
  change (groupCohomology.H0Iso (T.fixedQuotientCoefficient A)).hom
    (T.fixedH0Projection A z) = (groupCohomology.H0Iso (T.fixedQuotientCoefficient A)).hom 0
  rw [map_zero, groupCohomology.map_id_comp_H0Iso_hom_apply]
  apply Subtype.ext
  change (T.fixedCoefficientSubmodule A).mkQ
    ((groupCohomology.H0Iso (T.fullInertiaCoefficient A)).hom z).val = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  intro σ hσ
  exact ((groupCohomology.H0Iso (T.fullInertiaCoefficient A)).hom z).property ⟨σ, hσ⟩

/-- 同じ実際の H⁰→H¹ 連結準同型は単射。局所幾何や hclass は不要。 -/
theorem ResidualCyclicStage.fixedConnecting_injective : Function.Injective (T.fixedConnecting A) := by
  have he := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp
    (groupCohomology.mapShortComplex₃_exact (T.fixedCoefficientSequence_shortExact A) (i := 0) rfl)
  change LinearMap.range (T.fixedH0Projection A).hom = LinearMap.ker (T.fixedConnecting A).hom at he
  have hr : LinearMap.range (T.fixedH0Projection A).hom = ⊥ := by
    rw [T.fixedH0Projection_zero]
    exact LinearMap.range_zero
  exact LinearMap.ker_eq_bot.mp (he.symm.trans hr)

end
end DkMath.FLT.Frey.Source
```

## 3. 同じ係数核との実際の同型

δ をその像である同じ係数核に制限し、全単射な整数線形写像として構成する。

ソース: `DkMath/FLT/FreyFixedConnectingKernel.lean`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFixedConnectingInjective
import DkMath.FLT.FreyFixedQuotientTrivial

#print "file: DkMath.FLT.FreyFixedConnectingKernel"

/-!
# 同じ不変剰余類と実際の H¹ 係数写像の核の同型

実際の δ の単射性と長完全系列の正確性から、標準の核への整数線形同型を構成する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
-- 核の部分加群構造は、元の H¹ から継承した構造を使う。
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))

/-- 元の F→Q の包含による実際の通常の H¹ 係数写像。 -/
abbrev ResidualCyclicStage.fixedH1CoefficientMap :=
  groupCohomology.map
    (A := TrivialCharacterH1.coefficient (inertiaSubgroupIn A ℚ) (T.inertiaFixedUpperQuotient A))
    (B := T.fullInertiaCoefficient A) (MonoidHom.id (inertiaSubgroupIn A ℚ)) (T.fixedCoefficientInclusion A) 1

/-- 同じ実際の係数写像の整数線形核。 -/
abbrev ResidualCyclicStage.fixedH1CoefficientKernel := LinearMap.ker (T.fixedH1CoefficientMap A).hom

/-- 同じ連結準同型の像は、同じ実際の係数写像の核。 -/
theorem ResidualCyclicStage.fixedConnecting_range :
    LinearMap.range (T.fixedConnecting A).hom = T.fixedH1CoefficientKernel A := by
  exact (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp
    (groupCohomology.mapShortComplex₁_exact (T.fixedCoefficientSequence_shortExact A) (i := 0) rfl)

/-- 同じ δ の値を同じ核の元として保持する。 -/
def ResidualCyclicStage.fixedConnectingToKernel :
    groupCohomology.H0 (T.fixedQuotientCoefficient A) →ₗ[ℤ] T.fixedH1CoefficientKernel A :=
  (T.fixedConnecting A).hom.codRestrict (T.fixedH1CoefficientKernel A) (by
    intro z
    rw [← T.fixedConnecting_range]
    exact ⟨z, rfl⟩)

/-- 実際の単射な δ が与える、H⁰(Q/F) と係数核の整数線形同型。 -/
def ResidualCyclicStage.fixedConnectingKernelEquiv :
    groupCohomology.H0 (T.fixedQuotientCoefficient A) ≃ₗ[ℤ] T.fixedH1CoefficientKernel A :=
  LinearEquiv.ofBijective (T.fixedConnectingToKernel A) ⟨by
    intro x y hxy
    exact T.fixedConnecting_injective A (congrArg Subtype.val hxy), by
    intro v
    have hv : v.val ∈ LinearMap.range (T.fixedConnecting A).hom := by
      rw [T.fixedConnecting_range]
      exact v.property
    obtain ⟨z, hz⟩ := hv
    exact ⟨z, Subtype.ext hz⟩⟩

/-- 同じ (Q/F)^I と実際の係数核の同型。 -/
def ResidualCyclicStage.invariantConnectingKernelEquiv :
    (T.fixedQuotientCoefficient A).ρ.invariants ≃ₗ[ℤ] T.fixedH1CoefficientKernel A :=
  (CategoryTheory.Iso.toLinearEquiv (groupCohomology.H0Iso (T.fixedQuotientCoefficient A)).symm).trans
    (T.fixedConnectingKernelEquiv A)

variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)

include hp5 hq hqp haddr hA in
/-- 同じ局所幾何の下では Q/F 全体が固定なので、同じ Q/F 自体が係数核と同型。 -/
def ResidualCyclicStage.quotientConnectingKernelEquiv :
    T.fixedQuotientCoefficient A ≃ₗ[ℤ] T.fixedH1CoefficientKernel A :=
  (T.fixedQuotientInvariantEquiv hp5 hq hqp haddr A hA).symm.trans
    (T.invariantConnectingKernelEquiv A)

end
end DkMath.FLT.Frey.Source
```

## 4. 同じ剰余類・H⁰ 元・核元の厳密位数 p

元の p•y∈T と同じ非零性を使い、構成した同型で厳密位数を保つ。

ソース: `DkMath/FLT/FreyConnectingKernelPrimeOrder.lean`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFixedConnectingKernel

#print "file: DkMath.FLT.FreyConnectingKernelPrimeOrder"

/-!
# 同じ不変剰余類と実際の係数核の厳密位数 p

元の p•y∈T を使い、同じ剰余類、H⁰ 元、係数核の元とその巡回部分群を保持する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ点の Q での商類は、元の前像条件から p で消える。 -/
theorem NarrowAbsorptionObstruction.pointClass_killed
    (h : S.NarrowAbsorptionObstruction L T q A τ y) :
    p • (QuotientAddGroup.mk' T.upperStage)
      (⟨y, h.killed⟩ : Torsion S.rationalCurve (p ^ (n + 1 + 1))) = 0 := by
  rw [← map_nsmul]
  exact (QuotientAddGroup.eq_zero_iff (N := T.upperStage) _).mpr h.preimage

/-- 同じ Q/F の不変剰余類も p で消える。 -/
theorem NarrowAbsorptionObstruction.fixedCoset_killed
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    p • (T.fixedCosetInvariant hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x).val = 0 := by
  change p • (T.fixedCoefficientProjection A) ((QuotientAddGroup.mk' T.upperStage) _) = 0
  exact (map_nsmul (T.fixedCoefficientProjection A).hom p _).symm.trans
    ((congrArg (T.fixedCoefficientProjection A) h.pointClass_killed).trans (map_zero _))

/-- 元の同じ不変剰余類自体の厳密位数は p。 -/
theorem NarrowAbsorptionObstruction.fixedCoset_order_eq_prime
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    addOrderOf (T.fixedCosetInvariant hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x) = p := by
  apply addOrderOf_eq_prime_iff.mpr
  constructor
  · apply Subtype.ext
    exact h.fixedCoset_killed hp5
  · intro hz
    exact h.fixedCoset_ne_zero hp5 (congrArg Subtype.val hz)

/-- 標準 H⁰ 同型で写した同じ H⁰ 元も厳密位数 p。 -/
theorem NarrowAbsorptionObstruction.fixedCosetH0_order_eq_prime
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    addOrderOf (T.fixedCosetH0 hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x) = p := by
  exact ((CategoryTheory.Iso.toLinearEquiv (groupCohomology.H0Iso (T.fixedQuotientCoefficient A))).symm.toAddEquiv.addOrderOf_eq
    (T.fixedCosetInvariant hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩)).trans
      (h.fixedCoset_order_eq_prime hp5)

end

section KernelElement
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

/-- 同じ不変剰余類を、構成済みの同型で元の実際の係数核へ写す。 -/
noncomputable def ResidualCyclicStage.fixedCosetKernelElement
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) : T.fixedH1CoefficientKernel A :=
  T.invariantConnectingKernelEquiv A (T.fixedCosetInvariant hp5 hq hqp haddr A hA x)

/-- この同じ核元の値は、以前の同じ慣性 H¹ 類である。 -/
theorem ResidualCyclicStage.fixedCosetKernelElement_val
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    (T.fixedCosetKernelElement hp5 hq hqp haddr A hA x).val =
      T.fixedInertiaH1Class hp5 hq hqp haddr A hA x :=
  T.fixedCoset_connecting hp5 hq hqp haddr A hA x
end KernelElement

noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ実際の係数核の元自身も、同型によって厳密位数 p を持つ。 -/
theorem NarrowAbsorptionObstruction.fixedKernel_order_eq_prime
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    addOrderOf (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x) = p := by
  exact ((T.invariantConnectingKernelEquiv A).toAddEquiv.addOrderOf_eq
    (T.fixedCosetInvariant hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩)).trans
      (h.fixedCoset_order_eq_prime hp5)

/-- 同じ核元が生成する実際の巡回部分群の濃度は p。核全体の濃度は主張しない。 -/
theorem NarrowAbsorptionObstruction.fixedKernel_cyclic_card
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    Nat.card (AddSubgroup.zmultiples
      (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x)) = p := by
  exact (Nat.card_zmultiples _).trans (h.fixedKernel_order_eq_prime hp5)

end
end DkMath.FLT.Frey.Source
```

## 5. 核全体の濃度と位数 p の巡回部分群の証明書

元の有限捩れ商の濃度から核の正の p 冪濃度を内部計算し、同じ算術証明書へ接続する。

ソース: `DkMath/FLT/FreyConnectingKernelCertificate.lean`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyConnectingKernelPrimeOrder

#print "file: DkMath.FLT.FreyConnectingKernelCertificate"

/-!
# 同じ係数核の濃度と位数 p の巡回部分群の算術証明書

核全体は同じ Q/F と同型。濃度積と p 冪上界を内部計算し、元の同じ証明書へ接続する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)

/-- 元の同じ剰余類を Q/F の同型へ渡すと、元の同じ核元になる。 -/
theorem ResidualCyclicStage.quotientKernelEquiv_coset
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA
      (T.fixedCosetInvariant hp5 hq hqp haddr A hA x).val =
      T.fixedCosetKernelElement hp5 hq hqp haddr A hA x := rfl

include hp5 hq hqp haddr hA in
/-- 実際の係数核の濃度と元の固定部分群の濃度の積は、元の Q の濃度 p^(n+3)。 -/
theorem ResidualCyclicStage.fixedKernel_card_mul_fixed :
    Nat.card (T.fixedH1CoefficientKernel A) * Nat.card (T.inertiaFixedUpperQuotient A) = p ^ (n + 3) := by
  have he := Nat.card_congr (T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA).toEquiv
  calc
    Nat.card (T.fixedH1CoefficientKernel A) * Nat.card (T.inertiaFixedUpperQuotient A) =
        Nat.card (T.fixedQuotientCoefficient A) * Nat.card (T.inertiaFixedUpperQuotient A) := by rw [he]
    _ = Nat.card T.upperQuotient :=
      (T.inertiaFixedUpperQuotient A).card_eq_card_quotient_mul_card_addSubgroup.symm
    _ = p ^ (n + 3) := T.upperQuotient_card

include hp5 hq hqp haddr hA in
/-- 同じ係数核全体の濃度は、上界 n+3 の p 冪。 -/
theorem ResidualCyclicStage.fixedKernel_prime_power_profile :
    ∃ s ≤ n + 3, Nat.card (T.fixedH1CoefficientKernel A) = p ^ s := by
  have hd : Nat.card (T.fixedH1CoefficientKernel A) ∣ p ^ (n + 3) :=
    ⟨Nat.card (T.inertiaFixedUpperQuotient A), (T.fixedKernel_card_mul_fixed A hp5 hq hqp haddr hA).symm⟩
  exact (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hd

end

noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ障害の位数 p 核元により、核濃度の p 冪指数は正。 -/
theorem NarrowAbsorptionObstruction.fixedKernel_positive_profile
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    ∃ s, 1 ≤ s ∧ s ≤ n + 3 ∧ Nat.card (T.fixedH1CoefficientKernel A) = p ^ s := by
  let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
  have ho : addOrderOf k = p := h.fixedKernel_order_eq_prime hp5
  have hk : k ≠ 0 := by
    intro hz
    rw [hz, addOrderOf_zero] at ho
    exact (Fact.out : p.Prime).ne_one ho.symm
  have hc1 : Nat.card (T.fixedH1CoefficientKernel A) ≠ 1 := by
    intro hc
    exact hk ((Nat.card_eq_one_iff_unique.mp hc).1.elim k 0)
  obtain ⟨s, hs, hc⟩ := T.fixedKernel_prime_power_profile A hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) h.lies_over
  have hs0 : s ≠ 0 := by intro hz; exact hc1 (by rw [hc, hz, pow_zero])
  exact ⟨s, by omega, hs, hc⟩
end
end DkMath.FLT.Frey.Source

namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation CyclotomicKernelField CyclotomicKummerWeight ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] (S : Source p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ
variable
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)

include hline hζ hp5 hclass in
/-- 元の同じ算術証明書から、同じ剰余類・H⁰ 元・係数核の元と巡回部分群を出力する。 -/
theorem residual_exists_prime_cyclic_coefficient_kernel
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n) (q : ℕ)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : Field.absoluteGaloisGroup ℚ)
      (y : Points S.rationalCurve), ∃ h : S.NarrowAbsorptionObstruction L T q A τ y,
      let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
      let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x
      addOrderOf (T.fixedCosetInvariant hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x) = p ∧
      addOrderOf (T.fixedCosetH0 hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x) = p ∧
      addOrderOf k = p ∧ Nat.card (AddSubgroup.zmultiples k) = p ∧
      k.val = T.fixedInertiaH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x ∧
      ∃ s, 1 ≤ s ∧ s ≤ n + 3 ∧ Nat.card (T.fixedH1CoefficientKernel A) = p ^ s := by
  obtain ⟨n, T, q, A, τ, y, h⟩ := S.residual_exists_narrow_geometric_obstruction L hline hζ hp5 hclass hcofixed
  exact ⟨n, T, q, A, τ, y, h, h.fixedCoset_order_eq_prime hp5, h.fixedCosetH0_order_eq_prime hp5,
    h.fixedKernel_order_eq_prime hp5, h.fixedKernel_cyclic_card hp5,
    T.fixedCosetKernelElement_val hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩,
    h.fixedKernel_positive_profile hp5⟩
end
end DkMath.FLT.Frey.Source
```

## 検証

新規26宣言の checked type・constructor・opaque proof value の再帰依存監査と、
18件の公開入力監査を通常テスト入口へ追加した。
有限例の剪断作用では射影後の値は固定でも元の点は動くこと、線形核の実際の同型が同じ値と位数を保つことを検査する。
また、濃度25の零写像の核の中に濃度5の巡回部分群がある例で、核全体と生成部分群を区別する。
実行結果は `evidence/validation-note032-frey-connecting-kernel.txt` を参照。
