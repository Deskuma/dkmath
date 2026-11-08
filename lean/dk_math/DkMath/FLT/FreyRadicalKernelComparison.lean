/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyRadicalGeneratorCertificate

#print "file: DkMath.FLT.FreyRadicalKernelComparison"

/-!
# 根核と Frey 共通商核の比較の、同じ値による同値条件

核包含を仮定も結論もしない。実際に必要な算術命題を、全核元の評価、
または元の有限捩れ点の固定差分という同値な形で特定する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 元の共通射影の核への所属は、同じ全核元の評価の零性と同値。 -/
theorem ResidualCyclicStage.mem_commonProjection_kernel_iff_evaluations (σ : inertiaSubgroupIn A ℚ) :
    σ ∈ (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA).ker ↔
      ∀ k : T.fixedH1CoefficientKernel A, T.fixedKernelEvaluation A σ k = 0 := by
  change T.fixedKernelCommonProjection A hp5 hq hqp haddr hA σ = 1 ↔ _
  constructor
  · intro he k
    have hv := congrArg (T.fixedKernelCommonTameValues A hp5 hq hqp haddr hA) he
    rw [map_one] at hv
    exact congrArg Multiplicative.toAdd (congrFun hv k)
  · intro he
    apply T.fixedKernelCommonTameValues_injective A hp5 hq hqp haddr hA
    rw [map_one]
    apply funext
    intro k
    exact congrArg Multiplicative.ofAdd (he k)

/-- 同じ共通核への所属は、元の全有限捩れ点の固定差分が1になることと同値。 -/
theorem ResidualCyclicStage.mem_commonProjection_kernel_iff_fixed_differences (σ : inertiaSubgroupIn A ℚ) :
    σ ∈ (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA).ker ↔
      ∀ x : Torsion S.rationalCurve (p ^ (n + 1 + 1)),
        T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x σ = 1 := by
  rw [T.mem_commonProjection_kernel_iff_evaluations A hp5 hq hqp haddr hA σ]
  constructor
  · intro he x
    have hv := he (T.fixedCosetKernelElement hp5 hq hqp haddr A hA x)
    rw [T.fixedKernelEvaluation_coset A hp5 hq hqp haddr hA x σ] at hv
    exact congrArg Multiplicative.ofAdd hv
  · intro he k
    obtain ⟨x, rfl⟩ := T.exists_torsion_fixedKernelElement A hp5 hq hqp haddr hA k
    rw [T.fixedKernelEvaluation_coset A hp5 hq hqp haddr hA x σ]
    exact congrArg Multiplicative.toAdd (he x)

/-- 求める核包含は「同じ根を固定する元の全評価が零」という算術命題と同値。 -/
theorem ResidualCyclicStage.radical_kernel_comparison_iff_evaluations :
    (InertiaRadical.character (Fact.out : p.Prime) hq hqp.symm A hA (n + 3)).ker ≤
      (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA).ker ↔
      ∀ σ : inertiaSubgroupIn A ℚ,
        σ.val (InertiaRadical.radical p q (Fact.out : p.Prime) (n + 3)) =
          InertiaRadical.radical p q (Fact.out : p.Prime) (n + 3) →
        ∀ k : T.fixedH1CoefficientKernel A, T.fixedKernelEvaluation A σ k = 0 := by
  constructor
  · intro he σ hs
    apply (T.mem_commonProjection_kernel_iff_evaluations A hp5 hq hqp haddr hA σ).mp
    exact he ((InertiaRadical.character_eq_one_iff_root_fixed (Fact.out : p.Prime) hq hqp.symm A hA (n + 3) σ).mpr hs)
  · intro he σ hs
    apply (T.mem_commonProjection_kernel_iff_evaluations A hp5 hq hqp haddr hA σ).mpr
    exact he σ ((InertiaRadical.character_eq_one_iff_root_fixed (Fact.out : p.Prime) hq hqp.symm A hA (n + 3) σ).mp hs)

/-- 同じ核包含の、元の有限捩れ点の差分だけを使う同値な形。 -/
theorem ResidualCyclicStage.radical_kernel_comparison_iff_fixed_differences :
    (InertiaRadical.character (Fact.out : p.Prime) hq hqp.symm A hA (n + 3)).ker ≤
      (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA).ker ↔
      ∀ σ : inertiaSubgroupIn A ℚ,
        σ.val (InertiaRadical.radical p q (Fact.out : p.Prime) (n + 3)) =
          InertiaRadical.radical p q (Fact.out : p.Prime) (n + 3) →
        ∀ x : Torsion S.rationalCurve (p ^ (n + 1 + 1)),
          T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x σ = 1 := by
  constructor
  · intro he σ hs
    apply (T.mem_commonProjection_kernel_iff_fixed_differences A hp5 hq hqp haddr hA σ).mp
    exact he ((InertiaRadical.character_eq_one_iff_root_fixed (Fact.out : p.Prime) hq hqp.symm A hA (n + 3) σ).mpr hs)
  · intro he σ hs
    apply (T.mem_commonProjection_kernel_iff_fixed_differences A hp5 hq hqp haddr hA σ).mpr
    exact he σ ((InertiaRadical.character_eq_one_iff_root_fixed (Fact.out : p.Prime) hq hqp.symm A hA (n + 3) σ).mp hs)

end
end DkMath.FLT.Frey.Source
