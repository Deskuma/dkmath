/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyRadicalKernelClosure

#print "file: DkMath.FLT.FreyCommonTameCyclicClosure"

/-! # 実際の共通商の巡回性と同じ生成元による単一評価
未証明の巡回性や有限段分解を公開入力にしない。 -/
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

/-- 元の全段原始慣性生成元の像が、同じ H を生成する。 -/
theorem ResidualCyclicStage.commonProjection_generator_generates :
    ∀ h : T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA,
      h ∈ Subgroup.zpowers (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA
        (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA)) := by
  intro h
  obtain ⟨σ, rfl⟩ := T.fixedKernelCommonProjection_surjective A hp5 hq hqp haddr hA h
  obtain ⟨j, _, ε, he, hε, _⟩ := InertiaRadical.correction_of_primitive
    (Fact.out : p.Prime) hq hqp.symm A hA (n + 2) _
    (InertiaRadical.generator_primitive (Fact.out : p.Prime) hq hqp.symm A hA (n + 2)) σ
  have hkill := T.radical_kernel_le_commonProjection_kernel A hp5 hq hqp haddr hA hε
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨(j : ℤ), ?_⟩
  rw [zpow_natCast, he, map_mul, map_pow, show T.fixedKernelCommonProjection A hp5 hq hqp haddr hA ε = 1 from hkill, mul_one]

/-- 追加の hcyclic/hgen なしで、実際の Frey 共通商は巡回。 -/
theorem ResidualCyclicStage.commonTame_isCyclic :
    IsCyclic (T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA) := by
  apply isCyclic_iff_exists_zpowers_eq_top.mpr
  refine ⟨T.fixedKernelCommonProjection A hp5 hq hqp haddr hA
    (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA), eq_top_iff.mpr ?_⟩
  intro h _
  exact T.commonProjection_generator_generates A hp5 hq hqp haddr hA h

/-- 同じ具体的な γ での単一慣性評価が、元の全係数核上で単射。 -/
theorem ResidualCyclicStage.generator_evaluation_injective :
    Function.Injective (T.fixedKernelEvaluation A
      (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA)) :=
  T.fixedKernelCommon_generator_evaluation_injective A hp5 hq hqp haddr hA _
    (T.commonProjection_generator_generates A hp5 hq hqp haddr hA)

/-- 同じ核の濃度は、同じ固定係数群の濃度を割る。 -/
theorem ResidualCyclicStage.kernel_card_dvd_fixed_of_radical_generator :
    Nat.card (T.fixedH1CoefficientKernel A) ∣ Nat.card (T.inertiaFixedUpperQuotient A) :=
  AddSubgroup.card_dvd_of_injective (T.fixedKernelEvaluation A
    (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA)).toAddMonoidHom
    (T.generator_evaluation_injective A hp5 hq hqp haddr hA)
end
end DkMath.FLT.Frey.Source

