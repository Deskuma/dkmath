/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCommonTameEvaluation

#print "file: DkMath.FLT.FreyCommonTameGeneratorCriterion"

/-!
# 実際の共通商の生成元から単一慣性評価へ

このモジュールは生成元の消費側。巡回性や有限段分解の存在はここでは証明しない。
条件付き補題の入力を明示し、共通商の有限性だけから巡回性を推論しない。
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

/-- 同じ H の生成元での評価は、同じ K 全体で単射。 -/
theorem ResidualCyclicStage.fixedKernelCommon_generator_evaluation_injective
    (g : T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA)
    (hg : ∀ h, h ∈ Subgroup.zpowers g) :
    Function.Injective (T.fixedKernelCommonEvaluation A hp5 hq hqp haddr hA g) := by
  intro x y he
  apply T.fixedKernelCommonTameValues_separates A hp5 hq hqp haddr hA x y
  intro h
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg h)
  change T.fixedKernelCommonCharacter A hp5 hq hqp haddr hA x (g ^ j) =
    T.fixedKernelCommonCharacter A hp5 hq hqp haddr hA y (g ^ j)
  rw [map_zpow, map_zpow]
  exact congrArg (fun v => v ^ j) (congrArg Multiplicative.ofAdd he)

/-- 巡回性が別途得られれば、実際の慣性元 γ による単一評価を構成できる。 -/
theorem ResidualCyclicStage.exists_single_evaluation_of_common_isCyclic
    (hcyclic : IsCyclic (T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA)) :
    ∃ γ : inertiaSubgroupIn A ℚ, Function.Injective (T.fixedKernelEvaluation A γ) ∧
      Nat.card (T.fixedH1CoefficientKernel A) ∣ Nat.card (T.inertiaFixedUpperQuotient A) := by
  let := hcyclic
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA)
  obtain ⟨γ, rfl⟩ := T.fixedKernelCommonProjection_surjective A hp5 hq hqp haddr hA g
  have hi := T.fixedKernelCommon_generator_evaluation_injective A hp5 hq hqp haddr hA _ hg
  change Function.Injective (T.fixedKernelEvaluation A γ) at hi
  exact ⟨γ, hi, AddSubgroup.card_dvd_of_injective (T.fixedKernelEvaluation A γ).toAddMonoidHom hi⟩

/-- 模範解答型の有限段分解が得られれば、同じ γ の像が H を生成する。 -/
theorem ResidualCyclicStage.commonProjection_generates_of_power_decomposition
    (γ : inertiaSubgroupIn A ℚ)
    (hgen : ∀ τ : inertiaSubgroupIn A ℚ, ∃ (j : ℕ) (x w : inertiaSubgroupIn A ℚ),
      τ = γ ^ j * x ^ (p ^ (n + 3)) * w ^ (p ^ (n + 3))) :
    ∀ h : T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA,
      h ∈ Subgroup.zpowers (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA γ) := by
  intro h
  obtain ⟨τ, rfl⟩ := T.fixedKernelCommonProjection_surjective A hp5 hq hqp haddr hA h
  obtain ⟨j, x, w, he⟩ := hgen τ
  have hv : T.fixedKernelCommonProjection A hp5 hq hqp haddr hA τ =
      (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA γ) ^ j := by
    rw [he, map_mul, map_mul, map_pow, map_pow, map_pow,
      T.fixedKernelCommonTame_pow_stage A hp5 hq hqp haddr hA,
      T.fixedKernelCommonTame_pow_stage A hp5 hq hqp haddr hA, mul_one, mul_one]
  exact Subgroup.mem_zpowers_iff.mpr ⟨(j : ℤ), (zpow_natCast _ j).trans hv.symm⟩

/-- 有限段分解を仮定する条件付き巡回性。分解の存在は別途必要。 -/
theorem ResidualCyclicStage.common_isCyclic_of_power_decomposition
    (γ : inertiaSubgroupIn A ℚ)
    (hgen : ∀ τ : inertiaSubgroupIn A ℚ, ∃ (j : ℕ) (x w : inertiaSubgroupIn A ℚ),
      τ = γ ^ j * x ^ (p ^ (n + 3)) * w ^ (p ^ (n + 3))) :
    IsCyclic (T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA) := by
  apply isCyclic_iff_exists_zpowers_eq_top.mpr
  refine ⟨T.fixedKernelCommonProjection A hp5 hq hqp haddr hA γ, eq_top_iff.mpr ?_⟩
  intro h _
  exact T.commonProjection_generates_of_power_decomposition A hp5 hq hqp haddr hA γ hgen h

/-- 有限段分解が得られれば、同じ γ の単一慣性評価が単射。 -/
theorem ResidualCyclicStage.single_evaluation_of_power_decomposition
    (γ : inertiaSubgroupIn A ℚ)
    (hgen : ∀ τ : inertiaSubgroupIn A ℚ, ∃ (j : ℕ) (x w : inertiaSubgroupIn A ℚ),
      τ = γ ^ j * x ^ (p ^ (n + 3)) * w ^ (p ^ (n + 3))) :
    Function.Injective (T.fixedKernelEvaluation A γ) :=
  T.fixedKernelCommon_generator_evaluation_injective A hp5 hq hqp haddr hA _
    (T.commonProjection_generates_of_power_decomposition A hp5 hq hqp haddr hA γ hgen)

end
end DkMath.FLT.Frey.Source
