/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyRadicalKernelComparison
import DkMath.Lib.NumberTheory.InertiaTailGaloisRoots

#print "file: DkMath.FLT.FreyTailKernelVanishing"

/-!
# 全根固定 tail の Frey 共通商における消滅

体内根 → 有限商の p 因子排除 → 群内根という証明済みの経路を消費する。
元の共通商の一様指数で tail を消す。有限一段だけを固定する補正元はまだ対象外。
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

/-- 元の全 q 根を固定する慣性元は、同じ実際の Frey 共通商で消える。 -/
theorem ResidualCyclicStage.allRadicals_commonProjection_eq_one (σ : inertiaSubgroupIn A ℚ)
    (hr : ∀ (α : AlgebraicClosure ℚ) (k : ℕ), α ^ (p ^ k) = (q : AlgebraicClosure ℚ) → σ.val α = α) :
    T.fixedKernelCommonProjection A hp5 hq hqp haddr hA σ = 1 :=
  InertiaResidue.allRadicals_map_eq_one (Fact.out : p.Prime) hq hqp.symm A hA
    (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA) (n + 3)
    (T.fixedKernelCommonTame_pow_stage A hp5 hq hqp haddr hA) σ hr

/-- 全根固定 tail は、元の全係数核の評価で零となる。 -/
theorem ResidualCyclicStage.allRadicals_evaluations_eq_zero (σ : inertiaSubgroupIn A ℚ)
    (hr : ∀ (α : AlgebraicClosure ℚ) (k : ℕ), α ^ (p ^ k) = (q : AlgebraicClosure ℚ) → σ.val α = α)
    (k : T.fixedH1CoefficientKernel A) : T.fixedKernelEvaluation A σ k = 0 :=
  (T.mem_commonProjection_kernel_iff_evaluations A hp5 hq hqp haddr hA σ).mp
    (T.allRadicals_commonProjection_eq_one A hp5 hq hqp haddr hA σ hr) k

/-- 同じ tail による元の全有限捩れ点の固定差分も消える。 -/
theorem ResidualCyclicStage.allRadicals_fixed_differences_eq_one (σ : inertiaSubgroupIn A ℚ)
    (hr : ∀ (α : AlgebraicClosure ℚ) (k : ℕ), α ^ (p ^ k) = (q : AlgebraicClosure ℚ) → σ.val α = α)
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x σ = 1 :=
  (T.mem_commonProjection_kernel_iff_fixed_differences A hp5 hq hqp haddr hA σ).mp
    (T.allRadicals_commonProjection_eq_one A hp5 hq hqp haddr hA σ hr) x

/-- 全根固定体の核に対する実際の包含。有限段の根指標の核包含とは区別する。 -/
theorem ResidualCyclicStage.tailFixing_le_commonProjection_kernel :
    (InertiaResidue.tailField A p q).fixingSubgroup.subgroupOf (inertiaSubgroupIn A ℚ) ≤
      (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA).ker := by
  intro σ hσ
  exact T.allRadicals_commonProjection_eq_one A hp5 hq hqp haddr hA σ
    ((InertiaResidue.mem_tailFixing_iff_all_radicals A σ).mp hσ)
end
end DkMath.FLT.Frey.Source
