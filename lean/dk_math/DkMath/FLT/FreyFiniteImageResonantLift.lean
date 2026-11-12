/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteImageFixedCriterion

#print "file: DkMath.FLT.FreyFiniteImageResonantLift"

/-! # 同じ有限作用像の生成と共鳴符号から非零 D 類へ
himage と hsign は明示入力。有限性・開性だけで巡回性を結論しない。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 全 D の密度を入力とせず、同じ有限像の生成と符号から元の非零 D 類を構成する。 -/
theorem NarrowAbsorptionObstruction.decomposition_lift_of_finite_image_sign
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (himage : ∀ σ : A.decompositionSubgroup ℚ, (T.finiteDecompositionProjection A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over) σ ∈ Subgroup.zpowers ((T.finiteDecompositionProjection A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over) φ))
    (hsign : let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
      let v := T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k
      ((q : ZMod p) = 1 ∧ T.fixedDecompositionAction A φ v = v) ∨
      ((q : ZMod p) = -1 ∧ T.fixedDecompositionAction A φ v = -v)) :
    ∃ c : groupCohomology.cocycles₁ (T.fixedDecompositionCoefficient A),
      Continuous (fun σ : A.decompositionSubgroup ℚ => (c σ : T.inertiaFixedUpperQuotient A)) ∧
      T.decompositionInertiaRestriction A (groupCohomology.H1π _ c) = (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩).val ∧
      groupCohomology.H1π _ c ≠ 0 :=
  h.decomposition_lift_of_kernel_fixed hp5
    ((h.decomposition_fixed_iff_resonant_sign_of_finite_image hp5 φ hφ himage).mpr hsign)
end
end DkMath.FLT.Frey.Source
