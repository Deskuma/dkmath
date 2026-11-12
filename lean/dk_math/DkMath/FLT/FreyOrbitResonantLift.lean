/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyKernelOrbitCriterion
import DkMath.FLT.FreyFiniteImageResonantLift

#print "file: DkMath.FLT.FreyOrbitResonantLift"

/-! # 同じ障害元の軌道条件と共鳴符号
有限作用像全体を生成する仮定は外せるが、軌道条件と符号の算術的証明はまだ必要。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ障害元の軌道条件の下で、D 固定性は元の共鳴符号条件と同値。 -/
theorem NarrowAbsorptionObstruction.decomposition_fixed_iff_resonant_sign_of_orbit
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (horbit : T.KernelOrbitGenerated A hp5 h.prime h.ne_torsion_prime (Or.inr h.support)
      h.lies_over φ
      (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support)
        A h.lies_over ⟨y, h.killed⟩)) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support)
      A h.lies_over ⟨y, h.killed⟩
    let v := T.fixedKernelEvaluation A
      (InertiaRadical.generator (Fact.out : p.Prime) h.prime
        h.ne_torsion_prime.symm A h.lies_over) k
    (∀ σ, T.kernelDecompositionAction A hp5 h.prime h.ne_torsion_prime
      (Or.inr h.support) h.lies_over σ k = k) ↔
      ((q : ZMod p) = 1 ∧ T.fixedDecompositionAction A φ v = v) ∨
      ((q : ZMod p) = -1 ∧ T.fixedDecompositionAction A φ v = -v) := by
  have he := T.kernel_fixed_iff_eigenvalue_of_orbit A hp5 h.prime
    h.ne_torsion_prime (Or.inr h.support) h.lies_over φ hφ
    (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime
      (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩) horbit
  constructor
  · intro hD
    have hv := he.mp hD
    rcases h.resonance with hplus | hminus
    · exact Or.inl ⟨hplus, hv.trans (h.generatorValue_q_smul_plus hp5 hplus)⟩
    · exact Or.inr ⟨hminus, hv.trans (h.generatorValue_q_smul_minus hp5 hminus)⟩
  · intro hs
    apply he.mpr
    rcases hs with ⟨hplus, hv⟩ | ⟨hminus, hv⟩
    · exact hv.trans (h.generatorValue_q_smul_plus hp5 hplus).symm
    · exact hv.trans (h.generatorValue_q_smul_minus hp5 hminus).symm

/-- 軌道条件と符号から、同じ連続な非零 D コホモロジー類を得る。 -/
theorem NarrowAbsorptionObstruction.decomposition_lift_of_orbit_sign
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (horbit : T.KernelOrbitGenerated A hp5 h.prime h.ne_torsion_prime (Or.inr h.support)
      h.lies_over φ
      (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support)
        A h.lies_over ⟨y, h.killed⟩))
    (hsign : let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
      let v := T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k
      ((q : ZMod p) = 1 ∧ T.fixedDecompositionAction A φ v = v) ∨
      ((q : ZMod p) = -1 ∧ T.fixedDecompositionAction A φ v = -v)) :
    ∃ c : groupCohomology.cocycles₁ (T.fixedDecompositionCoefficient A),
      Continuous (fun σ : A.decompositionSubgroup ℚ =>
        (c σ : T.inertiaFixedUpperQuotient A)) ∧
      T.decompositionInertiaRestriction A (groupCohomology.H1π _ c) =
        (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime
          (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩).val ∧
      groupCohomology.H1π _ c ≠ 0 :=
  h.decomposition_lift_of_kernel_fixed hp5
    ((h.decomposition_fixed_iff_resonant_sign_of_orbit hp5 φ hφ horbit).mpr hsign)

end
end DkMath.FLT.Frey.Source
