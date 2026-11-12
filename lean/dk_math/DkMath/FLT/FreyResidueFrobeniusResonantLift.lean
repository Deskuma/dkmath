/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidueFrobeniusOpenQuotient
import DkMath.FLT.FreyOrbitResonantLift

#print "file: DkMath.FLT.FreyResidueFrobeniusResonantLift"

/-! # 実際の局所 Frobenius から同じ障害元の固定性判定へ
有限像生成と軌道条件を内部供給する。共鳴符号の算術的証明は別途必要。 -/
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

/-- 同じ K の各元に対し、軌道条件は実際の局所データから供給される。 -/
theorem ResidualCyclicStage.kernelOrbitGenerated_of_frobenius
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (k : T.fixedH1CoefficientKernel A) :
    T.KernelOrbitGenerated A hp5 hq hqp haddr hA φ k :=
  T.kernelOrbitGenerated_of_finite_image A hp5 hq hqp haddr hA φ
    (T.finiteDecomposition_generated_of_frobenius A hp5 hq hqp haddr hA φ hφ) k

/-- 同じ K の D 固定性は、実際の Frobenius 一元による固定性と同値。 -/
theorem ResidualCyclicStage.kernel_fixed_iff_frobenius
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (k : T.fixedH1CoefficientKernel A) :
    (∀ σ, T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k) ↔
      T.kernelDecompositionAction A hp5 hq hqp haddr hA φ k = k :=
  T.kernel_fixed_iff_frobenius_of_orbit A hp5 hq hqp haddr hA φ k
    (T.kernelOrbitGenerated_of_frobenius A hp5 hq hqp haddr hA φ hφ k)

variable {T} {A} {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 軌道生成を外部入力にせず、同じ障害元の D 固定性を共鳴符号で判定する。 -/
theorem NarrowAbsorptionObstruction.decomposition_fixed_iff_resonant_sign
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support)
      A h.lies_over ⟨y, h.killed⟩
    let v := T.fixedKernelEvaluation A
      (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k
    (∀ σ, T.kernelDecompositionAction A hp5 h.prime h.ne_torsion_prime
      (Or.inr h.support) h.lies_over σ k = k) ↔
      ((q : ZMod p) = 1 ∧ T.fixedDecompositionAction A φ v = v) ∨
      ((q : ZMod p) = -1 ∧ T.fixedDecompositionAction A φ v = -v) :=
  h.decomposition_fixed_iff_resonant_sign_of_orbit hp5 φ hφ
    (T.kernelOrbitGenerated_of_frobenius A hp5 h.prime h.ne_torsion_prime
      (Or.inr h.support) h.lies_over φ hφ _)

/-- 共鳴符号から、同じ連続代表を持つ非零通常 H¹(D,F) 類を構成する。 -/
theorem NarrowAbsorptionObstruction.decomposition_lift_of_resonant_sign
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
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
    ((h.decomposition_fixed_iff_resonant_sign hp5 φ hφ).mpr hsign)

end
end DkMath.FLT.Frey.Source
