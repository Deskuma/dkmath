/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFrobeniusLiftIndependence

#print "file: DkMath.FLT.FreyDenseResonantFixed"

/-! # 密度と同じ γ の値から hD を供給する正確な同値条件
密度・固有値の算術的証明はここでは与えない。 -/
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

/-- 密度の下で、元の任意の核元の全 D 固定性を同じ γ の固有値で判定する。 -/
theorem ResidualCyclicStage.decomposition_fixed_iff_eigenvalue_of_dense
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (k : T.fixedH1CoefficientKernel A)
    (hdense : (A.inertiaSubgroup ℚ ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤) :
    (∀ σ, T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k) ↔
      T.fixedDecompositionAction A φ
        (T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA) k) =
      q • T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA) k :=
  (T.kernel_fixed_iff_of_dense_join A hp5 hq hqp haddr hA φ k hdense).trans
    (T.kernelFrobenius_fixed_iff A hp5 hq hqp haddr hA φ hφ k)
end
end DkMath.FLT.Frey.Source
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 明示した密度の下で、共鳴二分岐の正しい符号は同じ障害核元の hD と同値。 -/
theorem NarrowAbsorptionObstruction.decomposition_fixed_iff_resonant_sign_of_dense
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (hdense : (A.inertiaSubgroup ℚ ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    let v := T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k
    (∀ σ, T.kernelDecompositionAction A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over σ k = k) ↔
      ((q : ZMod p) = 1 ∧ T.fixedDecompositionAction A φ v = v) ∨
      ((q : ZMod p) = -1 ∧ T.fixedDecompositionAction A φ v = -v) := by
  have he := T.decomposition_fixed_iff_eigenvalue_of_dense A hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) h.lies_over φ hφ (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩) hdense
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
end
end DkMath.FLT.Frey.Source
