/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidualObstructionSign
import DkMath.Lib.Algebra.PrimeOrderSignSeparation

#print "file: DkMath.FLT.FreyResidualObstructionMinusBranch"

/-! # 残余 p 捩れ像に入る障害値と負の共鳴枝
同じ値が p 捩れ像に入るという条件の下で、負の符号枝では D 固定性が成立しない。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open DkMath.Lib.Algebra.PrimeOrderSignSeparation
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ障害値が残余 p 捩れから来れば、その固定作用は符号反転と異なる。 -/
theorem NarrowAbsorptionObstruction.generatorValue_not_neg_of_residual
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (hres : h.GeneratorValueFromResidual hp5) (φ : A.decompositionSubgroup ℚ) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    let v := T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k
    T.fixedDecompositionAction A φ v ≠ -v := by
  have ho := h.generatorValue_order_eq_prime hp5
  dsimp only at ho
  apply fixed_ne_neg_of_order_gt_two _ _ (by rw [ho]; omega)
  exact h.generatorValue_fixed_of_residual hp5 hcofixed hres φ

/-- 負の共鳴枝では、同じ p 捩れ像条件は障害核元の D 固定性を排除する。 -/
theorem NarrowAbsorptionObstruction.not_decomposition_fixed_of_residual_minus
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (hres : h.GeneratorValueFromResidual hp5) (hqneg : (q : ZMod p) = -1)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    ¬ ∀ σ, T.kernelDecompositionAction A hp5 h.prime h.ne_torsion_prime
      (Or.inr h.support) h.lies_over σ k = k := by
  dsimp only
  intro hD
  have he := (h.frobenius_fixed_criterion hp5 φ hφ).mp (hD φ)
  rw [h.generatorValue_q_smul_minus hp5 hqneg] at he
  exact h.generatorValue_not_neg_of_residual hp5 hcofixed hres φ he

end
end DkMath.FLT.Frey.Source
