/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidualCofixedUpperClass

#print "file: DkMath.FLT.FreyResidualObstructionSign"

/-! # 同じ障害値が元の p 捩れから来る場合の符号
代表の存在は明示条件。q≡1 の枝では符号を供給し、q≡-1 の枝との関係を分ける。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ生成元評価値が元の p 捩れで表されるという、明示的な像条件。 -/
def NarrowAbsorptionObstruction.GeneratorValueFromResidual
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) : Prop :=
  ∃ x : Torsion S.rationalCurve (p ^ (n + 1 + 1)), p • x.val = 0 ∧
    (T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime
      h.ne_torsion_prime.symm A h.lies_over)
      (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime
        (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩)).val =
      (QuotientAddGroup.mk' T.upperStage) x

/-- cofixed 性の下で、同じ p 捩れ像条件は同じ障害値の全 D 固定性を与える。 -/
theorem NarrowAbsorptionObstruction.generatorValue_fixed_of_residual
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (hres : h.GeneratorValueFromResidual hp5) (σ : A.decompositionSubgroup ℚ) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    let v := T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k
    T.fixedDecompositionAction A σ v = v := by
  obtain ⟨x, hx, hv⟩ := hres
  apply Subtype.ext
  change T.upperQuotientAction σ.val _ = _
  rw [hv]
  exact T.upperClass_fixed_of_cofixed_p_torsion hcofixed x hx σ.val

/-- q≡1 の枝で、同じ p 捩れ像条件から実際の障害核元の D 固定性を得る。 -/
theorem NarrowAbsorptionObstruction.decomposition_fixed_of_residual_plus
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (hres : h.GeneratorValueFromResidual hp5) (hq1 : (q : ZMod p) = 1)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    ∀ σ, T.kernelDecompositionAction A hp5 h.prime h.ne_torsion_prime
      (Or.inr h.support) h.lies_over σ k = k := by
  apply (h.decomposition_fixed_iff_resonant_sign hp5 φ hφ).mpr
  exact Or.inl ⟨hq1, h.generatorValue_fixed_of_residual hp5 hcofixed hres φ⟩

/-- 同じ障害値は非零なので、底の残余直線の像からは生じない。 -/
theorem NarrowAbsorptionObstruction.generatorValue_not_from_base
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1)))
    (hx : x.val ∈ pointSubgroup S.rationalCurve p L) :
    (T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime
      h.ne_torsion_prime.symm A h.lies_over)
      (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime
        (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩)).val ≠
      (QuotientAddGroup.mk' T.upperStage) x := by
  intro hv
  have hz : T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime
      h.ne_torsion_prime.symm A h.lies_over)
      (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime
        (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩) = 0 := by
    apply Subtype.ext
    exact hv.trans (T.upperClass_eq_zero_of_base x hx)
  have ho := h.generatorValue_order_eq_prime hp5
  dsimp only at ho
  rw [hz, addOrderOf_zero] at ho
  omega

end
end DkMath.FLT.Frey.Source
