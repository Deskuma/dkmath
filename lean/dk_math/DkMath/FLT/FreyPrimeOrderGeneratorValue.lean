/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDecompositionInvariantObstruction

#print "file: DkMath.FLT.FreyPrimeOrderGeneratorValue"

/-! # 同じ具体的生成元での実際の障害値の厳密位数 p
F 全体を p で消えると仮定せず、元の同じ障害核元の位数を輸送する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 単一評価の単射性により、同じ障害値は厳密位数 p を持つ。 -/
theorem NarrowAbsorptionObstruction.generatorValue_order_eq_prime
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    addOrderOf (T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k) = p := by
  exact (addOrderOf_injective (T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over)).toAddMonoidHom
    (T.generator_evaluation_injective A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over) _).trans
      (h.fixedKernel_order_eq_prime hp5)

/-- 同じ障害値への自然数倍は、その整数を p で還元しても同じ。 -/
theorem NarrowAbsorptionObstruction.generatorValue_nsmul_mod
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) (m : ℕ) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    let v := T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k
    m • v = (m % p) • v := by
  have he := mod_addOrderOf_nsmul
    (T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over)
      (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩)) m
  rw [h.generatorValue_order_eq_prime hp5] at he
  exact he.symm
end
end DkMath.FLT.Frey.Source

