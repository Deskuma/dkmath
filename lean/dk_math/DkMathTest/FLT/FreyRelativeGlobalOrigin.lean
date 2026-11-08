/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyRelativeGlobalObstructionCertificate


#print "file: DkMathTest.FLT.FreyRelativeGlobalOrigin"

namespace FreyRelativeGlobalOriginTest
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : DkMath.FLT.Frey.Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)

-- Same actual point, same global Q representative, same local F cocycle.
example (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    groupCohomology.mapCocycles₁ (MonoidHom.id (inertiaSubgroupIn A ℚ)) (T.fixedCoefficientInclusion A)
      (T.continuousConnectingCocycle A hp5 hq hqp haddr hA x) =
    groupCohomology.mapCocycles₁ (inertiaSubgroupIn A ℚ).subtype (T.globalInertiaCoefficient A)
      (T.fullGlobalCocycle x) :=
  T.continuousCocycle_global_origin A hp5 hq hqp haddr hA x

example (σ : A.decompositionSubgroup ℚ) (z : T.inertiaFixedUpperQuotient A) :
    T.upperQuotientAction σ.val z.val ∈ T.inertiaFixedUpperQuotient A :=
  T.decomposition_preserves_fixed A σ z

-- Coefficient boundary model: a nonzero invariant value can be a Q-valued coboundary.
-- Multiplication by6 has order5 on ZMod25; its invariants are killed by5.
example : (6 : ZMod 25) ^ 5 = 1 := by decide
example : ∀ z : ZMod 25, 6 * z = z ↔ 5 * z = 0 := by decide
example : (6 : ZMod 25) * 1 - 1 = 5 ∧ (6 : ZMod 25) * 5 = 5 ∧ (5 : ZMod 25) ≠ 0 := by decide

-- A conjugation need not preserve a chosen subgroup without a normalizer condition.
example : let a : Equiv.Perm (Fin 3) := Equiv.swap 1 2
          let t : Equiv.Perm (Fin 3) := Equiv.swap 0 1
          a * t * a⁻¹ ≠ t ∧ a * t * a⁻¹ ≠ 1 := by decide
end
end FreyRelativeGlobalOriginTest

#print axioms DkMath.Lib.NumberTheory.ValuationInertia.mem_decomposition_of_mem_inertia
#print axioms DkMath.Lib.NumberTheory.ValuationInertia.decomposition_conj_mem_inertia
#print axioms DkMath.Lib.NumberTheory.ValuationInertia.decomposition_inv_conj_mem_inertia
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fullGlobalCoefficient
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fullGlobalCoefficientTopology
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fullGlobalCocycle
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fullGlobalCocycle_apply
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fullGlobalCocycle_continuous
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fullGlobalClass_zero
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.globalInertiaCoefficient
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.globalInertiaRestriction
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.globalCocycle_restrict
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.globalClass_restrict
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousCocycle_global_restriction
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.decomposition_preserves_fixed
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedDecompositionAction
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedDecompositionCoefficient
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedDecompositionAction_injective
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.globalTranslateTorsion
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.globalTranslate_upperClass
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.globalCocycle_conjugate
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousCocycle_decomposition_conjugate
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousCocycle_global_origin
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousClass_global_origin_square
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.relative_global_class_boundary
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_translate_continuous_nonzero
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_translate_class_boundary
