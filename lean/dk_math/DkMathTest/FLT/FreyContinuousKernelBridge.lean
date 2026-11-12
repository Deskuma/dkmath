/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CyclotomicWeightTwoTarget
import DkMath.FLT.FreyContinuousObstructionCertificate


#print "file: DkMathTest.FLT.FreyContinuousKernelBridge"

namespace FreyContinuousKernelBridgeTest
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : DkMath.FLT.Frey.Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)

-- Same class and same cocycle, with actual continuity supplied internally.
example (k : T.fixedH1CoefficientKernel A) :
    ContinuousTrivialCharacterH1.forgetClass
      (T.continuousKernelCharacter A hp5 hq hqp haddr hA k) = k.val :=
  T.continuousKernelCharacter_forget A hp5 hq hqp haddr hA k

example (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    groupCohomology.H1π _ (T.continuousConnectingCocycle A hp5 hq hqp haddr hA x) =
      T.fixedConnecting A (T.fixedCosetH0 hp5 hq hqp haddr A hA x) :=
  T.continuousConnectingClass_eq_delta A hp5 hq hqp haddr hA x

-- A finite consistent model: sharp n=0 cardinalities do not themselves imply contradiction.
private def model (x : ZMod 5) : ZMod 25 := 5 * (x.val : ZMod 25)
example : ∀ x y : ZMod 5, model (x + y) = model x + model y := by decide
example : Function.Injective model := by decide
example : model 1 ≠ 0 := by decide
example : 1 + 2 = 3 ∧ 1 ≤ 2 ∧ 2 * 1 ≤ 3 := by omega

-- The B2 numerator step is checked arithmetic, separate from class-group vanishing.
example : ¬ (5 : ℤ) ∣ (bernoulli 2).num :=
  CyclotomicClassVanishing.prime_not_dvd_bernoulli_two_numerator (by decide)
end
end FreyContinuousKernelBridgeTest

#print axioms DkMath.Lib.NumberTheory.CyclotomicClassVanishing.weightTwoComponent
#print axioms DkMath.Lib.NumberTheory.CyclotomicClassVanishing.weightTwo_eq_bot_iff
#print axioms DkMath.Lib.NumberTheory.CyclotomicClassVanishing.bernoulli_two_numerator
#print axioms DkMath.Lib.NumberTheory.CyclotomicClassVanishing.prime_not_dvd_bernoulli_two_numerator
#print axioms DkMath.Lib.RepresentationTheory.ContinuousTrivialCharacterH1.cocycle
#print axioms DkMath.Lib.RepresentationTheory.ContinuousTrivialCharacterH1.cocycle_continuous
#print axioms DkMath.Lib.RepresentationTheory.ContinuousTrivialCharacterH1.forgetClass
#print axioms DkMath.Lib.RepresentationTheory.ContinuousTrivialCharacterH1.forgetClass_evaluate
#print axioms DkMath.Lib.RepresentationTheory.ContinuousTrivialCharacterH1.forgetClass_injective
#print axioms DkMath.Lib.RepresentationTheory.ContinuousTrivialCharacterH1.forgetClass_ne_zero
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelCharacter
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelCharacter_apply
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelCharacter_injective
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelCharacter_forget
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousConnectingCocycle
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousConnectingCocycle_continuous
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousConnectingCocycle_eq
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousConnectingClass_eq_delta
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelTameCharacter
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelTameCharacter_mk
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelTameCocycle_mk
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelTameClass_inflation
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousKernelTameCharacter_injective
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.cyclic_balanced_profile
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.stage_zero_card_profile
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.stage_one_card_profile
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.continuous_kernel_detected
#print axioms DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.continuous_class_nonzero
