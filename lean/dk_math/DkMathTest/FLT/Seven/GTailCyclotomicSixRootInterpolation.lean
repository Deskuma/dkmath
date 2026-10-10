/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailCyclotomicSixRootInterpolation

#print "file: DkMathTest.FLT.Seven.GTailCyclotomicSixRootInterpolation"

namespace DkMathTest.FLT.Seven.GTailCyclotomicSixRootInterpolation

open DkMath.FLT.Seven DkMath.Lib.NumberTheory DkMath.CosmicFormula
open SevenCyclotomicDegreeSixInt
local instance : Fact (Nat.Prime 43) := ⟨by decide⟩
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩
local notation "K" => sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide)
local notation "Z" => (⟨⟨-2, 3, -4⟩, ⟨5, -6, 7⟩⟩ : SevenCyclotomicDegreeSixInt.Ring)
local notation "W" => (⟨⟨-43, 0, 0⟩, ⟨86, 0, 0⟩⟩ : SevenCyclotomicDegreeSixInt.Ring)

-- Both matrix candidates are verified as inverse coordinate maps, without determinants.
example (v : Fin 6 → ℤ) : sixPowerCoordinates (sixPowerCoefficients v) = v :=
  sixPowerCoordinates_coefficients v
example (v : Fin 6 → ZMod 43) : sixPowerCoefficients (sixPowerCoordinates v) = v :=
  sixPowerCoefficients_coordinates v
example : coordinates Z = ![-2, 3, -4, 5, -6, 7] := by decide
example : sixPowerCoefficients (coordinates Z) = ![-5, 13, 2, 5, -2, -6] := by decide
example (j : Fin 6) : ((sixPowerCoefficients (coordinates Z) j : ℤ) : ZMod 43) =
    sixPowerCoefficients (fun i => (coordinates Z i : ZMod 43)) j :=
  sixPowerCoefficients_intCast _ _ j
example : ∀ i : Fin 6,
    evalCyclotomicFromSeventhRoot (sixSlotRoot (11 : ZMod 43) i)
        (sixSlotRoot_ne_zero _ (by decide) i) (sixSlotRoot_pow_seven _ (by decide) i)
        (sixSlotRoot_ne_one _ (by decide) (by decide) i) Z =
      (sixPowerPolynomial 43 Z).eval (sixSlotRoot (11 : ZMod 43) i) := fun _i =>
  evalCyclotomic_eq_sixPowerPolynomial _ _ _ _ Z
example : ∀ i : Fin 6, (sixPowerPolynomial 43 Z).eval (sixSlotRoot (11 : ZMod 43) i) =
    ![17, 29, 11, 18, 34, 21] i := by
  have hv : ∀ i : Fin 6, (-5 : ZMod 43) + 13 * sixSlotRoot (11 : ZMod 43) i +
      2 * sixSlotRoot (11 : ZMod 43) i ^ 2 + 5 * sixSlotRoot (11 : ZMod 43) i ^ 3 +
      (-2) * sixSlotRoot (11 : ZMod 43) i ^ 4 + (-6) * sixSlotRoot (11 : ZMod 43) i ^ 5 =
        ![17, 29, 11, 18, 34, 21] i := by decide
  simpa [sixPowerPolynomial, Fin.sum_univ_succ, Polynomial.eval_monomial,
    sixPowerCoefficients, coordinates, add_assoc] using hv
example (z : SevenCyclotomicDegreeSixInt.Ring) :
    (∀ i : Fin 6, z ∈ K i) ↔ ∀ j : Fin 6, (43 : ℤ) ∣ coordinates z j := by
  rw [mem_all_sixRootKernel_iff_coordinates_zero]
  simp only [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_ofNat]

example : (⨅ i : Fin 6, K i) = cyclotomicScalarIdeal 43 :=
  iInf_sixRootKernel_eq_scalarIdeal _ _ _ _
example : (∏ i : Fin 6, K i) = cyclotomicScalarIdeal 43 :=
  prod_sixRootKernel_eq_scalarIdeal _ _ _ _
example : (43 : SevenCyclotomicDegreeSixInt.Ring) ∈ cyclotomicScalarIdeal 43 := by
  rw [cyclotomicScalarIdeal, Ideal.mem_span_singleton]
  exact dvd_refl _
example : ∀ i : Fin 6, (43 : SevenCyclotomicDegreeSixInt.Ring) ∈ K i := by
  apply Ideal.mem_iInf.mp
  rw [iInf_sixRootKernel_eq_scalarIdeal]
  rw [cyclotomicScalarIdeal, Ideal.mem_span_singleton]
  exact dvd_refl _
example : W = ofReal ((-43 : ℤ) : SevenRealCubicInt) +
    zeta * ofReal ((86 : ℤ) : SevenRealCubicInt) := by
  have h43 : ((-43 : ℤ) : SevenRealCubicInt) = ⟨-43, 0, 0⟩ := rfl
  have h86 : ((86 : ℤ) : SevenRealCubicInt) = ⟨86, 0, 0⟩ := rfl
  rw [h43, h86]
  ext <;> norm_num [ofReal, zeta]
example : ∀ j : Fin 6, (43 : ℤ) ∣ coordinates W j := by decide
example : W ∈ cyclotomicScalarIdeal 43 := (mem_cyclotomicScalarIdeal_iff _ _).mpr (by decide)
example : ∀ i : Fin 6, W ∈ K i := by
  rw [mem_all_sixRootKernel_iff_coordinates_zero]
  decide

private theorem ratio11 : gtailSevenTailRatio 43 9 4 = 11 := by
  dsimp [gtailSevenTailRatio]
  apply (div_eq_iff (by decide : (9 : ZMod 43) ≠ 0)).mpr
  decide
private theorem selective43 (i : Fin 6) : gtailCyclotomicLinearFactor 9 4 ∈ K i ↔ i = 0 := by
  have h := gtailCyclotomicLinearFactor_mem_sixRootKernel_iff
    (q := 43) 9 4 (by decide) (by decide) (by decide) i
  simpa only [ratio11] using h
example : ∀ i : Fin 6, gtailCyclotomicLinearFactor 9 4 ∈ K i ↔ i = 0 := selective43
example : gtailCyclotomicLinearFactor 9 4 ∉ (⨅ i : Fin 6, K i) := by
  intro h
  have h1 := Ideal.mem_iInf.mp h (1 : Fin 6)
  exact (by decide : (1 : Fin 6) ≠ 0) ((selective43 1).mp h1)
example : gtailCyclotomicLinearFactor 9 4 ∉ cyclotomicScalarIdeal 43 := by
  rw [← iInf_sixRootKernel_eq_scalarIdeal (11 : ZMod 43) (by decide) (by decide) (by decide)]
  intro h
  exact (by decide : (1 : Fin 6) ≠ 0) ((selective43 1).mp (Ideal.mem_iInf.mp h 1))
example : gtailCyclotomicLinearFactor 9 4 ∉ (∏ i : Fin 6, K i) := by
  rw [prod_sixRootKernel_eq_scalarIdeal, ← iInf_sixRootKernel_eq_scalarIdeal
    (11 : ZMod 43) (by decide) (by decide) (by decide)]
  intro h
  exact (by decide : (1 : Fin 6) ≠ 0) ((selective43 1).mp (Ideal.mem_iInf.mp h 1))
example : (13 : ℕ) ∣ 13 ∧ ¬ (13 : ℕ) ∣ GTail 7 1 13 30 := by decide
example : gtailSevenTailRatio 13 30 13 = 1 := by
  dsimp [gtailSevenTailRatio]
  apply (div_eq_iff (by decide : (30 : ZMod 13) ≠ 0)).mpr
  decide
example : ¬ ∃ r : ZMod 7, r ^ 7 = 1 ∧ r ≠ 1 := by decide
example : ¬ Fermat7Equation 5 8 9 := by
  unfold Fermat7Equation
  decide

#print axioms DkMath.FLT.Seven.sixPowerCoefficients
#print axioms DkMath.FLT.Seven.sixPowerCoordinates
#print axioms DkMath.FLT.Seven.sixPowerCoordinates_coefficients
#print axioms DkMath.FLT.Seven.sixPowerCoefficients_coordinates
#print axioms DkMath.FLT.Seven.sixPowerCoefficients_intCast
#print axioms DkMath.FLT.Seven.sixPowerPolynomial
#print axioms DkMath.FLT.Seven.sixPowerPolynomial_coeff
#print axioms DkMath.FLT.Seven.sixPowerPolynomial_natDegree_le
#print axioms DkMath.FLT.Seven.evalCyclotomic_eq_sixPowerPolynomial
#print axioms DkMath.FLT.Seven.mem_all_sixRootKernel_iff_coordinates_zero
#print axioms DkMath.FLT.Seven.cyclotomicScalarIdeal
#print axioms DkMath.FLT.Seven.coordinates_natCast_mul
#print axioms DkMath.FLT.Seven.mem_cyclotomicScalarIdeal_iff
#print axioms DkMath.FLT.Seven.iInf_sixRootKernel_eq_scalarIdeal
#print axioms DkMath.FLT.Seven.prod_sixRootKernel_eq_scalarIdeal

end DkMathTest.FLT.Seven.GTailCyclotomicSixRootInterpolation
