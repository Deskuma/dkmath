/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailCyclotomicLocalEval
import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicRamifiedPrime

#print "file: DkMathTest.FLT.Seven.GTailCyclotomicLocalEval"

namespace DkMathTest.FLT.Seven.GTailCyclotomicLocalEval

open DkMath.FLT.Seven DkMath.Lib.NumberTheory
local instance : Fact (Nat.Prime 43) := ⟨by decide⟩

private theorem beta11 : seventhRootBeta (11 : ZMod 43) = 16 := by
  have hi : (11 : ZMod 43)⁻¹ = 4 := by
    apply inv_eq_of_mul_eq_one_right
    decide
  rw [seventhRootBeta, hi]
  decide

local notation "E" => evalRealFromSeventhRoot (11 : ZMod 43)
  (by decide) (by decide) (by decide)

example : E SevenRealCubicInt.alpha = 16 := by
  rw [evalRealFromSeventhRoot_alpha, beta11]
example : E ((-9 : ℤ) : SevenRealCubicInt) = -9 := map_intCast E _
example : E (⟨-2, 3, -4⟩ : SevenRealCubicInt) =
    (-2 : ZMod 43) + 3 * 16 - 4 * 16 ^ 2 := by
  change (-2 : ZMod 43) + 3 * seventhRootBeta (11 : ZMod 43) +
    -4 * seventhRootBeta (11 : ZMod 43) ^ 2 = _
  rw [beta11]
  ring
example (x y : SevenRealCubicInt) : E (x * y) = E x * E y := map_mul E x y

open SevenCyclotomicDegreeSixInt
local notation "C" => evalCyclotomicFromSeventhRoot (11 : ZMod 43)
  (by decide) (by decide) (by decide)

example : C zeta = 11 := evalCyclotomicFromSeventhRoot_zeta _ _ _ _
example : C (ofReal SevenRealCubicInt.alpha) = 16 := by
  rw [evalCyclotomicFromSeventhRoot_alpha, beta11]
example (x : SevenRealCubicInt) : C (ofReal x) = E x :=
  evalCyclotomicFromSeventhRoot_ofReal _ _ _ _ x
example (x y : SevenCyclotomicDegreeSixInt.Ring) : C (x * y) = C x * C y := map_mul C x y

-- Actual Tail instance: no Fermat premise and no signed-depth packet.
open DkMath.CosmicFormula
local notation "T" => gtailCyclotomicEval (q := 43) 9 4
  (by decide) (by decide) (by decide)

example : (43 : ℕ) ∣ 5 ^ 2 + 5 * 8 + 8 ^ 2 ∧ 43 ∣ GTail 7 1 4 9 := by decide
example : ¬ Fermat7Equation 5 8 9 := by
  unfold Fermat7Equation
  decide
example : gtailSevenResidueRoot 43 5 8 = 37 := by
  dsimp [gtailSevenResidueRoot]
  apply (div_eq_iff (by decide : (8 : ZMod 43) ≠ 0)).mpr
  decide
private theorem tail11 : gtailSevenTailRatio 43 9 4 = 11 := by
  dsimp [gtailSevenTailRatio]
  apply (div_eq_iff (by decide : (9 : ZMod 43) ≠ 0)).mpr
  decide
example : T zeta = 11 := by
  rw [gtailCyclotomicEval, evalCyclotomicFromSeventhRoot_zeta, tail11]
example : T (gtailCyclotomicLinearFactor 9 4) = 0 :=
  gtailCyclotomicEval_linearFactor _ _ _ _ _
example : gtailCyclotomicLinearFactor 9 4 ∈ RingHom.ker T :=
  gtailCyclotomicLinearFactor_mem_ker _ _ _ _ _
example : T (ofReal (13 : SevenRealCubicInt) - zeta * ofReal (9 : SevenRealCubicInt)) = 0 :=
  gtailCyclotomicEval_linearFactor _ _ _ _ _
example : C (ofReal (13 : SevenRealCubicInt) - zeta * ofReal (9 : SevenRealCubicInt)) =
    (13 : ZMod 43) - 11 * 9 := by
  have h13 : E (13 : SevenRealCubicInt) = (13 : ZMod 43) := map_natCast E 13
  have h9 : E (9 : SevenRealCubicInt) = (9 : ZMod 43) := map_natCast E 9
  simp only [map_sub, map_mul, evalCyclotomicFromSeventhRoot_zeta,
    evalCyclotomicFromSeventhRoot_ofReal]
  rw [h13, h9]
example : (13 : ZMod 43) - 11 * 9 = 0 := by decide
example : eisensteinResidueRingHom (gtailSevenResidueRoot 43 5 8)
    (gtailSevenResidueRoot_polynomial (by decide) (by decide)) (gtailSevenNormCoord 5 8) = 0 :=
  gtailSevenNormCoord_mem_residueIdeal (by decide) (by decide)

-- Missing-premise and separate degree-two controls.
example : (13 : ℕ) ∣ 14 ^ 2 + 14 * 29 + 29 ^ 2 ∧
    (13 : ℕ) ∣ 13 ∧ ¬ (13 : ℕ) ∣ GTail 7 1 13 30 := by decide
example : (2 : ZMod 3) ^ 2 - 2 + 1 = 0 ∧ (2 : ZMod 3) = 1 - 2 := by decide
example : ¬ ∃ t : ZMod 5, t ^ 2 - t + 1 = 0 := by decide
example : SevenCyclotomicDegreeSixInt.ramifiedEval zeta = (1 : ZMod 7) :=
  SevenCyclotomicDegreeSixInt.ramifiedEval_zeta

#print axioms DkMath.FLT.Seven.gtailCyclotomicLinearFactor
#print axioms DkMath.FLT.Seven.gtailCyclotomicEval
#print axioms DkMath.FLT.Seven.gtailCyclotomicEval_linearFactor
#print axioms DkMath.FLT.Seven.gtailCyclotomicLinearFactor_mem_ker
#print axioms DkMath.FLT.Seven.evalCyclotomicFromSeventhRoot
#print axioms DkMath.FLT.Seven.evalCyclotomicFromSeventhRoot_zeta
#print axioms DkMath.FLT.Seven.evalCyclotomicFromSeventhRoot_ofReal
#print axioms DkMath.FLT.Seven.evalCyclotomicFromSeventhRoot_alpha
#print axioms DkMath.FLT.Seven.evalRealFromSeventhRoot
#print axioms DkMath.FLT.Seven.evalRealFromSeventhRoot_alpha
#print axioms DkMath.FLT.Seven.evalRealFromSeventhRoot_intCast

end DkMathTest.FLT.Seven.GTailCyclotomicLocalEval
