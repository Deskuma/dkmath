import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJet

open DkMath.FLT.Seven
open DkMath.FLT.Seven.SevenRealCubic
open DkMath.FLT.Seven.SevenRealCubicInt
open scoped NumberField Pointwise

namespace DkMath.FLT.Seven.SevenRealCubic

noncomputable section

#check directOrbitPairAxisUnitOne
#check directOrbit_rotate_axis_pow
#check directOrbit_rotate_twice_axis_pow
#check directOrbitSquareTwistCoeff0
#check directOrbit_squareTwist_coeff0_norm_eq_one
#check thetaSevenUnit_isUnit
#check seven_eq_eisensteinAxis_cube_mul_unit
#check theta_coordinate_decomposition
#check thetaLinear_pow_seven
#check thetaSquare_pow_seven
#check thetaLinear_pow_seven_mod49_neutral
#check thetaSquare_pow_seven_mod49_neutral
#check projectiveLog_pow_seven
#check unit_isSeventhPower_iff_projectiveLog_eq_zero
#check ZMod.intCast_zmod_eq_zero_iff_dvd

def r40ScratchCyclicTrace (x : SevenRealCubicInt) : SevenRealCubicInt :=
  x + rotateEquiv x + rotateEquiv (rotateEquiv x)

-- The coordinate expansion and ring normalization require the larger budget.
theorem r40_trace_coordinate_formula_scratch (A B C : ℤ) :
    r40ScratchCyclicTrace
        (eisensteinAxis ^ 2 * ofThetaCoordinates A B C) =
      ofInt (7 * (3 * A - 10 * B + 35 * C)) := by
  have h2 : eisensteinAxis ^ 2 = (⟨9, -6, 1⟩ : SevenRealCubicInt) := by
    exact eisensteinAxis_sq_coordinates
  rw [h2]
  apply SevenRealCubicInt.ext <;>
    norm_num [r40ScratchCyclicTrace, ofThetaCoordinates,
      ofInt, eisensteinAxis, rotateEquiv, rotateHom, SevenRealCubicInt.mul,
      pow_two, pow_succ] <;>
    ring

private theorem r40_dvd_seven_of_zmod_seven_zero (m : ℤ)
    (hm : (m : ZMod 7) = 0) : (7 : ℤ) ∣ m := by
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd m 7).mp hm

theorem r40_thetaLinear_pow_seven_mod49_scratch (A B C : ℤ) :
    (49 : ℤ) ∣
      thetaLinearInt ((ofThetaCoordinates A B C) ^ 7) -
        7 * B * A ^ 6 := by
  have hB : (7 : ℤ) ∣ seventhThetaLinearBFactor A B C - A ^ 6 := by
    apply r40_dvd_seven_of_zmod_seven_zero
    push_cast
    rw [seventhThetaLinearBFactor_modSeven]
    ring
  rcases hB with ⟨qB, hqB⟩
  refine ⟨B * qB + C ^ 2 * seventhThetaLinearCFactor A C, ?_⟩
  rw [thetaLinear_pow_seven]
  simp only [seventhThetaLinearQuotient]
  linear_combination 7 * B * hqB

theorem r40_thetaSquare_pow_seven_mod49_scratch (A B C : ℤ) :
    (49 : ℤ) ∣
      thetaSquareInt ((ofThetaCoordinates A B C) ^ 7) -
        7 * (C * A ^ 6 + 3 * B ^ 2 * A ^ 5) := by
  have hC : (7 : ℤ) ∣ seventhThetaSquareCFactor A B C - A ^ 6 := by
    apply r40_dvd_seven_of_zmod_seven_zero
    push_cast
    rw [seventhThetaSquareCFactor_modSeven]
    ring
  have hB : (7 : ℤ) ∣ seventhThetaSquareBFactor A B - 3 * A ^ 5 := by
    apply r40_dvd_seven_of_zmod_seven_zero
    push_cast
    rw [seventhThetaSquareBFactor_modSeven]
    ring
  rcases hC with ⟨qC, hqC⟩
  rcases hB with ⟨qB, hqB⟩
  refine ⟨C * qC + B ^ 2 * qB, ?_⟩
  rw [thetaSquare_pow_seven]
  simp only [seventhThetaSquareQuotient]
  linear_combination 7 * C * hqC + 7 * B ^ 2 * hqB

example (A B C : ℤ) :
    (49 : ℤ) ∣
      thetaLinearInt ((ofThetaCoordinates A B C) ^ 7) -
        7 * B * A ^ 6 :=
  thetaLinear_pow_seven_mod49_neutral A B C

example (A B C : ℤ) :
    (49 : ℤ) ∣
      thetaSquareInt ((ofThetaCoordinates A B C) ^ 7) -
        7 * (C * A ^ 6 + 3 * B ^ 2 * A ^ 5) :=
  thetaSquare_pow_seven_mod49_neutral A B C

end
end DkMath.FLT.Seven.SevenRealCubic
