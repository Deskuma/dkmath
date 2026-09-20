import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJet

namespace DkMathTest.FLT.SevenTracePlaneBinaryCubicR46Scratch

open DkMath.FLT.Seven
open DkMath.FLT.Seven.SevenRealCubic
open DkMath.FLT.Seven.SevenRealCubicInt

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! R46 scratch: exact integer trace-plane coordinates and the norm cubic. -/

theorem trace_plane_parameterization
    {A B C : ℤ} (h : 3 * A - 10 * B + 35 * C = 0) :
    ∃ r s : ℤ,
      A = 5 * (r + s) ∧ B = 5 * r - 2 * s ∧ C = r - s := by
  have hr : (3 : ℤ) ∣ B - 2 * C := by
    refine ⟨A - 3 * B + 11 * C, ?_⟩
    linarith
  have hs : (3 : ℤ) ∣ B - 5 * C := by
    refine ⟨A - 3 * B + 10 * C, ?_⟩
    linarith
  rcases hr with ⟨r, hr⟩
  rcases hs with ⟨s, hs⟩
  refine ⟨r, s, ?_, ?_, ?_⟩ <;> linarith

theorem trace_plane_parameterization_converse (r s : ℤ) :
    3 * (5 * (r + s)) - 10 * (5 * r - 2 * s) + 35 * (r - s) = 0 := by
  ring

theorem norm_trace_plane_parameterized (r s : ℤ) :
    SevenRealCubicInt.norm
        (ofThetaCoordinates (5 * (r + s)) (5 * r - 2 * s) (r - s)) =
      -(r ^ 3 - 4 * r ^ 2 * s - 11 * r * s ^ 2 + 43 * s ^ 3) := by
  norm_num [SevenRealCubicInt.norm, ofThetaCoordinates,
    eisensteinAxis_sq_coordinates,
    eisensteinAxis, ofInt, mul, pow_two, pow_succ]
  ring

theorem rho_trace_plane_pair :
    (-20 : ℤ) = 5 * (-3 + -1) ∧
      (-13 : ℤ) = 5 * (-3) - 2 * (-1) ∧
      (-2 : ℤ) = (-3) - (-1) := by
  norm_num

theorem rho_binary_cubic_value :
    (-3 : ℤ) ^ 3 - 4 * (-3 : ℤ) ^ 2 * (-1 : ℤ) -
        11 * (-3 : ℤ) * (-1 : ℤ) ^ 2 + 43 * (-1 : ℤ) ^ 3 = -1 := by
  norm_num

theorem rho_binary_cubic_norm_value :
    -((-3 : ℤ) ^ 3 - 4 * (-3 : ℤ) ^ 2 * (-1 : ℤ) -
        11 * (-3 : ℤ) * (-1 : ℤ) ^ 2 + 43 * (-1 : ℤ) ^ 3) = 1 := by
  norm_num

theorem projective_trace_plane_congruence
    (u : SevenRealCubicIntˣ) (r s : ℤ)
    (hcoord : (u : SevenRealCubicInt) =
      ofThetaCoordinates (5 * (r + s)) (5 * r - 2 * s) (r - s))
    (hlog : projectiveLog (Additive.ofMul u) = (1, 1)) :
    (r : ZMod 7) = 3 * (s : ZMod 7) := by
  have hA : thetaConstModSeven (u : SevenRealCubicInt) ≠ 0 :=
    thetaConstModSeven_unit_ne_zero u
  have hfirst := congrArg Prod.fst hlog
  have hsecond := congrArg Prod.snd hlog
  rw [projectiveLog_apply] at hfirst hsecond
  change thetaLinearModSeven (u : SevenRealCubicInt) /
      thetaConstModSeven (u : SevenRealCubicInt) = 1 at hfirst
  change thetaSquareModSeven (u : SevenRealCubicInt) /
      thetaConstModSeven (u : SevenRealCubicInt) -
        (thetaLinearModSeven (u : SevenRealCubicInt) /
          thetaConstModSeven (u : SevenRealCubicInt)) ^ 2 /
            (2 : ZMod 7) = 1 at hsecond
  have hconst :
      thetaConstModSeven
          (ofThetaCoordinates (5 * (r + s)) (5 * r - 2 * s) (r - s)) =
        (5 * (r + s) : ZMod 7) := by
    norm_num [thetaConstModSeven, ofThetaCoordinates, ofInt,
      eisensteinAxis_sq_coordinates, eisensteinAxis,
      SevenRealCubicInt.mul, pow_two, pow_succ]
    ring
  have hlinear :
      thetaLinearModSeven
          (ofThetaCoordinates (5 * (r + s)) (5 * r - 2 * s) (r - s)) =
        (5 * r - 2 * s : ZMod 7) := by
    norm_num [thetaLinearModSeven, ofThetaCoordinates, ofInt,
      eisensteinAxis_sq_coordinates, eisensteinAxis,
      SevenRealCubicInt.mul, pow_two, pow_succ]
    ring
  have hsquare :
      thetaSquareModSeven
          (ofThetaCoordinates (5 * (r + s)) (5 * r - 2 * s) (r - s)) =
        (r - s : ZMod 7) := by
    norm_num [thetaSquareModSeven, ofThetaCoordinates, ofInt,
      eisensteinAxis_sq_coordinates, eisensteinAxis,
      SevenRealCubicInt.mul, pow_two, pow_succ]
  rw [hcoord, hconst, hlinear] at hfirst
  rw [hcoord, hconst, hlinear, hsquare] at hsecond
  rw [hcoord, hconst] at hA
  have hfirst' :
      (5 * (r : ZMod 7) - 2 * (s : ZMod 7)) =
        5 * ((r : ZMod 7) + (s : ZMod 7)) := by
    simpa using (div_eq_iff hA).mp hfirst
  rw [hfirst'] at hsecond
  rw [div_self hA] at hsecond
  norm_num at hsecond
  have hhalf : (2 : ZMod 7)⁻¹ = 4 := by
    exact ZMod.inv_eq_of_mul_eq_one 7 2 4 (by
      change ((8 : ℕ) : ZMod 7) = ((1 : ℕ) : ZMod 7)
      rw [ZMod.natCast_eq_natCast_iff]
      decide)
  rw [hhalf] at hsecond
  have hsecond' :
      (r : ZMod 7) - (s : ZMod 7) =
        5 * (5 * ((r : ZMod 7) + (s : ZMod 7))) := by
    have hratio :
        ((r : ZMod 7) - (s : ZMod 7)) /
            (5 * ((r : ZMod 7) + (s : ZMod 7))) = 5 := by
      calc
        _ = (((r : ZMod 7) - (s : ZMod 7)) /
            (5 * ((r : ZMod 7) + (s : ZMod 7))) - 4) + 4 := by ring
        _ = 1 + 4 := by rw [hsecond]
        _ = 5 := by norm_num
    have hcross := (div_eq_iff hA).mp hratio
    simpa using hcross
  ring_nf at hsecond' ⊢
  have hseven : (7 : ZMod 7) = 0 := by decide
  linear_combination 2 * hsecond' + (7 * (r : ZMod 7) + 7 * (s : ZMod 7)) * hseven

theorem rho_projective_trace_plane_congruence :
    ((-3 : ℤ) : ZMod 7) = 3 * ((-1 : ℤ) : ZMod 7) := by
  apply projective_trace_plane_congruence
    (u := directOrbitDeepJetRho) (r := -3) (s := -1)
  · exact directOrbitDeepJetRho_val
  · exact directOrbitDeepJetRho_projectiveLog

end DkMathTest.FLT.SevenTracePlaneBinaryCubicR46Scratch
