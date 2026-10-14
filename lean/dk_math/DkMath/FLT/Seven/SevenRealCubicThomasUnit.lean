/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicHighDepthFive
import DkMath.FLT.Seven.SevenRealCubicThetaSeventhPowerDepth

#print "file: DkMath.FLT.Seven.SevenRealCubicThomasUnit"

namespace DkMath.FLT.Seven

open SevenRealCubicInt

noncomputable section

namespace SevenRealCubic

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

private theorem inv_eleven_zmod_seven : (11 : ZMod 7)⁻¹ = 2 := by
  exact ZMod.inv_eq_of_mul_eq_one 7 11 2 (by
    change ((22 : ℕ) : ZMod 7) = ((1 : ℕ) : ZMod 7)
    rw [ZMod.natCast_eq_natCast_iff]
    decide)

private theorem inv_four_zmod_seven_thomas : (4 : ZMod 7)⁻¹ = 2 := by
  exact ZMod.inv_eq_of_mul_eq_one 7 4 2 (by
    change ((8 : ℕ) : ZMod 7) = ((1 : ℕ) : ZMod 7)
    rw [ZMod.natCast_eq_natCast_iff]
    decide)

/-! ## Part A: the Thomas root in the integral cubic order -/

/-- The root of the Thomas `n = 6` cubic form inside the real cubic order. -/
def thomasLambda : SevenRealCubicInt := alpha ^ 2 + alpha - 1

theorem thomasLambda_eq_coordinates :
    thomasLambda = ⟨-1, 1, 1⟩ := by
  ext <;> norm_num [thomasLambda, alpha, mul, pow_two]

theorem thomasLambda_cubic_relation :
    thomasLambda ^ 3 - 5 * thomasLambda ^ 2 -
      8 * thomasLambda - 1 = 0 := by
  rw [thomasLambda_eq_coordinates]
  change
    (⟨-1, 1, 1⟩ : SevenRealCubicInt) ^ 3 -
        ofInt 5 * (⟨-1, 1, 1⟩ : SevenRealCubicInt) ^ 2 -
        ofInt 8 * (⟨-1, 1, 1⟩ : SevenRealCubicInt) - ofInt 1 = 0
  ext <;> norm_num [mul, pow_succ, ofInt]

theorem thomasLambda_norm :
    norm thomasLambda = 1 := by
  rw [thomasLambda_eq_coordinates]
  norm_num [SevenRealCubicInt.norm]

private theorem thomas_isUnit_of_norm_one
    {x : SevenRealCubicInt} (hx : norm x = 1) : IsUnit x := by
  apply IsUnit.of_mul_eq_one
    (rotateEquiv x * rotateEquiv (rotateEquiv x))
  calc
    x * (rotateEquiv x * rotateEquiv (rotateEquiv x)) =
        x * rotateEquiv x * rotateEquiv (rotateEquiv x) := by ring
    _ = (norm x : SevenRealCubicInt) :=
      mul_rotateEquiv_mul_rotateEquiv_sq_eq_norm x
    _ = 1 := by simp [hx]

theorem thomasLambda_isUnit : IsUnit thomasLambda :=
  thomas_isUnit_of_norm_one thomasLambda_norm

/-- The canonical unit lift of `thomasLambda`. -/
def thomasLambdaUnit : SevenRealCubicIntˣ :=
  thomasLambda_isUnit.unit

@[simp] theorem thomasLambdaUnit_val :
    (thomasLambdaUnit : SevenRealCubicInt) = thomasLambda :=
  thomasLambda_isUnit.unit_spec

/-! ## Part B: theta coordinates and the projective class -/

theorem thomasLambda_eq_thetaCoordinates :
    thomasLambda = ofThetaCoordinates 11 7 1 := by
  rw [thomasLambda_eq_coordinates]
  ext <;>
    norm_num [ofThetaCoordinates, eisensteinAxis_sq_coordinates,
      eisensteinAxis, mul, ofInt, pow_two]

theorem thomasLambda_theta_coordinates :
    thetaConstInt thomasLambda = 11 ∧
      thetaLinearInt thomasLambda = 7 ∧
      thetaSquareInt thomasLambda = 1 := by
  rw [thomasLambda_eq_thetaCoordinates]
  exact ofThetaCoordinates_coordinates 11 7 1

theorem thomasLambda_projectiveLog :
    projectiveLog (Additive.ofMul thomasLambdaUnit) = (0, 2) := by
  have hconst :
      thetaConstModSeven (thomasLambdaUnit : SevenRealCubicInt) = 4 := by
    rw [thomasLambdaUnit_val, thomasLambda_eq_thetaCoordinates]
    norm_num [thetaConstModSeven, ofThetaCoordinates,
      eisensteinAxis_sq_coordinates, eisensteinAxis, mul, ofInt, pow_two]
    decide
  have hlin :
      thetaLinearModSeven (thomasLambdaUnit : SevenRealCubicInt) = 0 := by
    rw [thomasLambdaUnit_val, thomasLambda_eq_thetaCoordinates]
    norm_num [thetaLinearModSeven, ofThetaCoordinates,
      eisensteinAxis_sq_coordinates, eisensteinAxis, mul, ofInt, pow_two]
    decide
  have hsq :
      thetaSquareModSeven (thomasLambdaUnit : SevenRealCubicInt) = 1 := by
    rw [thomasLambdaUnit_val, thomasLambda_eq_thetaCoordinates]
    norm_num [thetaSquareModSeven, ofThetaCoordinates,
      eisensteinAxis_sq_coordinates, eisensteinAxis, mul, ofInt, pow_two]
  have hx : unitNilpotentX thomasLambdaUnit = 0 := by
    rw [unitNilpotentX, hlin, hconst]
    simp
  have hy : unitNilpotentY thomasLambdaUnit = 2 := by
    rw [unitNilpotentY, hsq, hconst]
    simp [div_eq_mul_inv, inv_four_zmod_seven_thomas]
  rw [projectiveLog_apply]
  rw [hx, hy]
  norm_num

theorem thomasLambda_unit_relation :
    thomasLambda ^ 2 * (1 + alpha) = alpha ^ 6 := by
  ext <;> norm_num [thomasLambda, alpha, mul, pow_succ]

/-! ## Part C: the Thomas plane and its norm form -/

def thomasPlaneElement (R S : ℤ) : SevenRealCubicInt :=
  (R : SevenRealCubicInt) - thomasLambda * S

theorem norm_thomasPlaneElement (R S : ℤ) :
    norm (thomasPlaneElement R S) = F5 R S := by
  rw [thomasPlaneElement, thomasLambda_eq_coordinates]
  norm_num [F5, SevenRealCubicInt.norm, mul, pow_two,
    ofInt, fst_intCast, snd_intCast, thd_intCast]
  ring

theorem thomasPlaneElement_theta_coordinates (R S : ℤ) :
    thetaConstInt (thomasPlaneElement R S) = R - 11 * S ∧
      thetaLinearInt (thomasPlaneElement R S) = -7 * S ∧
      thetaSquareInt (thomasPlaneElement R S) = -S := by
  rw [thomasPlaneElement, thomasLambda_eq_coordinates]
  constructor
  · norm_num [thetaConstInt, fst_sub, fst_intCast, fst_mul, ofInt]
    ring
  · constructor
    · norm_num [thetaLinearInt, snd_sub, snd_intCast, snd_mul, ofInt]
      ring
    · norm_num [thetaSquareInt, thd_sub, thd_intCast, thd_mul, ofInt]

theorem thomasPlaneElement_theta_plane (R S : ℤ) :
    thetaLinearInt (thomasPlaneElement R S) =
      7 * thetaSquareInt (thomasPlaneElement R S) := by
  obtain ⟨_, hlin, hsq⟩ := thomasPlaneElement_theta_coordinates R S
  rw [hlin, hsq]
  ring

/-! ## Part D: norm-one lift -/

theorem thomasPlaneElement_isUnit {R S : ℤ}
    (hfive : F5 R S = 1) : IsUnit (thomasPlaneElement R S) := by
  apply thomas_isUnit_of_norm_one
  rw [norm_thomasPlaneElement, hfive]

/-! ## Part E: theta multiplication and inverse depth -/

theorem thetaLinearInt_mul (x y : SevenRealCubicInt) :
    thetaLinearInt (x * y) =
      thetaConstInt x * thetaLinearInt y +
        thetaLinearInt x * thetaConstInt y -
        14 * (thetaLinearInt x * thetaSquareInt y +
          thetaSquareInt x * thetaLinearInt y) +
        91 * thetaSquareInt x * thetaSquareInt y := by
  rcases x with ⟨a, b, c⟩
  rcases y with ⟨d, e, f⟩
  simp [thetaConstInt, thetaLinearInt, thetaSquareInt]
  ring

theorem thetaSquareInt_mul (x y : SevenRealCubicInt) :
    thetaSquareInt (x * y) =
      thetaConstInt x * thetaSquareInt y +
        thetaLinearInt x * thetaLinearInt y +
        thetaSquareInt x * thetaConstInt y -
        7 * (thetaLinearInt x * thetaSquareInt y +
          thetaSquareInt x * thetaLinearInt y) +
        35 * thetaSquareInt x * thetaSquareInt y := by
  rcases x with ⟨a, b, c⟩
  rcases y with ⟨d, e, f⟩
  simp [thetaConstInt, thetaLinearInt, thetaSquareInt]
  ring

theorem thetaNilpotentDepth_inv
    (u : SevenRealCubicIntˣ) (n : ℕ)
    (hdepth : ThetaNilpotentDepth n
      (u : SevenRealCubicInt)) :
    ThetaNilpotentDepth n
      ((u⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) := by
  let x : SevenRealCubicInt := u
  let y : SevenRealCubicInt := (u⁻¹ : SevenRealCubicIntˣ)
  let A : ℤ := thetaConstInt x
  let B : ℤ := thetaLinearInt x
  let C : ℤ := thetaSquareInt x
  let D : ℤ := thetaConstInt y
  let E : ℤ := thetaLinearInt y
  let F : ℤ := thetaSquareInt y
  have hxy : x * y = 1 := by
    change (u : SevenRealCubicInt) *
      ((u⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) = 1
    rw [← Units.val_mul]
    simp
  have hA : ¬(7 : ℤ) ∣ A := by
    intro hdiv
    apply thetaConstModSeven_unit_ne_zero u
    change ((A : ℤ) : ZMod 7) = 0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd A 7).mpr hdiv
  have hcop : IsCoprime ((7 : ℤ) ^ n) A := by
    exact ((show Prime (7 : ℤ) by norm_num).coprime_iff_not_dvd.mpr hA).pow_left
  have hB : (7 : ℤ) ^ n ∣ B := by
    simpa [x, A, B] using hdepth.1
  have hC : (7 : ℤ) ^ n ∣ C := by
    simpa [x, A, C] using hdepth.2
  have hlin_zero : thetaLinearInt (x * y) = 0 := by
    rw [hxy]
    norm_num [thetaLinearInt]
  have hsq_zero : thetaSquareInt (x * y) = 0 := by
    rw [hxy]
    norm_num [thetaSquareInt]
  have hrest_lin : (7 : ℤ) ^ n ∣
      B * D - 14 * (B * F + C * E) + 91 * C * F := by
    have hBD : (7 : ℤ) ^ n ∣ B * D := dvd_mul_of_dvd_left hB D
    have hBF : (7 : ℤ) ^ n ∣ B * F := dvd_mul_of_dvd_left hB F
    have hCE : (7 : ℤ) ^ n ∣ C * E := dvd_mul_of_dvd_left hC E
    have hCF : (7 : ℤ) ^ n ∣ C * F := dvd_mul_of_dvd_left hC F
    have hsum : (7 : ℤ) ^ n ∣ B * F + C * E := dvd_add hBF hCE
    have h14 : (7 : ℤ) ^ n ∣ 14 * (B * F + C * E) := by
      simpa [mul_comm] using dvd_mul_of_dvd_right hsum 14
    have h91 : (7 : ℤ) ^ n ∣ 91 * C * F := by
      simpa [mul_assoc, mul_comm] using dvd_mul_of_dvd_right hCF 91
    exact dvd_add (dvd_sub hBD h14) h91
  have hrest_sq : (7 : ℤ) ^ n ∣
      B * E + C * D - 7 * (B * F + C * E) + 35 * C * F := by
    have hBE : (7 : ℤ) ^ n ∣ B * E := dvd_mul_of_dvd_left hB E
    have hCD : (7 : ℤ) ^ n ∣ C * D := dvd_mul_of_dvd_left hC D
    have hBF : (7 : ℤ) ^ n ∣ B * F := dvd_mul_of_dvd_left hB F
    have hCE : (7 : ℤ) ^ n ∣ C * E := dvd_mul_of_dvd_left hC E
    have hCF : (7 : ℤ) ^ n ∣ C * F := dvd_mul_of_dvd_left hC F
    have hsum : (7 : ℤ) ^ n ∣ B * F + C * E := dvd_add hBF hCE
    have h7 : (7 : ℤ) ^ n ∣ 7 * (B * F + C * E) := by
      simpa [mul_comm] using dvd_mul_of_dvd_right hsum 7
    have h35 : (7 : ℤ) ^ n ∣ 35 * C * F := by
      simpa [mul_assoc, mul_comm] using dvd_mul_of_dvd_right hCF 35
    exact dvd_add (dvd_sub (dvd_add hBE hCD) h7) h35
  have hAE : (7 : ℤ) ^ n ∣ A * E := by
    have hwhole : (7 : ℤ) ^ n ∣
        A * E + B * D - 14 * (B * F + C * E) +
          91 * C * F := by
      rw [← thetaLinearInt_mul, hlin_zero]
      exact dvd_zero _
    convert dvd_sub hwhole hrest_lin using 1
    ring
  have hAF : (7 : ℤ) ^ n ∣ A * F := by
    have hwhole : (7 : ℤ) ^ n ∣
        A * F + B * E + C * D - 7 * (B * F + C * E) +
          35 * C * F := by
      rw [← thetaSquareInt_mul, hsq_zero]
      exact dvd_zero _
    convert dvd_sub hwhole hrest_sq using 1
    ring
  have hE : (7 : ℤ) ^ n ∣ E := hcop.dvd_of_dvd_mul_left hAE
  have hF : (7 : ℤ) ^ n ∣ F := hcop.dvd_of_dvd_mul_left hAF
  exact ⟨by simpa [y, E] using hE, by simpa [y, F] using hF⟩

noncomputable def thomasPlaneUnit (R S : ℤ)
    (hfive : F5 R S = 1) : SevenRealCubicIntˣ :=
  (thomasPlaneElement_isUnit hfive).unit

@[simp] theorem thomasPlaneUnit_val (R S : ℤ)
    (hfive : F5 R S = 1) :
    (thomasPlaneUnit R S hfive : SevenRealCubicInt) =
      thomasPlaneElement R S :=
  (thomasPlaneElement_isUnit hfive).unit_spec

/-! ## Part F: cyclic normalization -/

theorem thomas_sigma5_normalization
    {R S : ℤ} (hfive : F5 R S = 1)
    (hdepth : (7 : ℤ) ^ 8 ∣ R * S * (R + S)) :
    ∃ R' S' : ℤ,
      F5 R' S' = 1 ∧
      Q5 R' S' = Q5 R S ∧
      T5 R' S' = T5 R S ∧
      (7 : ℤ) ^ 8 ∣ S' ∧
      ¬(7 : ℤ) ∣ R' := by
  have hcop := eisenstein_current_highDepthFive_pairwise_coprime
    (by simpa [F5] using hfive)
  rcases eisenstein_current_highDepthFive_deep_factor hcop hdepth with
    hR | hS | hsum
  · refine ⟨-R - S, R, ?_, ?_, ?_, hR.1, ?_⟩
    · calc
        F5 (-R - S) R = F5 R S := sigma5_F5_invariant R S
        _ = 1 := hfive
    · simpa using sigma5_Q5_invariant R S
    · simpa using sigma5_T5_invariant R S
    · intro hdiv
      apply hR.2.2
      rcases hdiv with ⟨k, hk⟩
      refine ⟨-k, ?_⟩
      nlinarith [hk]
  · exact ⟨R, S, hfive, rfl, rfl, hS.1, hS.2.1⟩
  · refine ⟨S, -R - S, ?_, ?_, ?_, ?_, hsum.2.2⟩
    · calc
        F5 S (-R - S) = F5 (-R - S) R := by
          simpa using sigma5_F5_invariant (-R - S) R
        _ = F5 R S := sigma5_F5_invariant R S
        _ = 1 := hfive
    · calc
        Q5 S (-R - S) = Q5 (-R - S) R := by
          simpa using sigma5_Q5_invariant (-R - S) R
        _ = Q5 R S := sigma5_Q5_invariant R S
    · calc
        T5 S (-R - S) = T5 (-R - S) R := by
          simpa using sigma5_T5_invariant (-R - S) R
        _ = T5 R S := sigma5_T5_invariant R S
    · rcases hsum.1 with ⟨k, hk⟩
      refine ⟨-k, ?_⟩
      nlinarith [hk]

/-! ## Part G: the current depth-eight Thomas unit -/

theorem thomasPlaneUnit_depth_eight
    {R S : ℤ} (hfive : F5 R S = 1)
    (hS : (7 : ℤ) ^ 8 ∣ S) :
    ThetaNilpotentDepth 8
  (thomasPlaneUnit R S hfive : SevenRealCubicInt) := by
  obtain ⟨_, hlin, hsq⟩ := thomasPlaneElement_theta_coordinates R S
  rw [ThetaNilpotentDepth, thomasPlaneUnit_val, hlin, hsq]
  constructor
  · simpa [mul_comm] using dvd_mul_of_dvd_right hS 7
  · exact dvd_neg.mpr hS

theorem thomasPlaneUnit_exists_seven_pow
    {R S : ℤ} (hfive : F5 R S = 1)
    (hS : (7 : ℤ) ^ 8 ∣ S) :
    ∃ t : SevenRealCubicIntˣ,
      thomasPlaneUnit R S hfive = t ^ (7 ^ 8) := by
  apply unit_is_pow_seven_pow_of_inverse_depth
  exact thetaNilpotentDepth_inv (thomasPlaneUnit R S hfive) 8
    (thomasPlaneUnit_depth_eight hfive hS)

theorem thomasPlaneUnit_projectiveLog_zero
    {R S : ℤ} (hfive : F5 R S = 1)
    (hS : (7 : ℤ) ^ 8 ∣ S) :
    projectiveLog
      (Additive.ofMul (thomasPlaneUnit R S hfive)) = 0 := by
  apply thetaNilpotentDepth_one_projectiveLog_zero
  exact thetaNilpotentDepth_mono (by norm_num : 1 ≤ 8)
    (thomasPlaneUnit_depth_eight hfive hS)

/-! ## Part H: the exact seventh-root return equation -/

theorem thomasPlane_seventh_root_equation
    (A B C : ℤ)
    (hplane : thetaLinearInt ((ofThetaCoordinates A B C) ^ 7) =
      7 * thetaSquareInt ((ofThetaCoordinates A B C) ^ 7)) :
    seventhThetaLinearQuotient A B C =
      7 * seventhThetaSquareQuotient A B C := by
  have hlin := thetaLinear_pow_seven A B C
  have hsq := thetaSquare_pow_seven A B C
  rw [hlin, hsq] at hplane
  apply mul_left_cancel₀ (by norm_num : (7 : ℤ) ≠ 0)
  convert hplane using 1

theorem thomasPlane_seventh_root_B_dvd
    (t : SevenRealCubicIntˣ)
    (hplane : thetaLinearInt ((t : SevenRealCubicInt) ^ 7) =
      7 * thetaSquareInt ((t : SevenRealCubicInt) ^ 7)) :
    (7 : ℤ) ∣ thetaLinearInt (t : SevenRealCubicInt) := by
  let A : ℤ := thetaConstInt (t : SevenRealCubicInt)
  let B : ℤ := thetaLinearInt (t : SevenRealCubicInt)
  let C : ℤ := thetaSquareInt (t : SevenRealCubicInt)
  have ht : (t : SevenRealCubicInt) = ofThetaCoordinates A B C := by
    exact theta_coordinate_decomposition (t : SevenRealCubicInt)
  have hplane' : thetaLinearInt ((ofThetaCoordinates A B C) ^ 7) =
      7 * thetaSquareInt ((ofThetaCoordinates A B C) ^ 7) := by
    rw [← ht]
    exact hplane
  have heq := thomasPlane_seventh_root_equation A B C hplane'
  have hA : ¬(7 : ℤ) ∣ A := by
    intro hdiv
    apply thetaConstModSeven_unit_ne_zero t
    change ((A : ℤ) : ZMod 7) = 0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd A 7).mpr hdiv
  have hquot : (7 : ℤ) ∣ seventhThetaLinearQuotient A B C := by
    rw [heq]
    exact dvd_mul_right 7 _
  have hterm : (7 : ℤ) ∣ 7 * C ^ 2 * seventhThetaLinearCFactor A C := by
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left (dvd_refl (7 : ℤ)) (C ^ 2))
      (seventhThetaLinearCFactor A C)
  have hprod : (7 : ℤ) ∣ B * seventhThetaLinearBFactor A B C := by
    rw [seventhThetaLinearQuotient] at hquot
    convert dvd_sub hquot hterm using 1
    ring
  have hcop : IsCoprime (7 : ℤ) (seventhThetaLinearBFactor A B C) :=
    (show Prime (7 : ℤ) by norm_num).coprime_iff_not_dvd.mpr
      (seventhThetaLinearBFactor_not_seven_dvd hA)
  have hB : (7 : ℤ) ∣ B := hcop.dvd_of_dvd_mul_right hprod
  simpa [B] using hB

theorem thomasPlaneUnit_seventh_root_B_dvd
    {R S : ℤ} (hfive : F5 R S = 1)
    (_hS : (7 : ℤ) ^ 8 ∣ S)
    {t : SevenRealCubicIntˣ}
    (hroot : thomasPlaneUnit R S hfive = t ^ 7) :
    (7 : ℤ) ∣ thetaLinearInt (t : SevenRealCubicInt) := by
  have hval : (thomasPlaneUnit R S hfive : SevenRealCubicInt) =
      (t : SevenRealCubicInt) ^ 7 := by
    simpa only [Units.val_pow_eq_pow_val] using congrArg Units.val hroot
  have hplaneU := thomasPlaneElement_theta_plane R S
  have hplane : thetaLinearInt ((t : SevenRealCubicInt) ^ 7) =
      7 * thetaSquareInt ((t : SevenRealCubicInt) ^ 7) := by
    rw [← hval]
    rw [thomasPlaneUnit_val]
    exact hplaneU
  exact thomasPlane_seventh_root_B_dvd t hplane

end SevenRealCubic

end
end DkMath.FLT.Seven
