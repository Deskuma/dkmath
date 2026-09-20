/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicSimplestCubicCertificate
import DkMath.FLT.Three.EisensteinUnitSectors

#print "file: DkMath.FLT.Seven.SevenRealCubicEisensteinCubeCertificate"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open DkMath.FLT.Three
open DkMath.NumberTheory.TraceOneQuadratic
open scoped NumberField Pointwise

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000

namespace SevenRealCubic

def sourcePlaneNormSevenQParameter (A m : ℤ) : ℤ :=
  A ^ 2 - 19 * A * m + 91 * m ^ 2

def sourcePlaneNormSevenKParameter (A m : ℤ) : ℤ :=
  -13 * A ^ 3 + 357 * A ^ 2 * m - 3234 * A * m ^ 2 + 9653 * m ^ 3

theorem sourcePlaneNormSevenQuadratic_parameter (A m : ℤ) :
    sourcePlaneNormSevenQuadratic (2 * A - 21 * m) (-3 * A + 28 * m) =
      7 * sourcePlaneNormSevenQParameter A m := by
  simp [sourcePlaneNormSevenQuadratic, sourcePlaneNormSevenQParameter]
  ring

theorem sourcePlaneNormSevenJacobian_parameter (A m : ℤ) :
    sourcePlaneNormSevenJacobian (2 * A - 21 * m) (-3 * A + 28 * m) =
      7 * sourcePlaneNormSevenKParameter A m := by
  simp [sourcePlaneNormSevenJacobian, sourcePlaneNormSevenKParameter]
  ring

theorem sourcePlaneNormSevenQParameter_nonneg (A m : ℤ) :
    0 ≤ sourcePlaneNormSevenQParameter A m := by
  simp [sourcePlaneNormSevenQParameter]
  nlinarith [sq_nonneg (2 * A - 19 * m), sq_nonneg m]

theorem sourcePlaneNormSevenQParameter_pos_of_norm_eq_neg_seven
    {A m : ℤ}
    (hF : sourcePlaneNormSevenForm (2 * A - 21 * m) (-3 * A + 28 * m) = -7) :
    0 < sourcePlaneNormSevenQParameter A m := by
  have hnonneg := sourcePlaneNormSevenQParameter_nonneg A m
  by_contra hpos
  have hq : sourcePlaneNormSevenQParameter A m = 0 := by omega
  have hsum : (2 * A - 19 * m) ^ 2 + 3 * m ^ 2 = 0 := by
    simp [sourcePlaneNormSevenQParameter] at hq
    nlinarith
  have hm : m = 0 := by nlinarith [sq_nonneg (2 * A - 19 * m)]
  have hA : A = 0 := by nlinarith [hsum]
  subst A
  subst m
  norm_num [sourcePlaneNormSevenForm] at hF

theorem sourcePlaneNormSevenThetaNorm_parameter (A m : ℤ) :
    norm (ofThetaCoordinates A (14 * m) (3 * m)) =
      A ^ 3 - 35 * A ^ 2 * m + 392 * A * m ^ 2 - 1421 * m ^ 3 := by
  norm_num [ofThetaCoordinates, eisensteinAxis_sq_coordinates,
    eisensteinAxis, SevenRealCubicInt.norm, SevenRealCubicInt.mul,
    SevenRealCubicInt.ofInt,
    pow_two]
  ring

theorem sourcePlaneNormSeven_mordell_parameter (A m : ℤ)
    (hF : sourcePlaneNormSevenForm (2 * A - 21 * m) (-3 * A + 28 * m) = -7) :
    sourcePlaneNormSevenKParameter A m ^ 2 + 27 =
      196 * sourcePlaneNormSevenQParameter A m ^ 3 := by
  have hcert := sourcePlaneNormSevenCovariant_certificate hF
  rw [sourcePlaneNormSevenQuadratic_parameter,
    sourcePlaneNormSevenJacobian_parameter] at hcert
  obtain ⟨q, k, hq, hk, hM⟩ := hcert
  have hq' : q = sourcePlaneNormSevenQParameter A m := by
    nlinarith
  have hk' : k = sourcePlaneNormSevenKParameter A m := by
    nlinarith
  rw [← hq', ← hk']
  exact hM

theorem sourcePlaneNormSeven_pow_ten_dvd_A_cube_sub_one
    {A m : ℤ} (hm : (7 : ℤ) ^ 9 ∣ m)
    (hnorm : A ^ 3 - 35 * A ^ 2 * m + 392 * A * m ^ 2 - 1421 * m ^ 3 = 1) :
    (7 : ℤ) ^ 10 ∣ A ^ 3 - 1 := by
  rcases hm with ⟨t, ht⟩
  refine ⟨5 * A ^ 2 * t - 392 * 7 ^ 8 * A * t ^ 2 +
      1421 * 7 ^ 17 * t ^ 3, ?_⟩
  calc
    A ^ 3 - 1 = 35 * A ^ 2 * m - 392 * A * m ^ 2 +
        1421 * m ^ 3 := by nlinarith [hnorm]
    _ = (7 : ℤ) ^ 10 *
        (5 * A ^ 2 * t - 392 * 7 ^ 8 * A * t ^ 2 +
          1421 * 7 ^ 17 * t ^ 3) := by
      rw [ht]
      ring

theorem sourcePlaneNormSeven_pow_ten_dvd_K_add_thirteen
    {A m : ℤ} (hm : (7 : ℤ) ^ 9 ∣ m)
    (hnorm : A ^ 3 - 35 * A ^ 2 * m + 392 * A * m ^ 2 - 1421 * m ^ 3 = 1) :
    (7 : ℤ) ^ 10 ∣ sourcePlaneNormSevenKParameter A m + 13 := by
  have hA := sourcePlaneNormSeven_pow_ten_dvd_A_cube_sub_one hm hnorm
  rcases hA with ⟨u, hu⟩
  rcases hm with ⟨t, ht⟩
  refine ⟨-13 * u + 51 * A ^ 2 * t - 462 * 7 ^ 9 * A * t ^ 2 +
      1379 * 7 ^ 18 * t ^ 3, ?_⟩
  rw [show sourcePlaneNormSevenKParameter A m + 13 =
      -13 * (A ^ 3 - 1) + 357 * A ^ 2 * m -
        3234 * A * m ^ 2 + 9653 * m ^ 3 by
      simp [sourcePlaneNormSevenKParameter]
      ring, hu, ht,
    show (7 : ℤ) ^ 10 = 7 ^ 9 * 7 by ring]
  ring

theorem sourcePlaneNormSevenKParameter_odd
    {A m : ℤ} (hM : sourcePlaneNormSevenKParameter A m ^ 2 + 27 =
      196 * sourcePlaneNormSevenQParameter A m ^ 3) :
    Odd (sourcePlaneNormSevenKParameter A m) := by
  rcases Int.even_or_odd (sourcePlaneNormSevenKParameter A m) with h | h
  · rcases h with ⟨t, ht⟩
    have hfour : (4 : ℤ) ∣ sourcePlaneNormSevenKParameter A m ^ 2 + 27 := by
      rw [hM]
      refine ⟨49 * sourcePlaneNormSevenQParameter A m ^ 3, ?_⟩
      ring
    have hsquare : (4 : ℤ) ∣ sourcePlaneNormSevenKParameter A m ^ 2 := by
      rw [ht]
      refine ⟨t ^ 2, ?_⟩
      ring
    have h27 : (4 : ℤ) ∣ 27 := by
      simpa using (dvd_sub hfour hsquare)
    norm_num at h27
  · exact h

theorem sourcePlaneNormSevenKParameter_h_parameter
    {A m h : ℤ} (hk : sourcePlaneNormSevenKParameter A m = 2 * h + 3) :
    sourcePlaneNormSevenKParameter A m ^ 2 + 27 =
      4 * (h ^ 2 + 3 * h + 9) := by
  rw [hk]
  ring

def eisensteinPiSeven : EisensteinInt := eisensteinCoord 2 1

theorem eisensteinPiSeven_norm : norm eisensteinPiSeven = 7 := by
  rw [eisensteinPiSeven, eisenstein_norm_coords]
  norm_num

theorem eisensteinPiSeven_sq : eisensteinPiSeven ^ 2 = eisensteinCoord 3 5 := by
  rw [eisensteinPiSeven]
  ext <;> simp [eisensteinCoord, pow_two]

theorem sourcePlaneNormSeven_h_parameter_exists
    {A m : ℤ} (hM : sourcePlaneNormSevenKParameter A m ^ 2 + 27 =
      196 * sourcePlaneNormSevenQParameter A m ^ 3) :
    ∃ h : ℤ, sourcePlaneNormSevenKParameter A m = 2 * h + 3 := by
  have hodd := sourcePlaneNormSevenKParameter_odd hM
  rcases hodd with ⟨t, ht⟩
  refine ⟨t - 1, ?_⟩
  linarith

theorem sourcePlaneNormSeven_pow_ten_dvd_h_add_eight
    {A m h : ℤ}
    (hk : sourcePlaneNormSevenKParameter A m = 2 * h + 3)
    (hK : (7 : ℤ) ^ 10 ∣ sourcePlaneNormSevenKParameter A m + 13) :
    (7 : ℤ) ^ 10 ∣ h + 8 := by
  rcases hK with ⟨t, ht⟩
  have hEq : 2 * (h + 8) = (7 : ℤ) ^ 10 * t := by
    calc
      2 * (h + 8) = sourcePlaneNormSevenKParameter A m + 13 := by
        rw [hk]
        ring
      _ = (7 : ℤ) ^ 10 * t := ht
  have hdiv : (7 : ℤ) ^ 10 ∣ (h + 8) * 2 := by
    refine ⟨t, ?_⟩
    calc
      (h + 8) * 2 = 2 * (h + 8) := by ring
      _ = (7 : ℤ) ^ 10 * t := hEq
  exact (by norm_num : IsCoprime ((7 : ℤ) ^ 10) 2).dvd_of_dvd_mul_right hdiv

theorem eisensteinMordellElement_norm
    {h q : ℤ} (hM : (2 * h + 3) ^ 2 + 27 = 196 * q ^ 3) :
    norm (eisensteinCoord h 3) = 49 * q ^ 3 := by
  rw [eisenstein_norm_coords]
  nlinarith

theorem eisensteinPiSeven_sq_mul_coordinate
    (h r s : ℤ)
    (hh : h = 3 * r - 5 * s) (hthree : 3 = 5 * r + 8 * s) :
    eisensteinCoord h 3 =
      eisensteinPiSeven ^ 2 * eisensteinCoord r s := by
  rw [eisensteinPiSeven_sq]
  ext <;> simp [eisensteinCoord]
  · linarith
  · linarith

theorem eisenstein_square_strip_norm
    {h q r s : ℤ}
    (hM : (2 * h + 3) ^ 2 + 27 = 196 * q ^ 3)
    (hh : h = 3 * r - 5 * s) (hthree : 3 = 5 * r + 8 * s) :
    norm (eisensteinCoord r s) = q ^ 3 := by
  have hz := eisensteinMordellElement_norm hM
  have hstrip := eisensteinPiSeven_sq_mul_coordinate h r s hh hthree
  rw [hstrip, eisenstein_norm_mul, pow_two, eisenstein_norm_mul,
    eisensteinPiSeven_norm] at hz
  nlinarith [hz]

theorem eisenstein_square_strip_parameters
    {h : ℤ} (h49 : (49 : ℤ) ∣ h + 8) :
    ∃ r s : ℤ,
      h = 3 * r - 5 * s ∧
      3 = 5 * r + 8 * s ∧
      49 * r = 8 * h + 15 ∧
      49 * s = -5 * h + 9 := by
  rcases h49 with ⟨t, ht⟩
  have hh : h = 49 * t - 8 := by linarith
  refine ⟨8 * t - 1, 1 - 5 * t, ?_, ?_, ?_, ?_⟩
  · rw [hh]
    ring
  · ring
  · rw [hh]
    ring
  · rw [hh]
    ring

theorem eisenstein_square_strip_parameters_high_depth
    {h : ℤ} (h70 : (7 : ℤ) ^ 10 ∣ h + 8) :
    ∃ r s : ℤ,
      h = 3 * r - 5 * s ∧
      3 = 5 * r + 8 * s ∧
      49 * r = 8 * h + 15 ∧
      49 * s = -5 * h + 9 ∧
      (7 : ℤ) ^ 8 ∣ r + 1 ∧
      (7 : ℤ) ^ 8 ∣ s - 1 := by
  rcases h70 with ⟨t, ht⟩
  have hh : h = (7 : ℤ) ^ 10 * t - 8 := by linarith
  refine ⟨8 * 7 ^ 8 * t - 1, 1 - 5 * 7 ^ 8 * t, ?_, ?_, ?_, ?_,
    ⟨8 * t, by ring⟩, ⟨-5 * t, by ring⟩⟩
  · rw [hh]
    ring
  · ring
  · rw [hh]
    ring
  · rw [hh]
    ring

theorem eisenstein_cube_product_of_norm_cube
    {q r s : ℤ}
    (hnorm : norm (eisensteinCoord r s) = q ^ 3) :
    eisensteinCoord r s * conj (eisensteinCoord r s) =
      (eisensteinCoord q 0) ^ 3 := by
  rw [traceOne_mul_conj, hnorm]
  ext <;> simp [DkMath.NumberTheory.TraceOneQuadratic.ofInt,
    eisensteinCoord, pow_succ]

theorem eisenstein_cube_extraction_of_relPrime
    {q r s : ℤ}
    (hrel : EisensteinRelPrime (eisensteinCoord r s)
      (conj (eisensteinCoord r s)))
    (hnorm : norm (eisensteinCoord r s) = q ^ 3) :
    ∃ epsilon : EisensteinIntˣ, ∃ gamma : EisensteinInt,
      eisensteinCoord r s = (epsilon : EisensteinInt) * gamma ^ 3 := by
  have hcop : IsUnit (gcd (eisensteinCoord r s)
      (conj (eisensteinCoord r s))) :=
    isUnit_gcd_of_eisensteinRelPrime hrel
  exact exists_unit_mul_cube_of_coprime_mul_eq_cube hcop
    (eisenstein_cube_product_of_norm_cube hnorm)

theorem eisenstein_sector_cube_normalization
    {q r s : ℤ}
    (hrel : EisensteinRelPrime (eisensteinCoord r s)
      (conj (eisensteinCoord r s)))
    (hnorm : norm (eisensteinCoord r s) = q ^ 3) :
    ∃ sector : EisensteinUnitSector, ∃ gamma : EisensteinInt,
      eisensteinCoord r s = sector.rep * gamma ^ 3 := by
  obtain ⟨epsilon, gamma, hEq⟩ :=
    eisenstein_cube_extraction_of_relPrime hrel hnorm
  obtain ⟨sector, delta, _, hsector⟩ :=
    exists_sector_mul_cube_of_unit epsilon
  refine ⟨sector, delta * gamma, ?_⟩
  calc
    eisensteinCoord r s = (epsilon : EisensteinInt) * gamma ^ 3 := hEq
    _ = (sector.rep * delta ^ 3) * gamma ^ 3 := by rw [hsector]
    _ = sector.rep * (delta * gamma) ^ 3 := by
      rw [mul_pow]
      ring

def eisensteinCubeFirstCoordinate (R S : ℤ) : ℤ :=
  R ^ 3 - 3 * R * S ^ 2 - S ^ 3

def eisensteinCubeSecondCoordinate (R S : ℤ) : ℤ :=
  3 * R * S * (R + S)

theorem eisenstein_sector_second_coordinate
    (sector : EisensteinUnitSector) (R S : ℤ) :
    (eisensteinPiSeven ^ 2 * sector.rep *
        (eisensteinCoord R S) ^ 3).snd =
      match sector with
      | .one =>
          5 * eisensteinCubeFirstCoordinate R S +
            8 * eisensteinCubeSecondCoordinate R S
      | .tau =>
          8 * eisensteinCubeFirstCoordinate R S +
            3 * eisensteinCubeSecondCoordinate R S
      | .tauSq =>
          3 * eisensteinCubeFirstCoordinate R S -
            5 * eisensteinCubeSecondCoordinate R S := by
  cases sector <;>
    norm_num [eisensteinPiSeven, EisensteinUnitSector.rep,
      eisensteinTau, eisensteinCubeFirstCoordinate,
      eisensteinCubeSecondCoordinate, eisensteinCoord,
      DkMath.NumberTheory.TraceOneQuadratic.ofInt, tau, pow_succ]
  all_goals ring

end SevenRealCubic
end
end DkMath.FLT.Seven
