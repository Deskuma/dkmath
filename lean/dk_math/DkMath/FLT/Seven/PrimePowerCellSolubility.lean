/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimePowerCellSystems

#print "file: DkMath.FLT.Seven.PrimePowerCellSolubility"

namespace DkMath.FLT.Seven

set_option linter.unnecessarySeqFocus false

private theorem seven_not_dvd_of_prime_ne {q : ℕ} (hq : Nat.Prime q)
    (hq7 : q ≠ 7) : ¬ q ∣ 7 := by
  intro h
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp h with h1 | h7
  · exact hq.ne_one h1
  · exact hq7 h7

theorem seven_isUnit_zmod_primePower {q e : ℕ} (hq : Nat.Prime q)
    (hq7 : q ≠ 7) (he : 0 < e) : IsUnit (7 : ZMod (q ^ e)) :=
  isUnit_zmod_primePower_of_not_dvd hq he (seven_not_dvd_of_prime_ne hq hq7)

theorem fortyNine_isUnit_zmod_primePower {q e : ℕ} (hq : Nat.Prime q)
    (hq7 : q ≠ 7) (he : 0 < e) : IsUnit (49 : ZMod (q ^ e)) := by
  convert (seven_isUnit_zmod_primePower hq hq7 he).mul
    (seven_isUnit_zmod_primePower hq hq7 he) using 1 <;> norm_num

theorem leftCorrection_isUnit_of_leftCubic_eq_zero_primePower {q e : ℕ}
    (hq : Nat.Prime q) (hq7 : q ≠ 7) (he : 0 < e) (t : ZMod (q ^ e))
    (hP : leftCubicNormalizedZMod t = 0) :
    IsUnit (leftCorrectionNormalizedZMod t) := by
  have h7 := seven_isUnit_zmod_primePower hq hq7 he
  apply isUnit_of_dvd_unit _ h7
  refine ⟨-6 * t ^ 2 + 22 * t - 19, ?_⟩
  calc
    (7 : ZMod (q ^ e)) = (60 * t - 88) * leftCubicNormalizedZMod t +
        (-6 * t ^ 2 + 22 * t - 19) * leftCorrectionNormalizedZMod t := by
      simp [leftCubicNormalizedZMod, leftCorrectionNormalizedZMod]
      ring
    _ = _ := by rw [hP]; ring

theorem rightCorrection_isUnit_of_rightCubic_eq_zero_primePower {q e : ℕ}
    (hq : Nat.Prime q) (hq7 : q ≠ 7) (he : 0 < e) (t : ZMod (q ^ e))
    (hQ : rightCubicNormalizedZMod t = 0) :
    IsUnit (rightCorrectionNormalizedZMod t) := by
  have h7 := seven_isUnit_zmod_primePower hq hq7 he
  apply isUnit_of_dvd_unit _ h7
  refine ⟨-6 * t ^ 2 - 34 * t - 47, ?_⟩
  calc
    (7 : ZMod (q ^ e)) = (60 * t + 148) * rightCubicNormalizedZMod t +
        (-6 * t ^ 2 - 34 * t - 47) * rightCorrectionNormalizedZMod t := by
      simp [rightCubicNormalizedZMod, rightCorrectionNormalizedZMod]
      ring
    _ = _ := by rw [hQ]; ring

private theorem left_scaled_root_pp {M : ℕ} (t C : ZMod M)
    (hroot : leftCubicNormalizedZMod t = 0) :
    leftCubicZMod (t * C ^ 2) (C ^ 2) = 0 := by
  rw [show leftCubicZMod (t * C ^ 2) (C ^ 2) =
      C ^ 6 * leftCubicNormalizedZMod t by
    simp [leftCubicZMod, leftCubicNormalizedZMod]; ring, hroot, mul_zero]

private theorem right_scaled_root_pp {M : ℕ} (t C : ZMod M)
    (hroot : rightCubicNormalizedZMod t = 0) :
    rightCubicZMod (t * C ^ 2) (C ^ 2) = 0 := by
  rw [show rightCubicZMod (t * C ^ 2) (C ^ 2) =
      C ^ 6 * rightCubicNormalizedZMod t by
    simp [rightCubicZMod, rightCubicNormalizedZMod]; ring, hroot, mul_zero]

private theorem left_scaled_correction_pp {M : ℕ} (t C : ZMod M) :
    leftCorrectionZMod (t * C ^ 2) (C ^ 2) =
      C ^ 4 * leftCorrectionNormalizedZMod t := by
  simp [leftCorrectionZMod, leftCorrectionNormalizedZMod]; ring

private theorem right_scaled_correction_pp {M : ℕ} (t C : ZMod M) :
    rightCorrectionZMod (t * C ^ 2) (C ^ 2) =
      C ^ 4 * rightCorrectionNormalizedZMod t := by
  simp [rightCorrectionZMod, rightCorrectionNormalizedZMod]; ring

theorem nonempty_primePowerSolution_sevenV {q e : ℕ} (_hq : Nat.Prime q)
    (_he : 0 < e) (row : EndpointRoutingRow) :
    Nonempty (AwayRoutingPrimePowerSolution (q ^ e) row .sevenV) := by
  cases row with
  | y => exact ⟨⟨1, 0, 0, 1, isUnit_one, rfl, isUnit_one, rfl, by
      norm_num [AwayFirstCoordinatePrimePowerEquation,
        AwayFirstCoordinateLocalEquation]⟩⟩
  | z => exact ⟨⟨-1, 0, 1, 0, isUnit_one, rfl, isUnit_one.neg, rfl, by
      simp [AwayFirstCoordinatePrimePowerEquation, AwayFirstCoordinateLocalEquation]; ring⟩⟩
  | sum => exact ⟨⟨-1, 0, 1, -1, ⟨isUnit_one, isUnit_one.neg⟩, by
      simp [AwayEndpointPrimePowerEquation, AwayEndpointLocalEquation],
      isUnit_one.neg, rfl, by
      simp [AwayFirstCoordinatePrimePowerEquation, AwayFirstCoordinateLocalEquation]; ring⟩⟩

theorem nonempty_primePowerSolution_leftCubic_of_root {q e : ℕ}
    (hq : Nat.Prime q) (hq7 : q ≠ 7) (he : 0 < e) (t : ZMod (q ^ e))
    (hroot : leftCubicNormalizedZMod t = 0) (row : EndpointRoutingRow) :
    Nonempty (AwayRoutingPrimePowerSolution (q ^ e) row .leftCubic) := by
  let L := leftCorrectionNormalizedZMod t
  have hL : IsUnit L := leftCorrection_isUnit_of_leftCubic_eq_zero_primePower
    hq hq7 he t hroot
  have h49 := fortyNine_isUnit_zmod_primePower hq hq7 he
  cases row with
  | y =>
      let C : ZMod (q ^ e) := -49 * L
      have hC : IsUnit C := h49.neg.mul hL
      exact ⟨⟨t*C^2, C^2, 0, C^5, hC.pow 5, rfl, hC.pow 2,
        left_scaled_root_pp t C hroot, by
          simp only [AwayFirstCoordinatePrimePowerEquation,
            AwayFirstCoordinateLocalEquation]
          rw [left_scaled_correction_pp]; dsimp [C, L]; ring⟩⟩
  | z =>
      let C : ZMod (q ^ e) := 49 * L
      have hC : IsUnit C := h49.mul hL
      exact ⟨⟨t*C^2, C^2, C^5, 0, hC.pow 5, rfl, hC.pow 2,
        left_scaled_root_pp t C hroot, by
          simp only [AwayFirstCoordinatePrimePowerEquation,
            AwayFirstCoordinateLocalEquation]
          rw [left_scaled_correction_pp]; dsimp [C, L]; ring⟩⟩
  | sum =>
      let C : ZMod (q ^ e) := 49 * L
      have hC : IsUnit C := h49.mul hL
      exact ⟨⟨t*C^2, C^2, C^5, -(C^5), ⟨hC.pow 5, (hC.pow 5).neg⟩,
        by simp [AwayEndpointPrimePowerEquation, AwayEndpointLocalEquation], hC.pow 2,
        left_scaled_root_pp t C hroot, by
          simp only [AwayFirstCoordinatePrimePowerEquation,
            AwayFirstCoordinateLocalEquation]
          rw [left_scaled_correction_pp]; dsimp [C, L]; ring⟩⟩

theorem nonempty_primePowerSolution_rightCubic_of_root {q e : ℕ}
    (hq : Nat.Prime q) (hq7 : q ≠ 7) (he : 0 < e) (t : ZMod (q ^ e))
    (hroot : rightCubicNormalizedZMod t = 0) (row : EndpointRoutingRow) :
    Nonempty (AwayRoutingPrimePowerSolution (q ^ e) row .rightCubic) := by
  let R := rightCorrectionNormalizedZMod t
  have hR : IsUnit R := rightCorrection_isUnit_of_rightCubic_eq_zero_primePower
    hq hq7 he t hroot
  have h49 := fortyNine_isUnit_zmod_primePower hq hq7 he
  cases row with
  | y =>
      let C : ZMod (q ^ e) := 49 * R
      have hC : IsUnit C := h49.mul hR
      exact ⟨⟨t*C^2, C^2, 0, C^5, hC.pow 5, rfl, hC.pow 2,
        right_scaled_root_pp t C hroot, by
          simp only [AwayFirstCoordinatePrimePowerEquation,
            AwayFirstCoordinateLocalEquation]
          rw [right_scaled_correction_pp]; dsimp [C, R]; ring⟩⟩
  | z =>
      let C : ZMod (q ^ e) := -49 * R
      have hC : IsUnit C := h49.neg.mul hR
      exact ⟨⟨t*C^2, C^2, C^5, 0, hC.pow 5, rfl, hC.pow 2,
        right_scaled_root_pp t C hroot, by
          simp only [AwayFirstCoordinatePrimePowerEquation,
            AwayFirstCoordinateLocalEquation]
          rw [right_scaled_correction_pp]; dsimp [C, R]; ring⟩⟩
  | sum =>
      let C : ZMod (q ^ e) := -49 * R
      have hC : IsUnit C := h49.neg.mul hR
      exact ⟨⟨t*C^2, C^2, C^5, -(C^5), ⟨hC.pow 5, (hC.pow 5).neg⟩,
        by simp [AwayEndpointPrimePowerEquation, AwayEndpointLocalEquation], hC.pow 2,
        right_scaled_root_pp t C hroot, by
          simp only [AwayFirstCoordinatePrimePowerEquation,
            AwayFirstCoordinateLocalEquation]
          rw [right_scaled_correction_pp]; dsimp [C, R]; ring⟩⟩

end DkMath.FLT.Seven
