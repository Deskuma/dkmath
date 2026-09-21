/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

namespace DkMath.FLT.Seven

noncomputable section

def scratchPhaseBeta {K : Type*} [Field K] (r : K) (n : ℕ) : K :=
  1 + r ^ n + (r ^ n)⁻¹

def scratchPhaseKummer {K : Type*} [Field K] (r : K) (n : ℕ) : K :=
  scratchPhaseBeta r n * (1 + scratchPhaseBeta r n)

theorem scratch_phase_kummer_one
    {K : Type*} [Field K] (r : K) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    scratchPhaseKummer r 2 * (1 + r) ^ 7 =
      - (scratchPhaseKummer r 1) ^ 2 := by
  have hr0 : r ≠ 0 := by
    intro h
    rw [h] at hr7
    norm_num at hr7
  have hsum : r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1 = 0 := by
    have hprod : (r - 1) * (r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1) = 0 := by
      linear_combination hr7
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hr1)
  have hr1i : r⁻¹ = r ^ 6 := by
    field_simp [hr0]
    rw [hr7]
  have hr2i : (r ^ 2)⁻¹ = r ^ 5 := by
    field_simp [hr0]
    rw [hr7]
  simp only [scratchPhaseKummer, scratchPhaseBeta, pow_one]
  rw [hr1i, hr2i]
  ring_nf
  have hp8 : r ^ 8 = r := by
    calc r ^ 8 = r ^ 7 * r := by ring
      _ = r := by rw [hr7, one_mul]
  have hp9 : r ^ 9 = r ^ 2 := by
    calc r ^ 9 = r ^ 7 * r ^ 2 := by ring
      _ = r ^ 2 := by rw [hr7, one_mul]
  have hp10 : r ^ 10 = r ^ 3 := by
    calc r ^ 10 = r ^ 7 * r ^ 3 := by ring
      _ = r ^ 3 := by rw [hr7, one_mul]
  have hp11 : r ^ 11 = r ^ 4 := by
    calc r ^ 11 = r ^ 7 * r ^ 4 := by ring
      _ = r ^ 4 := by rw [hr7, one_mul]
  have hp12 : r ^ 12 = r ^ 5 := by
    calc r ^ 12 = r ^ 7 * r ^ 5 := by ring
      _ = r ^ 5 := by rw [hr7, one_mul]
  have hp13 : r ^ 13 = r ^ 6 := by
    calc r ^ 13 = r ^ 7 * r ^ 6 := by ring
      _ = r ^ 6 := by rw [hr7, one_mul]
  have hp14 : r ^ 14 = 1 := by
    calc r ^ 14 = r ^ 7 * r ^ 7 := by ring
      _ = 1 := by simp [hr7]
  have hp15 : r ^ 15 = r := by
    calc r ^ 15 = r ^ 7 * r ^ 8 := by ring
      _ = r := by rw [hr7, hp8, one_mul]
  have hp16 : r ^ 16 = r ^ 2 := by
    calc r ^ 16 = r ^ 7 * r ^ 9 := by ring
      _ = r ^ 2 := by rw [hr7, hp9, one_mul]
  have hp17 : r ^ 17 = r ^ 3 := by
    calc r ^ 17 = r ^ 7 * r ^ 10 := by ring
      _ = r ^ 3 := by rw [hr7, hp10, one_mul]
  have hp18 : r ^ 18 = r ^ 4 := by
    calc r ^ 18 = r ^ 7 * r ^ 11 := by ring
      _ = r ^ 4 := by rw [hr7, hp11, one_mul]
  have hp19 : r ^ 19 = r ^ 5 := by
    calc r ^ 19 = r ^ 7 * r ^ 12 := by ring
      _ = r ^ 5 := by rw [hr7, hp12, one_mul]
  have hp24 : r ^ 24 = r ^ 3 := by
    calc r ^ 24 = r ^ 21 * r ^ 3 := by ring
      _ = r ^ 3 := by rw [show r ^ 21 = 1 by
        calc r ^ 21 = (r ^ 7) ^ 3 := by ring
          _ = 1 := by rw [hr7, one_pow], one_mul]
  simp only [hr7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16,
    hp17, hp18, hp19, hp24]
  linear_combination 240 * hsum

end
end DkMath.FLT.Seven
