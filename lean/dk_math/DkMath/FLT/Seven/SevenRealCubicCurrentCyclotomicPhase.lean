/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicCurrentCyclotomicAddress

#print "file: DkMath.FLT.Seven.SevenRealCubicCurrentCyclotomicPhase"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open scoped NumberField

namespace SevenRealCubic

set_option linter.style.longLine false

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! The three possible real traces of a nontrivial seventh-root phase. -/

def currentBeta (r : (ZMod q)ˣ) (n : ℕ) : ZMod q :=
  1 + (r : ZMod q) ^ n + ((r : ZMod q) ^ n)⁻¹

@[simp] theorem currentBeta_one (r : (ZMod q)ˣ) :
    currentBeta r 1 = 1 + (r : ZMod q) + ((r : ZMod q)⁻¹) := by
  simp [currentBeta]

@[simp] theorem currentBeta_two (r : (ZMod q)ˣ) :
    currentBeta r 2 = 1 + (r : ZMod q) ^ 2 + ((r : ZMod q) ^ 2)⁻¹ := by
  rfl

@[simp] theorem currentBeta_three (r : (ZMod q)ˣ) :
    currentBeta r 3 = 1 + (r : ZMod q) ^ 3 + ((r : ZMod q) ^ 3)⁻¹ := by
  rfl

private theorem current_beta_cubic
    [Fact (Nat.Prime q)] (r : (ZMod q)ˣ) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    currentBeta r 1 ^ 3 - 2 * currentBeta r 1 ^ 2 -
        currentBeta r 1 + 1 = 0 := by
  let t : ZMod q := (r : ZMod q)
  have ht0 : t ≠ 0 := r.ne_zero
  have ht7 : t ^ 7 = 1 := congrArg Units.val hr7
  have ht1 : t ≠ 1 := by
    intro h
    apply hr1
    exact Units.ext h
  have hsum :
      t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 +
          t ^ 2 + t + 1 = 0 := by
    have hprod :
        (t - 1) * (t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 +
          t ^ 2 + t + 1) = 0 := by
      linear_combination ht7
    exact (mul_eq_zero.mp hprod).resolve_left
      (sub_ne_zero.mpr ht1)
  simp only [currentBeta, pow_one]
  change
    (1 + (r : ZMod q) + ((r : ZMod q)⁻¹)) ^ 3 -
        2 * (1 + (r : ZMod q) + ((r : ZMod q)⁻¹)) ^ 2 -
        (1 + (r : ZMod q) + ((r : ZMod q)⁻¹)) + 1 = 0
  field_simp [ht0]
  linear_combination hsum

private theorem current_beta_factorization
    [Fact (Nat.Prime q)] (r : (ZMod q)ˣ) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1)
    (x : ZMod q) :
    (x - currentBeta r 1) * (x - currentBeta r 2) *
        (x - currentBeta r 3) =
      x ^ 3 - 2 * x ^ 2 - x + 1 := by
  let t : ZMod q := (r : ZMod q)
  have ht0 : t ≠ 0 := r.ne_zero
  have ht7 : t ^ 7 = 1 := congrArg Units.val hr7
  have ht1 : t ≠ 1 := by
    intro h
    apply hr1
    exact Units.ext h
  have hsum :
      t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 +
          t ^ 2 + t + 1 = 0 := by
    have hprod :
        (t - 1) * (t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 +
          t ^ 2 + t + 1) = 0 := by
      linear_combination ht7
    exact (mul_eq_zero.mp hprod).resolve_left
      (sub_ne_zero.mpr ht1)
  have hti : t⁻¹ = t ^ 6 := by
    field_simp [ht0]
    rw [ht7]
  have hti2 : (t ^ 2)⁻¹ = t ^ 5 := by
    field_simp [ht0]
    rw [ht7]
  have hti3 : (t ^ 3)⁻¹ = t ^ 4 := by
    field_simp [ht0]
    rw [ht7]
  simp only [currentBeta, pow_one]
  change
    (x - (1 + t + t⁻¹)) *
        (x - (1 + t ^ 2 + (t ^ 2)⁻¹)) *
        (x - (1 + t ^ 3 + (t ^ 3)⁻¹)) =
      x ^ 3 - 2 * x ^ 2 - x + 1
  rw [hti, hti2, hti3]
  ring_nf
  have ht8 : t ^ 8 = t := by
    calc
      t ^ 8 = t ^ 7 * t := by ring
      _ = t := by rw [ht7, one_mul]
  have ht9 : t ^ 9 = t ^ 2 := by
    calc
      t ^ 9 = t ^ 7 * t ^ 2 := by ring
      _ = t ^ 2 := by rw [ht7, one_mul]
  have ht10 : t ^ 10 = t ^ 3 := by
    calc
      t ^ 10 = t ^ 7 * t ^ 3 := by ring
      _ = t ^ 3 := by rw [ht7, one_mul]
  have ht11 : t ^ 11 = t ^ 4 := by
    calc
      t ^ 11 = t ^ 7 * t ^ 4 := by ring
      _ = t ^ 4 := by rw [ht7, one_mul]
  have ht12 : t ^ 12 = t ^ 5 := by
    calc
      t ^ 12 = t ^ 7 * t ^ 5 := by ring
      _ = t ^ 5 := by rw [ht7, one_mul]
  have ht14 : t ^ 14 = 1 := by
    calc
      t ^ 14 = t ^ 7 * t ^ 7 := by ring
      _ = 1 := by simp [ht7]
  have ht15 : t ^ 15 = t := by
    calc
      t ^ 15 = t ^ 7 * t ^ 8 := by ring
      _ = t := by rw [ht7, ht8, one_mul]
  simp only [ht15, ht14, ht12, ht11, ht10, ht9, ht8, ht7]
  ring_nf
  linear_combination (4 * x - x ^ 2 - 4) * hsum

theorem current_phase_alignment
    [Fact (Nat.Prime q)] (r : (ZMod q)ˣ) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1)
    (hroot : x ^ 3 - 2 * x ^ 2 - x + 1 = 0) :
    ∃ k : Fin 3, x = currentBeta r (k.val + 1) := by
  have hfactor := current_beta_factorization r hr7 hr1 x
  rw [hroot] at hfactor
  rcases mul_eq_zero.mp hfactor with h12 | h3
  · rcases mul_eq_zero.mp h12 with h1 | h2
    · exact ⟨0, sub_eq_zero.mp h1⟩
    · exact ⟨1, sub_eq_zero.mp h2⟩
  · exact ⟨2, sub_eq_zero.mp h3⟩

theorem CurrentMuSevenResidueAddress.phase_alignment
    {q : ℕ} [Fact (Nat.Prime q)]
    (a : CurrentMuSevenResidueAddress q)
    (hroot : (a.evalReal alpha) ^ 3 - 2 * (a.evalReal alpha) ^ 2 -
        a.evalReal alpha + 1 = 0) :
    ∃ k : Fin 3, a.evalReal alpha = currentBeta a.ratio (k.val + 1) := by
  exact current_phase_alignment a.ratio a.ratio_pow_seven
    a.ratio_ne_one hroot

end SevenRealCubic
end
end DkMath.FLT.Seven
