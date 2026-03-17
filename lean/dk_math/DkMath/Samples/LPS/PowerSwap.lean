/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- LPS module: Lander, Parkin, and Selfridge conjecture research

import Mathlib

namespace DkMath
namespace Samples

/-- Power-swap relation: `a^b = b^a`. -/
def PowerSwap (a b : ℕ) : Prop := a ^ b = b ^ a

/--
対角線上の `a ^ a = a ^ a` より PowerSwap が成り立つ。
-/
theorem powerSwap_refl (a : ℕ) : PowerSwap a a := by
  unfold PowerSwap
  rfl

/--
PowerSwap は对称関係である。
-/
theorem powerSwap_symm {a b : ℕ} (h : PowerSwap a b) : PowerSwap b a := by
  unfold PowerSwap at *
  simpa [eq_comm] using h

/--
古典的な非自明例：`2^4 = 4^2 = 16`。
反転指数交点の最初の標本。
-/
theorem powerSwap_two_four : PowerSwap 2 4 := by
  unfold PowerSwap
  norm_num

/--
`2^4 = 4^2` の対称版。
-/
theorem powerSwap_four_two : PowerSwap 4 2 := by
  exact powerSwap_symm powerSwap_two_four

/-- 非自明なペア `(2,4)` と `(4,2)` は同時に成立する。 -/
theorem powerSwap_pair_two_four :
    PowerSwap 2 4 ∧ PowerSwap 4 2 := by
  exact ⟨powerSwap_two_four, powerSwap_four_two⟩

/-- 非自明解の存在。 -/
theorem exists_powerSwap_nontrivial :
    ∃ a b : ℕ, a ≠ b ∧ PowerSwap a b := by
  refine ⟨2, 4, by decide, powerSwap_two_four⟩

/--
`PowerSwap a 1` なら `a = 1`
`a^1 = 1^a = 1` なので、a は 1 でなければならない。
-/
theorem powerSwap_with_one {a : ℕ} (h : PowerSwap a 1) :
    a = 1 := by
  simp [PowerSwap] at h
  omega

/-! ## PowerSwap の簡易性質 -/

/-- `PowerSwap a b` なら `PowerSwap b a`。 -/
theorem powerSwap_iff_symm {a b : ℕ} :
    PowerSwap a b ↔ PowerSwap b a := by
  constructor
  · exact powerSwap_symm
  · exact powerSwap_symm

end Samples
end DkMath
