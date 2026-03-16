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

/--
`1^a = a^1 = a` より、1 を片側に持つ場合は (a=1) のみ成り立つ。
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
