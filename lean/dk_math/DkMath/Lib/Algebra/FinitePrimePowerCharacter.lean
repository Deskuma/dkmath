/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Nat.Prime.Basic

#print "file: DkMath.Lib.Algebra.FinitePrimePowerCharacter"

/-!
# p 冪濃度の群に値を持つ準同型の像と核商

非自明な値があれば像の指数は正。野生慣性や分岐の消滅は仮定しない。
-/
namespace DkMath.Lib.Algebra.FinitePrimePowerCharacter
variable {Γ A : Type*} [Group Γ] [Group A] (f : Γ →* A)

/-- 同じ準同型の核商と実際の像の濃度は一致する。 -/
theorem card_quotient_kernel : Nat.card (Γ ⧸ f.ker) = Nat.card f.range :=
  Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv

/-- 値域の濃度 p^m から、像と核商の同じ濃度 p^s を内部計算する。 -/
theorem image_profile {p m : ℕ} (hp : p.Prime) (hA : Nat.card A = p ^ m) :
    ∃ s ≤ m, Nat.card f.range = p ^ s ∧ Nat.card (Γ ⧸ f.ker) = p ^ s ∧ f.ker.index = p ^ s := by
  have hd : Nat.card f.range ∣ p ^ m := hA ▸ Subgroup.card_subgroup_dvd_card f.range
  obtain ⟨s, hs, hc⟩ := (Nat.dvd_prime_pow hp).mp hd
  exact ⟨s, hs, hc, (card_quotient_kernel f).trans hc, (Subgroup.index_ker f).trans hc⟩

/-- 非自明な同じ準同型では s≥1。像と開核候補の指数を取り違えない。 -/
theorem nontrivial_image_profile {p m : ℕ} (hp : p.Prime) (hA : Nat.card A = p ^ m)
    (hf : ∃ g, f g ≠ 1) :
    ∃ s, 1 ≤ s ∧ s ≤ m ∧ Nat.card f.range = p ^ s ∧
      Nat.card (Γ ⧸ f.ker) = p ^ s ∧ f.ker.index = p ^ s := by
  obtain ⟨s, hs, hc, hq, hi⟩ := image_profile f hp hA
  have hne : Nat.card f.range ≠ 1 := by
    intro h
    have hsub := (Nat.card_eq_one_iff_unique.mp h).1
    obtain ⟨g, hg⟩ := hf
    exact hg (congrArg Subtype.val (hsub.elim (⟨f g, ⟨g, rfl⟩⟩ : f.range) 1))
  have hs0 : s ≠ 0 := by intro h; exact hne (by rw [hc, h, pow_zero])
  exact ⟨s, by omega, hs, hc, hq, hi⟩

end DkMath.Lib.Algebra.FinitePrimePowerCharacter
