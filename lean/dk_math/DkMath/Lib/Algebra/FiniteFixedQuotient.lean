/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card

#print "file: DkMath.Lib.Algebra.FiniteFixedQuotient"

/-!
# 有限群上の作用差の像と固定点の個数

`φ-1` の像が `K` に入れば、核・像の濃度公式から
`#T ≤ #Fix(φ) * #K`。巡回性や特性方程式は不要である。
-/

namespace DkMath.Lib.Algebra.FiniteFixedQuotient

variable {G : Type*} [AddCommGroup G] [Finite G]

/-- 作用差の吸収先の濃度から、実際の固定部分群の濃度を下から抑える。 -/
theorem card_le_card_fixed_mul (φ : G →+ G) (K : AddSubgroup G)
    (habs : ∀ x, φ x - x ∈ K) :
    Nat.card G ≤ Nat.card (φ - AddMonoidHom.id G).ker * Nat.card K := by
  let δ := φ - AddMonoidHom.id G
  have hr : δ.range ≤ K := by
    rintro _ ⟨x, rfl⟩
    exact habs x
  have hrc : Nat.card δ.range ≤ Nat.card K :=
    Nat.card_le_card_of_injective (AddSubgroup.inclusion hr) (AddSubgroup.inclusion_injective hr)
  have he : Nat.card G = Nat.card δ.range * Nat.card δ.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup δ.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange δ).toEquiv]
  calc
    Nat.card G = Nat.card δ.ker * Nat.card δ.range := he.trans (Nat.mul_comm _ _)
    _ ≤ Nat.card δ.ker * Nat.card K := Nat.mul_le_mul_left _ hrc

/-- 位数 `n²` の群で、差を位数 `n` の群へ吸収すれば固定点は少なくとも `n` 個。 -/
theorem le_card_fixed_of_card_square (φ : G →+ G) (K : AddSubgroup G)
    {n : ℕ} (hn : 0 < n) (hG : Nat.card G = n ^ 2) (hK : Nat.card K = n)
    (habs : ∀ x, φ x - x ∈ K) : n ≤ Nat.card (φ - AddMonoidHom.id G).ker := by
  have h := card_le_card_fixed_mul φ K habs
  rw [hG, hK, pow_two] at h
  exact Nat.le_of_mul_le_mul_right h hn

end DkMath.Lib.Algebra.FiniteFixedQuotient
