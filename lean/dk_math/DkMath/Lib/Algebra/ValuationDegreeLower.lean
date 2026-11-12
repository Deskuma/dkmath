/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.ValuationPoleSpace

#print "file: DkMath.Lib.Algebra.ValuationDegreeLower"

/-!
# 極位数の合同類で独立性を検出する

[DkMath.Lib] 係数体の値の指数がdの倍数なら、異なるmod dの指数を持つ関数は独立。
有限和の最大項は一つだけなので相殺しない。分離性や標数0は要求しない。
-/
namespace DkMath.Lib.Algebra.ValuationDegreeLower
open WithZero
variable {E F : Type*} [Field E] [Field F] [Algebra E F]

/-- [DkMath.Lib] 異なる付値合同類を持つ有限族は係数体上独立である。
係数を掛けても値の合同類が重ならず、唯一の最大項が零和を排除する。 -/
theorem linearIndependent_of_value_classes (v : Valuation F ℤᵐ⁰) (d : ℤ)
    (hscalar : ∀ a : E, a ≠ 0 → ∃ m : ℤ, v (algebraMap E F a) = exp (d * m))
    {n : ℕ} (u : Fin n → F) (t : Fin n → ℤ) (hu : ∀ i, v (u i) = exp (t i))
    (hsep : ∀ i j : Fin n, ∀ r s : ℤ, d * r + t i = d * s + t j → i = j) :
    LinearIndependent E u := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha
  by_contra! hne
  obtain ⟨i, hi⟩ := hne
  let S : Finset (Fin n) := Finset.univ.filter fun i => a i ≠ 0
  have hS : S.Nonempty := ⟨i, by simp [S, hi]⟩
  obtain ⟨j, hj, hmax⟩ := S.exists_max_image (fun i => v (a i • u i)) hS
  have haj : a j ≠ 0 := (Finset.mem_filter.mp hj).2
  have huj : u j ≠ 0 := v.ne_zero_iff.mp (by rw [hu]; exact exp_ne_zero)
  have hvj : v (a j • u j) ≠ 0 := v.ne_zero_iff.mpr (smul_ne_zero haj huj)
  have hsum : v (∑ i, a i • u i) = v (a j • u j) := by
    apply v.map_sum_eq_of_lt (Finset.mem_univ j)
    intro l hl
    have hlj : l ≠ j := by simpa only [Finset.mem_singleton] using (Finset.mem_sdiff.mp hl).2
    by_cases hal0 : a l = 0
    · rw [hal0, zero_smul, map_zero]
      exact lt_of_le_of_ne zero_le (Ne.symm hvj)
    have hal : a l ≠ 0 := hal0
    have hlS : l ∈ S := by simp [S, hal]
    apply lt_of_le_of_ne (hmax l hlS)
    intro heq
    obtain ⟨r, hr⟩ := hscalar (a l) hal
    obtain ⟨s, hs⟩ := hscalar (a j) haj
    simp only [Algebra.smul_def, map_mul, hr, hs, hu, ← exp_add, exp_inj] at heq
    exact hlj (hsep l j r s heq)
  rw [ha, map_zero] at hsum
  exact hvj hsum.symm

end DkMath.Lib.Algebra.ValuationDegreeLower
