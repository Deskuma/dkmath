/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.RingTheory.Valuation.ValuationSubring

#print "file: DkMath.Lib.Algebra.ValuationSeparatedRoots"

/-!
# NOTE-031-002C4: 単元の差を持つ二根のどちらに近づくか

v(a−b)=1なら、tが両根へ同時に近づくことはない。
v((t−a)(t−b))<1なら、ちょうど一方との差が1未満、他方との差は1となる。
二根が付値環に属せばtも整となる。楕円曲線・素数・torsion・完備性は不要である。
-/
namespace DkMath.Lib.Algebra.ValuationSeparatedRoots
variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

/-- 第一根へ近づくと、単元で分離した第二根との差の付値は厳密に1である。 -/
theorem right_eq_one_of_near_left (v : Valuation K Γ₀) {a b t : K}
    (hsep : v (a - b) = 1) (ha : v (t - a) < 1) : v (t - b) = 1 := by
  have he : t - b = (t - a) + (a - b) := by ring
  rw [he, Valuation.map_add_eq_of_lt_right _ (by rwa [hsep]), hsep]

/-- 第二根へ近づく場合の対称な結論。 -/
theorem left_eq_one_of_near_right (v : Valuation K Γ₀) {a b t : K}
    (hsep : v (a - b) = 1) (hb : v (t - b) < 1) : v (t - a) = 1 :=
  right_eq_one_of_near_left v (by rwa [Valuation.map_sub_swap]) hb

/-- 二根の差が単元なら、小さい積はちょうど一方の根への近さを与える。
近くない側の付値まで1と確定させ、単なる選言より強い排他性を保持する。 -/
theorem branches_of_small_product (v : Valuation K Γ₀) {a b t : K}
    (hsep : v (a - b) = 1) (hp : v ((t - a) * (t - b)) < 1) :
    (v (t - a) < 1 ∧ v (t - b) = 1) ∨ (v (t - a) = 1 ∧ v (t - b) < 1) := by
  by_cases ha : v (t - a) < 1
  · exact Or.inl ⟨ha, right_eq_one_of_near_left v hsep ha⟩
  · have hb : v (t - b) < 1 := by
      by_contra hn
      have hle : 1 ≤ v (t - a) * v (t - b) := by
        calc 1 = 1 * 1 := (one_mul _).symm
          _ ≤ v (t - a) * v (t - b) := mul_le_mul' (le_of_not_gt ha) (le_of_not_gt hn)
      rw [← map_mul] at hle
      exact (not_lt.mpr hle) hp
    exact Or.inr ⟨left_eq_one_of_near_right v hsep hb, hb⟩

/-- 二つの枝への近さは同時には成立しない。 -/
theorem not_both_near (v : Valuation K Γ₀) {a b t : K} (hsep : v (a - b) = 1) :
    ¬ (v (t - a) < 1 ∧ v (t - b) < 1) := by
  rintro ⟨ha, hb⟩
  rw [right_eq_one_of_near_left v hsep ha] at hb
  exact lt_irrefl _ hb

/-- 整な二根の一方へ近づく元は整となる。積の小ささから近さを先に証明する。
この補題が、傾きの整性のための独立したモニック二次式の評価を代替する。 -/
theorem mem_of_small_product (A : ValuationSubring K) {a b t : K} (ha : a ∈ A) (hb : b ∈ A)
    (hsep : A.valuation (a - b) = 1) (hp : A.valuation ((t - a) * (t - b)) < 1) : t ∈ A := by
  rcases branches_of_small_product A.valuation hsep hp with h | h
  · have hd : t - a ∈ A := (A.valuation_le_one_iff _).mp h.1.le
    have ht : t - a + a ∈ A := A.toSubring.add_mem hd ha
    simpa only [sub_add_cancel] using ht
  · have hd : t - b ∈ A := (A.valuation_le_one_iff _).mp h.2.le
    have ht : t - b + b ∈ A := A.toSubring.add_mem hd hb
    simpa only [sub_add_cancel] using ht

end DkMath.Lib.Algebra.ValuationSeparatedRoots
