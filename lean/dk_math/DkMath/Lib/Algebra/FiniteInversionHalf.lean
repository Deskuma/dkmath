/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

#print "file: DkMath.Lib.Algebra.FiniteInversionHalf"

/-!
# 有限群の反転対から一方だけを数える和

[DkMath.Lib] 非零元をsと−sへ互いに交わらず分割する集合を半集合と呼ぶ。
反転不変な関数の和は、半集合の代表の選び方に依存しない。
和を2で割る証明を避けるため、値の群の標数2も許す。
-/
namespace DkMath.Lib.Algebra.FiniteInversionHalf
open scoped BigOperators
variable {G B : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] [AddCommMonoid B]

/-- [DkMath.Lib] 同じ有限群の非零元の反転対を一方ずつ取った集合という条件。 -/
def IsHalf (s : Finset G) : Prop :=
  s ∪ s.image Neg.neg = Finset.univ.erase 0 ∧ Disjoint s (s.image Neg.neg)

private lemma nonzero {s : Finset G} (hs : IsHalf s) {x : G} (hx : x ∈ s) : x ≠ 0 := by
  have h := hs.1 ▸ (Finset.mem_union_left (s.image Neg.neg) hx)
  exact (Finset.mem_erase.mp h).1

private lemma not_neg {s : Finset G} (hs : IsHalf s) {x : G} (hx : x ∈ s) : -x ∉ s := by
  intro hh
  exact (Finset.disjoint_left.mp hs.2) hh (Finset.mem_image.mpr ⟨x,hx,rfl⟩)

private lemma one_side {s : Finset G} (hs : IsHalf s) {x : G} (hx : x ≠ 0) : x ∈ s ∨ -x ∈ s := by
  have h : x ∈ s ∪ s.image Neg.neg := hs.1.symm ▸ (Finset.mem_erase.mpr ⟨hx,Finset.mem_univ _⟩)
  rcases Finset.mem_union.mp h with h | h
  · exact Or.inl h
  · obtain ⟨y,hy,he⟩ := Finset.mem_image.mp h
    exact Or.inr (by simpa only [← he, neg_neg] using hy)

/-- [DkMath.Lib] 反転不変な関数の半集合和は代表の選択に依存しない。2を約分しない。 -/
theorem sum_eq {s t : Finset G} (hs : IsHalf s) (ht : IsHalf t) (f : G → B)
    (hf : ∀ x, f (-x) = f x) : ∑ x ∈ s, f x = ∑ x ∈ t, f x := by
  have hd : (s \ t).image Neg.neg = t \ s := by
    ext x
    simp only [Finset.mem_image, Finset.mem_sdiff]
    constructor
    · rintro ⟨y,⟨hys,hyt⟩,rfl⟩
      refine ⟨(one_side ht (nonzero hs hys)).resolve_left hyt, not_neg hs hys⟩
    · rintro ⟨hxt,hxs⟩
      refine ⟨-x,⟨(one_side hs (nonzero ht hxt)).resolve_left hxs, not_neg ht hxt⟩,neg_neg x⟩
  have hsd : ∑ x ∈ s \ t, f x = ∑ x ∈ t \ s, f x := by
    rw [← hd, Finset.sum_image (fun _ _ _ _ he => neg_injective he)]
    exact Finset.sum_congr rfl (fun x _ => (hf x).symm)
  rw [← Finset.sum_inter_add_sum_sdiff s t f, ← Finset.sum_inter_add_sum_sdiff t s f,
    Finset.inter_comm t s, hsd]

/-- [DkMath.Lib] ZMod nの1,…,⌊n/2⌋を同じ加法同型で移した巡回半集合。 -/
noncomputable def cyclicHalf {n : ℕ} (e : ZMod n ≃+ G) : Finset G :=
  (Finset.Icc 1 (n / 2)).image (fun j : ℕ => e (j : ZMod n))

/-- [DkMath.Lib] 奇数nの巡回半集合は実際に全非零反転対を一度ずつ数える。 -/
theorem cyclicHalf_isHalf {n : ℕ} (hn : Odd n) (e : ZMod n ≃+ G) : IsHalf (cyclicHalf e) := by
  classical
  have hn0 := hn.pos
  have : NeZero n := ⟨hn0.ne'⟩
  have hm : n / 2 < n := Nat.div_lt_self hn0 (by decide)
  have hi {j k : ℕ} (hj : j < n) (hk : k < n) (he : e (j : ZMod n) = e (k : ZMod n)) : j = k := by
    have he' := congrArg ZMod.val (e.injective he)
    simpa only [ZMod.val_natCast_of_lt hj, ZMod.val_natCast_of_lt hk] using he'
  have hz {j : ℕ} (hj : 0 < j) (hjn : j < n) : e (j : ZMod n) ≠ 0 := by
    intro he
    have hh := hi hjn hn0 (he.trans (by simpa only [Nat.cast_zero] using e.map_zero.symm))
    omega
  constructor
  · ext x
    constructor
    · intro hx
      refine Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
        exact hz (Finset.mem_Icc.mp hj).1 (lt_of_le_of_lt (Finset.mem_Icc.mp hj).2 hm)
      · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy
        exact neg_ne_zero.mpr (hz (Finset.mem_Icc.mp hj).1 (lt_of_le_of_lt (Finset.mem_Icc.mp hj).2 hm))
    · intro hx
      have hx0 := (Finset.mem_erase.mp hx).1
      let z := e.symm x
      have hzx : e z = x := e.apply_symm_apply x
      have hz0 : z ≠ 0 := by intro h; apply hx0; rw [← hzx,h,e.map_zero]
      have hj0 : 0 < z.val := by
        have hh : z.val ≠ 0 := fun h => hz0 ((ZMod.val_eq_zero z).mp h)
        omega
      have hjn : z.val < n := ZMod.val_lt z
      by_cases hj : z.val ≤ n / 2
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨z.val,Finset.mem_Icc.mpr ⟨hj0,hj⟩,
          (congrArg e (ZMod.natCast_zmod_val z)).trans hzx⟩)
      · have hk : n - z.val ∈ Finset.Icc 1 (n / 2) := by
          obtain ⟨m,hm⟩ := hn
          simp only [Finset.mem_Icc]; omega
        have he : -e ((n - z.val : ℕ) : ZMod n) = x := by
          rw [Nat.cast_sub hjn.le, ZMod.natCast_self, zero_sub, map_neg, neg_neg, ZMod.natCast_zmod_val]
          exact hzx
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e ((n - z.val : ℕ) : ZMod n),
          Finset.mem_image.mpr ⟨n-z.val,hk,rfl⟩,he⟩)
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hy
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hy
    have hsum : ((j+k : ℕ) : ZMod n) = 0 := by
      apply e.injective
      rw [Nat.cast_add,map_add,e.map_zero]
      exact (eq_neg_iff_add_eq_zero.mp he.symm)
    have hd : n ∣ j+k := (ZMod.natCast_eq_zero_iff (j+k) n).mp hsum
    have hj' := Finset.mem_Icc.mp hj
    have hk' := Finset.mem_Icc.mp hk
    have hlt : j+k < n := by obtain ⟨m,hm⟩ := hn; omega
    exact (not_le.mpr hlt) (Nat.le_of_dvd (by omega) hd)

/-- [DkMath.Lib] 任意の半集合の和を巡回生成元の正の半周の和へ書き換える。
代表選択の差は反転不変性だけで吸収し、値の群の2可逆性を要求しない。 -/
theorem sum_eq_cyclic {n : ℕ} (hn : Odd n) (e : ZMod n ≃+ G) {s : Finset G}
    (hs : IsHalf s) (f : G → B) (hf : ∀ x, f (-x) = f x) :
    ∑ x ∈ s, f x = ∑ j ∈ Finset.Icc 1 (n/2), f (e (j : ZMod n)) := by
  classical
  rw [sum_eq hs (cyclicHalf_isHalf hn e) f hf, cyclicHalf]
  apply Finset.sum_image
  intro j hj k hk he
  have hn0 := hn.pos
  have : NeZero n := ⟨hn0.ne'⟩
  have hm : n/2 < n := Nat.div_lt_self hn0 (by decide)
  have he' := congrArg ZMod.val (e.injective he)
  simpa only [ZMod.val_natCast_of_lt (lt_of_le_of_lt (Finset.mem_Icc.mp hj).2 hm),
    ZMod.val_natCast_of_lt (lt_of_le_of_lt (Finset.mem_Icc.mp hk).2 hm)] using he'

end DkMath.Lib.Algebra.FiniteInversionHalf
