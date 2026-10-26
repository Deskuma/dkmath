/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.FiniteInversionHalf

#print "file: DkMath.Lib.Algebra.FiniteInversionHalfTransport"

/-!
# 同じ有限核の加法同型に沿った半集合の輸送

[DkMath.Lib] 還元写像が単射なら、元の核と還元像は加法同型となる。
この同型で半集合を運び、反転不変なモーメントの和を保つ。
還元像で番号を振り直した半集合との違いは代表独立性で吸収する。
-/
namespace DkMath.Lib.Algebra.FiniteInversionHalf
open scoped BigOperators
variable {G H B : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
  [DecidableEq G] [DecidableEq H] [AddCommMonoid B]

/-- [DkMath.Lib] 同じ有限群の加法同型で半集合を運ぶ。反転との可換性を保持する。 -/
theorem IsHalf.image {s : Finset G} (hs : IsHalf s) (e : G ≃+ H) : IsHalf (s.image e) := by
  have hn : (s.image e).image Neg.neg = (s.image Neg.neg).image e := by
    rw [Finset.image_image,Finset.image_image]
    congr 1
    funext x
    exact (e.map_neg x).symm
  constructor
  · rw [hn,← Finset.image_union,hs.1]
    ext y
    simp only [Finset.mem_image,Finset.mem_erase,Finset.mem_univ,and_true]
    constructor
    · rintro ⟨x,hx,rfl⟩ he
      exact hx (e.injective (he.trans e.map_zero.symm))
    · intro hy
      exact ⟨e.symm y,(fun he => hy (by rw [← e.apply_symm_apply y,he,e.map_zero])),e.apply_symm_apply y⟩
  · rw [hn]
    apply Finset.disjoint_left.mpr
    intro y hy hy'
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hy
    obtain ⟨x',hx',he'⟩ := Finset.mem_image.mp hy'
    exact (Finset.disjoint_left.mp hs.2) hx ((e.injective (he'.trans he.symm)) ▸ hx')

/-- [DkMath.Lib] 同じ核の加法同型を介して、任意の二つの半集合上のモーメント和を比較する。
値の群で2を割らず、剰余で代表が変わっても同じ和を得る。 -/
theorem sum_eq_equiv {s : Finset G} {t : Finset H} (hs : IsHalf s) (ht : IsHalf t)
    (e : G ≃+ H) (f : H → B) (hf : ∀ x, f (-x) = f x) :
    ∑ x ∈ s, f (e x) = ∑ y ∈ t, f y := by
  rw [← sum_eq (hs.image e) ht f hf,Finset.sum_image (fun _ _ _ _ h => e.injective h)]

end DkMath.Lib.Algebra.FiniteInversionHalf
