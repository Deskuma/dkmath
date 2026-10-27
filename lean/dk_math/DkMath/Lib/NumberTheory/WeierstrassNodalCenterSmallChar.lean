/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.WeierstrassNodalCenter

#print "file: DkMath.Lib.NumberTheory.WeierstrassNodalCenterSmallChar"

/-!
# 標数2・3での節点中心の一次比較

[DkMath.Lib] 6=0では特異点の `6x²+b₂x+b₄=0` が一次式になる。
同じ反転半核の座標和とtモーメント和を比較し、b₂の非零性で中心を一意にする。
12や1728を約分せず、標数2,3を同じ証明で扱う。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassNodalCenterSmallChar
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassVeluPolynomial
open EllipticNodalTorsion.NodalTorsion WeierstrassNodalFrame
open DkMath.Lib.Algebra.FiniteInversionHalf
open scoped BigOperators
variable {k : Type*} [Field k] [DecidableEq k]

/-- [DkMath.Lib] 6=0でも、同じ奇数巡回核の候補中心は同じ多項式商の特異点のx座標に等しい。
二つの特異点の一次化されたt式と、同じ半核のモーメントを比較する。 -/
theorem candidate_center_eq_singular_of_six_eq_zero (W : WeierstrassCurve k)
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {n : ℕ}
    (hn : Odd n) (h6 : (6 : k) = 0) (e : ZMod n ≃+ G)
    (f : G →+ W.toAffine.Point) (hf : Function.Injective f)
    (s : Finset G) (hs : IsHalf s) {x₀ y₀ α : k}
    (F : Frame W x₀ y₀ α) (hsep : α ≠ -W.a₁ - α)
    (X Y : k) (he : (polynomialModel W s (fun q => (f q).xc) (fun q => (f q).yc)).toAffine.Equation X Y)
    (hsg : ¬ (polynomialModel W s (fun q => (f q).xc) (fun q => (f q).yc)).toAffine.Nonsingular X Y) :
    X = (n : k) * x₀ - ∑ q : G, (f q).xc := by
  let V := polynomialModel W s (fun q => (f q).xc) (fun q => (f q).yc)
  let P := f (e 1)
  let u := tc W x₀ y₀ α P
  let δ := 2 * α + W.a₁
  let z := fun j : ℕ => u ^ j / (1 - u ^ j) ^ 2
  let Z := ∑ j ∈ Finset.Icc 1 (n / 2), z j
  let c := (n : k) * x₀ - ∑ q : G, (f q).xc
  have hd : δ ≠ 0 := by
    intro hh
    apply hsep
    dsimp [δ] at hh
    linear_combination hh
  have hord : addOrderOf P = n :=
    (addOrderOf_injective f hf (e 1)).trans ((e.addOrderOf_eq 1).trans (ZMod.addOrderOf_one n))
  have hcoord (j : ℕ) (hj : j ∈ Finset.Icc 1 (n / 2)) : (f (e (j : ZMod n))).xc = x₀ + δ ^ 2 * z j := by
    have hmul : f (e (j : ZMod n)) = j • P := by
      rw [← Nat.smul_one_eq_cast, map_nsmul, map_nsmul]
    rw [hmul]
    exact nsmul_xc F hsep P hord (Finset.mem_Icc.mp hj).1
      (lt_of_le_of_lt (Finset.mem_Icc.mp hj).2 (Nat.div_lt_self hn.pos (by decide)))
  have hxneg (q : G) : (f (-q)).xc = (f q).xc := by
    rw [map_neg]
    cases f q <;> rfl
  have hfull : (∑ q : G, (f q).xc) = 2 * ∑ q ∈ s, (f q).xc := by
    have hh := Finset.sum_erase_add (Finset.univ : Finset G) (fun q => (f q).xc) (Finset.mem_univ 0)
    rw [← hs.1, Finset.sum_union hs.2, Finset.sum_image (by intro a _ b _ h; exact neg_injective h)] at hh
    simp only [map_zero, hxneg] at hh
    change (∑ q ∈ s, (f q).xc) + (∑ q ∈ s, (f q).xc) + 0 = _ at hh
    linear_combination hh.symm
  have hhalf : (∑ q ∈ s, (f q).xc) = ((n / 2 : ℕ) : k) * x₀ + δ ^ 2 * Z := by
    rw [sum_eq_cyclic hn e hs (fun q => (f q).xc) hxneg]
    dsimp only [Z]
    rw [Finset.sum_congr rfl hcoord, Finset.sum_add_distrib, Finset.sum_const,
      Nat.card_Icc, Finset.mul_sum]
    have hh : n / 2 + 1 - 1 = n / 2 := by omega
    rw [hh, nsmul_eq_mul]
  have hodd : (n : k) = 2 * ((n / 2 : ℕ) : k) + 1 := by
    obtain ⟨m, rfl⟩ := hn
    have hh : (2 * m + 1) / 2 = m := by omega
    rw [hh]
    push_cast
    ring
  have hc : c = x₀ - 2 * δ ^ 2 * Z := by
    dsimp only [c]
    rw [hfull, hhalf]
    linear_combination x₀ * hodd
  obtain ⟨hb2, hb4, -, -⟩ := b_invariants F
  change W.b₂ = δ ^ 2 - 12 * x₀ at hb2
  change W.b₄ = 6 * x₀ ^ 2 - δ ^ 2 * x₀ at hb4
  have hT : (∑ q ∈ s, momentT W (f q).xc) = δ ^ 4 * Z := by
    rw [sum_eq_cyclic hn e hs (fun q => momentT W (f q).xc)
      (fun q => by rw [map_neg]; exact (WeierstrassNodalVelu.point_moments_neg W (f q)).1)]
    dsimp only [Z]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hcoord j hj]
    simp only [momentT, hb2, hb4]
    linear_combination δ ^ 4 * (z j) ^ 2 * h6
  have hsrc : momentT W x₀ = 0 := by
    simp only [momentT, b₂, b₄]
    linear_combination W.a₁ * F.hFY - 2 * F.hFX
  have htarget : momentT V X = 0 := by
    have hsg' : ¬ V.toAffine.Nonsingular X Y := hsg
    have he' : V.toAffine.Equation X Y := he
    rw [nonsingular_iff'] at hsg'
    push Not at hsg'
    obtain ⟨hX, hY⟩ := hsg' he'
    simp only [momentT, b₂, b₄]
    linear_combination V.a₁ * hY - 2 * hX
  have hb := polynomialModel_b_invariants W s (fun q => (f q).xc) (fun q => (f q).yc)
  have h12 : (12 : k) = 0 := by linear_combination 2 * h6
  have hdiff : δ ^ 2 * (X - c) = 0 := by
    change 6 * X ^ 2 + (polynomialModel W s (fun q => (f q).xc) (fun q => (f q).yc)).b₂ * X +
      (polynomialModel W s (fun q => (f q).xc) (fun q => (f q).yc)).b₄ = 0 at htarget
    rw [hb.1, hb.2.1, hT, hb2, hb4] at htarget
    rw [hc]
    linear_combination htarget - (X ^ 2 + x₀ ^ 2) * h6 + (x₀ * X + δ ^ 4 * Z) * h12
  exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left (pow_ne_zero 2 hd))

/-- [DkMath.Lib] 任意標数で、同じ奇数巡回核の候補中心は同じ多項式商の特異点のx座標。
12≠0ではc₄,c₆の二乗・三乗、12=0では特異点の一次化されたt式を使う。
どちらも同じ核、同じ半集合、同じ特異点を保持する。 -/
theorem candidate_center_eq_singular (W : WeierstrassCurve k)
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {n : ℕ}
    (hn : Odd n) (hn0 : (n : k) ≠ 0) (e : ZMod n ≃+ G)
    (f : G →+ W.toAffine.Point) (hf : Function.Injective f)
    (s : Finset G) (hs : IsHalf s) {x₀ y₀ α : k}
    (F : Frame W x₀ y₀ α) (hsep : α ≠ -W.a₁ - α)
    (X Y : k) (he : (polynomialModel W s (fun q => (f q).xc) (fun q => (f q).yc)).toAffine.Equation X Y)
    (hsg : ¬ (polynomialModel W s (fun q => (f q).xc) (fun q => (f q).yc)).toAffine.Nonsingular X Y) :
    X = (n : k) * x₀ - ∑ q : G, (f q).xc := by
  by_cases h12 : (12 : k) = 0
  · have htwo : (2 : k) * 6 = 0 := by linear_combination h12
    have h6 : (6 : k) = 0 := by
      rcases mul_eq_zero.mp htwo with h2 | h6
      · linear_combination 3 * h2
      · exact h6
    exact candidate_center_eq_singular_of_six_eq_zero W hn h6 e f hf s hs F hsep X Y he hsg
  · have hi := WeierstrassNodalVelu.polynomialModel_invariants W hn e f hf s hs F hsep
    have hb := polynomialModel_b_invariants W s (fun q => (f q).xc) (fun q => (f q).yc)
    exact WeierstrassNodalCenter.candidate_center_eq_singular W _ hn hn0 h12 e f hf s hs F hsep
      hb.1 hi.1 hi.2.1 X Y he hsg

end DkMath.Lib.NumberTheory.WeierstrassNodalCenterSmallChar
