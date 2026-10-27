/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.WeierstrassNodalVelu

#print "file: DkMath.Lib.NumberTheory.WeierstrassNodalCenter"

/-!
# 節点中心の二乗・三乗による識別

[DkMath.Lib] 同じ特異点の偏微分と方程式から、b₂+12xの二乗と三乗は
それぞれc₄と−c₆に一致する。二乗だけでは符号が残るが、非零な場合は
三乗と合わせることで中心の向きを決められる。係数の約分は行わない。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassNodalCenter
open WeierstrassCurve WeierstrassCurve.Affine
variable {k : Type*} [Field k]

/-- [DkMath.Lib] 同じ特異点ではc₄=(b₂+12x)²、c₆=−(b₂+12x)³。
二つの偏微分と方程式から係数a₃,a₄,a₆を置き換えるだけなので任意標数で成立する。 -/
theorem singular_invariants (W : WeierstrassCurve k) (x y : k)
    (he : W.toAffine.Equation x y) (hs : ¬ W.toAffine.Nonsingular x y) :
    W.c₄ = (W.b₂ + 12 * x) ^ 2 ∧ W.c₆ = -(W.b₂ + 12 * x) ^ 3 := by
  rw [nonsingular_iff'] at hs
  push Not at hs
  obtain ⟨hX, hY⟩ := hs he
  rw [equation_iff] at he
  have ha₃ : W.a₃ = -2 * y - W.a₁ * x := by linear_combination hY
  have ha₄ : W.a₄ = W.a₁ * y - 3 * x ^ 2 - 2 * W.a₂ * x := by linear_combination -hX
  have ha₆ : W.a₆ = y ^ 2 + W.a₁ * x * y + W.a₃ * y - x ^ 3 - W.a₂ * x ^ 2 - W.a₄ * x := by
    linear_combination -he
  simp only [c₄, c₆, b₂, b₄, b₆, ha₆, ha₄, ha₃]
  constructor <;> ring

/-- [DkMath.Lib] 非零な二つの量の二乗と三乗が等しければ、元の量も等しい。
標数2でも成立し、符号の選択を余分な仮定にしない。 -/
theorem eq_of_sq_cube_eq {a b : k} (hb : b ≠ 0)
    (h₂ : a ^ 2 = b ^ 2) (h₃ : a ^ 3 = b ^ 3) : a = b := by
  have h : b ^ 2 * (a - b) = 0 := by linear_combination h₃ - a * h₂
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hb))

open EllipticNodalTorsion.NodalTorsion WeierstrassNodalFrame
open DkMath.Lib.Algebra.FiniteInversionHalf
open scoped BigOperators

/-- [DkMath.Lib] 同じ奇数巡回核の候補中心cは、12(c−x₀)=(n²−1)δ²を満たす。
核の全点を反転半集合へ畳み、同じ節点比の原始根と整数Pascal証明書を使う。
12で割らずに示すので標数2,3にも成立する。 -/
theorem candidate_center_scaled [DecidableEq k] (W : WeierstrassCurve k)
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {n : ℕ}
    (hn : Odd n) (hn0 : (n : k) ≠ 0) (e : ZMod n ≃+ G)
    (f : G →+ W.toAffine.Point) (hf : Function.Injective f)
    (s : Finset G) (hs : IsHalf s) {x₀ y₀ α : k}
    (F : Frame W x₀ y₀ α) (hsep : α ≠ -W.a₁ - α) :
    12 * ((n : k) * x₀ - (∑ q : G, (f q).xc) - x₀) =
      ((n : k) ^ 2 - 1) * (2 * α + W.a₁) ^ 2 := by
  let P := f (e 1)
  let u := tc W x₀ y₀ α P
  let δ := 2 * α + W.a₁
  let z := fun j : ℕ => u ^ j / (1 - u ^ j) ^ 2
  have hord : addOrderOf P = n :=
    (addOrderOf_injective f hf (e 1)).trans ((e.addOrderOf_eq 1).trans (ZMod.addOrderOf_one n))
  have hu : IsPrimitiveRoot u n := hord ▸ primitiveRoot_tc F hsep P
  have hz (j : ℕ) (hj : j ∈ Finset.Icc 1 (n / 2)) : z j * (1 - u ^ j) ^ 2 = u ^ j := by
    have hj' := Finset.mem_Icc.mp hj
    have hjn : j < n := lt_of_le_of_lt hj'.2 (Nat.div_lt_self hn.pos (by decide))
    exact div_mul_cancel₀ _ (pow_ne_zero 2 (sub_ne_zero.mpr (hu.pow_ne_one_of_pos_of_lt (by omega) hjn).symm))
  have hp := (OddRootPairMoments.power_sums hu hn z hz).1
  have hcert : (24 : k) * ((OddRootPairMoments.firstCoefficient n : ℤ) : k) =
      (n : k) * ((n : k) ^ 2 - 1) := by
    have hh := congrArg (fun a : ℤ => (a : k)) (OddRootPairMoments.firstCoefficient_certificate hn)
    push_cast at hh
    exact hh
  have hxneg (q : G) : (f (-q)).xc = (f q).xc := by
    rw [map_neg]
    cases f q <;> rfl
  have hfull : (∑ q : G, (f q).xc) = 2 * ∑ q ∈ s, (f q).xc := by
    have he := Finset.sum_erase_add (Finset.univ : Finset G) (fun q => (f q).xc) (Finset.mem_univ 0)
    rw [← hs.1, Finset.sum_union hs.2, Finset.sum_image (by intro a _ b _ h; exact neg_injective h)] at he
    simp only [map_zero, hxneg] at he
    change (∑ q ∈ s, (f q).xc) + (∑ q ∈ s, (f q).xc) + 0 = _ at he
    linear_combination he.symm
  have hhalf : (∑ q ∈ s, (f q).xc) =
      ((n / 2 : ℕ) : k) * x₀ + δ ^ 2 * ∑ j ∈ Finset.Icc 1 (n / 2), z j := by
    rw [sum_eq_cyclic hn e hs (fun q => (f q).xc) hxneg]
    have hcoord (j : ℕ) (hj : j ∈ Finset.Icc 1 (n / 2)) : (f (e (j : ZMod n))).xc = x₀ + δ ^ 2 * z j := by
      have he : f (e (j : ZMod n)) = j • P := by
        rw [← Nat.smul_one_eq_cast, map_nsmul, map_nsmul]
      rw [he]
      exact nsmul_xc F hsep P hord (Finset.mem_Icc.mp hj).1
        (lt_of_le_of_lt (Finset.mem_Icc.mp hj).2 (Nat.div_lt_self hn.pos (by decide)))
    rw [Finset.sum_congr rfl hcoord, Finset.sum_add_distrib, Finset.sum_const,
      Nat.card_Icc, Finset.mul_sum]
    have hh : n / 2 + 1 - 1 = n / 2 := by omega
    rw [hh, nsmul_eq_mul]
  have hodd : (n : k) = 2 * ((n / 2 : ℕ) : k) + 1 := by
    obtain ⟨m, rfl⟩ := hn
    have he : (2 * m + 1) / 2 = m := by omega
    rw [he]
    push_cast
    ring
  have hmul : (n : k) * (12 * ((n : k) * x₀ - (∑ q : G, (f q).xc) - x₀) -
      ((n : k) ^ 2 - 1) * δ ^ 2) = 0 := by
    rw [hfull, hhalf]
    linear_combination -24 * δ ^ 2 * hp + δ ^ 2 * hcert +
      (12 * (n : k) * x₀) * hodd
  have hh := (mul_eq_zero.mp hmul).resolve_left hn0
  exact sub_eq_zero.mp hh

/-- [DkMath.Lib] 12が非零なら、同じ奇数巡回核からの候補中心は標的の特異点のx座標に等しい。
標的について同じb₂と、重みn⁴,n⁶のc₄,c₆公式を保持する。二乗・三乗の両方で
接方向の符号を固定し、最後に12を消去する。標数2,3はこの消去の外に残る。 -/
theorem candidate_center_eq_singular [DecidableEq k] (W V : WeierstrassCurve k)
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {n : ℕ}
    (hn : Odd n) (hn0 : (n : k) ≠ 0) (h12 : (12 : k) ≠ 0) (e : ZMod n ≃+ G)
    (f : G →+ W.toAffine.Point) (hf : Function.Injective f)
    (s : Finset G) (hs : IsHalf s) {x₀ y₀ α : k}
    (F : Frame W x₀ y₀ α) (hsep : α ≠ -W.a₁ - α)
    (hb : V.b₂ = W.b₂) (h4 : V.c₄ = (n : k) ^ 4 * W.c₄)
    (h6 : V.c₆ = (n : k) ^ 6 * W.c₆)
    (X Y : k) (he : V.toAffine.Equation X Y) (hsg : ¬ V.toAffine.Nonsingular X Y) :
    X = (n : k) * x₀ - ∑ q : G, (f q).xc := by
  let δ := 2 * α + W.a₁
  let c := (n : k) * x₀ - ∑ q : G, (f q).xc
  have hδ : δ ≠ 0 := by
    intro hz
    apply hsep
    dsimp [δ] at hz
    linear_combination hz
  have hc : V.b₂ + 12 * c = (n : k) ^ 2 * δ ^ 2 := by
    have hcand := candidate_center_scaled W hn hn0 e f hf s hs F hsep
    have hb2 := (b_invariants F).1
    change 12 * (c - x₀) = ((n : k) ^ 2 - 1) * δ ^ 2 at hcand
    change W.b₂ = δ ^ 2 - 12 * x₀ at hb2
    rw [hb]
    linear_combination hcand + hb2
  have hi := singular_invariants V X Y he hsg
  have hcW := c_invariants F
  have hsquare : (V.b₂ + 12 * X) ^ 2 = ((n : k) ^ 2 * δ ^ 2) ^ 2 := by
    calc
      _ = V.c₄ := hi.1.symm
      _ = (n : k) ^ 4 * W.c₄ := h4
      _ = ((n : k) ^ 2 * δ ^ 2) ^ 2 := by rw [hcW.1]; dsimp [δ]; ring
  have hcube : (V.b₂ + 12 * X) ^ 3 = ((n : k) ^ 2 * δ ^ 2) ^ 3 := by
    apply neg_injective
    calc
      _ = V.c₆ := hi.2.symm
      _ = (n : k) ^ 6 * W.c₆ := h6
      _ = -((n : k) ^ 2 * δ ^ 2) ^ 3 := by rw [hcW.2]; dsimp [δ]; ring
  have hB := eq_of_sq_cube_eq (mul_ne_zero (pow_ne_zero 2 hn0) (pow_ne_zero 2 hδ)) hsquare hcube
  have hdiff : 12 * (X - c) = 0 := by linear_combination hB - hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left h12)

end DkMath.Lib.NumberTheory.WeierstrassNodalCenter
