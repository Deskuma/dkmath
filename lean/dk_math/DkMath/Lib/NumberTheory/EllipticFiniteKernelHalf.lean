/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelNonsingular

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelHalf"

/-!
# 奇数位数の同じ実点核から、反転対の片側を選ぶ

[DkMath.Lib] 有限型HをFin(card H)へ番号付けし、Qと−Qのうち番号の小さい方を選ぶ。
奇数性により非零点Qは−Qと異なるので、全ての非零反転対からちょうど一つ選ばれる。
巡回生成元は不要であり、非巡回の奇数核にも使える。
半核はVélu係数の分母2を導入しないための添字集合だが、既存の標的との係数一致は別の定理である。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine EllipticTorsionRepresentation
variable {K : Type*} [Field K] (E : WeierstrassCurve K)
noncomputable local instance instDecidableEqEllipticFiniteKernelHalf {α : Type*} : DecidableEq α := Classical.decEq _

/-- [DkMath.Lib] 同じ核の反転対から番号の小さい点を取った有限部分集合。Oを除く。 -/
noncomputable def halfKernel (H : AddSubgroup (Points E)) [Fintype H] : Finset H :=
  Finset.univ.filter (fun Q => Q ≠ 0 ∧ Fintype.equivFin H Q < Fintype.equivFin H (-Q))

/-- [DkMath.Lib] 半核への所属の具体的な判定。 -/
theorem mem_halfKernel (H : AddSubgroup (Points E)) [Fintype H] (Q : H) :
    Q ∈ halfKernel E H ↔ Q ≠ 0 ∧ Fintype.equivFin H Q < Fintype.equivFin H (-Q) := by
  simp only [halfKernel, Finset.mem_filter, Finset.mem_univ, true_and]

/-- [DkMath.Lib] 奇数核の非零点は、その反対点とは異なる。 -/
theorem neg_ne_self_of_odd_kernel (H : AddSubgroup (Points E))
    (hodd : Odd (Nat.card H)) (Q : H) (hQ : Q ≠ 0) : -Q ≠ Q := by
  intro he
  apply hQ
  exact Subtype.ext (eq_zero_of_mem_odd_kernel_fixed E H hodd Q.val Q.property
    (congrArg Subtype.val he))

/-- [DkMath.Lib] 同じ非零反転対では、ちょうど片側が半核に入る。 -/
theorem mem_halfKernel_or_neg (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (Q : H) (hQ : Q ≠ 0) :
    Q ∈ halfKernel E H ∨ -Q ∈ halfKernel E H := by
  have hn : Fintype.equivFin H Q ≠ Fintype.equivFin H (-Q) :=
    fun he => neg_ne_self_of_odd_kernel E H hodd Q hQ ((Fintype.equivFin H).injective he).symm
  rcases lt_or_gt_of_ne hn with h | h
  · exact Or.inl ((mem_halfKernel E H Q).mpr ⟨hQ, h⟩)
  · exact Or.inr ((mem_halfKernel E H (-Q)).mpr ⟨neg_ne_zero.mpr hQ, by simpa only [neg_neg] using h⟩)

/-- [DkMath.Lib] 半核に選んだ点の反対点は半核に入らない。奇数性はこの排他性には不要。 -/
theorem neg_not_mem_halfKernel (H : AddSubgroup (Points E)) [Fintype H]
    (Q : H) (hQ : Q ∈ halfKernel E H) : -Q ∉ halfKernel E H := by
  intro hn
  have h := (mem_halfKernel E H Q).mp hQ |>.2
  have h' := (mem_halfKernel E H (-Q)).mp hn |>.2
  simp only [neg_neg] at h'
  exact lt_asymm h h'

/-- [DkMath.Lib] 同じ奇数核は、Oと二つの互いに交わらない半核に分かれる。 -/
theorem halfKernel_partition (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) :
    halfKernel E H ∪ (halfKernel E H).image Neg.neg = Finset.univ.erase 0 ∧
      Disjoint (halfKernel E H) ((halfKernel E H).image Neg.neg) := by
  constructor
  · ext Q
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro (h | ⟨R, hR, rfl⟩)
      · exact (mem_halfKernel E H Q).mp h |>.1
      · exact neg_ne_zero.mpr ((mem_halfKernel E H R).mp hR).1
    · intro hQ
      rcases mem_halfKernel_or_neg E H hodd Q hQ with h | h
      · exact Or.inl h
      · exact Or.inr ⟨-Q, h, neg_neg Q⟩
  · apply Finset.disjoint_left.mpr
    intro Q hQ hn
    obtain ⟨R, hR, he⟩ := Finset.mem_image.mp hn
    exact neg_not_mem_halfKernel E H R hR (he.symm ▸ hQ)

/-- [DkMath.Lib] 半核の点数は、同じ全核の点数から1を除いて二等分した値。 -/
theorem card_halfKernel (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) : 2 * (halfKernel E H).card + 1 = Nat.card H := by
  obtain ⟨hu, hd⟩ := halfKernel_partition E H hodd
  have hc := Finset.card_union_of_disjoint hd
  rw [hu, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ,
    Finset.card_image_of_injective _ neg_injective, Fintype.card_eq_nat_card] at hc
  have hp : 0 < Nat.card H := Nat.card_pos
  omega

/-- [DkMath.Lib] 非自明な奇数核では半核が空でない。

`card_halfKernel` の等式を `1 < Nat.card H` と組み合わせるだけの算術補題である。
特殊ファイバー因子の二重根を選ぶ前に、半核の代表を実際に一つ供給する入口になる。
自明核ではこの命題の仮定が成立しないため、一次因子の判別式を誤って零としない。
-/
theorem halfKernel_nonempty_of_one_lt_card (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (hcard : 1 < Nat.card H) :
    (halfKernel E H).Nonempty := by
  by_contra h
  have hempty : halfKernel E H = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hc := card_halfKernel E H hodd
  rw [hempty, Finset.card_empty] at hc
  omega

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
