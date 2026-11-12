/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticNodalTorsion
import DkMath.Lib.NumberTheory.WeierstrassVeluReduction
import DkMath.Lib.NumberTheory.EllipticFunctionField
import DkMath.Lib.NumberTheory.EllipticNodalTorsionBound
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

#print "file: DkMath.Lib.NumberTheory.WeierstrassNodalFrame"

/-!
# 同じ節点の接方向から座標と不変量を読む

[DkMath.Lib] 既存のFrameと節点比tcを再利用する。δ=2α+a₁は二接方向の差。
同じ点Pの比uについて(x(P)−x₀)(1−u)²=δ²uとなる。
この恒等式を有限核へ適用すれば、原始根の反転対のモーメント計算と接続できる。
2,3の逆数や、新たな正規形への点の移し替えは使わない。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassNodalFrame
open WeierstrassCurve WeierstrassCurve.Affine EllipticNodalTorsion.NodalTorsion IsLocalRing
variable {k : Type*} [Field k] {W : WeierstrassCurve k} {x₀ y₀ α : k}

/-- [DkMath.Lib] 同じFrameからb₂,b₄,b₆,b₈を節点x₀と方向差δで表示する。任意標数で成立。 -/
theorem b_invariants (F : Frame W x₀ y₀ α) :
    let δ := 2 * α + W.a₁
    W.b₂ = δ ^ 2 - 12 * x₀ ∧ W.b₄ = 6 * x₀ ^ 2 - δ ^ 2 * x₀ ∧
      W.b₆ = δ ^ 2 * x₀ ^ 2 - 4 * x₀ ^ 3 ∧ W.b₈ = 3 * x₀ ^ 4 - δ ^ 2 * x₀ ^ 3 := by
  have ha₂ : W.a₂ = α ^ 2 + W.a₁ * α - 3 * x₀ := by linear_combination -F.hα
  have ha₃ : W.a₃ = -2 * y₀ - W.a₁ * x₀ := by linear_combination F.hFY
  have ha₄ : W.a₄ = W.a₁ * y₀ - 3 * x₀ ^ 2 - 2 * W.a₂ * x₀ := by linear_combination -F.hFX
  have ha₆ : W.a₆ = y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - x₀ ^ 3 - W.a₂ * x₀ ^ 2 - W.a₄ * x₀ := by
    linear_combination -F.he
  dsimp only
  simp only [b₂, b₄, b₆, b₈, ha₆, ha₄, ha₃, ha₂]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- [DkMath.Lib] 同じ節点のc₄=δ⁴、c₆=−δ⁶。標数2,3でも係数を約分しない。 -/
theorem c_invariants (F : Frame W x₀ y₀ α) :
    W.c₄ = (2 * α + W.a₁) ^ 4 ∧ W.c₆ = -(2 * α + W.a₁) ^ 6 := by
  obtain ⟨h2,h4,h6,-⟩ := b_invariants F
  simp only [c₄, c₆, h2, h4, h6]
  constructor <;> ring

/-- [DkMath.Lib] 同じFrameの判別式は零であり、二方向が分離すればc₄は非零である。 -/
theorem nodal_invariants (F : Frame W x₀ y₀ α) (hsep : α ≠ -W.a₁ - α) : W.Δ = 0 ∧ W.c₄ ≠ 0 := by
  have hδ : 2 * α + W.a₁ ≠ 0 := by
    intro he
    apply hsep
    linear_combination he
  constructor
  · obtain ⟨h2,h4,h6,h8⟩ := b_invariants F
    simp only [WeierstrassCurve.Δ,h2,h4,h6,h8]
    ring
  · rw [(c_invariants F).1]
    exact pow_ne_zero 4 hδ

/-- [DkMath.Lib] 同じ滑らかな有限点のxは、節点比uを使う分母払い済み恒等式を満たす。 -/
theorem x_tc_identity (F : Frame W x₀ y₀ α) {x y : k} (h : W.toAffine.Nonsingular x y) :
    (x - x₀) * (1 - tc W x₀ y₀ α (.some x y h)) ^ 2 =
      (2 * α + W.a₁) ^ 2 * tc W x₀ y₀ α (.some x y h) := by
  have hfac := factor_eq F h.1
  have hn := (factors_ne_zero F h).2
  let a := y - y₀ - α * (x - x₀)
  let b := y - y₀ - (-W.a₁ - α) * (x - x₀)
  have hb : b ≠ 0 := hn
  have hab : b - a = (2 * α + W.a₁) * (x - x₀) := by dsimp [a,b]; ring
  have hf : a * b = (x - x₀) ^ 3 := hfac
  change (x - x₀) * (1 - a / b) ^ 2 = (2 * α + W.a₁) ^ 2 * (a / b)
  rw [one_sub_div hb, div_pow]
  rw [show (x - x₀) * ((b - a) ^ 2 / b ^ 2) = ((x - x₀) * (b - a) ^ 2) / b ^ 2 by ring,
    show (2 * α + W.a₁) ^ 2 * (a / b) = ((2 * α + W.a₁) ^ 2 * a) / b by ring]
  apply (div_eq_div_iff (pow_ne_zero 2 hb) hb).mpr
  rw [hab]
  linear_combination -(2 * α + W.a₁) ^ 2 * b * hf

/-- [DkMath.Lib] 分離した二方向では、非零点の同じ節点比uは1でない。 -/
theorem tc_ne_one (F : Frame W x₀ y₀ α) (hsep : α ≠ -W.a₁ - α)
    (P : W.toAffine.Point) (hP : P ≠ 0) : tc W x₀ y₀ α P ≠ 1 :=
  fun he => hP (eq_zero_of_tc_eq_one F hsep P he)

/-- [DkMath.Lib] 同じ非零点のx座標を、反転不変なz=u/(1−u)²で表示する。 -/
theorem xc_eq (F : Frame W x₀ y₀ α) (hsep : α ≠ -W.a₁ - α)
    (P : W.toAffine.Point) (hP : P ≠ 0) :
    P.xc = x₀ + (2 * α + W.a₁) ^ 2 *
      (tc W x₀ y₀ α P / (1 - tc W x₀ y₀ α P) ^ 2) := by
  have hn : 1 - tc W x₀ y₀ α P ≠ 0 := sub_ne_zero.mpr (Ne.symm (tc_ne_one F hsep P hP))
  rcases P with _ | ⟨x,y,h⟩
  · exact (hP rfl).elim
  · have hi := x_tc_identity F h
    change x = _
    field_simp [hn]
    linear_combination hi

/-- [DkMath.Lib] 同じ一般ファイバーモデルの中心・方向を、同じ剰余曲線のFrameへ運ぶ。
モデルの等式だけを使い、中心や方向を選び直さない。 -/
theorem residue_frame_of_model {L : Type*} [Field L] (A : ValuationSubring L)
    (M : WeierstrassCurve A) (V : WeierstrassCurve L) (hM : M.map A.subtype = V)
    (C : EllipticCriticalCentre.CriticalCentre A V) (D : EllipticTangentDirections.TangentDirections C) :
    Frame (M.map (residue A)) (residue A ⟨C.x,C.x_mem⟩) (residue A ⟨C.y,C.y_mem⟩)
      (residue A ⟨D.α,D.α_mem⟩) ∧
      residue A ⟨D.α,D.α_mem⟩ ≠ -(M.map (residue A)).a₁ - residue A ⟨D.α,D.α_mem⟩ := by
  subst V
  exact EllipticNodalTorsionBound.residue_frame M C D

variable [DecidableEq k]

/-- [DkMath.Lib] 同じ点の節点比は、その点の実際の加法位数の原始根である。 -/
theorem primitiveRoot_tc (F : Frame W x₀ y₀ α) (hsep : α ≠ -W.a₁ - α)
    (P : W.toAffine.Point) : IsPrimitiveRoot (tc W x₀ y₀ α P) (addOrderOf P) :=
  (IsPrimitiveRoot.iff_def _ _).mpr
    ⟨by rw [← tc_nsmul F, addOrderOf_nsmul_eq_zero, tc_zero],
      fun l hl => addOrderOf_dvd_iff_nsmul_eq_zero.mpr
        (eq_zero_of_tc_eq_one F hsep _ (by rw [tc_nsmul F]; exact hl))⟩

/-- [DkMath.Lib] 同じ実際のk倍点のxを、同じ原始根のk乗で表示する。
位数未満の正のkを保ち、Oの便宜座標を有限点公式へ入れない。 -/
theorem nsmul_xc (F : Frame W x₀ y₀ α) (hsep : α ≠ -W.a₁ - α)
    (P : W.toAffine.Point) {n : ℕ} (horder : addOrderOf P = n) {j : ℕ} (hj : 0 < j) (hjn : j < n) :
    (j • P).xc = x₀ + (2 * α + W.a₁) ^ 2 *
      ((tc W x₀ y₀ α P) ^ j / (1 - (tc W x₀ y₀ α P) ^ j) ^ 2) := by
  have hne : j • P ≠ 0 := by
    intro he
    have hd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr he
    rw [horder] at hd
    exact (not_le.mpr hjn) (Nat.le_of_dvd hj hd)
  simpa only [tc_nsmul F] using xc_eq F hsep (j • P) hne

end DkMath.Lib.NumberTheory.WeierstrassNodalFrame
