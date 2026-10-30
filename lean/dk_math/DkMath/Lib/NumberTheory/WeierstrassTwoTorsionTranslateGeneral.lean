/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.WeierstrassTwoTorsionTranslate
import DkMath.Lib.NumberTheory.WeierstrassDiscriminantRoots
import DkMath.Lib.NumberTheory.WeierstrassDiscriminantAssembly
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

#print "file: DkMath.Lib.NumberTheory.WeierstrassTwoTorsionTranslateGeneral"

/-!
# 一般 Weierstrass 形の二捩れ根差公式

`WeierstrassTwoTorsionTranslate` の既存定理は `a₁ = a₃ = 0` の正規化形を扱う。
本モジュールでは座標変換を介さず、二捩れ点の y 座標条件と平方完成三次式を
直接使って、一般係数でも同じ根差恒等式を証明する。
-/

namespace DkMath.Lib.NumberTheory.WeierstrassTwoTorsionTranslateGeneral

open WeierstrassCurve
open scoped WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory.WeierstrassDiscriminantRoots
open DkMath.Lib.NumberTheory.WeierstrassDiscriminantAssembly

variable {k : Type*} [Field k] [NeZero (2 : k)] [DecidableEq k]

omit [DecidableEq k] in
/-- [DkMath.Lib] 三つの相異なる2捩れ根の一次対称式を係数へ戻す。

`Cubic.b_eq_three_roots` は、首係数4の2捩れ三次式の二次係数が
`-4 (e₁+e₂+e₃)` であることを与える。`b₂ = a₁² + 4a₂` を展開すると、
一般 Weierstrass 形で必要な
`4 (e₁+e₂+e₃) = -(a₁²+4a₂)` が得られる。
-/
theorem two_torsion_root_sum
    (W : WeierstrassCurve k)
    {e₁ e₂ e₃ : k}
    (h₁ : W.twoTorsionPolynomial.toPoly.eval e₁ = 0)
    (h₂ : W.twoTorsionPolynomial.toPoly.eval e₂ = 0)
    (h₃ : W.twoTorsionPolynomial.toPoly.eval e₃ = 0)
    (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃) :
    4 * (e₁ + e₂ + e₃) = -(W.a₁ ^ 2 + 4 * W.a₂) := by
  have h4 : (4 : k) ≠ 0 := by
    simpa only [show (4 : k) = 2 ^ 2 by ring] using
      pow_ne_zero 2 (NeZero.ne (2 : k))
  have hb := Cubic.b_eq_three_roots (P := W.twoTorsionPolynomial) h4
    (roots_eq_three W (NeZero.ne (2 : k)) e₁ e₂ e₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃)
  have hb' : W.a₁ ^ 2 + 4 * W.a₂ = 4 * -(e₁ + e₂ + e₃) := by
    simpa only [RingHom.id_apply, twoTorsionPolynomial, b₂] using hb
  rw [hb']
  ring

omit [NeZero (2 : k)] in
/-- [DkMath.Lib] affine 2捩れ点の y 座標条件。

`2T=0` を点群の等式から取り出すと、点とその反転の y 座標が一致する。
`Affine.Point.negY` を展開すると、一般 Weierstrass 形で使う
`2 t + a₁ e + a₃ = 0` が得られる。これは根差積特殊化で `hTtwo` を
実際の2捩れ点から供給するための局所教材補題である。
-/
theorem two_torsion_y_condition
    (W : WeierstrassCurve k) {e t : k} (h : W.toAffine.Nonsingular e t)
    (htor : 2 • (Affine.Point.some e t h) = 0) :
    2 * t + W.a₁ * e + W.a₃ = 0 := by
  rw [two_nsmul, add_eq_zero_iff_eq_neg, Affine.Point.neg_some,
    Affine.Point.some.injEq] at htor
  obtain ⟨_, ht⟩ := htor
  dsimp only [Affine.negY] at ht
  linear_combination ht

/-- [DkMath.Lib] 一般 Weierstrass 形の二捩れ根差恒等式。

`T=(e₁,t₁)` は `2T=0` を y 座標条件
`2 t₁ + a₁ e₁ + a₃ = 0` で表す。`e₁,e₂,e₃` は平方完成三次式の
三根であり、三つの対称式は `b₂,b₄,b₆` の係数形で入力する。
従って `a₁,a₃` をゼロ化する変数変換を行わず、実際の加法公式から
`(e₂-x(T+Q))(x(Q)-e₁)=(e₂-e₁)(x(Q)-e₃)` を得る。
-/
theorem translated_root_difference_general
    (W : WeierstrassCurve k)
    {e₁ e₂ e₃ t₁ x y : k}
    (hσ₁ : 4 * (e₁ + e₂ + e₃) = -(W.a₁ ^ 2 + 4 * W.a₂))
    (hz : (2 * y + W.a₁ * x + W.a₃) ^ 2 =
      4 * (x - e₁) * (x - e₂) * (x - e₃))
    (hTtwo : 2 * t₁ + W.a₁ * e₁ + W.a₃ = 0)
    (hxe : x ≠ e₁) :
    (e₂ - W.toAffine.addX e₁ x
      (W.toAffine.slope e₁ x t₁ y)) * (x - e₁) =
      (e₂ - e₁) * (x - e₃) := by
  have hd : x - e₁ ≠ 0 := sub_ne_zero.mpr hxe
  have h4 : (4 : k) ≠ 0 := by
    simpa only [show (4 : k) = 2 ^ 2 by ring] using pow_ne_zero 2 (NeZero.ne (2 : k))
  have hσ₁' : 4 * (e₁ + e₂ + e₃) =
      -(W.toAffine.a₁ ^ 2 + 4 * W.toAffine.a₂) := by
    simpa only [WeierstrassCurve.toAffine] using hσ₁
  have hTtwo' : 2 * t₁ + W.toAffine.a₁ * e₁ + W.toAffine.a₃ = 0 := by
    simpa only [WeierstrassCurve.toAffine] using hTtwo
  have hslope : W.toAffine.slope e₁ x t₁ y = (y - t₁) / (x - e₁) := by
    rw [Affine.slope_of_X_ne hxe.symm]
    field_simp [hd]
    ring
  rw [hslope]
  have hm :
      2 * ((y - t₁) / (x - e₁)) + W.toAffine.a₁ =
        (2 * y + W.toAffine.a₁ * x + W.toAffine.a₃) / (x - e₁) := by
    field_simp [hd]
    linear_combination -hTtwo'
  have hma :
      ((y - t₁) / (x - e₁)) ^ 2 + W.toAffine.a₁ * ((y - t₁) / (x - e₁)) =
        (((2 * y + W.toAffine.a₁ * x + W.toAffine.a₃) / (x - e₁)) ^ 2 -
          W.toAffine.a₁ ^ 2) / 4 := by
    rw [← hm]
    field_simp [hd, h4]
    ring
  have hquot :
      ((2 * y + W.toAffine.a₁ * x + W.toAffine.a₃) / (x - e₁)) ^ 2 =
        4 * (x - e₂) * (x - e₃) / (x - e₁) := by
    rw [div_pow, hz]
    field_simp [hd]
  simp only [Affine.addX]
  rw [hma, hquot]
  field_simp [hd, h4]
  linear_combination (x - e₁) * hσ₁'

/-- [DkMath.Lib] 三根の実在から一般形の根差恒等式を供給する。

前定理の平方完成三次式 `hz` を、既存の
`tangent_square_eq_root_product` から構成する版である。これにより入力は
三つの二捩れ根、根の分離、曲線方程式、二捩れ点の y 座標条件へ戻る。
平行移動後のモデルを作らず、一般係数のまま半核点へ適用できる。
-/
theorem translated_root_difference_general_of_roots
    (W : WeierstrassCurve k)
    {e₁ e₂ e₃ t₁ x y : k}
    (h₁ : W.twoTorsionPolynomial.toPoly.eval e₁ = 0)
    (h₂ : W.twoTorsionPolynomial.toPoly.eval e₂ = 0)
    (h₃ : W.twoTorsionPolynomial.toPoly.eval e₃ = 0)
    (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃)
    (hσ₁ : 4 * (e₁ + e₂ + e₃) = -(W.a₁ ^ 2 + 4 * W.a₂))
    (hTtwo : 2 * t₁ + W.a₁ * e₁ + W.a₃ = 0)
    (hQ : W.toAffine.Equation x y) (hxe : x ≠ e₁) :
    (e₂ - W.toAffine.addX e₁ x
      (W.toAffine.slope e₁ x t₁ y)) * (x - e₁) =
      (e₂ - e₁) * (x - e₃) := by
  apply translated_root_difference_general W hσ₁
    (tangent_square_eq_root_product W (NeZero.ne (2 : k)) e₁ e₂ e₃
      h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ x y hQ) hTtwo hxe

/-- [DkMath.Lib] 一般形の根差恒等式を有限積へ持ち上げる。

各添字で `translated_root_difference_general_of_roots` を適用し、既存の
`product_root_difference_relation` へ渡すだけの有限積層である。従って、
根の分離・各点の曲線方程式・二捩れ点の y 条件は、個々の点の入力として
明示的に保持される。半核を `s` として選べば、一般 Weierstrass 形の
`B_{jk} H_j = (e_k-e_j)^n H_l` の前段になる。
-/
theorem translated_root_product_relation_general
    {ι : Type*}
    (W : WeierstrassCurve k)
    (s : Finset ι) (x y : ι → k)
    (t₁ e₁ e₂ e₃ : k)
    (h₁ : W.twoTorsionPolynomial.toPoly.eval e₁ = 0)
    (h₂ : W.twoTorsionPolynomial.toPoly.eval e₂ = 0)
    (h₃ : W.twoTorsionPolynomial.toPoly.eval e₃ = 0)
    (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃)
    (hσ₁ : 4 * (e₁ + e₂ + e₃) = -(W.a₁ ^ 2 + 4 * W.a₂))
    (hTtwo : 2 * t₁ + W.a₁ * e₁ + W.a₃ = 0)
    (hEq : ∀ q ∈ s, W.toAffine.Equation (x q) (y q))
    (hxe : ∀ q ∈ s, x q ≠ e₁) :
    (∏ q ∈ s, (e₂ - W.toAffine.addX e₁ (x q)
      (W.toAffine.slope e₁ (x q) t₁ (y q)))) *
        (∏ q ∈ s, (x q - e₁)) =
      (e₂ - e₁) ^ s.card * ∏ q ∈ s, (x q - e₃) := by
  apply product_root_difference_relation s x
    (fun q => W.toAffine.addX e₁ (x q)
      (W.toAffine.slope e₁ (x q) t₁ (y q))) e₁ e₂ e₃
  intro q hq
  have h := translated_root_difference_general_of_roots W h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hσ₁
    hTtwo (hEq q hq) (hxe q hq)
  calc
    _ = (e₂ - e₁) * (x q - e₃) := h
    _ = -((e₁ - e₂) * (x q - e₃)) := by ring

end DkMath.Lib.NumberTheory.WeierstrassTwoTorsionTranslateGeneral
