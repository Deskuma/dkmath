/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.WeierstrassNodalOrbit

#print "file: DkMath.Lib.NumberTheory.WeierstrassNodalDistance"

/-!
# 節点からの非零距離と正規化座標和

[DkMath.Lib] 分離した節点の滑らかな有限点は節点と異なるx座標を持つ。
巡回軌道の正規化和は、定数n*x₀−Σx(jQ)からn²(x(nP)−x₀)だけ離れる。
nが体で非零ならこの距離は非零である。これは候補中心からの分離であり、
候補中心が同じ商曲線の特異点であることは別に証明しなければならない。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassNodalDistance
open WeierstrassCurve WeierstrassCurve.Affine
open EllipticNodalTorsion.NodalTorsion WeierstrassNodalFrame WeierstrassNodalOrbit
open scoped BigOperators
variable {k : Type*} [Field k] [DecidableEq k] {W : WeierstrassCurve k} {x₀ y₀ α : k}

omit [DecidableEq k] in
/-- [DkMath.Lib] 分離した節点の非零な滑らかな実点は、節点と異なるx座標を持つ。
節点比の分子・分母、接方向の差のいずれも非零であることから導く。 -/
theorem xc_ne_centre (F : Frame W x₀ y₀ α) (hsep : α ≠ -W.a₁ - α)
    (P : W.toAffine.Point) (hP : P ≠ 0) : P.xc ≠ x₀ := by
  have hd : 2 * α + W.a₁ ≠ 0 := by
    intro h
    apply hsep
    linear_combination h
  have ht := tc_ne_zero F P
  have hn : 1 - tc W x₀ y₀ α P ≠ 0 := sub_ne_zero.mpr (tc_ne_one F hsep P hP).symm
  have hz : (2 * α + W.a₁) ^ 2 *
      (tc W x₀ y₀ α P / (1 - tc W x₀ y₀ α P) ^ 2) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hd) (div_ne_zero ht (pow_ne_zero 2 hn))
  intro he
  have he' := xc_eq F hsep P hP
  rw [he] at he'
  apply hz
  linear_combination he'.symm

/-- [DkMath.Lib] 同じ巡回軌道の正規化x座標和と、候補中心の差。
この等式は標数の制限なく成立し、定数項を商標的の節点と仮定しない。 -/
theorem normalized_x_sub_candidate (F : Frame W x₀ y₀ α) (hsep : α ≠ -W.a₁ - α)
    {n : ℕ} (P Q : W.toAffine.Point)
    (hQ : IsPrimitiveRoot (tc W x₀ y₀ α Q) n) (hP : n • P ≠ 0) :
    ((∑ j ∈ Finset.range n, (P + j • Q).xc) - (∑ j ∈ Finset.range n, (j • Q).xc)) -
      ((n : k) * x₀ - ∑ j ∈ Finset.range n, (j • Q).xc) =
        (n : k) ^ 2 * ((n • P).xc - x₀) := by
  rw [normalized_x_sum F hsep P Q hQ hP]
  ring

/-- [DkMath.Lib] nが体で非零なら、衝突しない同じ軌道の正規化和は候補中心と異なる。
商の非特異性を結論するには、この候補が標的の節点中心である証明が別に必要。 -/
theorem normalized_x_ne_candidate (F : Frame W x₀ y₀ α) (hsep : α ≠ -W.a₁ - α)
    {n : ℕ} (hn : (n : k) ≠ 0) (P Q : W.toAffine.Point)
    (hQ : IsPrimitiveRoot (tc W x₀ y₀ α Q) n) (hP : n • P ≠ 0) :
    (∑ j ∈ Finset.range n, (P + j • Q).xc) - (∑ j ∈ Finset.range n, (j • Q).xc) ≠
      (n : k) * x₀ - ∑ j ∈ Finset.range n, (j • Q).xc := by
  have hd : (n : k) ^ 2 * ((n • P).xc - x₀) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hn) (sub_ne_zero.mpr (xc_ne_centre F hsep _ hP))
  intro he
  apply hd
  rw [← normalized_x_sub_candidate F hsep P Q hQ hP, he, sub_self]

end DkMath.Lib.NumberTheory.WeierstrassNodalDistance
