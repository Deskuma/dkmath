/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.Lib.NumberTheory.EllipticFiniteKernelDepthProduct
import DkMath.Lib.NumberTheory.WeierstrassDiscriminantRoots
import DkMath.Lib.NumberTheory.WeierstrassDiscriminantAssembly

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelRootProduct"

/-!
# 奇数核の接線分母と2捩れ三根

[DkMath.Lib] 幾何学的点群の同じ半核について、接線分母の積を2捩れ三根への
距離の積に分解する。奇数位数の核では半核点は2捩れでないので、各因子は非零。
この恒等式は局所付値や商判別式の積公式を仮定しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine
open EllipticTorsionRepresentation WeierstrassDiscriminantRoots
open DkMath.Lib.NumberTheory.WeierstrassDiscriminantAssembly
open scoped BigOperators
noncomputable local instance instDecidableEqEllipticFiniteKernelRootProduct {α : Type*} : DecidableEq α := Classical.decEq _

variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
  (H : AddSubgroup (Points E)) [Fintype H]

omit [CharZero K] [E.IsElliptic] [Fintype H] in
/-- [DkMath.Lib] 奇数位数の核の非零点の接線式は非零である。
零なら反転固定点となり、奇数位数の核に非零2捩れが生じる。 -/
theorem odd_kernel_tangent_ne_zero (ho : Odd (Nat.card H)) (Q : H) (hQ : Q ≠ 0) :
    2 * Q.val.yc + (E.map (algebraMap K (AlgebraicClosure K))).a₁ * Q.val.xc +
      (E.map (algebraMap K (AlgebraicClosure K))).a₃ ≠ 0 := by
  intro h
  have hQ0 : Q.val ≠ 0 := fun hz => hQ (Subtype.ext hz)
  have hf := point_neg_eq_of_tangent_zero (E.map (algebraMap K (AlgebraicClosure K))) Q.val hQ0 h
  exact neg_ne_self_of_odd_kernel E H ho Q hQ (Subtype.ext hf)

omit [E.IsElliptic] in
/-- [DkMath.Lib] 半核の実際の接線分母の積は、三根それぞれへの距離の積と4の冪に分かれる。
根は源曲線の2捩れ三次式の根であり、商側の根ではない。 -/
theorem half_tangent_product_eq_root_products (r₁ r₂ r₃ : AlgebraicClosure K)
    (h₁ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₁ = 0)
    (h₂ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₂ = 0)
    (h₃ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₃ = 0)
    (h₁₂ : r₁ ≠ r₂) (h₁₃ : r₁ ≠ r₃) (h₂₃ : r₂ ≠ r₃) :
    (∏ Q : halfKernel E H, (2 * Q.val.val.yc +
      (E.map (algebraMap K (AlgebraicClosure K))).a₁ * Q.val.val.xc +
      (E.map (algebraMap K (AlgebraicClosure K))).a₃) ^ 2) =
      (4 : AlgebraicClosure K) ^ (halfKernel E H).card *
        (∏ Q : halfKernel E H, (Q.val.val.xc - r₁)) *
        (∏ Q : halfKernel E H, (Q.val.val.xc - r₂)) *
        (∏ Q : halfKernel E H, (Q.val.val.xc - r₃)) := by
  have hpoint (Q : halfKernel E H) : Q.val.val ≠ 0 :=
    fun hz => ((mem_halfKernel E H Q.val).mp Q.property).1 (Subtype.ext hz)
  calc
    _ = ∏ Q : halfKernel E H, (4 : AlgebraicClosure K) * (Q.val.val.xc - r₁) *
        (Q.val.val.xc - r₂) * (Q.val.val.xc - r₃) := by
      apply Finset.prod_congr rfl
      intro Q _
      exact tangent_square_eq_root_product _ (by norm_num) r₁ r₂ r₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃
        _ _ (Point.nonsingular_xc_yc (hpoint Q)).1
    _ = _ := by simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_coe]

omit [E.IsElliptic] in
/-- [DkMath.Lib] 奇数核の半核点のx座標は、源曲線の2捩れ三根のいずれとも一致しない。
ここで必要な非零性は、接線分母が非零であることと三根分解から得られる。 -/
theorem half_x_sub_root_ne_zero (ho : Odd (Nat.card H)) (r₁ r₂ r₃ : AlgebraicClosure K)
    (h₁ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₁ = 0)
    (h₂ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₂ = 0)
    (h₃ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₃ = 0)
    (h₁₂ : r₁ ≠ r₂) (h₁₃ : r₁ ≠ r₃) (h₂₃ : r₂ ≠ r₃) (Q : halfKernel E H) :
    Q.val.val.xc - r₁ ≠ 0 ∧ Q.val.val.xc - r₂ ≠ 0 ∧ Q.val.val.xc - r₃ ≠ 0 := by
  have hQ : Q.val ≠ 0 := ((mem_halfKernel E H Q.val).mp Q.property).1
  have hQ0 : Q.val.val ≠ 0 := fun hz => hQ (Subtype.ext hz)
  have ht := odd_kernel_tangent_ne_zero E H ho Q.val hQ
  have hf := tangent_square_eq_root_product (E.map (algebraMap K (AlgebraicClosure K)))
    (by norm_num) r₁ r₂ r₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ _ _
    (Point.nonsingular_xc_yc hQ0).1
  have hn : 4 * (Q.val.val.xc - r₁) * (Q.val.val.xc - r₂) *
      (Q.val.val.xc - r₃) ≠ 0 := by rw [← hf]; exact pow_ne_zero _ ht
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).1).2,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).2, (mul_ne_zero_iff.mp hn).2⟩

omit [CharZero K] [E.IsElliptic] in
/-- [DkMath.Lib] 半核を添字にしたファイバー因子の次数は、元の核の位数に一致する。

`fiberFactor` は一本の単純根と半核各点の二重根から作るため、次数は
`2 * |halfKernel| + 1` である。半核分割公式をここで接続すると、
実際の奇数核の有限ファイバーに期待される次数 `|H|` を得る。 -/
theorem halfKernel_fiberFactor_natDegree (ho : Odd (Nat.card H))
    (e : AlgebraicClosure K) (ξ : halfKernel E H → AlgebraicClosure K) :
    (fiberFactor (Finset.univ : Finset (halfKernel E H)) e ξ).natDegree = Nat.card H := by
  rw [fiberFactor_natDegree]
  have hc := card_halfKernel E H ho
  rw [Finset.card_univ, Fintype.card_coe]
  omega

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
