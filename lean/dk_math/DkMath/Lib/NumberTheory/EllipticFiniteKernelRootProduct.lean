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

/-- [DkMath.Lib] 半核の各添字を明示した二捩れ根輸送。

`halfKernel` は反転対から一方だけを選ぶ有限集合である。ここではその選択を
隠さず、各 `Q : halfKernel E H` について `P + Q` の特殊化座標が標的
二捩れ多項式の根になることを直接記録する。これは `fiberFactor` の根包含を
作る幾何学側の入力であり、二重根（多重度）の主張は別の層に残す。 -/
theorem kernelAt_twoTorsion_root_halfKernel
    (P : Points E) (hP : P ∉ H) (hneg : -P = P)
    (Q : halfKernel E H) :
    (kernelModel E H).twoTorsionPolynomial.toPoly.eval
      (kernelXAt E H (P + Q.val.val)
        (add_not_mem_kernel E H P hP Q.val)) = 0 := by
  exact kernelAt_twoTorsion_root_translation E H P hP hneg Q.val

omit [CharZero K] [E.IsElliptic] in
/-- [DkMath.Lib] 半核ファイバー因子の根包含と次数上界から、実際のモニック分子を
`fiberFactor` へ同定する。

幾何学側は `kernelAt_twoTorsion_root_halfKernel` で各根の存在を供給するが、
各根が二重に現れることは自動ではない。そのため `hroots` は多重集合として
明示的に要求し、ここでは半核の次数公式だけを加えて、同定の代数部分を閉じる。 -/
theorem eq_halfKernel_fiberFactor_of_monic_of_roots_le
    (ho : Odd (Nat.card H))
    (e : AlgebraicClosure K) (ξ : halfKernel E H → AlgebraicClosure K)
    (p : Polynomial (AlgebraicClosure K)) (hp : p.Monic)
    (hroots : (fiberFactor (Finset.univ : Finset (halfKernel E H)) e ξ).roots ≤ p.roots)
    (hdeg : p.natDegree ≤ Nat.card H) :
    p = fiberFactor (Finset.univ : Finset (halfKernel E H)) e ξ := by
  apply eq_fiberFactor_of_monic_of_roots_le (Finset.univ : Finset (halfKernel E H))
    e ξ p hp hroots
  rw [halfKernel_fiberFactor_natDegree E H ho e ξ]
  exact hdeg

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
