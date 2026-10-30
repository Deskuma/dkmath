/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelPairRelation
import DkMath.Lib.NumberTheory.EllipticFiniteKernelNonsingular
import DkMath.Lib.NumberTheory.WeierstrassDiscriminantRoots

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelDiscriminantProduct"

/-!
# 奇数核 Vélu 商の判別式積

三つの源側2捩れ点を同じ判別式根差公式へ渡し、`kernelAt_twoTorsion_root` と
`kernelXAt_injective_on_twoTorsion` で商側の三根を供給する。半核の根差積と
接線平方積は `EllipticFiniteKernelPairRelation` が既に組み立てているため、ここでは
点の選択・根の分離・指数 `2 * |H⁺| + 1 = |H|` の輸送だけを行う。

この定理が閉じるのは NOTE-032 の判別式積 `hprod` であり、後続の局所付値計算や
一般 `hno` の大域算術を自動的に閉じるものではない。
-/

namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open EllipticFunctionField EllipticTorsionRepresentation
open DkMath.Lib.NumberTheory.WeierstrassDiscriminantAssembly
open DkMath.Lib.NumberTheory.WeierstrassDiscriminantRoots
open scoped BigOperators

noncomputable local instance instDecidableEqEllipticFiniteKernelDiscriminantProduct
    {α : Type*} : DecidableEq α := Classical.decEq _

variable {K : Type*} [Field K] [CharZero K]

/-- [DkMath.Lib] 奇数有限核に対する Vélu 判別式積公式。

`exists_three_nonzero_fixed_points` から選んだ三点は、奇数核の固定点消滅補題により
核外であり、`Point.isRoot_twoTorsionPolynomial_of_add_self` により源の2捩れ根になる。
商側では `kernelAt_twoTorsion_root` と `kernelXAt_injective_on_twoTorsion` が同じ三点を
相異なる二捩れ根へ送る。従って源・商の判別式表示を自動生成して、三枝の
`veluHalf_base_discriminant_product_of_three_two_torsion_points` を適用できる。
-/
theorem kernelModel_discriminant_product_of_odd_card
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) :
    (kernelModel E H).Δ *
      (∏ Q : halfKernel E H,
        (2 * Q.val.val.yc +
          (E.map (algebraMap K (AlgebraicClosure K))).a₁ * Q.val.val.xc +
          (E.map (algebraMap K (AlgebraicClosure K))).a₃) ^ 2) ^ 4 =
      (E.map (algebraMap K (AlgebraicClosure K))).Δ ^ Nat.card H := by
  let W : WeierstrassCurve (AlgebraicClosure K) :=
    E.map (algebraMap K (AlgebraicClosure K))
  obtain ⟨P, hP0, hneg, hinj⟩ := exists_three_nonzero_fixed_points E
  have hPout : ∀ i, P i ∉ H := by
    intro i hi
    exact hP0 i (eq_zero_of_mem_odd_kernel_fixed E H ho (P i) hi (hneg i))
  have hns : ∀ i, W.toAffine.Nonsingular (P i).xc (P i).yc := by
    intro i
    exact Point.nonsingular_xc_yc (hP0 i)
  have hsum : ∀ i, P i + P i = 0 := by
    intro i
    simpa only [hneg i] using (add_neg_cancel (P i))
  have htor : ∀ i, 2 • (Point.some (P i).xc (P i).yc (hns i) :
      W.toAffine.Point) = 0 := by
    intro i
    have heq : P i = Point.some (P i).xc (P i).yc (hns i) := by
      exact Point.eq_some_xc_yc (hP0 i)
    have hsum' : (P i : W.toAffine.Point) + P i = 0 := by
      exact hsum i
    rw [two_nsmul]
    rw [← heq]
    exact hsum'
  have hroot : ∀ i, W.twoTorsionPolynomial.toPoly.eval (P i).xc = 0 := by
    intro i
    have hi := Point.isRoot_twoTorsionPolynomial_of_add_self (W := W.toAffine)
      (hns i) (by simpa only [two_nsmul] using htor i)
    exact hi
  have hsep (i j : Fin 3) (hij : i ≠ j) : (P i).xc ≠ (P j).xc := by
    intro he
    apply hij
    apply hinj
    rcases point_eq_or_eq_neg_of_xc_eq E (P i) (P j) (hP0 i) (hP0 j) he with h | h
    · exact h
    · simpa only [hneg j] using h
  have h₁₂ : (P 0).xc ≠ (P 1).xc := hsep 0 1 (by decide)
  have h₁₃ : (P 0).xc ≠ (P 2).xc := hsep 0 2 (by decide)
  have h₂₃ : (P 1).xc ≠ (P 2).xc := hsep 1 2 (by decide)
  have hXsep (i j : Fin 3) (hij : i ≠ j) :
      kernelXAt E H (P i) (hPout i) ≠ kernelXAt E H (P j) (hPout j) := by
    intro he
    apply hij
    exact hinj (kernelXAt_injective_on_twoTorsion E H ho (P i) (P j)
      (hneg i) (hneg j) (hPout i) (hPout j) he)
  have hX₁₂ : kernelXAt E H (P 0) (hPout 0) ≠ kernelXAt E H (P 1) (hPout 1) :=
    hXsep 0 1 (by decide)
  have hX₁₃ : kernelXAt E H (P 0) (hPout 0) ≠ kernelXAt E H (P 2) (hPout 2) :=
    hXsep 0 2 (by decide)
  have hX₂₃ : kernelXAt E H (P 1) (hPout 1) ≠ kernelXAt E H (P 2) (hPout 2) :=
    hXsep 1 2 (by decide)
  have hΔ : W.Δ = 16 * (((P 1).xc - (P 0).xc) *
      ((P 2).xc - (P 0).xc) * ((P 2).xc - (P 1).xc)) ^ 2 := by
    have h := discriminant_eq_root_differences W (NeZero.ne (2 : AlgebraicClosure K))
      (P 0).xc (P 1).xc (P 2).xc (hroot 0) (hroot 1) (hroot 2)
      h₁₂ h₁₃ h₂₃
    calc
      W.Δ = 16 * (((P 0).xc - (P 1).xc) * ((P 0).xc - (P 2).xc) *
        ((P 1).xc - (P 2).xc)) ^ 2 := by simpa only [W] using h
      _ = _ := by ring
  have hΔ' : (kernelModel E H).Δ = 16 *
      ((kernelXAt E H (P 0) (hPout 0) - kernelXAt E H (P 1) (hPout 1)) *
        (kernelXAt E H (P 0) (hPout 0) - kernelXAt E H (P 2) (hPout 2)) *
        (kernelXAt E H (P 1) (hPout 1) - kernelXAt E H (P 2) (hPout 2))) ^ 2 := by
    apply discriminant_eq_root_differences (kernelModel E H)
      (NeZero.ne (2 : AlgebraicClosure K))
      (kernelXAt E H (P 0) (hPout 0)) (kernelXAt E H (P 1) (hPout 1))
      (kernelXAt E H (P 2) (hPout 2))
    · exact kernelAt_twoTorsion_root E H (P 0) (hPout 0) (hneg 0)
    · exact kernelAt_twoTorsion_root E H (P 1) (hPout 1) (hneg 1)
    · exact kernelAt_twoTorsion_root E H (P 2) (hPout 2) (hneg 2)
    · exact hX₁₂
    · exact hX₁₃
    · exact hX₂₃
  have hmain := veluHalf_base_discriminant_product_of_three_two_torsion_points E H ho
    (P 0) (P 1) (P 2) (hPout 0) (hPout 1) (hPout 2)
    (hneg 0) (hneg 1) (hns 0) (htor 0) (hns 1) (htor 1)
    (hroot 0) (hroot 1) (hroot 2) h₁₂ h₁₃ h₂₃
    W.Δ (kernelModel E H).Δ
    (∏ Q : halfKernel E H, (2 * Q.val.val.yc + W.a₁ * Q.val.val.xc + W.a₃) ^ 2)
    rfl
    hΔ
    hΔ'
  rw [card_halfKernel E H ho] at hmain
  simpa [W] using hmain

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
