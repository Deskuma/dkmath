/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelLocalIntegrality
import DkMath.Lib.NumberTheory.WeierstrassVeluPair

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelPair"

/-!
# 同じ平行移動和を半核代表の有理式へ変換する

[DkMath.Lib] 既存のX_H,Y_Hを新しい関数へ置き換えず、同じ一般点への群法から
反転対の二つの割線を計算する。半核の分割は巡回生成元に依存しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine WithZero
open EllipticFunctionField EllipticTorsionRepresentation WeierstrassVeluPair
open scoped BigOperators
variable {K : Type*} [Field K] [NeZero (2 : K)] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance instDecidableEqEllipticFiniteKernelPair {α : Type*} : DecidableEq α := Classical.decEq _

omit [NeZero (2 : K)] [E.IsElliptic] in
/-- [DkMath.Lib] 同じ奇数核上の任意の有限和をOと半核の反転対へ分割する。 -/
theorem sum_kernel_half {M : Type*} [AddCommMonoid M]
    (H : AddSubgroup (Points E)) [Fintype H] (ho : Odd (Nat.card H)) (f : H → M) :
    (∑ Q : H, f Q) = f 0 + ∑ Q ∈ halfKernel E H, (f Q + f (-Q)) := by
  obtain ⟨hp, hd⟩ := halfKernel_partition E H ho
  have he := Finset.sum_erase_add (Finset.univ : Finset H) f (Finset.mem_univ 0)
  rw [← hp, Finset.sum_union hd, Finset.sum_image (by intro a _ b _ h; exact neg_injective h)] at he
  rw [Finset.sum_add_distrib]
  exact he.symm.trans (by ac_rfl)

omit [NeZero (2 : K)] in
/-- [DkMath.Lib] 一般xは任意の定数座標と異なる。Oの極から直接証明する。 -/
theorem genericX_ne_const (a : AlgebraicClosure K) :
    genericX E (AlgebraicClosure K) ≠ algebraMap _ _ a := by
  intro he
  have hc := pointValuation_const_le_one E (0 : (E⁄(AlgebraicClosure K)).Point) a
  rw [← he, pointValuation_zero_genericX, ← exp_zero, exp_le_exp] at hc
  norm_num at hc

omit [NeZero (2 : K)] in
/-- [DkMath.Lib] 同じ実点Qと−Qの平行移動を、割線の二つの有理式へ接続する。 -/
theorem translated_pair (Q : (E⁄(AlgebraicClosure K)).Point) (hQ : Q ≠ 0) :
    let F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
    let W := E.map (algebraMap K F)
    let c := algebraMap (AlgebraicClosure K) F
    let x := genericX E (AlgebraicClosure K)
    let y := genericY E (AlgebraicClosure K)
    let tx := fun P : (E⁄(AlgebraicClosure K)).Point => transEquiv E (AlgebraicClosure K) P x
    let ty := fun P : (E⁄(AlgebraicClosure K)).Point => transEquiv E (AlgebraicClosure K) P y
    tx Q + tx (-Q) - 2 * c Q.xc = xCorrection W (c Q.xc) (c Q.yc) x ∧
      (2 * ty Q + W.a₁ * tx Q + W.a₃) + (2 * ty (-Q) + W.a₁ * tx (-Q) + W.a₃) =
        (2 * y + W.a₁ * x + W.a₃) * zCorrection W (c Q.xc) (c Q.yc) x := by
  cases Q with
  | zero => exact (hQ rfl).elim
  | some a b hab =>
    dsimp only
    have hx := genericX_ne_const E a
    have hqn := (E.toAffine.baseChange_nonsingular
      (f := Algebra.ofId (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField)
      (algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField).injective a b).mpr hab
    have hqe := hqn.1
    have hn : (algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField)
        ((E.toAffine⁄(AlgebraicClosure K)).negY a b) =
        (E.toAffine⁄(E.toAffine⁄(AlgebraicClosure K)).FunctionField).negY
          (algebraMap _ _ a) (algebraMap _ _ b) := by
      simp only [negY, map_sub, map_neg, map_mul]
      rfl
    simp only [Point.neg_some, transEquiv_genericX, transEquiv_genericY, EllipticFunctionField.genericPoint,
      Point.baseChange, Point.map_some, Algebra.ofId_apply, hn,
      Point.add_of_X_ne hx, Point.xc_some, Point.yc_some, slope_of_X_ne hx]
    exact ⟨secant_pair_x _ hx (generic_equation E _) hqe,
      secant_pair_z _ hx (generic_equation E _) hqe⟩

omit [NeZero (2 : K)] in
/-- [DkMath.Lib] 同じX_Hの半核表示。既存関数のまま明示的有理式へ展開する。 -/
theorem veluX_half (H : AddSubgroup (Points E)) [Fintype H] (ho : Odd (Nat.card H)) :
    let F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
    veluX E H = genericX E (AlgebraicClosure K) + ∑ Q ∈ halfKernel E H,
      xCorrection (E.map (algebraMap K F)) (algebraMap _ F Q.val.xc)
        (algebraMap _ F Q.val.yc) (genericX E (AlgebraicClosure K)) := by
  dsimp only
  have hs := sum_kernel_half E H ho (fun Q => transEquiv E (AlgebraicClosure K) Q.val
    (genericX E (AlgebraicClosure K)) - algebraMap _ _ Q.val.xc)
  have he : veluX E H = ∑ Q : H, (transEquiv E (AlgebraicClosure K) Q.val
      (genericX E (AlgebraicClosure K)) - algebraMap _ _ Q.val.xc) := by
    simp only [veluX, kernelTrace, map_sum, Finset.sum_sub_distrib]
  rw [he, hs]
  have hz : transEquiv E (AlgebraicClosure K) (0 : H).val
      (genericX E (AlgebraicClosure K)) - algebraMap _ _ (0 : H).val.xc =
      genericX E (AlgebraicClosure K) := by
    change transEquiv E (AlgebraicClosure K) (0 : (E⁄(AlgebraicClosure K)).Point)
      (genericX E (AlgebraicClosure K)) - algebraMap _ _ (0 : AlgebraicClosure K) = _
    rw [transEquiv_zero, map_zero, sub_zero]; rfl
  rw [hz]
  congr 1
  apply Finset.sum_congr rfl
  intro Q hQ
  have hQ0 : Q.val ≠ 0 := fun he => (mem_halfKernel E H Q).mp hQ |>.1 <| Subtype.ext he
  have hn : (-Q.val).xc = Q.val.xc := by
    cases (Q.val : (E⁄(AlgebraicClosure K)).Point) <;> rfl
  simp only [AddSubgroup.coe_neg, hn]
  have hp : transEquiv E (AlgebraicClosure K) Q.val (genericX E (AlgebraicClosure K)) +
      transEquiv E (AlgebraicClosure K) (-Q.val) (genericX E (AlgebraicClosure K)) -
      2 * algebraMap _ _ Q.val.xc = xCorrection _ _ _ _ := (translated_pair E Q.val hQ0).1
  linear_combination hp

omit [NeZero (2 : K)] in
/-- [DkMath.Lib] 同じ平方完成座標2Y_H+a₁X_H+a₃の半核表示。
補正和のO項を含めて数えることで、余分な|H|a₃を残さない。 -/
theorem veluZ_half (H : AddSubgroup (Points E)) [Fintype H] (ho : Odd (Nat.card H)) :
    let F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
    let W := E.map (algebraMap K F)
    let x := genericX E (AlgebraicClosure K)
    let z := 2 * genericY E (AlgebraicClosure K) + W.a₁ * x + W.a₃
    2 * veluY E H + W.a₁ * veluX E H + W.a₃ = z * (1 + ∑ Q ∈ halfKernel E H,
      zCorrection W (algebraMap _ F Q.val.xc) (algebraMap _ F Q.val.yc) x) := by
  dsimp only
  let F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
  let W := E.map (algebraMap K F)
  let x := genericX E (AlgebraicClosure K)
  let y := genericY E (AlgebraicClosure K)
  let c := algebraMap (AlgebraicClosure K) F
  let f : H → F := fun Q => 2 * transEquiv E (AlgebraicClosure K) Q.val y +
    W.a₁ * transEquiv E (AlgebraicClosure K) Q.val x + W.a₃
  have hc₁ : c (E⁄(AlgebraicClosure K)).a₁ = W.a₁ := by
    exact (IsScalarTower.algebraMap_apply K (AlgebraicClosure K) F E.a₁).symm
  have hc₃ : c (E⁄(AlgebraicClosure K)).a₃ = W.a₃ := by
    exact (IsScalarTower.algebraMap_apply K (AlgebraicClosure K) F E.a₃).symm
  have hs := congrArg c (kernel_coordinate_correction E H)
  simp only [map_add, map_mul, map_natCast, hc₁, hc₃, map_sum] at hs
  have ht : 2 * veluY E H + W.a₁ * veluX E H + W.a₃ = ∑ Q : H, f Q := by
    dsimp only [f]
    simp only [veluX, veluY, kernelTrace, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, map_sum]
    change 2 * (_ - ∑ Q : H, c Q.val.yc) + W.a₁ * (_ - ∑ Q : H, c Q.val.xc) + W.a₃ = _
    linear_combination -hs
  change 2 * veluY E H + W.a₁ * veluX E H + W.a₃ = _
  rw [ht, sum_kernel_half E H ho f]
  have h0 : f 0 = 2 * y + W.a₁ * x + W.a₃ := by
    change 2 * transEquiv E (AlgebraicClosure K) (0 : (E⁄(AlgebraicClosure K)).Point) y +
      W.a₁ * transEquiv E (AlgebraicClosure K) (0 : (E⁄(AlgebraicClosure K)).Point) x + W.a₃ = _
    rw [transEquiv_zero]; rfl
  rw [h0]
  have hp : (∑ Q ∈ halfKernel E H, (f Q + f (-Q))) =
      (2 * y + W.a₁ * x + W.a₃) * ∑ Q ∈ halfKernel E H,
        zCorrection W (c Q.val.xc) (c Q.val.yc) x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro Q hQ
    exact (translated_pair E Q.val (fun he => (mem_halfKernel E H Q).mp hQ |>.1 <| Subtype.ext he)).2
  rw [hp]
  ring

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
