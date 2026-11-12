/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticWeilInfinity
import DkMath.Lib.NumberTheory.EllipticTranslationInfinity

#print "file: DkMath.Lib.NumberTheory.EllipticWeilTransport"

/-!
# 無限遠点を含む全点の付値輸送

有限点間では割線・接線の合同から付値環を比較し、移動先がOなら次数付値に接続する。
移動元がOの場合は逆の平行移動を使う。この三つを合わせ、同じ実際の関数体上で
全点の付値と整数位数の輸送を証明する。n-torsionの移動ではファイバー指示関数が不変となる。
この結論は付値の一致であり、比例定数の構成やWeil対の非退化性は後続の課題である。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open WeierstrassCurve WeierstrassCurve.Affine WithZero
open EllipticFunctionField
variable {K : Type*} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
attribute [local instance] geometricCoordinateRing_isDedekindDomain

open Classical in
/-- 全点の実際の付値。Oでは次数付値を、有限点では高さ1素イデアルの付値を用いる。 -/
noncomputable def pointValuation (P : (E⁄(AlgebraicClosure K)).Point) :
    Valuation (E.toAffine⁄(AlgebraicClosure K)).FunctionField ℤᵐ⁰ :=
  if hP : P = 0 then EllipticInfinityValuation.valuationInfty (E.toAffine⁄(AlgebraicClosure K))
  else finitePointValuation E P hP

open Classical in
/-- 平行移動と逆移動は関数体でも相殺する。 -/
theorem transEquiv_neg_apply (S : (E⁄(AlgebraicClosure K)).Point) (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) :
    transEquiv E (AlgebraicClosure K) (-S) (transEquiv E (AlgebraicClosure K) S f) = f := by
  have h := DFunLike.congr_fun (transEquiv_add E (AlgebraicClosure K) (-S) S) f
  simpa only [neg_add_cancel, transEquiv_zero, AlgEquiv.coe_refl, id_eq, AlgEquiv.trans_apply] using h.symm

open Classical in
/-- 移動元・移動先がOの場合も含む付値輸送。関数は任意で、零関数も許す。 -/
theorem pointValuation_transEquiv (P S : (E⁄(AlgebraicClosure K)).Point)
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) :
    pointValuation E P (transEquiv E (AlgebraicClosure K) S f) = pointValuation E (P + S) f := by
  classical
  by_cases hP : P = 0
  · subst P
    rw [zero_add, pointValuation, dite_eq_left rfl]
    by_cases hS : S = 0
    · subst S
      simp [pointValuation, transEquiv_zero]
    · rw [pointValuation, dite_eq_right hS]
      have h := valuation_placeOf_neg_transEquiv E (AlgebraicClosure K) (-S)
        (neg_ne_zero.mpr hS) (transEquiv E (AlgebraicClosure K) S f)
      simp only [neg_neg] at h
      rw [transEquiv_neg_apply] at h
      exact h.symm
  · rw [pointValuation, dite_eq_right hP]
    by_cases hPS : P + S = 0
    · have hS : S ≠ 0 := by rintro rfl; exact hP (by simpa using hPS)
      have he : P = -S := eq_neg_of_add_eq_zero_left hPS
      rw [hPS, pointValuation, dite_eq_left rfl]
      subst P
      exact valuation_placeOf_neg_transEquiv E (AlgebraicClosure K) S hS f
    · rw [pointValuation, dite_eq_right hPS]
      exact valuation_transEquiv_eq E (AlgebraicClosure K) hP hPS f

open Classical in
/-- 位数の定義は、全点の付値の負の整数指数と一致する。 -/
theorem pointOrder_eq_neg_log (P : Points E) (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField)
    (hf : f ≠ 0) : pointOrder E P f hf = -log (pointValuation E P f) := by
  classical
  unfold pointOrder pointValuation
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact (h₂ h₁).elim
  · exact (h₁ h₂).elim
  · rfl

open Classical in
/-- 非零関数の整数位数も全点で輸送される。非零性は実際の自己同型から供給する。 -/
theorem pointOrder_transEquiv (P S : Points E)
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (hf : f ≠ 0) :
    pointOrder E P (transEquiv E (AlgebraicClosure K) S f)
      ((transEquiv E (AlgebraicClosure K) S).toRingEquiv.map_ne_zero_iff.mpr hf) = pointOrder E (P + S) f hf := by
  exact (pointOrder_eq_neg_log E P _ _).trans
    ((congrArg (fun z : ℤᵐ⁰ => -log z) (pointValuation_transEquiv E P S f)).trans
      (pointOrder_eq_neg_log E (P + S) f hf).symm)

variable [CharZero K]

open Classical in
/-- 全点での乗法的付値公式。零点+1はexp(−1)、極−1はexp(1)に対応する。 -/
theorem pointValuation_weilFunction (n : ℕ) (hn : n ≠ 0) (T : Points E)
    (hT : n • T = 0) (P : Points E) :
    pointValuation E P (weilFunction E n hn T hT) =
      exp (-((if n • P = T then 1 else 0) - (if n • P = 0 then 1 else 0) : ℤ)) := by
  have hv := (pointValuation E P).ne_zero_iff.mpr (weilFunction_ne_zero E n hn T hT)
  have ho := pointOrder_eq_neg_log E P _ (weilFunction_ne_zero E n hn T hT)
  rw [pointOrder_weilFunction E n hn T hT P] at ho
  exact (exp_log hv).symm.trans (congrArg exp (by omega))

open Classical in
/-- 移動先Oも含むWeil関数の乗法的付値。任意のSに対する輸送公式である。 -/
theorem pointValuation_transEquiv_weilFunction (n : ℕ) (hn : n ≠ 0) (T : Points E)
    (hT : n • T = 0) (P S : Points E) :
    pointValuation E P (transEquiv E (AlgebraicClosure K) S (weilFunction E n hn T hT)) =
      exp (-((if n • (P + S) = T then 1 else 0) - (if n • (P + S) = 0 then 1 else 0) : ℤ)) := by
  exact (pointValuation_transEquiv E P S _).trans (pointValuation_weilFunction E n hn T hT (P + S))

open Classical in
/-- 同じWeil関数の、平行移動後の全点での位数。P+S=Oもこの式に含まれる。 -/
theorem pointOrder_transEquiv_weilFunction (n : ℕ) (hn : n ≠ 0) (T : Points E)
    (hT : n • T = 0) (P S : Points E) :
    pointOrder E P (transEquiv E (AlgebraicClosure K) S (weilFunction E n hn T hT))
      ((transEquiv E (AlgebraicClosure K) S).toRingEquiv.map_ne_zero_iff.mpr (weilFunction_ne_zero E n hn T hT)) =
      (if n • (P + S) = T then 1 else 0) - (if n • (P + S) = 0 then 1 else 0) := by
  exact (pointOrder_transEquiv E P S _ (weilFunction_ne_zero E n hn T hT)).trans
    (pointOrder_weilFunction E n hn T hT (P + S))

open Classical in
/-- n-torsionによる平行移動は同じ関数の全点での位数を保存する。
同じ因子という点ごとの内容を固定するが、因子型や比例定数をここでは導入しない。 -/
theorem pointOrder_transEquiv_weilFunction_of_torsion (n : ℕ) (hn : n ≠ 0) (T : Points E)
    (hT : n • T = 0) (P S : Points E) (hS : n • S = 0) :
    pointOrder E P (transEquiv E (AlgebraicClosure K) S (weilFunction E n hn T hT))
      ((transEquiv E (AlgebraicClosure K) S).toRingEquiv.map_ne_zero_iff.mpr (weilFunction_ne_zero E n hn T hT)) =
      pointOrder E P (weilFunction E n hn T hT) (weilFunction_ne_zero E n hn T hT) := by
  classical
  rw [pointOrder_transEquiv_weilFunction, pointOrder_weilFunction, smul_add, hS, add_zero]

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
