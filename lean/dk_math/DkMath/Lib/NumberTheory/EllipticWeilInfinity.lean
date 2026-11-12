/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticWeilValuation
import DkMath.Lib.NumberTheory.EllipticPointIdealNorm
import DkMath.Lib.NumberTheory.EllipticInfinityValuation

#print "file: DkMath.Lib.NumberTheory.EllipticWeilInfinity"

/-!
# 無限遠点に隠れた一つの極

ファイバーのn²点からOだけを除き、CRTでノルム次数を求める。
次数付値を用いれば、同じ分子の無限遠点の位数は次数の負となる。
商ではn²が消え、非零目標には一重極−1、零目標には0が残る。
有限点とOを合わせた全点の位数公式も、同じ実際のValuationから得る。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WithZero
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
attribute [local instance] geometricCoordinateRing_isDedekindDomain

open Classical in
/-- 次数にOの寄与を足すとn²になる。自然数の切り捨て減算を使わない計数式。 -/
theorem normDegree_weilNumerator_balance (n : ℕ) (hn : n ≠ 0) (T : Points E) (hT : n • T = 0) :
    (Algebra.norm (AlgebraicClosure K)[X] (weilNumerator E n hn T hT)).natDegree +
      (if T = 0 then 1 else 0) = n ^ 2 := by
  classical
  let s : Finset (E.toAffine⁄(AlgebraicClosure K)).Point := (fiber_finite E n hn T).toFinset
  have hd := EllipticPointIdealNorm.natDegree_norm_of_span_eq_prod
    (E.baseChange (AlgebraicClosure K)) s (span_weilNumerator E n hn T hT)
  have hc : s.card = n ^ 2 := by
    change (fiber_finite E n hn T).toFinset.card = _
    rw [← Set.ncard_eq_toFinset_card (fiberSet E n T) (fiber_finite E n hn T), fiber_card E n hn T]
  have hm : (0 : (E.toAffine⁄(AlgebraicClosure K)).Point) ∈ s ↔ T = 0 := by
    change (0 : Points E) ∈ (fiber_finite E n hn T).toFinset ↔ T = 0
    rw [Set.Finite.mem_toFinset, mem_fiberSet, smul_zero, eq_comm]
  rw [Finset.filter_ne'] at hd
  by_cases hT0 : T = 0
  · rw [ite_eq_left hT0]
    have he := Finset.card_erase_add_one (hm.mpr hT0)
    omega
  · rw [ite_eq_right hT0]
    have he : s.erase 0 = s := Finset.erase_eq_of_notMem (fun h => hT0 (hm.mp h))
    rw [he] at hd
    omega

open Classical in
/-- 整数で書いたノルム次数公式。Oにある一つのファイバー点を明示的に差し引く。 -/
theorem normDegree_weilNumerator (n : ℕ) (hn : n ≠ 0) (T : Points E) (hT : n • T = 0) :
    ((Algebra.norm (AlgebraicClosure K)[X] (weilNumerator E n hn T hT)).natDegree : ℤ) =
      (n : ℤ) ^ 2 - if T = 0 then 1 else 0 := by
  have h := congrArg (fun k : ℕ => (k : ℤ)) (normDegree_weilNumerator_balance E n hn T hT)
  push_cast at h
  split_ifs at h ⊢ <;> omega

omit [CharZero K] in
/-- Oに対応する実際の無限遠点付値で、非零関数の整数位数を読む。 -/
noncomputable def infinityOrder (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (_hf : f ≠ 0) : ℤ :=
  -log (EllipticInfinityValuation.valuationInfty (E.toAffine⁄(AlgebraicClosure K)) f)

open Classical in
/-- 同じ分子の無限遠点の位数はノルム次数の負である。 -/
theorem infinityOrder_weilNumerator (n : ℕ) (hn : n ≠ 0) (T : Points E) (hT : n • T = 0) :
    infinityOrder E (algebraMap (E.toAffine⁄(AlgebraicClosure K)).CoordinateRing
      (E.toAffine⁄(AlgebraicClosure K)).FunctionField (weilNumerator E n hn T hT))
      (algebraMap_weilNumerator_ne_zero E n hn T hT) =
      -((n : ℤ) ^ 2 - if T = 0 then 1 else 0) := by
  rw [infinityOrder, EllipticInfinityValuation.valuationInfty_algebraMap_of_ne_zero _
    (weilNumerator_ne_zero E n hn T hT), log_exp, normDegree_weilNumerator E n hn T hT]

open Classical in
/-- 商のOでの位数。非零目標では有限零点の個数の差1が一重極として現れる。 -/
theorem infinityOrder_weilFunction (n : ℕ) (hn : n ≠ 0) (T : Points E) (hT : n • T = 0) :
    infinityOrder E (weilFunction E n hn T hT) (weilFunction_ne_zero E n hn T hT) =
      if T = 0 then 0 else -1 := by
  rw [infinityOrder, weilFunction, map_div₀,
    EllipticInfinityValuation.valuationInfty_algebraMap_of_ne_zero _ (weilNumerator_ne_zero E n hn T hT),
    EllipticInfinityValuation.valuationInfty_algebraMap_of_ne_zero _ (weilNumerator_ne_zero E n hn 0 (smul_zero n)),
    ← exp_sub, log_exp, normDegree_weilNumerator E n hn T hT,
    normDegree_weilNumerator E n hn 0 (smul_zero n)]
  simp only [ite_true]
  split_ifs <;> ring

omit [CharZero K] in
open Classical in
/-- 全点の位数。有限点は既存の場所で、Oはノルム次数から構成した付値で測る。 -/
noncomputable def pointOrder (P : Points E) (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField)
    (hf : f ≠ 0) : ℤ :=
  if hP : P = 0 then infinityOrder E f hf else finitePointOrder E P hP f hf

open Classical in
/-- 有限点とOを合わせた、同じ商の全点の位数公式。 -/
theorem pointOrder_weilFunction (n : ℕ) (hn : n ≠ 0) (T : Points E) (hT : n • T = 0)
    (P : Points E) :
    pointOrder E P (weilFunction E n hn T hT) (weilFunction_ne_zero E n hn T hT) =
      (if n • P = T then 1 else 0) - (if n • P = 0 then 1 else 0) := by
  classical
  by_cases hP : P = 0
  · subst P
    rw [pointOrder, dite_eq_left rfl, infinityOrder_weilFunction]
    simp only [smul_zero, ite_true]
    by_cases hT0 : T = 0
    · simp [hT0]
    · simp [hT0, Ne.symm hT0]
  · rw [pointOrder, dite_eq_right hP, order_weilFunction E n hn T hT P hP]

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
