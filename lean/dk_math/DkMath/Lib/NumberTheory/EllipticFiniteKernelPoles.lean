/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernel
import DkMath.Lib.NumberTheory.EllipticCoordinatePoles

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelPoles"

/-!
# NOTE-032-005C₂b: 同じ正規化座標和の極と非定数性

[DkMath.Lib] 有限核Hの総和で、Oに極を持つのは移動量Q=Oの一項だけ。
他の項と補正定数の付値は1以下なので、厳密に大きい一項の値は相殺されない。
これからX_H,Y_HのOでの値exp(2),exp(3)を証明し、同じ核の不変性でHの全点へ運ぶ。
Hの外では全項が正則である。したがって極の支持は正確に同じHとなる。

定数はOでも正則なので、二関数は非定数かつ非零である。
この章は実際の関数の局所位数までを固定する。商曲線方程式、固定体の生成、
標的の非特異性や点群写像は別の証明である。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WithZero
open EllipticFunctionField EllipticTorsionRepresentation
open scoped BigOperators
variable {K : Type*} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance instDecidableEqEllipticFiniteKernelPoles : DecidableEq (AlgebraicClosure K) := Classical.decEq _

/-- [DkMath.Lib] Oだけに極を持つ関数の正規化平行移動和は、Oで同じ極を保つ。
最大の一項の値と他の全項の値を厳密に分離する。 -/
theorem normalized_trace_valuation_zero (H : AddSubgroup (Points E)) [Fintype H]
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (c : AlgebraicClosure K)
    (hregular : ∀ P : Points E, P ≠ 0 → pointValuation E P f ≤ 1)
    (hpole : 1 < pointValuation E 0 f) :
    pointValuation E 0 (kernelTrace E H f -
      algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField c) =
      pointValuation E 0 f := by
  classical
  have hv (Q : H) : pointValuation E 0 (transEquiv E (AlgebraicClosure K) Q.val f) =
      pointValuation E Q.val f := by
    have hz : (0 : (E⁄(AlgebraicClosure K)).Point) +
        (show (E⁄(AlgebraicClosure K)).Point from Q.val) = Q.val := zero_add _
    exact (pointValuation_transEquiv E 0 Q.val f).trans
      (congrArg (fun P : (E⁄(AlgebraicClosure K)).Point => pointValuation E P f) hz)
  have hsum : pointValuation E 0 (kernelTrace E H f) = pointValuation E 0 f := by
    unfold kernelTrace
    calc
      _ = pointValuation E 0 (transEquiv E (AlgebraicClosure K) (0 : H).val f) := by
        apply (pointValuation E 0).map_sum_eq_of_lt (Finset.mem_univ (0 : H))
        intro Q hQ
        have hn : Q ≠ 0 := by simpa using (Finset.mem_sdiff.mp hQ).2
        have hnval : Q.val ≠ 0 := fun he => hn (Subtype.ext he)
        rw [hv Q, hv 0]
        exact (hregular Q.val hnval).trans_lt hpole
      _ = pointValuation E 0 f := hv 0
  apply Eq.trans ((pointValuation E 0).map_sub_eq_of_lt_left ?_) hsum
  rw [hsum]
  exact (pointValuation_zero_const_le_one E c).trans_lt hpole

/-- [DkMath.Lib] 正規化x座標和のOでの値はexp(2)、すなわち極の位数は2。 -/
theorem veluX_valuation_zero (H : AddSubgroup (Points E)) [Fintype H] :
    pointValuation E 0 (veluX E H) = exp (2 : ℤ) := by
  unfold veluX
  rw [normalized_trace_valuation_zero E H _ _ (pointValuation_genericX_le_one E)]
  · exact pointValuation_zero_genericX E
  · rw [pointValuation_zero_genericX, ← exp_zero, exp_lt_exp]
    norm_num

/-- [DkMath.Lib] 正規化y座標和のOでの値はexp(3)、すなわち極の位数は3。 -/
theorem veluY_valuation_zero (H : AddSubgroup (Points E)) [Fintype H] :
    pointValuation E 0 (veluY E H) = exp (3 : ℤ) := by
  unfold veluY
  rw [normalized_trace_valuation_zero E H _ _ (pointValuation_genericY_le_one E)]
  · exact pointValuation_zero_genericY E
  · rw [pointValuation_zero_genericY, ← exp_zero, exp_lt_exp]
    norm_num

/-- [DkMath.Lib] 同じX_Hは係数体のどの定数とも異なる。Oでの極が定数性を排除する。 -/
theorem veluX_ne_const (H : AddSubgroup (Points E)) [Fintype H] (c : AlgebraicClosure K) :
    veluX E H ≠ algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField c := by
  intro he
  have h := pointValuation_zero_const_le_one E c
  rw [← he, veluX_valuation_zero, ← exp_zero, exp_le_exp] at h
  norm_num at h

/-- [DkMath.Lib] 同じY_Hも係数体のどの定数とも異なる。 -/
theorem veluY_ne_const (H : AddSubgroup (Points E)) [Fintype H] (c : AlgebraicClosure K) :
    veluY E H ≠ algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField c := by
  intro he
  have h := pointValuation_zero_const_le_one E c
  rw [← he, veluY_valuation_zero, ← exp_zero, exp_le_exp] at h
  norm_num at h

/-- [DkMath.Lib] 非定数性から、位数を論じるための同じX_Hの非零性を供給する。 -/
theorem veluX_ne_zero (H : AddSubgroup (Points E)) [Fintype H] : veluX E H ≠ 0 := by
  simpa only [map_zero] using veluX_ne_const E H 0

/-- [DkMath.Lib] 同じY_Hの非零性。零関数へ整数位数を付けないために明示する。 -/
theorem veluY_ne_zero (H : AddSubgroup (Points E)) [Fintype H] : veluY E H ≠ 0 := by
  simpa only [map_zero] using veluY_ne_const E H 0

/-- [DkMath.Lib] Oの外で正則な関数の平行移動和は、同じ核Hの外で正則。
P+Q=OならP=−Q∈Hとなるため、全項の移動先は有限点である。 -/
theorem normalized_trace_regular_outside (H : AddSubgroup (Points E)) [Fintype H]
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (c : AlgebraicClosure K)
    (hregular : ∀ P : Points E, P ≠ 0 → pointValuation E P f ≤ 1)
    (P : Points E) (hP : P ∉ H) :
    pointValuation E P (kernelTrace E H f -
      algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField c) ≤ 1 := by
  apply (pointValuation E P).map_sub_le _ (pointValuation_const_le_one E P c)
  unfold kernelTrace
  apply (pointValuation E P).map_sum_le
  intro Q _
  have ht : pointValuation E P (transEquiv E (AlgebraicClosure K) Q.val f) =
      pointValuation E (P + Q.val) f := pointValuation_transEquiv E P Q.val f
  rw [ht]
  apply hregular
  intro hz
  apply hP
  rw [eq_neg_of_add_eq_zero_left hz]
  exact H.neg_mem Q.property

/-- [DkMath.Lib] X_Hは同じ実点核Hの外では正則である。 -/
theorem veluX_regular_outside (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) : pointValuation E P (veluX E H) ≤ 1 :=
  normalized_trace_regular_outside E H _ _ (pointValuation_genericX_le_one E) P hP

/-- [DkMath.Lib] Y_Hも同じ核Hの外では正則である。 -/
theorem veluY_regular_outside (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) : pointValuation E P (veluY E H) ≤ 1 :=
  normalized_trace_regular_outside E H _ _ (pointValuation_genericY_le_one E) P hP

/-- [DkMath.Lib] 同じ核の任意の点でX_Hの値はexp(2)。Oからの輸送と不変性を使う。 -/
theorem veluX_valuation_of_mem (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∈ H) : pointValuation E P (veluX E H) = exp (2 : ℤ) := by
  have he : pointValuation E (0 : Points E)
      (transEquiv E (AlgebraicClosure K) P (veluX E H)) =
      pointValuation E ((0 : Points E) + P) (veluX E H) :=
    pointValuation_transEquiv E 0 P (veluX E H)
  rw [veluX_translation E H ⟨P, hP⟩, zero_add] at he
  exact he.symm.trans (veluX_valuation_zero E H)

/-- [DkMath.Lib] 同じ核の任意の点でY_Hの値はexp(3)。 -/
theorem veluY_valuation_of_mem (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∈ H) : pointValuation E P (veluY E H) = exp (3 : ℤ) := by
  have he : pointValuation E (0 : Points E)
      (transEquiv E (AlgebraicClosure K) P (veluY E H)) =
      pointValuation E ((0 : Points E) + P) (veluY E H) :=
    pointValuation_transEquiv E 0 P (veluY E H)
  rw [veluY_translation E H ⟨P, hP⟩, zero_add] at he
  exact he.symm.trans (veluY_valuation_zero E H)

/-- [DkMath.Lib] 二つの構成済み関数の極の支持は、正確に同じ実点核Hである。 -/
theorem velu_pole_support (H : AddSubgroup (Points E)) [Fintype H] (P : Points E) :
    (1 < pointValuation E P (veluX E H) ↔ P ∈ H) ∧
      (1 < pointValuation E P (veluY E H) ↔ P ∈ H) := by
  constructor
  · constructor
    · intro hp
      by_contra hn
      exact (not_lt_of_ge (veluX_regular_outside E H P hn)) hp
    · intro hp
      rw [veluX_valuation_of_mem E H P hp, ← exp_zero, exp_lt_exp]
      norm_num
  · constructor
    · intro hp
      by_contra hn
      exact (not_lt_of_ge (veluY_regular_outside E H P hn)) hp
    · intro hp
      rw [veluY_valuation_of_mem E H P hp, ← exp_zero, exp_lt_exp]
      norm_num

/-- [DkMath.Lib] 非零性を明示した実際の局所整数位数は、核上で−2と−3である。
正の極次数2,3と負の整数位数を取り違えない。 -/
theorem velu_orders_of_mem (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∈ H) :
    pointOrder E P (veluX E H) (veluX_ne_zero E H) = -2 ∧
      pointOrder E P (veluY E H) (veluY_ne_zero E H) = -3 := by
  constructor
  · rw [pointOrder_eq_neg_log, veluX_valuation_of_mem E H P hP, log_exp]
  · rw [pointOrder_eq_neg_log, veluY_valuation_of_mem E H P hP, log_exp]

/-- [DkMath.Lib] 実際の極集合の位数は、同じ有限核Hの位数に等しい。
Oも極集合の一点として数え、有限アフィン点だけへ切り詰めない。 -/
theorem card_velu_pole_support (H : AddSubgroup (Points E)) [Fintype H] :
    Nat.card {P : Points E // 1 < pointValuation E P (veluX E H)} = Nat.card H ∧
      Nat.card {P : Points E // 1 < pointValuation E P (veluY E H)} = Nat.card H := by
  constructor
  · exact Nat.card_congr (Equiv.subtypeEquivRight (fun P => (velu_pole_support E H P).1))
  · exact Nat.card_congr (Equiv.subtypeEquivRight (fun P => (velu_pole_support E H P).2))

/-- [DkMath.Lib] 同じ有限極集合上の極位数の総和は2|H|と3|H|。
局所整数位数の負を足す式として固定し、未構成のisogenyの次数とは区別する。 -/
theorem velu_total_pole_orders (H : AddSubgroup (Points E)) [Fintype H] :
    (∑ P : H, -pointOrder E P.val (veluX E H) (veluX_ne_zero E H)) = 2 * (Nat.card H : ℤ) ∧
      (∑ P : H, -pointOrder E P.val (veluY E H) (veluY_ne_zero E H)) = 3 * (Nat.card H : ℤ) := by
  constructor
  · calc
      _ = ∑ _P : H, (2 : ℤ) := Finset.sum_congr rfl (fun P _ => by
        rw [(velu_orders_of_mem E H P.val P.property).1]
        norm_num)
      _ = _ := by simp [Nat.card_eq_fintype_card, mul_comm]
  · calc
      _ = ∑ _P : H, (3 : ℤ) := Finset.sum_congr rfl (fun P _ => by
        rw [(velu_orders_of_mem E H P.val P.property).2]
        norm_num)
      _ = _ := by simp [Nat.card_eq_fintype_card, mul_comm]

/-- [DkMath.Lib] 同じX_Hは係数体上超越的であり、その多項式代入は単射となる。
Y_Hとの組の代数的独立性を意味しない。 -/
theorem veluX_transcendental (H : AddSubgroup (Points E)) [Fintype H] :
    Transcendental (AlgebraicClosure K) (veluX E H) := by
  apply transcendental_of_point_pole E 0
  change 1 < pointValuation E (0 : (E⁄(AlgebraicClosure K)).Point) (veluX E H)
  rw [veluX_valuation_zero, ← exp_zero, exp_lt_exp]
  norm_num

/-- [DkMath.Lib] 同じY_Hも個別には係数体上超越的である。
二関数を結ぶ標的曲線方程式の構成とは両立し、その方程式の証明とは別である。 -/
theorem veluY_transcendental (H : AddSubgroup (Points E)) [Fintype H] :
    Transcendental (AlgebraicClosure K) (veluY E H) := by
  apply transcendental_of_point_pole E 0
  change 1 < pointValuation E (0 : (E⁄(AlgebraicClosure K)).Point) (veluY E H)
  rw [veluY_valuation_zero, ← exp_zero, exp_lt_exp]
  norm_num

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
