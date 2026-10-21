/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_WeierstrassCurve_Affine_valuation_weilFun.lean.
Upstream blob: b3f224d0557e987b11afe147aa507cd7fa5837c9
Modified for DkMath: proved Dedekind provider, guarded existing functions,
and integer-valued zero/pole order on nonzero functions.
-/

import DkMath.Lib.NumberTheory.EllipticWeilFunction
import DkMath.Lib.NumberTheory.EllipticPointIdealValuation

#print "file: DkMath.Lib.NumberTheory.EllipticWeilValuation"

/-!
# 既存のWeil分子と商の有限点付値

同じ座標環のDedekind性を証明から供給し、実際の有限場所で関数を測る。
分子はファイバー上で一重に消え、それ以外では消えない。
商の零点・極の位数は二つのファイバーの指示関数の差になる。
乗法的付値はexp(−ord)という符号規約を持つので、零点の位数と符号を混同しない。
零関数の位数はこの整数値APIでは定義せず、f≠0を要求する。P=Oも対象外である。
無限遠点の次数・平行移動の付値輸送・Weil対の存在はまだ証明しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open WeierstrassCurve WeierstrassCurve.Affine WithZero
open IsDedekindDomain.HeightOneSpectrum
open EllipticFunctionField EllipticPointIdealValuation
variable {K : Type*} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]

/-- 代数閉包上の同じ座標環のDedekind性。外部の環構造仮定として受け取らない。 -/
theorem geometricCoordinateRing_isDedekindDomain :
    IsDedekindDomain (E.toAffine⁄(AlgebraicClosure K)).CoordinateRing := by
  have : (E.toAffine⁄(AlgebraicClosure K)).IsElliptic := by
    change (E.map (algebraMap K (AlgebraicClosure K))).IsElliptic
    rw [WeierstrassCurve.isElliptic_iff, WeierstrassCurve.map_Δ]
    exact E.isUnit_Δ.map _
  exact EllipticCoordinateRing.isDedekindDomain

attribute [local instance] geometricCoordinateRing_isDedekindDomain

/-- 実際の有限点Pに対応する場所の、同じ関数体上の乗法的離散付値。 -/
noncomputable def finitePointValuation (P : Points E) (hP : P ≠ 0) :
    Valuation (E.toAffine⁄(AlgebraicClosure K)).FunctionField ℤᵐ⁰ :=
  (placeOf E (AlgebraicClosure K) P hP).valuation _

/-- 非零関数の付値も非零であり、その整数指数を安全に読み取れる。 -/
theorem finitePointValuation_ne_zero (P : Points E) (hP : P ≠ 0)
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (hf : f ≠ 0) :
    finitePointValuation E P hP f ≠ 0 := (finitePointValuation E P hP).ne_zero_iff.mpr hf

/-- 有限点での零点・極の位数。零点を正、極を負にする。
f≠0を要求するので、WithZero.log 0の便宜的な値を零関数の位数とは解釈しない。 -/
noncomputable def finitePointOrder (P : Points E) (hP : P ≠ 0)
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (_hf : f ≠ 0) : ℤ :=
  -log (finitePointValuation E P hP f)

/-- 商の位数は差になる。分子と分母の非零性を明示し、logの乗除法則の条件を満たす。 -/
theorem finitePointOrder_div (P : Points E) (hP : P ≠ 0)
    (f g : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (hf : f ≠ 0) (hg : g ≠ 0) :
    finitePointOrder E P hP (f / g) (div_ne_zero hf hg) =
      finitePointOrder E P hP f hf - finitePointOrder E P hP g hg := by
  rw [finitePointOrder, map_div₀, log_div (finitePointValuation_ne_zero E P hP f hf)
    (finitePointValuation_ne_zero E P hP g hg), finitePointOrder, finitePointOrder]
  omega

variable [CharZero K]

open Classical in
/-- 実際の分子は、nP=Tの有限点で一重に消える。その他の有限点では付値1。
span_weilNumeratorの実際のイデアル等式を、相異なる点の積の付値公式へ渡す。 -/
theorem valuation_weilNumerator (n : ℕ) (hn : n ≠ 0) (T : Points E) (hT : n • T = 0)
    (P : Points E) (hP : P ≠ 0) :
    finitePointValuation E P hP
      (algebraMap (E.toAffine⁄(AlgebraicClosure K)).CoordinateRing
        (E.toAffine⁄(AlgebraicClosure K)).FunctionField (weilNumerator E n hn T hT)) =
      if n • P = T then exp (-1 : ℤ) else 1 := by
  change (placeOf E (AlgebraicClosure K) P hP).valuation _ _ = _
  rw [valuation_of_algebraMap]
  have hs := span_weilNumerator E n hn T hT
  have h := intValuation_of_span_eq_prod E (AlgebraicClosure K)
    (fiber_finite E n hn T).toFinset hs P hP
  have hm : (P : (E.toAffine⁄(AlgebraicClosure K)).Point) ∈
      (fiber_finite E n hn T).toFinset ↔ n • P = T := (fiber_finite E n hn T).mem_toFinset
  apply h.trans
  split_ifs with hmem hEq hEq
  · rfl
  · exact (hEq (hm.mp hmem)).elim
  · exact (hmem (hm.mpr hEq)).elim
  · rfl

open Classical in
/-- 商の乗法的付値は、分子と零ファイバーの分母の付値の比になる。 -/
theorem valuation_weilFunction (n : ℕ) (hn : n ≠ 0) (T : Points E) (hT : n • T = 0)
    (P : Points E) (hP : P ≠ 0) :
    finitePointValuation E P hP (weilFunction E n hn T hT) =
      (if n • P = T then exp (-1 : ℤ) else 1) /
      (if n • P = 0 then exp (-1 : ℤ) else 1) := by
  rw [weilFunction, map_div₀, valuation_weilNumerator E n hn T hT P hP,
    valuation_weilNumerator E n hn 0 (smul_zero n) P hP]

open Classical in
/-- 分子の零点の位数はファイバーの指示関数。値1は一重零点を表す。 -/
theorem order_weilNumerator (n : ℕ) (hn : n ≠ 0) (T : Points E) (hT : n • T = 0)
    (P : Points E) (hP : P ≠ 0) :
    finitePointOrder E P hP (algebraMap (E.toAffine⁄(AlgebraicClosure K)).CoordinateRing
      (E.toAffine⁄(AlgebraicClosure K)).FunctionField (weilNumerator E n hn T hT))
      (algebraMap_weilNumerator_ne_zero E n hn T hT) = if n • P = T then 1 else 0 := by
  rw [finitePointOrder, valuation_weilNumerator E n hn T hT P hP]
  split <;> simp only [log_exp, neg_neg, log_one, neg_zero]

open Classical in
/-- 商の有限点での零点・極の位数は二つの指示関数の差となる。両方成立すれば相殺される。 -/
theorem order_weilFunction (n : ℕ) (hn : n ≠ 0) (T : Points E) (hT : n • T = 0)
    (P : Points E) (hP : P ≠ 0) :
    finitePointOrder E P hP (weilFunction E n hn T hT) (weilFunction_ne_zero E n hn T hT) =
      (if n • P = T then 1 else 0) - (if n • P = 0 then 1 else 0) := by
  change finitePointOrder E P hP (_ / _) _ = _
  rw [finitePointOrder_div E P hP _ _ (algebraMap_weilNumerator_ne_zero E n hn T hT)
    (algebraMap_weilNumerator_ne_zero E n hn 0 (smul_zero n)),
    order_weilNumerator E n hn T hT P hP,
    order_weilNumerator E n hn 0 (smul_zero n) P hP]

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
