/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyGeometricWeilPairing
import DkMathTest.FLT.FreyWeilGalois

#print "file: DkMathTest.FLT.FreyGeometricWeilPairing"

/-!
# NOTE-028: A・B・Cと実際の円分行列式の回帰

同じSource 2で引き戻しの正確な次数4、固定体、実際の有限原像での局所上界を検査する。
非零目標はある移動によって必ず識別されることを新たに確認する。指定した非対角値そのものの数値計算はしない。
指数37の次数1369と非退化性、任意のSource 37の円分行列式にも一般定理だけで到達する。
-/
namespace FreyGeometricWeilPairingTest
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation EllipticFunctionField CyclotomicRootModule
open DkMath.FLT.Frey
open FreyResidualRepresentationTest FreyWeilCharacterTest FreyWeilBicharacterTest
open FreyWeilFunctionTest FreyWeilValuationTest
local instance : sample.rationalCurve.IsElliptic := sample.rationalCurve_isElliptic
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
attribute [local instance] geometricCoordinateRing_isDedekindDomain
local notation "E" => sample.rationalCurve

/-- 引き戻しは同じ実際の2倍一般点のx座標を測る。 -/
theorem actual_pull_x : multiplicationPull E 2 (by decide) (genericX E (AlgebraicClosure ℚ)) =
    (2 • genericPoint E (AlgebraicClosure ℚ)).xc := multiplicationPull_genericX E 2 (by decide)

/-- y座標も同じ2倍点の座標である。 -/
theorem actual_pull_y : multiplicationPull E 2 (by decide) (genericY E (AlgebraicClosure ℚ)) =
    (2 • genericPoint E (AlgebraicClosure ℚ)).yc := multiplicationPull_genericY E 2 (by decide)

/-- 反転は一般の2倍点のyを固定しない。余分な2を除く証明の前提を実際の関数で測る。 -/
theorem actual_negation_moves_y :
    negEquiv E (AlgebraicClosure ℚ) (multiplicationPull E 2 (by decide) (genericY E (AlgebraicClosure ℚ))) ≠
      multiplicationPull E 2 (by decide) (genericY E (AlgebraicClosure ℚ)) :=
  negEquiv_multiplicationPull_genericY_ne E 2 (by decide)

/-- 座標だけでなく関数体全体の拡大次数が4以下である。 -/
theorem actual_degree_bound :
    Module.finrank (multiplicationPull E 2 (by decide)).fieldRange
      (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField ≤ 4 :=
  (finiteDimensional_finrank_multiplicationPull E 2 (by decide)).2

/-- 固定体との比較により同じ次数は正確に4となる。 -/
theorem actual_degree :
    Module.finrank (multiplicationPull E 2 (by decide)).fieldRange
      (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField = 4 :=
  finrank_multiplicationPull E 2 (by decide)

/-- 指数37でも巨大な多項式を展開せず、正確な次数1369へ到達する。 -/
theorem degree_thirtySeven :
    Module.finrank (multiplicationPull E 37 (by decide)).fieldRange
      (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField = 1369 :=
  finrank_multiplicationPull E 37 (by decide)

/-- 実際の2-torsion平行移動の自己同型群は四元である。 -/
theorem actual_translation_group_card : Nat.card (torsionTranslationGroup E 2) = 4 :=
  card_torsionTranslationGroup E 2 (by decide)

/-- 固定体に対する同じ関数体の次数も4である。 -/
theorem actual_fixed_degree :
    Module.finrank (torsionFixedField E 2) (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField = 4 :=
  finrank_torsionFixedField E 2 (by decide)

/-- 028-Bの一致は同じ実際の二つの中間体の等式である。 -/
theorem actual_fixed_field : (multiplicationPull E 2 (by decide)).fieldRange = torsionFixedField E 2 :=
  multiplicationRange_eq_torsionFixedField E 2 (by decide)

/-- 2U=(0,0)となる既存の実際の有限点Uで、局所付値の上界を回帰する。 -/
theorem actual_local_pullback (f : (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField)
    (k : ℕ) (hk : (placeOf E (AlgebraicClosure ℚ) (2 • fourPoint)
      fourPoint_not_two_torsion).valuation _ f ≤ WithZero.exp (-(k : ℤ))) :
    (placeOf E (AlgebraicClosure ℚ) fourPoint fourPoint_ne_zero).valuation _
      (multiplicationPull E 2 (by decide) f) ≤ WithZero.exp (-(k : ℤ)) :=
  valuation_multiplicationPull_le E 2 (by decide) fourPoint fourPoint_ne_zero
    fourPoint_not_two_torsion f k hk

/-- 非零目標(0,0)を識別する実際のtorsion移動が存在する。対角値1だけではない。 -/
theorem actual_target_detected : ∃ Q : Torsion E 2,
    sample.curve_weilAlternatingBicharacter 2 (by decide) Q target ≠ 1 := by
  classical
  by_contra h
  push Not at h
  exact target_ne_zero (weilAlternatingBicharacter_nondegenerate_right E 2 (by decide) target h)

/-- 別の実際の非零目標(4,−2)も、同じ対で識別される。 -/
theorem other_target_detected : ∃ Q : Torsion E 2,
    sample.curve_weilAlternatingBicharacter 2 (by decide) Q otherTarget ≠ 1 := by
  classical
  by_contra h
  push Not at h
  exact otherTarget_ne_zero (weilAlternatingBicharacter_nondegenerate_right E 2 (by decide) otherTarget h)

/-- 左非退化性も同じSourceのAPIで使用できる。 -/
theorem actual_left_nondegenerate (Q : Torsion E 2)
    (hQ : ∀ T, sample.curve_weilAlternatingBicharacter 2 (by decide) Q T = 1) : Q = 0 :=
  sample.curve_weilAlternatingBicharacter_nondegenerate 2 (by decide) Q hQ

/-- 指数37の全torsion点に対して、値が全て1なら零と判定できる。 -/
theorem nondegenerate_thirtySeven (T : Torsion E 37)
    (hT : ∀ Q, weilAlternatingBicharacter E 37 (by decide) Q T = 1) : T = 0 :=
  weilAlternatingBicharacter_nondegenerate_right E 37 (by decide) T hT

/-- 指数1の境界でも同じ非退化性が成立する。 -/
theorem exponent_one (T : Torsion E 1)
    (hT : ∀ Q, weilAlternatingBicharacter E 1 (by decide) Q T = 1) : T = 0 :=
  weilAlternatingBicharacter_nondegenerate_right E 1 (by decide) T hT

/-- 新たなRootPairingの値は、前章までの同じ非対角の単元値である。 -/
theorem pairing_same_value : (geometricRootPairing E 2 (by decide)).value target otherTarget =
    sample.curve_weilTranslationUnit 2 (by decide) otherTarget target := rfl

/-- 実際のSource 2からWeilPairingDataを構成できる。 -/
noncomputable def actualPairing : sample.ResidualWeilPairingData := sample.residual_geometricWeilPairingData

/-- Source 2の円分行列式は対データの追加入力なしで成立する。 -/
theorem actual_determinant : sample.residualDeterminantCharacter = cyclotomicCharacter 2 :=
  sample.residual_determinant_eq_cyclotomic

/-- 任意のSource 37でも同じ無条件の幾何学的接続が働く。 -/
theorem determinant_thirtySeven (S : Source 37) : S.residualDeterminantCharacter = cyclotomicCharacter 37 :=
  S.residual_determinant_eq_cyclotomic

/-- 任意の37乗根への実際の係数作用を、同じSourceの残余行列式の冪で記述できる。 -/
theorem roots_thirtySeven (S : Source 37) (σ : Field.absoluteGaloisGroup ℚ) (ζ : AlgebraicClosure ℚ)
    (hζ : ζ ^ 37 = 1) : σ.toAlgHom ζ = ζ ^ (LinearMap.det (S.residualRepresentation σ)).val :=
  S.residual_apply_eq_pow_det σ ζ hζ

end FreyGeometricWeilPairingTest
