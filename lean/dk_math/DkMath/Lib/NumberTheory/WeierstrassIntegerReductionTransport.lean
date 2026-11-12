/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.WeierstrassIntegralChangeReduction
import DkMath.Lib.NumberTheory.WeierstrassIntegralModelTransport

#print "file: DkMath.Lib.NumberTheory.WeierstrassIntegerReductionTransport"

/-!
# 同じ整数化の点同型で、滑らかな還元条件を輸送する

[DkMath.Lib] 整数モデルを任意の延長付値環へ写した同じ整モデルを使う。
既存整数化の共通分母dが付値1なら、既存clearingChangeは付値環上の単元変数変換へ持ち上がる。
この持ち上げと元の点同型を同定し、整数化前後の点の滑らかな還元を双方向に比較する。
dを割る場所を除く条件を型に保持し、判別式の付値比較だけで点の輸送を済ませない。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassRationalIntegralModel
open WeierstrassCurve WeierstrassCurve.Affine
open IsLocalRing WeierstrassVariableChange EllipticTorsionRepresentation
open EllipticGoodReductionSeparation WeierstrassIntegralChangeReduction
noncomputable local instance instDecidableEqWeierstrassIntegerReductionTransport {α : Type*} : DecidableEq α :=
  Classical.decEq _

/-- [DkMath.Lib] 同じ整数曲線の係数を付値環へ入れた標準モデル。点や曲線を選び直さない。 -/
def integerValuationModel {L : Type*} [Field L] (A : ValuationSubring L) (W : WeierstrassCurve ℤ) :
    WeierstrassCurve A := W.map (Int.castRingHom A)

/-- [DkMath.Lib] 同じ標準モデルの一般ファイバーは、同じ整数係数を元の体へ写した曲線。 -/
theorem integerValuationModel_map {L : Type*} [Field L] (A : ValuationSubring L) (W : WeierstrassCurve ℤ) :
    (integerValuationModel A W).map A.subtype = W.map (Int.castRingHom L) := by
  ext <;> simp only [integerValuationModel, WeierstrassCurve.map, Int.coe_castRingHom, map_intCast]

private theorem geometricPointEquiv_some' (W : WeierstrassCurve ℚ) {x y : AlgebraicClosure ℚ}
    (hxy : ((rationalModel W).toAffine⁄(AlgebraicClosure ℚ)).Nonsingular x y) :
    ∃ h, geometricPointEquiv W (Point.some x y hxy) =
      Point.some (vcX ((clearingChange W).map (algebraMap ℚ (AlgebraicClosure ℚ))) x)
        (vcY ((clearingChange W).map (algebraMap ℚ (AlgebraicClosure ℚ))) x y) h := by
  let eqm := congrArg (fun V : WeierstrassCurve ℚ => V.map (algebraMap ℚ (AlgebraicClosure ℚ)))
    (integerModel_map W)
  let hxy' : ((rationalModel W).map (algebraMap ℚ (AlgebraicClosure ℚ))).toAffine.Nonsingular x y := hxy
  let hn' : ((clearingChange W • W).map (algebraMap ℚ (AlgebraicClosure ℚ))).toAffine.Nonsingular x y := eqm ▸ hxy'
  let hn : (((clearingChange W • W).toAffine)⁄(AlgebraicClosure ℚ)).Nonsingular x y := hn'
  obtain ⟨h, he⟩ := geometricChangeEquiv_some W (clearingChange W) hn
  refine ⟨h, ?_⟩
  change geometricChangeEquiv W (clearingChange W) (pointEquivOfModelEq eqm (.some x y hxy)) = _
  exact (congrArg (geometricChangeEquiv W (clearingChange W))
    (pointEquivOfModelEq_some eqm hxy')).trans he

/-- [DkMath.Lib] dが単元の場所では、既存整数化を同じ付値環上の変数変換として実現できる。 -/
theorem exists_integral_clearingChange (W : WeierstrassCurve ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hd : A.valuation (commonDenominator W : AlgebraicClosure ℚ) = 1) :
    ∃ C : VariableChange A, C.map A.subtype = (clearingChange W).map (algebraMap ℚ (AlgebraicClosure ℚ)) := by
  have hu : IsUnit (commonDenominator W : A) := (A.valuation_eq_one_iff _).mpr hd
  obtain ⟨u, hu⟩ := hu
  refine ⟨⟨u⁻¹, 0, 0, 0⟩, ?_⟩
  apply VariableChange.ext
  · change (Units.map A.subtype.toMonoidHom u)⁻¹ =
      (Units.map (algebraMap ℚ (AlgebraicClosure ℚ)).toMonoidHom
        (Units.mk0 (commonDenominator W : ℚ)
          (Nat.cast_ne_zero.mpr (commonDenominator_ne_zero W))))⁻¹
    congr 1
    apply Units.ext
    have he := congrArg A.subtype hu
    simpa only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      Units.val_mk0, map_natCast] using he
  all_goals simp only [VariableChange.map, clearingChange, map_zero]

/-- [DkMath.Lib] 単元倍率の場所で、同じ既存幾何学的整数化同型は滑らかな還元条件を保つ。
標的の良還元や点の捩れ性を要求しない。 -/
theorem geometricPointEquiv_smooth_iff (W : WeierstrassCurve ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (M : WeierstrassCurve A)
    (hM : M.map A.subtype = W.map (algebraMap ℚ (AlgebraicClosure ℚ)))
    (hd : A.valuation (commonDenominator W : AlgebraicClosure ℚ) = 1)
    (P : Points (rationalModel W)) :
    HasSmoothReduction (integerValuationModel A (integerModel W)) P ↔
      HasSmoothReduction M (geometricPointEquiv W P) := by
  obtain ⟨C, hC⟩ := exists_integral_clearingChange W A hd
  have hi : integerValuationModel A (integerModel W) = C • M := by
    apply WeierstrassCurve.map_injective (f := A.subtype) Subtype.val_injective
    change (integerValuationModel A (integerModel W)).map A.subtype = (C • M).map A.subtype
    rw [integerValuationModel_map, ← map_variableChange, hM, hC, map_variableChange]
    have he := congrArg (fun V : WeierstrassCurve ℚ => V.map (algebraMap ℚ (AlgebraicClosure ℚ)))
      (integerModel_map W)
    rw [map_map] at he
    have hf : (algebraMap ℚ (AlgebraicClosure ℚ)).comp (Int.castRingHom ℚ) =
        Int.castRingHom (AlgebraicClosure ℚ) := by
      apply RingHom.ext
      intro n
      simp only [RingHom.comp_apply, Int.coe_castRingHom, map_intCast]
    rw [hf] at he
    exact he
  cases P with
  | zero =>
    change HasSmoothReduction (integerValuationModel A (integerModel W)) (0 : Points (rationalModel W)) ↔
      HasSmoothReduction M (geometricPointEquiv W (0 : Points (rationalModel W)))
    rw [map_zero]
    exact iff_of_true (hasSmoothReduction_zero _ _) (hasSmoothReduction_zero _ _)
  | some x y h =>
    obtain ⟨h', he⟩ := geometricPointEquiv_some' W h
    have hl := hasSmoothReduction_some_iff (integerValuationModel A (integerModel W)) h
    have hr := (Iff.of_eq (congrArg (fun Q => HasSmoothReduction M Q) he)).trans
      (hasSmoothReduction_some_iff M h')
    apply hl.trans
    apply Iff.trans _ hr.symm
    rw [hi]
    have hh := smoothCoordinates_iff A C M x y
    rw [hC] at hh
    exact hh

end DkMath.Lib.NumberTheory.WeierstrassRationalIntegralModel
