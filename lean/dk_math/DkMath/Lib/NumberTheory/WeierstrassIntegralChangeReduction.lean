/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.WeierstrassModelReduction

#print "file: DkMath.Lib.NumberTheory.WeierstrassIntegralChangeReduction"

/-!
# 付値環の単元による変数変換は滑らかな還元条件を保つ

[DkMath.Lib] C=(u,r,s,t)を付値環A上の変数変換とする。uはAの単元である。
一般ファイバーと剰余体へ同じCを写す。両座標の整性は変換の前後で同値となり、
整座標の剰余も同じ変換で結ばれる。剰余での非特異性の同値から、
非整点も含めたSmoothCoordinatesの同値を得る。2や3の単元性は要求しない。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassIntegralChangeReduction
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open WeierstrassVariableChange EllipticGoodReductionSeparation
variable {L : Type*} [Field L] (A : ValuationSubring L) (C : VariableChange A)

/-- [DkMath.Lib] 同じ付値環変数変換による両座標の整性は、前後で同値である。 -/
theorem coordinates_mem_iff (x y : L) :
    x ∈ A ∧ y ∈ A ↔ vcX (C.map A.subtype) x ∈ A ∧ vcY (C.map A.subtype) x y ∈ A := by
  constructor
  · rintro ⟨hx, hy⟩
    let X : A := ⟨x, hx⟩
    let Y : A := ⟨y, hy⟩
    exact ⟨show (((C.u : A) ^ 2 * X + C.r : A) : L) ∈ A from
      ((C.u : A) ^ 2 * X + C.r).property,
      show (((C.u : A) ^ 3 * Y + (C.u : A) ^ 2 * C.s * X + C.t : A) : L) ∈ A from
        ((C.u : A) ^ 3 * Y + (C.u : A) ^ 2 * C.s * X + C.t).property⟩
  · rintro ⟨hx, hy⟩
    let X : A := ⟨vcX (C.map A.subtype) x, hx⟩
    let Y : A := ⟨vcY (C.map A.subtype) x y, hy⟩
    have hxi : vcXInv (C.map A.subtype) (X : L) ∈ A :=
      show ((((C.u⁻¹ : Aˣ) : A) ^ 2 * (X - C.r) : A) : L) ∈ A from
        (((C.u⁻¹ : Aˣ) : A) ^ 2 * (X - C.r)).property
    have hyi : vcYInv (C.map A.subtype) (X : L) (Y : L) ∈ A :=
      show ((((C.u⁻¹ : Aˣ) : A) ^ 3 * (Y - C.t - C.s * (X - C.r)) : A) : L) ∈ A from
        (((C.u⁻¹ : Aˣ) : A) ^ 3 * (Y - C.t - C.s * (X - C.r))).property
    exact ⟨by simpa only [X, vcXInv_vcX] using hxi,
      by simpa only [X, Y, vcYInv_vcY] using hyi⟩

/-- [DkMath.Lib] 整な二座標の剰余を取る操作は、同じ変数変換と可換である。 -/
theorem residue_coordinates (x y : A) :
    residue A ((C.u : A) ^ 2 * x + C.r) = vcX (C.map (residue A)) (residue A x) ∧
      residue A ((C.u : A) ^ 3 * y + (C.u : A) ^ 2 * C.s * x + C.t) =
        vcY (C.map (residue A)) (residue A x) (residue A y) := by
  constructor <;> simp only [vcX, vcY, VariableChange.map, Units.coe_map, map_add, map_mul, map_pow] <;> rfl

/-- [DkMath.Lib] 同じ単元変数変換は滑らかな還元の座標条件を双方向に保つ。
全曲線の良還元を仮定せず、非整座標の枝も整性の同値によって保持する。 -/
theorem smoothCoordinates_iff (M : WeierstrassCurve A) (x y : L) :
    SmoothCoordinates (C • M) x y ↔
      SmoothCoordinates M (vcX (C.map A.subtype) x) (vcY (C.map A.subtype) x y) := by
  constructor
  · intro hs hx hy
    obtain ⟨hxi, hyi⟩ := (coordinates_mem_iff A C x y).mpr ⟨hx, hy⟩
    have hn := hs hxi hyi
    rw [← map_variableChange] at hn
    have hh := (nonsingular_variableChange_iff (C := C.map (residue A))
      (W := (M.map (residue A)).toAffine) _ _).mp hn
    have hc := residue_coordinates A C (⟨x, hxi⟩ : A) ⟨y, hyi⟩
    have heX : (⟨vcX (C.map A.subtype) x, hx⟩ : A) = (C.u : A) ^ 2 * ⟨x, hxi⟩ + C.r := rfl
    have heY : (⟨vcY (C.map A.subtype) x y, hy⟩ : A) =
        (C.u : A) ^ 3 * ⟨y, hyi⟩ + (C.u : A) ^ 2 * C.s * ⟨x, hxi⟩ + C.t := rfl
    rw [heX, heY, hc.1, hc.2]
    exact hh
  · intro hs hx hy
    obtain ⟨hxi, hyi⟩ := (coordinates_mem_iff A C x y).mp ⟨hx, hy⟩
    have hn := hs hxi hyi
    have hc := residue_coordinates A C (⟨x, hx⟩ : A) ⟨y, hy⟩
    have heX : (⟨vcX (C.map A.subtype) x, hxi⟩ : A) = (C.u : A) ^ 2 * ⟨x, hx⟩ + C.r := rfl
    have heY : (⟨vcY (C.map A.subtype) x y, hyi⟩ : A) =
        (C.u : A) ^ 3 * ⟨y, hy⟩ + (C.u : A) ^ 2 * C.s * ⟨x, hx⟩ + C.t := rfl
    rw [heX, heY, hc.1, hc.2] at hn
    rw [← map_variableChange]
    exact (nonsingular_variableChange_iff (C := C.map (residue A))
      (W := (M.map (residue A)).toAffine) _ _).mpr hn

end DkMath.Lib.NumberTheory.WeierstrassIntegralChangeReduction
