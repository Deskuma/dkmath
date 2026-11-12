/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyValuationArithmetic

#print "file: DkMathTest.FLT.FreyValuationArithmetic"

/-!
# NOTE-031-002A: 実際のtorsion座標と、合同・固定を区別する境界

y²+xy=x³+4x²+x上の点(-1/4,1/8)は実在する非零2-torsionである。
3上の付値環では両座標は整だが、2上ではxに極がある。指数の単元条件を落とせない。
また、付値環の非単元を法とする合同が元の等号を意味しないことも検査する。
Source 37の回帰は同じ曲線・同じ有限座標点を保持する条件付きの接続である。
-/
namespace FreyValuationArithmeticTest
open DkMath.Lib.NumberTheory ValuationInertia ValuationPrimeSupport
open WeierstrassCurve
noncomputable local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- 境界例の整係数モデル。 -/
def curveInt : WeierstrassCurve ℤ := ⟨1, 4, 0, 1, 0⟩

/-- 境界例の同じ有理曲線。 -/
def curve : WeierstrassCurve ℚ := curveInt.map (Int.castRingHom ℚ)

/-- 判別式225は非零であり、特異曲線を境界の代用にしていない。 -/
theorem curve_isElliptic : curve.IsElliptic := by
  rw [isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [curve, curveInt, Δ, b₂, b₄, b₆, b₈]

/-- (-1/4,1/8)は実際の非特異点である。 -/
theorem point_nonsingular : curve.toAffine.Nonsingular (-1 / 4) (1 / 8) := by
  norm_num [Affine.nonsingular_iff, Affine.equation_iff, curve, curveInt]

/-- 分母を持つ実際の有理点。 -/
def point : curve.toAffine.Point := Affine.Point.some (-1 / 4) (1 / 8) point_nonsingular

/-- 点は非零で2倍すると無限遠点となる。 -/
theorem point_nonzero_two_torsion : point ≠ 0 ∧ 2 • point = 0 := by
  constructor
  · exact Affine.Point.some_ne_zero _
  · have hneg : -point = point := by
      rw [point, Affine.Point.neg_some, Affine.Point.some.injEq]
      norm_num [Affine.negY, curve, curveInt]
    rw [two_nsmul]
    calc point + point = -point + point := congrArg (fun T => T + point) hneg.symm
      _ = 0 := neg_add_cancel point

/-- 3上では2が単元なので、この実際の2-torsion点の両座標は整となる。 -/
theorem point_integral_at_three (A : ValuationSubring ℚ) (hA : LiesOverPrime A 3) :
    (-1 / 4 : ℚ) ∈ A ∧ (1 / 8 : ℚ) ∈ A := by
  let W := curveInt.map (Int.castRingHom A)
  have hmodel : W.map A.subtype = curve := by
    dsimp [W, curve]
    rw [map_map]
    congr 1
  have hn : A.valuation (2 : ℚ) = 1 :=
    valuation_intCast_eq_one_of_not_dvd A (by decide)
      ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 2) (by norm_num)
  exact EllipticTorsionValuationIntegrality.torsion_coordinates_mem A W curve hmodel hn
    point_nonsingular point_nonzero_two_torsion.2

/-- 2上では同じ点のx座標に極がある。指数nの単元条件の必要性を実際の点で示す。 -/
theorem point_not_integral_at_two (A : ValuationSubring ℚ) (hA : LiesOverPrime A 2) :
    (-1 / 4 : ℚ) ∉ A := by
  intro hx
  have h2 : A.valuation (2 : ℚ) < 1 := (ValuationSubring.mem_nonunits_iff _).mp hA
  have h4 : A.valuation (4 : ℚ) < 1 := by
    rw [show (4 : ℚ) = 2 * 2 by norm_num, map_mul]
    exact (mul_le_of_le_one_left' h2.le).trans_lt h2
  have hprod : A.valuation (-1 / 4 : ℚ) * A.valuation (4 : ℚ) = 1 := by
    rw [← map_mul]
    norm_num
  have hlt : A.valuation (-1 / 4 : ℚ) * A.valuation (4 : ℚ) < 1 :=
    (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).mpr hx)).trans_lt h4
  exact hlt.ne hprod

/-- 指数が剰余標数に等しいと整性を失う実際の楕円曲線上の境界。 -/
theorem unit_hypothesis_boundary (A : ValuationSubring ℚ) (hA : LiesOverPrime A 2) :
    curve.IsElliptic ∧ point ≠ 0 ∧ 2 • point = 0 ∧ (-1 / 4 : ℚ) ∉ A :=
  ⟨curve_isElliptic, point_nonzero_two_torsion.1, point_nonzero_two_torsion.2,
    point_not_integral_at_two A hA⟩

/-- 1と4は3上で合同だが相異なる。合同から点固定へ進むには別の単射性が要る。 -/
theorem congruence_does_not_imply_equality (A : ValuationSubring ℚ) (hA : LiesOverPrime A 3) :
    (4 : ℚ) - 1 ∈ A.nonunits ∧ (4 : ℚ) ≠ 1 := by
  constructor
  · norm_num only [show (4 : ℚ) - 1 = 3 by norm_num]
    exact hA
  · norm_num

/-- z=0ではv(z)=0だが、padicValIntの零デフォルトを指数に使えば右辺は1となる。 -/
theorem zero_default_boundary (A : ValuationSubring ℚ) :
    A.valuation (0 : ℚ) ≠ A.valuation (3 : ℚ) ^ padicValInt 3 0 := by
  simp

/-- Source 37の同じ整数判別式の付値を、3上の任意の延長付値へ輸送する。 -/
theorem source37_discriminant (S : DkMath.FLT.Frey.Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 3) :
    A.valuation (S.curve.Δ : AlgebraicClosure ℚ) =
      A.valuation (3 : AlgebraicClosure ℚ) ^ (74 * padicValInt 3 (S.a * S.b * S.c)) :=
  S.valuation_discriminant_eq (by decide) A hA

/-- q=p=37でも判別式の算術は成立する。これをp-torsionの整性へ無条件に転用しない。 -/
theorem source37_at_p_arithmetic (S : DkMath.FLT.Frey.Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 37) :
    A.valuation (S.curve.Δ : AlgebraicClosure ℚ) =
      (A.valuation (37 : AlgebraicClosure ℚ) ^ (2 * padicValInt 37 (S.a * S.b * S.c))) ^ 37 :=
  S.valuation_discriminant_pth_power (by decide) A hA

/-- Source 37の良い素数では、実際の付値環の剰余曲線が楕円曲線となる。 -/
theorem source37_good_reduction (S : DkMath.FLT.Frey.Source 37)
    (hd : ¬ (3 : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 3) :
    ((S.valuationModel A).map (IsLocalRing.residue A)).IsElliptic :=
  S.valuation_reduction_isElliptic (by decide) (by decide) hd A hA

/-- Source 37の悪い素数では、同じc₄が延長付値でも単元となる。 -/
theorem source37_bad_c4 (S : DkMath.FLT.Frey.Source 37) (hd : (3 : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 3) :
    A.valuation (S.curve.c₄ : AlgebraicClosure ℚ) = 1 :=
  S.valuation_c4_eq_one (by decide) (by decide) hd A hA

/-- 同じSource 37の同じ有限torsion点は、3上の付値環で両座標が整となる。 -/
theorem source37_coordinates (S : DkMath.FLT.Frey.Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 3)
    {x y : AlgebraicClosure ℚ} (h : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (ht : 37 • (Affine.Point.some x y h) = 0) : x ∈ A ∧ y ∈ A :=
  S.residual_coordinates_mem (by decide) (by decide) A hA h ht

/-- 同じ点の慣性による座標変化は非単元。等号による固定へ結論を強めない。 -/
theorem source37_inertia_congruence (S : DkMath.FLT.Frey.Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 3)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ inertiaSubgroupIn A ℚ)
    {x y : AlgebraicClosure ℚ} (h : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (ht : 37 • (Affine.Point.some x y h) = 0) :
    σ x - x ∈ A.nonunits ∧ σ y - y ∈ A.nonunits :=
  S.residual_inertia_coordinate_congruence (by decide) (by decide) A hA σ hσ h ht

end FreyValuationArithmeticTest
