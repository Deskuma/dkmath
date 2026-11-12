/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyUnramifiedAway
import DkMathTest.FLT.FreyDoublingDepth

#print "file: DkMathTest.FLT.FreyUnramifiedAway"

/-!
# NOTE-031-002: 実際の奇数torsionの深さと最終の全点固定

y²+xy+5y=x³の(0,0)は非零3-torsionであり、5上で特異点へ還元する。
この実例で全倍点の深さの定理を検査し、任意の同じ中心に対してv(X)³=v(F₀)を得る。
Source 37の最終APIは全残余点を対象とし、悪い還元でも滑らかさの入力を要求しない。
-/
namespace FreyUnramifiedAwayTest
open WeierstrassCurve Affine DkMath.Lib.NumberTheory ValuationInertia ValuationPrimeSupport
open EllipticCriticalCentre EllipticCriticalCentreAlgebra EllipticTangentDirections EllipticTorsionDepth
open EllipticNodalReduction EllipticGoodReductionSeparation EllipticDepthInertia
open DkMath.Lib.RepresentationTheory LocalFixedCofixed
noncomputable local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- 実際の非零3-torsionを持ち、5上で乗法的還元を持つ整数曲線。 -/
def integerCurve : WeierstrassCurve ℤ := ⟨1, 0, 5, 0, 0⟩

/-- 同じ整数曲線の有理モデル。 -/
def curve : WeierstrassCurve ℚ := integerCurve.map (Int.castRingHom ℚ)

/-- 同じ整数曲線の付値環モデル。 -/
noncomputable def model (A : ValuationSubring (AlgebraicClosure ℚ)) : WeierstrassCurve A := integerCurve.map (Int.castRingHom A)

/-- モデルを取り直さず、同じ代数閉包上の一般ファイバーへ一致する。 -/
theorem model_map (A : ValuationSubring (AlgebraicClosure ℚ)) :
    (model A).map A.subtype = curve.baseChange (AlgebraicClosure ℚ) := by
  simp only [model, curve, WeierstrassCurve.baseChange, map_map]
  congr 1

/-- 判別式は−16750、c₄は−119であり、5は前者だけを割る。 -/
theorem invariants : integerCurve.Δ = -16750 ∧ integerCurve.c₄ = -119 := by
  norm_num [integerCurve, Δ, c₄, b₂, b₄, b₆, b₈]

/-- (0,0)は同じ一般ファイバーの実際の非特異点。 -/
theorem point_nonsingular : (curve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular 0 0 := by
  norm_num [curve, integerCurve, WeierstrassCurve.baseChange, nonsingular_iff, equation_iff]

/-- 実際の幾何学的な点。 -/
noncomputable def point : (curve.baseChange (AlgebraicClosure ℚ)).toAffine.Point := .some 0 0 point_nonsingular

/-- 実際の加法公式から2P=−P、従って3P=Oとなる。P自身は無限遠点でない。 -/
theorem point_three_torsion : point ≠ 0 ∧ 3 • point = 0 := by
  have hd : 2 • point = -point := by
    change 2 • Point.some 0 0 point_nonsingular = -Point.some 0 0 point_nonsingular
    rw [two_nsmul, Point.add_self_of_Y_ne (by norm_num [negY, curve, integerCurve, WeierstrassCurve.baseChange]), Point.neg_some, Point.some.injEq]
    norm_num [addX, addY, negY, slope, curve, integerCurve, WeierstrassCurve.baseChange]
  refine ⟨Point.some_ne_zero _, ?_⟩
  rw [show 3 = 2 + 1 by decide, add_nsmul, one_nsmul, hd, neg_add_cancel]

/-- 同じ曲線の臨界中心と二方向が実在する。付値の非零性・単元性を5上の算術から供給する。 -/
theorem exists_centre_directions (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 5) :
    ∃ C : CriticalCentre A (curve.baseChange (AlgebraicClosure ℚ)), Nonempty (TangentDirections C) := by
  let W := curve.baseChange (AlgebraicClosure ℚ)
  have hm : W = integerCurve.map (Int.castRingHom (AlgebraicClosure ℚ)) := by
    simp only [W, curve, WeierstrassCurve.baseChange, map_map]
    congr 1
  have hd : W.Δ = (-16750 : AlgebraicClosure ℚ) := by rw [hm, map_Δ, invariants.1]; norm_num
  have hc : W.c₄ = (-119 : AlgebraicClosure ℚ) := by rw [hm, map_c₄, invariants.2]; norm_num
  have hvd := valuation_intCast_lt_one_of_dvd A ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := -16750) (by norm_num)
  have hvc := valuation_intCast_eq_one_of_not_dvd A (by decide) ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := -119) (by norm_num)
  have hvd' : A.valuation (-16750 : AlgebraicClosure ℚ) < 1 := by simpa only [Int.cast_neg, Int.cast_ofNat] using hvd
  have hvc' : A.valuation (-119 : AlgebraicClosure ℚ) = 1 := by simpa only [Int.cast_neg, Int.cast_ofNat] using hvc
  obtain ⟨C⟩ := exists_criticalCentre A W
    (by rw [hm, map_a₁]; exact intCast_mem A _) (by rw [hm, map_a₂]; exact intCast_mem A _)
    (by rw [hm, map_a₃]; exact intCast_mem A _) (by rw [hm, map_a₄]; exact intCast_mem A _)
    (by rw [hm, map_a₆]; exact intCast_mem A _) (by rw [hd]; norm_num)
    (by rw [hd]; exact hvd') (by rw [hc]; exact hvc')
  have h2 : A.valuation (2 : AlgebraicClosure ℚ) = 1 := valuation_intCast_eq_one_of_not_dvd A (by decide)
    ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 2) (by norm_num)
  exact ⟨C, exists_tangentDirections A W C (by rw [hm, map_a₁]; exact intCast_mem A _) h2⟩

/-- (0,0)は5上で滑らかに還元しないため、同じ任意の中心へ近づく。 -/
theorem point_near (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 5)
    (C : CriticalCentre A (curve.baseChange (AlgebraicClosure ℚ))) : A.valuation ((0 : AlgebraicClosure ℚ) - C.x) < 1 := by
  apply (not_hasSmoothReduction_some_iff_of_model (model A) _ (model_map A) C point_nonsingular).mp
  rw [hasSmoothReduction_some_iff]
  have := charP_residueField A (by decide) hA
  intro hs
  have hn := hs A.zero_mem A.zero_mem
  change ((model A).map (IsLocalRing.residue A)).toAffine.Nonsingular 0 0 at hn
  have h5 : (5 : IsLocalRing.ResidueField A) = 0 := CharP.cast_eq_zero _ 5
  norm_num [model, integerCurve, nonsingular_iff, equation_iff, map_ofNat, h5] at hn
  exact hn h5

/-- 実際の3-torsion点について四状態の帰納を通し、j=1とv(X)³=v(F₀)を確定する。 -/
theorem point_depth (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 5)
    (C : CriticalCentre A (curve.baseChange (AlgebraicClosure ℚ))) (D : TangentDirections C) :
    A.valuation (equationDefect (curve.baseChange (AlgebraicClosure ℚ)) C.x C.y) < A.valuation ((0 : AlgebraicClosure ℚ) - C.x) ^ 2 ∧
      A.valuation ((0 : AlgebraicClosure ℚ) - C.x) ^ 3 = A.valuation (equationDefect (curve.baseChange (AlgebraicClosure ℚ)) C.x C.y) := by
  have h3 : A.valuation (3 : AlgebraicClosure ℚ) = 1 := valuation_intCast_eq_one_of_not_dvd A (by decide)
    ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 3) (by norm_num)
  obtain ⟨hs, j, hj1, hj2, he⟩ := odd_torsion_depth_of_model (model A) _ (model_map A) C D
    (by decide : Odd 3) (by decide : 3 ≤ 3) h3 point_nonsingular point_three_torsion.2 (point_near A hA C)
  have hj : j = 1 := by omega
  exact ⟨hs, by simpa only [hj, pow_one] using he⟩

/-- 同じSource 37では悪い素数3でも全残余点が固定される。滑らかさ・浅さの入力はない。 -/
theorem source37_bad_fixed (S : DkMath.FLT.Frey.Source 37) (hd : (3 : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 3)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ inertiaSubgroupIn A ℚ) (P : S.ResidualSpace) :
    S.residualRepresentation σ P = P := S.residual_fixed_at_bad_prime (by decide) (by decide) (by decide) (by decide) hd A hA σ hσ P

/-- 同じSource 37ではq≠2,37の任意の素数と全残余点について固定性が成り立つ。 -/
theorem source37_fixed (S : DkMath.FLT.Frey.Source 37) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ inertiaSubgroupIn A ℚ) (P : S.ResidualSpace) :
    S.residualRepresentation σ P = P := S.residual_fixed_away_two_self (by decide) hq hq2 hqp A hA σ hσ P

/-- 同じ部分加群と同じ商の両側を同時に固定する最終APIも、指数37へ特殊化できる。 -/
theorem source37_fixed_cofixed (S : DkMath.FLT.Frey.Source 37) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) (N : Submodule (ZMod 37) S.ResidualSpace) :
    FixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ) ∧ CofixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ) :=
  S.residual_fixed_and_cofixed_away_two_self (by decide) hq hq2 hqp A hA N

/-- 同じ曲線の整な有限点R=(2,1)。5上で滑らかに還元する復帰則の実例に使う。 -/
theorem smooth_point_nonsingular : (curve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular 2 1 := by
  norm_num [curve, integerCurve, WeierstrassCurve.baseChange, nonsingular_iff, equation_iff]

/-- RのY偏微分9は5上で単元なので、同じ整モデルで滑らかに還元する。 -/
theorem smooth_point_reduction (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 5) :
    HasSmoothReduction (model A) (Point.some 2 1 smooth_point_nonsingular) := by
  have := charP_residueField A (by decide) hA
  have h5 : (5 : IsLocalRing.ResidueField A) = 0 := CharP.cast_eq_zero _ 5
  have h9 : (9 : IsLocalRing.ResidueField A) ≠ 0 := by
    intro he
    have h1 : (1 : IsLocalRing.ResidueField A) = 0 := by linear_combination 2 * h5 - he
    exact one_ne_zero h1
  rw [hasSmoothReduction_some_iff]
  intro hx hy
  change ((model A).map (IsLocalRing.residue A)).toAffine.Nonsingular
    (IsLocalRing.residue A 2) (IsLocalRing.residue A 1)
  norm_num [model, integerCurve, nonsingular_iff, equation_iff, map_ofNat]
  right
  intro he
  apply h9
  linear_combination he

/-- R+P=(−5/4,−25/8)を実際の点加法で計算する。 -/
theorem return_coordinates :
    ∃ h : (curve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular (-5 / 4) (-25 / 8),
      Point.some 2 1 smooth_point_nonsingular + point = Point.some _ _ h := by
  have h : (curve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular (-5 / 4) (-25 / 8) := by
    norm_num [curve, integerCurve, WeierstrassCurve.baseChange, nonsingular_iff, equation_iff]
  refine ⟨h, ?_⟩
  unfold point
  rw [Point.add_of_X_ne (by norm_num : (2 : AlgebraicClosure ℚ) ≠ 0), Point.some.injEq]
  norm_num [addX, addY, negY, slope, curve, integerCurve, WeierstrassCurve.baseChange]

/-- 零成分部分群を仮定せず、整な滑らかなRとの加法がPの浅い深さと枝を保つことを実例で検査する。 -/
theorem integral_return_example (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 5)
    (C : CriticalCentre A (curve.baseChange (AlgebraicClosure ℚ))) (D : TangentDirections C) :
    ∃ (x y : AlgebraicClosure ℚ) (h : (curve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x y),
      Point.some 2 1 smooth_point_nonsingular + point = Point.some x y h ∧
      A.valuation (x - C.x) = A.valuation ((0 : AlgebraicClosure ℚ) - C.x) ∧
      A.valuation (EllipticShallowSlope.centreSlope C x y - EllipticShallowSlope.centreSlope C 0 0) < 1 := by
  obtain ⟨x, y, h, he, _, hp, _⟩ := EllipticIntegralReturn.integral_smooth_add_preserves_of_model (model A) _ (model_map A) C D
    smooth_point_nonsingular point_nonsingular (smooth_point_reduction A hA) (ofNat_mem A 2) (point_near A hA C)
  obtain ⟨hd, hb⟩ := hp (point_depth A hA C D).1
  exact ⟨x, y, h, he, hd, hb⟩

end FreyUnramifiedAwayTest
