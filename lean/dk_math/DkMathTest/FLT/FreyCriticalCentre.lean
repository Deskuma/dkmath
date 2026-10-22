/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCriticalCentre
import DkMathTest.FLT.FreyValuationArithmetic

#print "file: DkMathTest.FLT.FreyCriticalCentre"

/-!
# NOTE-031-002C2: 素数3の中心構成と、分母12を約分できない境界

前章の曲線のΔ=225,c₄=241から、実際に代数閉包上の臨界中心を構成する。
別の曲線では二候補を有理数で明示し、一方のX座標−5/6が3上で非整となることを示す。
したがって「c₄の平方根が単元なので、12で割っても整」という誤った短縮を排除する。
中心は曲線上のtorsion点ではなく、剰余特異点の持ち上げである。
-/
namespace FreyCriticalCentreTest
open DkMath.Lib.NumberTheory ValuationInertia ValuationPrimeSupport
open EllipticCriticalCentre EllipticCriticalCentreAlgebra WeierstrassCurve
open FreyValuationArithmeticTest
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- 前章の同じ整数モデルの実際の不変量。 -/
theorem curve_invariants : curveInt.Δ = 225 ∧ curveInt.c₄ = 241 := by
  norm_num [curveInt, Δ, c₄, b₂, b₄, b₆, b₈]

/-- 3上の全ての付値環で、同じ曲線の中心が実在し、そのずれはv(3)²、座標は慣性固定である。
有限体上の特異座標だけを与えて中心の存在を省略する回帰ではない。 -/
theorem exists_centre_at_three
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 3) :
    ∃ C : CriticalCentre A (curve.baseChange (AlgebraicClosure ℚ)),
      A.valuation (equationDefect (curve.baseChange (AlgebraicClosure ℚ)) C.x C.y) =
        A.valuation (3 : AlgebraicClosure ℚ) ^ 2 ∧
      ∀ (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)), σ ∈ inertiaSubgroupIn A ℚ →
        σ C.x = C.x ∧ σ C.y = C.y := by
  let W := curve.baseChange (AlgebraicClosure ℚ)
  have hm : W = curveInt.map (Int.castRingHom (AlgebraicClosure ℚ)) := by
    simp only [W, curve, baseChange, map_map]
    congr 1
  have hd : W.Δ = (225 : AlgebraicClosure ℚ) := by rw [hm, map_Δ, curve_invariants.1]; rfl
  have hc : W.c₄ = (241 : AlgebraicClosure ℚ) := by rw [hm, map_c₄, curve_invariants.2]; rfl
  have hsmall := valuation_intCast_lt_one_of_dvd A ((ValuationSubring.mem_nonunits_iff _).mp hA)
    (z := 225) (by norm_num)
  have hunit := valuation_intCast_eq_one_of_not_dvd A (by decide)
    ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 241) (by norm_num)
  obtain ⟨C⟩ := exists_criticalCentre A W
    (by rw [hm, map_a₁]; exact intCast_mem A _)
    (by rw [hm, map_a₂]; exact intCast_mem A _)
    (by rw [hm, map_a₃]; exact intCast_mem A _)
    (by rw [hm, map_a₄]; exact intCast_mem A _)
    (by rw [hm, map_a₆]; exact intCast_mem A _)
    (by rw [hd]; norm_num) (by rw [hd]; exact hsmall) (by rw [hc]; exact hunit)
  have h25 := valuation_intCast_eq_one_of_not_dvd A (by decide)
    ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 25) (by norm_num)
  change A.valuation (25 : AlgebraicClosure ℚ) = 1 at h25
  have h2 := valuation_intCast_eq_one_of_not_dvd A (by decide)
    ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 2) (by norm_num)
  refine ⟨C, ?_, fun σ hσ => C.inertia_fixed curve A h2 σ hσ⟩
  rw [C.defect_valuation, hd, show (225 : AlgebraicClosure ℚ) = 3 ^ 2 * 25 by norm_num,
    map_mul, map_pow, h25, mul_one]

/-- 同じ中心は、同じ整モデルの剰余曲線の実際の特異点へ還元する。 -/
theorem centre_residue_singular (A : ValuationSubring (AlgebraicClosure ℚ))
    (C : CriticalCentre A (curve.baseChange (AlgebraicClosure ℚ))) :
    let V := curveInt.map (Int.castRingHom A)
    let xr := IsLocalRing.residue A (⟨C.x, C.x_mem⟩ : A)
    let yr := IsLocalRing.residue A (⟨C.y, C.y_mem⟩ : A)
    (V.map (IsLocalRing.residue A)).toAffine.Equation xr yr ∧
      ¬ (V.map (IsLocalRing.residue A)).toAffine.Nonsingular xr yr := by
  apply C.residue_singular_of_model (curveInt.map (Int.castRingHom A))
  simp only [curve, baseChange, map_map]
  congr 1

/-- 二つの臨界中心候補を有理座標で追える別の曲線。 -/
def candidateCurve : WeierstrassCurve ℚ := ⟨1, 1, 0, 0, 3⟩

/-- c₄=25の二候補はX=0とX=−5/6となる。良い候補のずれは−3であり曲線上の点ではない。 -/
theorem candidate_identities : candidateCurve.c₄ = 25 ∧ candidateCurve.Δ = -4263 ∧
    centreX candidateCurve 5 = 0 ∧ centreY candidateCurve 5 = 0 ∧
    centreX candidateCurve (-5) = -5 / 6 ∧ equationDefect candidateCurve 0 0 = -3 := by
  norm_num [candidateCurve, c₄, Δ, b₂, b₄, b₆, b₈, centreX, centreY, equationDefect]

/-- 素数3では、一方の候補は整だが、もう一方は整でない。
分母12の単元性を仮定する代わりに、ずれを比較して候補を選ぶ必要がある。 -/
theorem candidate_boundary_at_three (A : ValuationSubring ℚ) (hA : LiesOverPrime A 3) :
    centreX candidateCurve 5 ∈ A ∧ centreX candidateCurve (-5) ∉ A := by
  refine ⟨candidate_identities.2.2.1 ▸ A.zero_mem, ?_⟩
  intro hx
  have h6 := valuation_intCast_lt_one_of_dvd A ((ValuationSubring.mem_nonunits_iff _).mp hA)
    (z := 6) (by norm_num)
  have h5 := valuation_intCast_eq_one_of_not_dvd A (by decide)
    ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := -5) (by norm_num)
  change A.valuation (-5 : ℚ) = 1 at h5
  have he : (6 : ℚ) * centreX candidateCurve (-5) = -5 := by
    norm_num [centreX, candidateCurve, b₂]
  have hv := congrArg A.valuation he
  rw [map_mul, h5] at hv
  have hle : A.valuation (6 : ℚ) * A.valuation (centreX candidateCurve (-5)) ≤ A.valuation (6 : ℚ) :=
    mul_le_of_le_one_right' ((A.valuation_le_one_iff _).mpr hx)
  rw [hv] at hle
  exact (not_lt.mpr hle) h6

/-- 素数2では符号を区別する新補題の単元条件を満たさない。奇素数の仮定を落とさない。 -/
theorem two_not_unit_at_two (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    A.valuation (2 : AlgebraicClosure ℚ) ≠ 1 := ((ValuationSubring.mem_nonunits_iff _).mp hA).ne

/-- 同じSource 37の悪い素数3で、中心の座標の慣性固定と同じずれの37乗の付値を供給する。
残余点の固定やSourceの存在に読み替えない。 -/
theorem source37_centre (S : DkMath.FLT.Frey.Source 37) (hd : (3 : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 3) :
    ∃ C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)),
      (∀ (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)), σ ∈ inertiaSubgroupIn A ℚ →
        σ C.x = C.x ∧ σ C.y = C.y) ∧
      A.valuation (equationDefect (S.rationalCurve.baseChange (AlgebraicClosure ℚ)) C.x C.y) =
        (A.valuation (3 : AlgebraicClosure ℚ) ^ (2 * padicValInt 3 (S.a * S.b * S.c))) ^ 37 :=
  S.exists_criticalCentre_at_bad_prime (by decide) (by decide) hd A hA

end FreyCriticalCentreTest
