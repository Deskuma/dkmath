/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernelZeroComponent
import DkMath.Lib.NumberTheory.EllipticFiniteKernelReductionSquare
import DkMath.Lib.NumberTheory.WeierstrassIntegerReductionTransport

#print "file: DkMath.FLT.FreyFiniteKernelReductionSquare"

/-!
# 同じSourceの還元可換図式と、既存整数標的の点への零成分輸送

特異核側では同じ付値環商標的での実際の還元が源の還元に一致する。
p以外では既存整数化の倍率が単元なので、既存整数点準同型の滑らかな還元を
同じ付値環点準同型と双方向に比較できる。悪い奇素数と2を同じ入口で扱う。
滑らかな核側の全零成分輸送、逆像判定、Δ深さ、q=pと一般hnoは残る。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticGoodReductionSeparation EllipticCriticalCentre WeierstrassVariableChange
open WeierstrassModelReduction WeierstrassRationalIntegralModel ValuationInertia
open ValuationPrimeSupport ValuationRationalPrimeSupport DkMath.Lib.RepresentationTheory
noncomputable local instance instDecidableEqFreyFiniteKernelReductionSquare {α : Type*} : DecidableEq α :=
  Classical.decEq _
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem prime_unit {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) :
    A.valuation (p : AlgebraicClosure ℚ) = 1 := by
  simpa only [pow_one] using prime_power_value_one A (Fact.out : p.Prime) hq
    ((ValuationSubring.mem_nonunits_iff _).mp hA) hqp 1

private theorem smooth_modelEquiv {k : Type*} [Field k] (A : ValuationSubring k)
    (M : WeierstrassCurve A) {W V : WeierstrassCurve k} (h : W = V) (P : W.toAffine.Point) :
    HasSmoothReduction M (pointModelEquiv h P) ↔ HasSmoothReduction M P := by
  subst V
  rfl

/-- 同じSource・核・付値環標的で、特異核側の実点商準同型と還元が可換。 -/
theorem residual_pointHom_reduction_square (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (C : CriticalCentre A (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))))
    (hd : Disjoint L (S.residualZeroComponent A)) (P : Points S.rationalCurve)
    (hP : HasSmoothReduction (S.valuationModel A) P) :
    pointEquivOfModelEq (S.residual_valuation_kernel_residue_eq_of_disjoint L hl hq hqp A hA hd)
      (modelReduce A (S.residualValuationKernelModel L hl hq hqp A hA) (S.residualKernelModel L hl)
        (S.residual_valuation_kernel_model_map hp2 L hl hq hqp A hA)
        (S.residualOddKernelPointHom hp2 L hl P)) =
      modelReduce A (S.valuationModel A) (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ)))
        (S.valuationModel_map A) P := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact oddKernelPointMap_reduction_square S.rationalCurve _ p (S.residual_kernel_killed L) A
    (S.valuationModel A) (S.valuationModel_map A) (prime_unit hq hqp A hA) C
    (S.residual_pointSubgroup_odd hp2 L hl) (S.residual_kernel_not_smooth_of_disjoint L A hd) P hP

/-- 悪い住所q≠pの特異核側の可換図式。p≥5で2上の幾何も内部供給する。 -/
theorem residual_pointHom_reduction_square_at_bad_place (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} [Fact q.Prime] (hqp : q ≠ p) (hbad : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hd : Disjoint L (S.residualZeroComponent A)) (P : Points S.rationalCurve)
    (hP : HasSmoothReduction (S.valuationModel A) P) :
    pointEquivOfModelEq (S.residual_valuation_kernel_residue_eq_of_disjoint L hl Fact.out hqp A hA hd)
      (modelReduce A (S.residualValuationKernelModel L hl Fact.out hqp A hA) (S.residualKernelModel L hl)
        (S.residual_valuation_kernel_model_map (by omega) L hl Fact.out hqp A hA)
        (S.residualOddKernelPointHom (by omega) L hl P)) =
      modelReduce A (S.valuationModel A) (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ)))
        (S.valuationModel_map A) P := by
  by_cases hq2 : q = 2
  · subst q
    obtain ⟨C, -, -, -⟩ := S.exists_dyadic_geometry hp5 A hA
    exact S.residual_pointHom_reduction_square (by omega) L hl Fact.out hqp A hA C hd P hP
  · obtain ⟨C, -, -, -⟩ := S.exists_criticalCentre_directions_at_bad_prime
      (Nat.Prime.pos (Fact.out : p.Prime)) hq2 (hbad.resolve_left hq2) A hA
    exact S.residual_pointHom_reduction_square (by omega) L hl Fact.out hqp A hA C hd P hP

/-- p以外の全住所で、同じ既存整数点準同型の像の滑らかさは、同じ付値環標的での条件と同値。
共通分母の単元性と既存の二つの点同型の対応を内部で使い、整数化後の像を選び直さない。 -/
theorem residual_integer_pointHom_smooth_iff (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) (P : Points S.rationalCurve) :
    HasSmoothReduction (integerValuationModel A (S.residualIntegerKernelModel L hl hs))
        (S.residualIntegerKernelPointHom hp2 L hl hs P) ↔
      HasSmoothReduction (S.residualValuationKernelModel L hl hq hqp A hA)
        (S.residualOddKernelPointHom hp2 L hl P) := by
  have hmodel := (S.residual_valuation_kernel_model_map hp2 L hl hq hqp A hA).trans
    (S.residual_descended_kernel_model_map L hl hs).symm
  have hi := geometricPointEquiv_smooth_iff (S.residualDescendedKernelModel L hl hs) A _ hmodel
    (S.residual_target_denominator_value_one hp2 L hl hs A hq hqp hA)
    (S.residualIntegerKernelPointHom hp2 L hl hs P)
  rw [S.residual_integer_kernel_pointHom_transport] at hi
  have hh := smooth_modelEquiv A (S.residualValuationKernelModel L hl hq hqp A hA)
    (S.residual_descended_kernel_model_map L hl hs) (S.residualDescendedKernelPointMap hp2 L hl hs P)
  rw [S.residual_descended_kernel_pointMap_transport] at hh
  exact hi.trans hh.symm

/-- 悪い奇素数と2の特異核側で、全零成分を同じ既存整数標的の点へ運ぶ一括終点。
Disjointと源の滑らかさを保持し、滑らかな核側の結論は混入しない。 -/
theorem residual_integer_pointHom_smooth_at_bad_place_of_disjoint (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L) {q : ℕ} [Fact q.Prime] (hqp : q ≠ p)
    (hbad : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hd : Disjoint L (S.residualZeroComponent A)) (P : Points S.rationalCurve)
    (hP : HasSmoothReduction (S.valuationModel A) P) :
    HasSmoothReduction (integerValuationModel A (S.residualIntegerKernelModel L hl hs))
      (S.residualIntegerKernelPointHom (by omega) L hl hs P) := by
  apply (S.residual_integer_pointHom_smooth_iff (by omega) L hl hs Fact.out hqp A hA P).mpr
  by_cases hq2 : q = 2
  · subst q
    exact S.residual_pointHom_smooth_at_two_of_disjoint hp5 L hl A hA hd P hP
  · exact S.residual_pointHom_smooth_at_bad_prime_of_disjoint (by omega) L hl
      hq2 hqp (hbad.resolve_left hq2) A hA hd P hP

end DkMath.FLT.Frey.Source
