/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernelNodalAll
import DkMath.FLT.FreyFiniteKernelGoodReduction

#print "file: DkMath.FLT.FreyFiniteKernelZeroComponentAway"

/-!
# p以外の全住所における同じ商写像の零成分輸送

p≥5の同じSource・一次元Lについて、悪い住所は前章の任意標数の節点輸送を使う。
良い奇素数住所では同じ核の商の良還元から、全点の像の滑らかさを供給する。
二つを統合してq≠pの全素数における前向き零成分輸送を得る。
剰余点の可換図式・逆像判定・p上の挙動はこの結果に含めない。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticGoodReductionSeparation WeierstrassRationalIntegralModel WeierstrassResidueModel
open ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport
open DkMath.Lib.RepresentationTheory
noncomputable local instance instDecidableEqFreyFiniteKernelZeroComponentAway {α : Type*} : DecidableEq α :=
  Classical.decEq _
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- p≥5、q≠pの任意住所で、同じ実点商準同型は源の全零成分を同じ付値環標的へ送る。
2・3、良還元、両核分岐を内部分類する。源点の滑らかさは保持する。 -/
theorem residual_pointHom_smooth_away (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} [Fact q.Prime] (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (P : Points S.rationalCurve) (hP : HasSmoothReduction (S.valuationModel A) P) :
    HasSmoothReduction (S.residualValuationKernelModel L hl Fact.out hqp A hA)
      (S.residualOddKernelPointHom (by omega) L hl P) := by
  by_cases hbad : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c
  · exact S.residual_pointHom_smooth_at_bad_place hp5 L hl hqp hbad A hA P hP
  · push Not at hbad
    let := S.finite_residualPointSubgroup L hl
    let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
    have hv2 := valuation_intCast_eq_one_of_not_dvd A (Fact.out : q.Prime)
      ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 2)
      (by intro h; exact hbad.1 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp (by exact_mod_cast h)))
    let : NeZero (2 : ResidueField A) := ⟨by
      have hr := (residue_ne_zero_iff A (2 : A)).mpr hv2
      simpa only [map_ofNat] using hr⟩
    have hunit : A.valuation (p : AlgebraicClosure ℚ) = 1 := by
      simpa only [pow_one] using prime_power_value_one A (Fact.out : p.Prime) Fact.out
        ((ValuationSubring.mem_nonunits_iff _).mp hA) hqp 1
    let := S.valuation_reduction_isElliptic (Fact.out : p.Prime).pos hbad.1 hbad.2 A hA
    exact oddKernelPointMap_smooth_of_good S.rationalCurve (pointSubgroup S.rationalCurve p L) p
      (S.residual_kernel_killed L) A (S.valuationModel A) (S.valuationModel_map A) hunit
      (S.residual_pointSubgroup_odd (by omega) L hl) ((S.valuationModel A).map (residue A)).Δ'.ne_zero P

/-- p≥5、q≠pの任意住所で、同じ既存整数標的への全零成分輸送。
同じLのガロア安定性と源点の滑らかさを保持する。 -/
theorem residual_integer_pointHom_smooth_away (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hst : IsStable S.residualRepresentation L) {q : ℕ} [Fact q.Prime] (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (P : Points S.rationalCurve) (hP : HasSmoothReduction (S.valuationModel A) P) :
    HasSmoothReduction (integerValuationModel A (S.residualIntegerKernelModel L hl hst))
      (S.residualIntegerKernelPointHom (by omega) L hl hst P) :=
  (S.residual_integer_pointHom_smooth_iff (by omega) L hl hst Fact.out hqp A hA P).mpr
    (S.residual_pointHom_smooth_away hp5 L hl hqp A hA P hP)

end DkMath.FLT.Frey.Source
