/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernelGoodReduction
import DkMath.Lib.NumberTheory.EllipticFiniteKernelZeroComponent

#print "file: DkMath.FLT.FreyFiniteKernelZeroComponent"

/-!
# 同じSourceの特異核側で、全零成分の像を同じ付値環標的へ運ぶ

同じ一次元Lが源の零成分p捩れと交わらない側では、非零実核点が全て特異に還元する。
同じ実点商準同型の全ての零成分像に、付値環標的での滑らかな還元を供給する。
臨界中心はSourceの奇素数・2進幾何から内部供給する。Lが零成分に入る側へは流用しない。
整数化後の点での還元判定、逆像判定、Δ深さ、一般hnoは別の残る接続である。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticGoodReductionSeparation EllipticCriticalCentre
open ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport
noncomputable local instance instDecidableEqFreyFiniteKernelZeroComponent {α : Type*} : DecidableEq α :=
  Classical.decEq _
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem prime_unit {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) :
    A.valuation (p : AlgebraicClosure ℚ) = 1 := by
  simpa only [pow_one] using prime_power_value_one A (Fact.out : p.Prime) hq
    ((ValuationSubring.mem_nonunits_iff _).mp hA) hqp 1

/-- 同じSourceの実点準同型は、p以外の全住所で非整なx座標を保つ。2も除外しない。 -/
theorem residual_pointHom_x_not_mem (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (P : Points S.rationalCurve) (hx : P.xc ∉ A) :
    (S.residualOddKernelPointHom hp2 L hl P).xc ∉ A := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact oddKernelPointMap_x_not_mem S.rationalCurve _ p (S.residual_kernel_killed L)
    A (S.valuationModel A) (S.valuationModel_map A) (prime_unit hq hqp A hA)
    (S.residual_pointSubgroup_odd hp2 L hl) P hx

/-- 同じ中心を持つ特異核側では、源の全零成分の点を同じ付値環標的へ運べる。 -/
theorem residual_pointHom_smooth_of_disjoint_geometry (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (C : CriticalCentre A (S.rationalCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))))
    (hd : Disjoint L (S.residualZeroComponent A))
    (P : Points S.rationalCurve) (hP : HasSmoothReduction (S.valuationModel A) P) :
    HasSmoothReduction (S.residualValuationKernelModel L hl hq hqp A hA)
      (S.residualOddKernelPointHom hp2 L hl P) := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact oddKernelPointMap_smooth_of_not_smooth_kernel S.rationalCurve _ A
    (S.valuationModel A) (S.valuationModel_map A) C p (S.residual_kernel_killed L)
    (prime_unit hq hqp A hA) (S.residual_pointSubgroup_odd hp2 L hl)
    (S.residual_kernel_not_smooth_of_disjoint L A hd) P hP

/-- 悪い奇素数q≠pの特異核側で、同じ全零成分の像の滑らかさを内部供給する。 -/
theorem residual_pointHom_smooth_at_bad_prime_of_disjoint (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hbad : (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hd : Disjoint L (S.residualZeroComponent A))
    (P : Points S.rationalCurve) (hP : HasSmoothReduction (S.valuationModel A) P) :
    HasSmoothReduction (S.residualValuationKernelModel L hl Fact.out hqp A hA)
      (S.residualOddKernelPointHom hp2 L hl P) := by
  obtain ⟨C,-,-,-⟩ := S.exists_criticalCentre_directions_at_bad_prime
    (Nat.Prime.pos (Fact.out : p.Prime)) hq2 hbad A hA
  exact S.residual_pointHom_smooth_of_disjoint_geometry hp2 L hl Fact.out hqp A hA C hd P hP

/-- 2進場所の特異核側でも、同じ全零成分の像の滑らかさを供給する。p≥5を保持する。 -/
theorem residual_pointHom_smooth_at_two_of_disjoint (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (hd : Disjoint L (S.residualZeroComponent A))
    (P : Points S.rationalCurve) (hP : HasSmoothReduction (S.valuationModel A) P) :
    HasSmoothReduction (S.residualValuationKernelModel L hl Nat.prime_two (by omega) A hA)
      (S.residualOddKernelPointHom (by omega) L hl P) := by
  obtain ⟨C,-,-,-⟩ := S.exists_dyadic_geometry hp5 A hA
  exact S.residual_pointHom_smooth_of_disjoint_geometry (by omega) L hl Nat.prime_two
    (by omega) A hA C hd P hP

end DkMath.FLT.Frey.Source
