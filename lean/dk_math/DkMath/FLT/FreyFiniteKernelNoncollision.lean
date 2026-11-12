/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernelCollision
import DkMath.Lib.NumberTheory.EllipticFiniteKernelNoncollision

#print "file: DkMath.FLT.FreyFiniteKernelNoncollision"

/-!
# 同じSourceの非衝突点と節点上の冪写像

同じ一次元Lが零成分に含まれるとき、核点の滑らかさ・点数・単元位数を
既存Sourceから供給する。非衝突の同じ点の商Xの剰余は、同じ源の剰余点の
p倍のx座標で表される。節点のFrameと非衝突は明示し、標的の非特異性を仮定しない。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticGoodReductionSeparation WeierstrassModelReduction
open ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport
open DkMath.Lib.RepresentationTheory EllipticNodalTorsion.NodalTorsion
open scoped BigOperators
noncomputable local instance instDecidableEqFreyFiniteKernelNoncollision {α : Type*} : DecidableEq α :=
  Classical.decEq _
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じSourceの非衝突点では、実際の商Xの剰余が同じ節点上のp倍点で表される。
同じLの零成分包含から核点の滑らかさを得て、点数と巡回列挙も内部供給する。 -/
theorem residual_kernelXAt_nodal_of_noncollision
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hle : L ≤ S.residualZeroComponent A) (P : Points S.rationalCurve)
    (hP : HasSmoothReduction (S.valuationModel A) P)
    (hout : ∀ Q : pointSubgroup S.rationalCurve p L,
      modelReduce A (S.valuationModel A) _ (S.valuationModel_map A) P ≠
        modelReduce A (S.valuationModel A) _ (S.valuationModel_map A) Q.val)
    {x₀ y₀ α : ResidueField A}
    (F : Frame ((S.valuationModel A).map (residue A)) x₀ y₀ α)
    (hsep : α ≠ -((S.valuationModel A).map (residue A)).a₁ - α) :
    let H := pointSubgroup S.rationalCurve p L
    letI := S.finite_residualPointSubgroup L hl
    letI := Fintype.ofFinite H
    let hs := S.residual_kernel_smooth_of_le L A hle
    let hp := not_mem_of_reduction_noncollision S.rationalCurve H A (S.valuationModel A)
      (S.valuationModel_map A) P hout
    let hn : A.valuation (p : AlgebraicClosure ℚ) = 1 := by
      simpa only [pow_one] using prime_power_value_one A (Fact.out : p.Prime) hq
        ((ValuationSubring.mem_nonunits_iff _).mp hA) hqp 1
    let hx := (kernelAt_coordinates_mem S.rationalCurve H p (S.residual_kernel_killed L) A
      (S.valuationModel A) (S.valuationModel_map A) hn hs P hP hout).1
    residue A ⟨kernelXAt S.rationalCurve H P hp, hx⟩ =
      (p : ResidueField A) ^ 2 * (p • modelReduce A (S.valuationModel A) _ (S.valuationModel_map A) P).xc +
        ((p : ResidueField A) - (p : ResidueField A) ^ 2) * x₀ -
        ∑ Q : H, (smoothKernelReduction S.rationalCurve H A (S.valuationModel A)
          (S.valuationModel_map A) hs Q).xc := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  have hunit : A.valuation (p : AlgebraicClosure ℚ) = 1 := by
    simpa only [pow_one] using prime_power_value_one A (Fact.out : p.Prime) hq
      ((ValuationSubring.mem_nonunits_iff _).mp hA) hqp 1
  exact kernelXAt_residue_nodal_prime S.rationalCurve _ p (S.residual_kernel_killed L) A
    (S.valuationModel A) (S.valuationModel_map A) hunit (S.residual_kernel_smooth_of_le L A hle)
    P hP hout (card_pointSubgroup S.rationalCurve p L hl) F hsep

end DkMath.FLT.Frey.Source
