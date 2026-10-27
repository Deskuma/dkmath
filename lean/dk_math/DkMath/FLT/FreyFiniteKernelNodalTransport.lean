/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernelNoncollision
import DkMath.Lib.NumberTheory.EllipticFiniteKernelNodalTransport

#print "file: DkMath.FLT.FreyFiniteKernelNodalTransport"

/-!
# 同じSourceの中心一致を条件とする全零成分輸送

同じLの核が零成分に含まれ、同じ剰余標的の臨界中心が候補値に一致するとき、
衝突と非衝突の両場合を併せ、同じ全点商準同型の全零成分像が滑らかになる。
安定性の下で既存整数標的へも接続する。中心一致の仮定は保持する。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticGoodReductionSeparation EllipticCriticalCentre WeierstrassModelReduction
open WeierstrassRationalIntegralModel ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport
open DkMath.Lib.RepresentationTheory EllipticNodalTorsion.NodalTorsion
open scoped BigOperators
noncomputable local instance instDecidableEqFreyFiniteKernelNodalTransport {α : Type*} : DecidableEq α :=
  Classical.decEq _
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じSource・同じLと同じ標的で、中心一致を条件として全零成分像が滑らかになる。
候補中心の一致、源の節点Frameと方向分離は外部仮定として保持する。 -/
theorem residual_pointHom_smooth_of_candidate (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hle : L ≤ S.residualZeroComponent A) {x₀ y₀ α : ResidueField A}
    (F : Frame ((S.valuationModel A).map (residue A)) x₀ y₀ α)
    (hsep : α ≠ -((S.valuationModel A).map (residue A)).a₁ - α)
    (C : CriticalCentre A (S.residualKernelModel L hl))
    (hc : letI := S.finite_residualPointSubgroup L hl
      letI := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
      residue A ⟨C.x, C.x_mem⟩ = (p : ResidueField A) * x₀ -
        ∑ Q : pointSubgroup S.rationalCurve p L,
          (smoothKernelReduction S.rationalCurve _ A (S.valuationModel A) (S.valuationModel_map A)
            (S.residual_kernel_smooth_of_le L A hle) Q).xc)
    (P : Points S.rationalCurve) (hP : HasSmoothReduction (S.valuationModel A) P) :
    HasSmoothReduction (S.residualValuationKernelModel L hl hq hqp A hA)
      (S.residualOddKernelPointHom hp2 L hl P) := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  have hunit : A.valuation (p : AlgebraicClosure ℚ) = 1 := by
    simpa only [pow_one] using prime_power_value_one A (Fact.out : p.Prime) hq
      ((ValuationSubring.mem_nonunits_iff _).mp hA) hqp 1
  exact oddKernelPointMap_smooth_of_candidate S.rationalCurve _ p (S.residual_kernel_killed L) A
    (S.valuationModel A) (S.valuationModel_map A) hunit (S.residual_kernel_smooth_of_le L A hle)
    (card_pointSubgroup S.rationalCurve p L hl) (S.residual_pointSubgroup_odd hp2 L hl) F hsep C hc P hP

/-- 安定な同じLの既存整数商標的への零成分輸送。中心一致は引き続き仮定する。 -/
theorem residual_integer_pointHom_smooth_of_candidate (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hst : IsStable S.residualRepresentation L) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hle : L ≤ S.residualZeroComponent A) {x₀ y₀ α : ResidueField A}
    (F : Frame ((S.valuationModel A).map (residue A)) x₀ y₀ α)
    (hsep : α ≠ -((S.valuationModel A).map (residue A)).a₁ - α)
    (C : CriticalCentre A (S.residualKernelModel L hl))
    (hc : letI := S.finite_residualPointSubgroup L hl
      letI := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
      residue A ⟨C.x, C.x_mem⟩ = (p : ResidueField A) * x₀ -
        ∑ Q : pointSubgroup S.rationalCurve p L,
          (smoothKernelReduction S.rationalCurve _ A (S.valuationModel A) (S.valuationModel_map A)
            (S.residual_kernel_smooth_of_le L A hle) Q).xc)
    (P : Points S.rationalCurve) (hP : HasSmoothReduction (S.valuationModel A) P) :
    HasSmoothReduction (integerValuationModel A (S.residualIntegerKernelModel L hl hst))
      (S.residualIntegerKernelPointHom hp2 L hl hst P) :=
  (S.residual_integer_pointHom_smooth_iff hp2 L hl hst hq hqp A hA P).mpr
    (S.residual_pointHom_smooth_of_candidate hp2 L hl hq hqp A hA hle F hsep C hc P hP)

end DkMath.FLT.Frey.Source
