/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelZeroComponent
import DkMath.Lib.NumberTheory.WeierstrassModelReduction

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelReductionSquare"

/-!
# 特異核側で、同じ商写像と実際の還元を可換にする

[DkMath.Lib] 前章の全零成分の両座標合同を、実際の還元点の等式へ昇格する。
源と商の剰余モデルは特異核側で等しいので、その等式による点の輸送を明示する。
O・有限整点・非整点を全て含む。滑らかな核の側へこの剰余モデル等式を流用しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open EllipticTorsionRepresentation EllipticGoodReductionSeparation EllipticSmoothReduction
open EllipticCriticalCentre WeierstrassModelReduction WeierstrassVariableChange ValuationResidue
noncomputable local instance instDecidableEqEllipticFiniteKernelReductionSquare {α : Type*} : DecidableEq α :=
  Classical.decEq _
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
  (H : AddSubgroup (Points E)) [Fintype H] (n : ℕ) (hkill : ∀ Q : H, n • Q.val = 0)
  (A : ValuationSubring (AlgebraicClosure K)) (M : WeierstrassCurve A)
  (hM : M.map A.subtype = E.map (algebraMap K (AlgebraicClosure K)))
  (hn : A.valuation (n : AlgebraicClosure K) = 1)
  (C : CriticalCentre A (E.map (algebraMap K (AlgebraicClosure K))))

include C in
/-- [DkMath.Lib] 特異核側の全零成分で、同じ実点商写像と同じモデルでの還元が可換。
像の滑らかさだけでなく、剰余モデルの等式輸送後の実際の点の一致を結論する。 -/
theorem oddKernelPointMap_reduction_square (ho : Odd (Nat.card H))
    (hbad : ∀ Q : H, Q.val ≠ 0 → ¬ HasSmoothReduction M Q.val)
    (P : Points E) (hsm : HasSmoothReduction M P) :
    pointEquivOfModelEq (valuationKernelModel_residue_eq_of_not_smooth E H n hkill A M hM hn hbad)
      (modelReduce A (valuationKernelModel E H n hkill A M hM hn) (kernelModel E H)
        (valuationKernelModel_map E H n hkill A M hM hn ho) (oddKernelPointMap E H ho P)) =
      modelReduce A M (E.map (algebraMap K (AlgebraicClosure K))) hM P := by
  let := kernelModel_isElliptic_of_odd_card E H ho
  by_cases hP : P ∈ H
  · have hz : P = 0 := by
      by_contra hnz
      exact hbad ⟨P, hP⟩ hnz hsm
    subst P
    rw [show oddKernelPointMap E H ho 0 = 0 from kernelPointMap_of_mem E H 0 H.zero_mem,
      modelReduce_zero, map_zero]
    exact (modelReduce_zero A M _ hM).symm
  have hP0 : P ≠ 0 := fun hz => hP (hz ▸ H.zero_mem)
  have he : oddKernelPointMap E H ho P = Point.some _ _ (kernelAt_nonsingular E H P hP) :=
    kernelPointMap_of_not_mem E H P hP
  have hns := Point.nonsingular_xc_yc hP0
  by_cases hx : P.xc ∈ A
  · have hy := EllipticTorsionValuationIntegrality.y_mem_of_x_mem A M _ hM hns.1 hx
    have hc := kernelAt_congr_of_not_smooth_kernel E H A M hM C hbad P hP hsm
    have hxi : kernelXAt E H P hP ∈ A := by
      have hi := A.add_mem _ _ ((A.valuation_le_one_iff _).mp hc.1.le) hx
      simpa only [sub_add_cancel] using hi
    have hyi : kernelYAt E H P hP ∈ A := by
      have hi := A.add_mem _ _ ((A.valuation_le_one_iff _).mp hc.2.le) hy
      simpa only [sub_add_cancel] using hi
    have hrx := (residue_eq_residue_iff_sub_mem_nonunits A hxi hx).mpr
      ((ValuationSubring.mem_nonunits_iff _).mpr hc.1)
    have hry := (residue_eq_residue_iff_sub_mem_nonunits A hyi hy).mpr
      ((ValuationSubring.mem_nonunits_iff _).mpr hc.2)
    have hs := (hasSmoothReduction_some_iff M hns).mp
      (by rwa [← Point.eq_some_xc_yc hP0]) hx hy
    have ht := oddKernelPointMap_smooth_of_not_smooth_kernel E H A M hM C n hkill hn ho hbad P hsm
    rw [he, hasSmoothReduction_some_iff] at ht
    have hts := ht hxi hyi
    rw [he, modelReduce_some A _ _ _ _ hxi hts]
    have hp : (P : (E.map (algebraMap K (AlgebraicClosure K))).toAffine.Point) =
        Point.some P.xc P.yc hns := Point.eq_some_xc_yc hP0
    have hsource := (congrArg (modelReduce A M _ hM) hp).trans
      (modelReduce_some A M _ hM hns hx hs)
    rw [hsource]
    exact residuePoint_eq A M _ hrx hry _ _
  · have ht := oddKernelPointMap_reduce_zero_of_x_not_mem E H n hkill A M hM hn ho P hx
    change modelReduce A (valuationKernelModel E H n hkill A M hM hn) (kernelModel E H)
      (valuationKernelModel_map E H n hkill A M hM hn ho) (oddKernelPointMap E H ho P) = 0 at ht
    rw [ht, map_zero]
    have hp : (P : (E.map (algebraMap K (AlgebraicClosure K))).toAffine.Point) =
        Point.some P.xc P.yc hns := Point.eq_some_xc_yc hP0
    exact ((congrArg (modelReduce A M _ hM) hp).trans
      (modelReduce_some_not_mem A M _ hM hns hx)).symm

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
