/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.Lib.NumberTheory.EllipticFiniteKernelNodalLevels
import DkMath.Lib.NumberTheory.ValuationRationalPrimeSupport
import DkMathTest.Lib.NumberTheory.EllipticFiniteKernelReduction

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelNodalLevels"

/-! 実3点核の7上で、節点距離の水準を使う商像の判定を検査する。 -/
namespace EllipticFiniteKernelNodalLevelsTest
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticCriticalCentre EllipticCriticalCentreAlgebra EllipticGoodReductionSeparation
open EllipticFiniteKernelReductionTest ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport
noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq _
local instance : sample.IsElliptic := ⟨by norm_num [sample, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]⟩
noncomputable local instance : Fintype sampleKernel := Fintype.ofFinset {0, Q, -Q} (by
  intro P
  change P ∈ ({0, Q, -Q} : Finset (Points sample)) ↔ P = 0 ∨ P = Q ∨ P = -Q
  simp only [Finset.mem_insert, Finset.mem_singleton])
private theorem three_unit (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 7) :
    A.valuation (3 : AlgebraicClosure ℚ) = 1 :=
  valuation_intCast_eq_one_of_not_dvd A (by decide : Nat.Prime 7)
    ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 3) (by norm_num)

/-- 実3点核の特異側では、中心誤差の深さを与えると、核外の特異点の商像の
滑らかさが半核水準との一致で判定される。中心の存在と深さは仮定として明示する。 -/
theorem sample_seven_level_criterion (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 7) (C : CriticalCentre A (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))))
    (T : CriticalCentre A (kernelModel sample sampleKernel)) (P : Points sample) (hP : P ∉ sampleKernel)
    (hPbad : ¬ HasSmoothReduction (localSource A) P)
    (hdeep : ∀ R ∈ halfKernel sample sampleKernel, A.valuation (4 * equationDefect
      (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))) C.x C.y) < A.valuation (R.val.xc - C.x) ^ 2) :
    HasSmoothReduction (valuationKernelModel sample sampleKernel 3 sample_killed A (localSource A)
      (localSource_map A) (three_unit A hA))
      (oddKernelPointMap sample sampleKernel (sampleKernel_card ▸ (by decide : Odd 3)) P) ↔
    ∃ R ∈ halfKernel sample sampleKernel, A.valuation (P.xc - C.x) = A.valuation (R.val.xc - C.x) :=
  singular_three_target_smooth_iff_kernel_level sample sampleKernel A C
    (sampleKernel_card ▸ (by decide : Odd 3)) P hP 3 sample_killed (localSource A) (localSource_map A)
    (three_unit A hA) T sampleKernel_card (sample_kernel_singular_at_seven A hA) hPbad hdeep

end EllipticFiniteKernelNodalLevelsTest
