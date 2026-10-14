/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CoarseTownPrimeHandoff
import DkMathTest.NumberTheory.LegendreSurvivor297Calibration

#print "file: DkMathTest.NumberTheory.LegendreHandoffRegression"

namespace DkMathTest.LegendreHandoffRegression

open DkMath.NumberTheory.Legendre DkMath.NumberTheory.Primitive DkMath.NumberTheory.StructuralArithmetic

private theorem support_function (n : ℕ) : squareOffsetPrimeSupport n = boundedSquareSupport n :=
  funext (squareOffsetPrimeSupport_eq_boundedSquareSupport n)

theorem six_handoff : coarseTownMaxHandoff {3} 6 5 2 := by
  unfold coarseTownMaxHandoff coarseTownFiberMaximumAt coarseFullTownActivePrimes
    coarseTownNonmaximumFiberSeats coarseFullTownPrimeFiber
  rw [support_function 6]
  simp only [and_assoc]
  decide +kernel

theorem eight_branching : coarseTownMaxHandoff {3} 8 5 2 ∧ coarseTownMaxHandoff {3} 8 5 7 := by
  unfold coarseTownMaxHandoff coarseTownFiberMaximumAt coarseFullTownActivePrimes
    coarseTownNonmaximumFiberSeats coarseFullTownPrimeFiber
  rw [support_function 8]
  simp only [and_assoc]
  decide +kernel

theorem six_gap_counterexample :
    coarseTownFiberMaximumAt {3} 6 5 4 ∧
      4 ∈ coarseFullTownPrimeFiber {3} 6 2 ∧ 8 ∈ coarseFullTownPrimeFiber {3} 6 2 ∧
      4 < 8 ∧ ¬ (2 * 5 : ℕ) ∣ 8 - 4 := by
  unfold coarseTownFiberMaximumAt coarseFullTownPrimeFiber
  rw [support_function 6]
  decide +kernel

theorem seven_shared_minimum :
    coarseTownFiberMinimumAt {3} 7 2 1 ∧ coarseTownFiberMinimumAt {3} 7 5 1 ∧
      1 ∈ coarseTownRightPackingRemainder {3} 7 := by
  rw [mem_coarseTownRightPackingRemainder_iff_minima (by decide +kernel)]
  unfold coarseTownFiberMinimumAt coarseFullTownPrimeFiber
  rw [support_function 7]
  decide +kernel

theorem seven_distinct_terminal_directions :
    2 ∈ coarseTownRightRepresentedPrimes {3} 7 ∧ 5 ∈ coarseTownRightRepresentedPrimes {3} 7 :=
  ⟨(coarseTownMin_represented_iff_retained seven_shared_minimum.1).mpr seven_shared_minimum.2.2,
   (coarseTownMin_represented_iff_retained seven_shared_minimum.2.1).mpr seven_shared_minimum.2.2⟩

theorem empty_fibers_have_no_extrema (q a : ℕ) :
    ¬ coarseTownFiberMaximumAt ∅ 0 q a ∧ ¬ coarseTownFiberMinimumAt ∅ 0 q a := by
  have he : coarsePrimeWorldFullTown ∅ 0 = ∅ := by decide +kernel
  simp [coarseTownFiberMaximumAt,coarseTownFiberMinimumAt,coarseFullTownPrimeFiber,he]

/-- Even uniform vertical sparsity permits multiple outgoing handoffs. -/
theorem uniform_branching_297 :
    (∀ q ∈ coarseOutsidePrimes (primeScalesUpTo 10) 297,
      coarsePrimeWorldPeriodCount (primeScalesUpTo 10) 297 ≤ q) ∧
    coarseTownMaxHandoff (primeScalesUpTo 10) 297 113 11 ∧
    coarseTownMaxHandoff (primeScalesUpTo 10) 297 113 71 := by
  have hq : 113 ∈ coarseOutsidePrimes (primeScalesUpTo 10) 297 := by decide +kernel
  have hp : 11 ∈ coarseOutsidePrimes (primeScalesUpTo 10) 297 := by decide +kernel
  have hr : 71 ∈ coarseOutsidePrimes (primeScalesUpTo 10) 297 := by decide +kernel
  have hm : coarseTownFiberMaximumAt (primeScalesUpTo 10) 297 113 44 := by
    unfold coarseTownFiberMaximumAt
    rw [coarseFullTownPrimeFiber_eq_divisibility_of_mem hq]
    unfold coarseTownDivisibilityFiber oldSupportSeatFiber
    rw [DkMathTest.LegendreSurvivor297Calibration.town297Seats_eq_production]
    decide +kernel
  have hf11 : 44 ∈ coarseFullTownPrimeFiber (primeScalesUpTo 10) 297 11 ∧
      88 ∈ coarseFullTownPrimeFiber (primeScalesUpTo 10) 297 11 := by
    rw [coarseFullTownPrimeFiber_eq_divisibility_of_mem hp]
    unfold coarseTownDivisibilityFiber oldSupportSeatFiber
    rw [DkMathTest.LegendreSurvivor297Calibration.town297Seats_eq_production]
    decide +kernel
  have hf71 : 44 ∈ coarseFullTownPrimeFiber (primeScalesUpTo 10) 297 71 ∧
      328 ∈ coarseFullTownPrimeFiber (primeScalesUpTo 10) 297 71 := by
    rw [coarseFullTownPrimeFiber_eq_divisibility_of_mem hr]
    unfold coarseTownDivisibilityFiber oldSupportSeatFiber
    rw [DkMathTest.LegendreSurvivor297Calibration.town297Seats_eq_production]
    decide +kernel
  have hA := mem_coarseFullTownActivePrimes.mpr ⟨hq,44,hm.1⟩
  have hpA := mem_coarseFullTownActivePrimes.mpr ⟨hp,44,hf11.1⟩
  have hrA := mem_coarseFullTownActivePrimes.mpr ⟨hr,44,hf71.1⟩
  refine ⟨?_,⟨hA,hpA,44,hm,?_⟩,⟨hA,hrA,44,hm,?_⟩⟩
  · decide +kernel
  · exact mem_coarseTownNonmaximumFiberSeats.mpr ⟨hf11.1,88,hf11.2,by decide⟩
  · exact mem_coarseTownNonmaximumFiberSeats.mpr ⟨hf71.1,328,hf71.2,by decide⟩

end DkMathTest.LegendreHandoffRegression
