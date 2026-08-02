/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.FiniteClosurePermutation
import Mathlib.Tactic

#print "file: DkMath.RH.Weave.Control.IndexShiftAudit"

namespace DkMath.RH.Weave.Control

open DkMath.RH.CFBRCProjection

/--
The first arm used by the historical 3D-B spiral experiment.

The explicit `first` and `last` coordinates make the two endpoint indexing
mistakes visible in the type of the construction.
-/
noncomputable def historicalSpiralA
    (first last : ℂ) (middle : List ℂ) : List ℂ :=
  first :: (middle ++ [last])

/--
The steps actually traversed by the historical second arm.

The original code formed the negated reverse copy but iterated over `vec2[:-1]`.
For `first :: middle ++ [last]`, the traversed steps are therefore
`-last`, followed by the negated reverse of `middle`; the final `-first` step is
missing.
-/
noncomputable def historicalSpiralBSteps
    (_first last : ℂ) (middle : List ℂ) : List ℂ :=
  (last :: middle.reverse).map fun z => -z

/-- Endpoint of the first historical spiral arm. -/
theorem historicalSpiralA_endpoint
    (first last : ℂ) (middle : List ℂ) :
    listEndpoint (historicalSpiralA first last middle) =
      first + listEndpoint middle + last := by
  unfold historicalSpiralA listEndpoint
  simp only [List.sum_cons, List.sum_append]
  simp
  abel

/-- Endpoint displacement contributed by the truncated reverse-negated arm. -/
theorem historicalSpiralBSteps_endpoint
    (first last : ℂ) (middle : List ℂ) :
    listEndpoint (historicalSpiralBSteps first last middle) =
      -(last + listEndpoint middle) := by
  unfold historicalSpiralBSteps
  rw [listEndpoint_map_neg]
  unfold listEndpoint
  simp only [List.sum_cons, List.sum_reverse]

/--
Final endpoint produced by the historical 3D-B indexing pattern.

The code started the second arm at `endpoint(A) + last` and then traversed every
negated reverse step except `-first`.
-/
noncomputable def historicalShiftedEndpoint
    (first last : ℂ) (middle : List ℂ) : ℂ :=
  listEndpoint (historicalSpiralA first last middle) + last +
    listEndpoint (historicalSpiralBSteps first last middle)

/--
The historical indexing pattern ends at `first + last`, not at the origin.

This algebraically records both mistakes in the old plotting code:

1. the second arm starts one extra `last` vector beyond the first endpoint;
2. the final `-first` reverse step is omitted.
-/
theorem historicalShiftedEndpoint_eq_first_add_last
    (first last : ℂ) (middle : List ℂ) :
    historicalShiftedEndpoint first last middle = first + last := by
  unfold historicalShiftedEndpoint
  rw [historicalSpiralA_endpoint, historicalSpiralBSteps_endpoint]
  abel

/-- The historical path is not closed whenever its exposed endpoint residue is nonzero. -/
theorem historicalShiftedEndpoint_ne_zero
    {first last : ℂ} (middle : List ℂ)
    (h : first + last ≠ 0) :
    historicalShiftedEndpoint first last middle ≠ 0 := by
  rw [historicalShiftedEndpoint_eq_first_add_last]
  exact h

/--
By contrast, the corrected full reverse-negated copy is a forced closure for
this path, independently of the vector values.
-/
theorem correctedHistoricalSpiral_forcedClosure
    (first last : ℂ) (middle : List ℂ) :
    listEndpoint
      (forcedReverseClosure (historicalSpiralA first last middle)) = 0 := by
  exact forcedReverseClosure_endpoint_eq_zero _

end DkMath.RH.Weave.Control
