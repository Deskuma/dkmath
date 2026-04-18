/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Tactic.IntervalCases
import DkMath.ABC.ValuationFlowBridge
import DkMath.NumberTheory.PrimitiveBeamExamples

#print "file: DkMath.ABC.ValuationFlowBridgeExamples"

namespace DkMath.ABC.ValuationFlowBridgeExamples

open DkMath.ABC
open DkMath.NumberTheory.ValuationFlow

/--
`31` is a primitive prime for `2^5 - 1`, so it is the smallest clean bridge
example for the primitive valuation-flow API.
-/
private theorem primitiveWitness_31_2_1_5 :
    PrimitivePrimeFlowWitness 31 2 1 5 := by
  refine ⟨by decide, by decide, ?_⟩
  intro k hk_pos hk_lt
  interval_cases k <;> decide

/-- Primitive primes give zero boundary load. -/
example : boundaryMass 31 2 1 = 0 := by
  exact primitive_prime_gives_zero_boundary_load primitiveWitness_31_2_1_5 (by decide)

/-- Primitive primes transfer diff load to the beam factor. -/
example : diffMass 31 2 1 5 = beamMass 31 2 1 5 := by
  exact primitive_prime_transfers_diff_load_to_beam
    primitiveWitness_31_2_1_5
    (by decide)
    (by decide)
    (by decide)

/-- The squarefree beam sample `GN 5 1 1 = 31` yields local load at most `1`. -/
example : diffMass 31 2 1 5 ≤ 1 := by
  have hGN : DkMath.CosmicFormulaBinom.GN 5 (2 - 1) 1 = 31 := by
    decide
  have hG_sq : Squarefree (DkMath.CosmicFormulaBinom.GN 5 (2 - 1) 1) := by
    simpa [hGN] using (show Squarefree 31 from (show Nat.Prime 31 by decide).squarefree)
  exact squarefree_beam_bounds_local_load
    (hd_prime := by decide)
    (hd_ge := by decide)
    (hab_lt := by decide)
    (hb := by decide)
    (hab := by decide)
    (hpnd := by decide)
    (hq := primitiveWitness_31_2_1_5)
    hG_sq

end DkMath.ABC.ValuationFlowBridgeExamples
