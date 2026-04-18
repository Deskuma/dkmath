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

/--
`7` and `13` are the two primitive primes for `6^3 - 5^3 = 91`, giving the
smallest clean two-channel primitive-flow example.
-/
private theorem primitiveWitness_7_6_5_3 :
    PrimitivePrimeFlowWitness 7 6 5 3 := by
  refine ⟨by decide, by decide, ?_⟩
  intro k hk_pos hk_lt
  interval_cases k <;> decide

private theorem primitiveWitness_13_6_5_3 :
    PrimitivePrimeFlowWitness 13 6 5 3 := by
  refine ⟨by decide, by decide, ?_⟩
  intro k hk_pos hk_lt
  interval_cases k <;> decide

/-- Finite-family packaging of the `7,13` primitive witness sample. -/
private theorem primitiveWitnessFamily_6_5_3
    (q : ℕ) (hq : q ∈ ({7, 13} : Finset ℕ)) :
    PrimitivePrimeFlowWitness q 6 5 3 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · exact primitiveWitness_7_6_5_3
  · exact primitiveWitness_13_6_5_3

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

/-- Two distinct primitive witnesses give two distinct prime channels on the diff side. -/
example :
    7 ≠ 13 ∧ Nat.Prime 7 ∧ Nat.Prime 13 ∧
      7 ∣ 6 ^ 3 - 5 ^ 3 ∧ 13 ∣ 6 ^ 3 - 5 ^ 3 := by
  exact distinct_primitive_witnesses_give_distinct_prime_channels
    primitiveWitness_7_6_5_3
    primitiveWitness_13_6_5_3
    (by decide)

/-- Two primitive channels force the support-mass lower bound on the diff. -/
example : 7 * 13 ≤ DkMath.ABC.supportMass (6 ^ 3 - 5 ^ 3) := by
  have hdiff_ne : 6 ^ 3 - 5 ^ 3 ≠ 0 := by decide
  exact primitive_channels_force_supportMass_lower_bound
    primitiveWitness_7_6_5_3
    primitiveWitness_13_6_5_3
    (by decide)
    hdiff_ne

/-- The same `7,13` sample lifts directly to the finite-family lower bound. -/
example : ({7, 13} : Finset ℕ).prod id ≤ DkMath.ABC.supportMass (6 ^ 3 - 5 ^ 3) := by
  have hdiff_ne : 6 ^ 3 - 5 ^ 3 ≠ 0 := by decide
  exact primitive_witness_family_force_supportMass_lower_bound
    (S := ({7, 13} : Finset ℕ))
    (a := 6)
    (b := 5)
    (d := 3)
    primitiveWitnessFamily_6_5_3
    hdiff_ne

end DkMath.ABC.ValuationFlowBridgeExamples
