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

/--
`7` is primitive for `4^3 - 2^3`, while `GN 3 (4 - 2) 2 = 28` is not
squarefree.  This sample separates the local no-lift route from the stronger
global squarefree route.
-/
private theorem primitiveWitness_7_4_2_3 :
    PrimitivePrimeFlowWitness 7 4 2 3 := by
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

/-- Packaged version of the `{7,13}` primitive witness family. -/
private def primitiveWitnessFamilyPack_6_5_3 : PrimitiveWitnessFamily 6 5 3 where
  support := ({7, 13} : Finset ℕ)
  witness := primitiveWitnessFamily_6_5_3

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
  have hNoLift : ¬ 31 ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 5 (2 - 1) 1 := by
    decide
  exact noLift_beam_bounds_local_load
    (hq := primitiveWitness_31_2_1_5)
    (hd := by decide)
    (hd1 := by decide)
    (hab_lt := by decide)
    hNoLift

/-- Squarefree `GN 5 1 1 = 31` is a sufficient condition for the same local load bound. -/
example : diffMass 31 2 1 5 ≤ 1 := by
  have hGN : DkMath.CosmicFormulaBinom.GN 5 (2 - 1) 1 = 31 := by
    decide
  have hG_sq : Squarefree (DkMath.CosmicFormulaBinom.GN 5 (2 - 1) 1) := by
    simpa [hGN] using (show Squarefree 31 from (show Nat.Prime 31 by decide).squarefree)
  exact squarefree_beam_bounds_local_load_local
    (hq := primitiveWitness_31_2_1_5)
    (hd := by decide)
    (hd1 := by decide)
    (hab_lt := by decide)
    hG_sq

/-- Compatibility sample for the older squarefree-beam API. -/
example : diffMass 31 2 1 5 ≤ 1 := by
  have hGN : DkMath.CosmicFormulaBinom.GN 5 (2 - 1) 1 = 31 := by
    decide
  have hG_sq : Squarefree (DkMath.CosmicFormulaBinom.GN 5 (2 - 1) 1) := by
    simpa [hGN] using (show Squarefree 31 from (show Nat.Prime 31 by decide).squarefree)
  exact squarefree_beam_bounds_local_load
    (hd_prime := by decide)
    (_hd_ge := by decide)
    (hab_lt := by decide)
    (_hb := by decide)
    (_hab := by decide)
    (_hpnd := by decide)
    (hq := primitiveWitness_31_2_1_5)
    hG_sq

/--
The local no-lift route can apply even when the full beam factor is not
squarefree: `GN 3 (4 - 2) 2 = 28 = 2^2 * 7`, but `7^2` does not divide it.
-/
example : diffMass 7 4 2 3 ≤ 1 := by
  have hGN_not_sq : ¬ Squarefree (DkMath.CosmicFormulaBinom.GN 3 (4 - 2) 2) := by
    decide
  have hNoLift : ¬ 7 ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 3 (4 - 2) 2 := by
    decide
  exact noLift_beam_bounds_local_load
    (hq := primitiveWitness_7_4_2_3)
    (hd := by decide)
    (hd1 := by decide)
    (hab_lt := by decide)
    hNoLift

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

/-- The packaged family exposes the same prime-channel family API. -/
example :
    Nat.Prime 7 ∧ 7 ∣ 6 ^ 3 - 5 ^ 3 := by
  exact PrimitiveWitnessFamily.primeChannelFamily
    primitiveWitnessFamilyPack_6_5_3
    7
    (by simp [primitiveWitnessFamilyPack_6_5_3])

/-- The packaged family also exposes the support-mass lower bound directly. -/
example :
    primitiveWitnessFamilyPack_6_5_3.support.prod id ≤
      DkMath.ABC.supportMass (6 ^ 3 - 5 ^ 3) := by
  exact PrimitiveWitnessFamily.supportMassLowerBound
    primitiveWitnessFamilyPack_6_5_3
    (by decide)

end DkMath.ABC.ValuationFlowBridgeExamples
