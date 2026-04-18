/- 
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Tactic.IntervalCases
import DkMath.ABC.ABC038Bridge

#print "file: DkMath.ABC.ABC038BridgeExamples"

namespace DkMath.ABC.ABC038BridgeExamples

open DkMath.ABC
open DkMath.NumberTheory.ValuationFlow

/-- A two-channel sample reused for the `ABC038` bridge wrapper. -/
private def primitiveWitnessFamilyPack_6_5_3 : PrimitiveWitnessFamily 6 5 3 where
  support := ({7, 13} : Finset ℕ)
  witness q hq := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · refine ⟨by decide, by decide, ?_⟩
      intro k hk_pos hk_lt
      interval_cases k <;> decide
    · refine ⟨by decide, by decide, ?_⟩
      intro k hk_pos hk_lt
      interval_cases k <;> decide

/--
The `ABC038` bridge reads a channel-count tail budget as an ordinary
`TailBound`.
-/
example : ABC.TailBound 1 91 1 91 := by
  have htail_count :
      (ABC.twoTail 91 : ℝ) ≤
        ((2 ^ primitiveWitnessFamilyPack_6_5_3.channelCount : ℕ) : ℝ) ^ (1 : ℝ) := by
    have hsqtail_one : ABC.sqTail 91 = 1 := by
      have hsqf91 : Squarefree 91 := by
        have hsq7 : Squarefree 7 := (show Nat.Prime 7 by decide).squarefree
        have hsq13 : Squarefree 13 := (show Nat.Prime 13 by decide).squarefree
        have hcop : Nat.Coprime 7 13 := by
          decide
        simpa using (Nat.squarefree_mul hcop).2 ⟨hsq7, hsq13⟩
      exact ABC.sqTail_eq_one_of_squarefree (by decide) hsqf91
    have htwoTail_le : (ABC.twoTail 91 : ℝ) ≤ (ABC.sqTail 91 : ℝ) := by
      exact ABC.twoTail_le_sqTail_real 91 (by decide)
    have hcount : primitiveWitnessFamilyPack_6_5_3.channelCount = 2 := by
      simp [PrimitiveWitnessFamily.channelCount, primitiveWitnessFamilyPack_6_5_3]
    calc
      (ABC.twoTail 91 : ℝ) ≤ (ABC.sqTail 91 : ℝ) := htwoTail_le
      _ = 1 := by norm_num [hsqtail_one]
      _ ≤ ((2 ^ primitiveWitnessFamilyPack_6_5_3.channelCount : ℕ) : ℝ) ^ (1 : ℝ) := by
        rw [hcount]
        norm_num
  exact tailBound_of_channelCount_tail_transport
    (F := primitiveWitnessFamilyPack_6_5_3)
    (u := 91)
    (v := 1)
    (htarget := by decide)
    (htransport := by simp)
    (hdiff_ne := by decide)
    (hγ_nonneg := by norm_num)
    htail_count

end DkMath.ABC.ABC038BridgeExamples
