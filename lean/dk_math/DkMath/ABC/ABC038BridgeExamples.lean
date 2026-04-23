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

/-- A one-channel sample with diff target `7`. -/
private def primitiveWitnessFamilyPack_14_7_1 : PrimitiveWitnessFamily 14 7 1 where
  support := ({7} : Finset ℕ)
  witness q hq := by
    have hq7 : q = 7 := by
      simpa only [Finset.mem_singleton] using hq
    subst hq7
    refine ⟨by decide, by decide, ?_⟩
    intro k hk_pos hk_lt
    omega

private def triple_6_1_7 : ABC.Triple :=
  ABC.Triple.mk 6 1 7 (by decide) (by decide)

private lemma channelCountTailBound_7 :
    (ABC.twoTail 7 : ℝ) ≤
      ((2 ^ primitiveWitnessFamilyPack_14_7_1.channelCount : ℕ) : ℝ) ^ (1 : ℝ) := by
  have hsqtail_one : ABC.sqTail 7 = 1 := by
    exact ABC.sqTail_eq_one_of_squarefree
      (by decide)
      ((show Nat.Prime 7 by decide).squarefree)
  have htwoTail_le : (ABC.twoTail 7 : ℝ) ≤ (ABC.sqTail 7 : ℝ) := by
    exact ABC.twoTail_le_sqTail_real 7 (by decide)
  have hcount : primitiveWitnessFamilyPack_14_7_1.channelCount = 1 := by
    simp [PrimitiveWitnessFamily.channelCount, primitiveWitnessFamilyPack_14_7_1]
  calc
    (ABC.twoTail 7 : ℝ) ≤ (ABC.sqTail 7 : ℝ) := htwoTail_le
    _ = 1 := by norm_num [hsqtail_one]
    _ ≤ ((2 ^ primitiveWitnessFamilyPack_14_7_1.channelCount : ℕ) : ℝ) ^ (1 : ℝ) := by
      rw [hcount]
      norm_num

private lemma targetRadTailBound_7 :
    (ABC.twoTail 7 : ℝ) ≤ (ABC.rad 7 : ℝ) ^ (1 : ℝ) := by
  exact targetRadTailBound_of_channelCount_tail
    (F := primitiveWitnessFamilyPack_14_7_1)
    (htarget := by decide)
    (hdiff_ne := by decide)
    (hγ_nonneg := by norm_num)
    channelCountTailBound_7

private lemma not_bad_6_1_7 :
    ¬ ABC.Bad (0 : ℝ) triple_6_1_7 := by
  unfold triple_6_1_7
  unfold ABC.Bad
  have hlhs :
      ((7).factorization.support.filter fun p => 2 ≤ (7).factorization p).prod id = 1 := by
    simpa [ABC.piSqRad] using
      (ABC.piSqRad_eq_one_of_squarefree
        (n := 7)
        (by decide)
        ((show Nat.Prime 7 by decide).squarefree))
  rw [hlhs]
  norm_num

/--
The `ABC038` bridge reads a channel-count tail budget as an ordinary
`TailBound`.
-/
example :
    (ABC.twoTail 91 : ℝ) ≤ (ABC.rad 91 : ℝ) ^ (1 : ℝ) := by
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
  exact targetRadTailBound_of_channelCount_tail
    (F := primitiveWitnessFamilyPack_6_5_3)
    (htarget := by decide)
    (hdiff_ne := by decide)
    (hγ_nonneg := by norm_num)
    htail_count

/--
The generic route can now be factored through a target-rad tail budget.
-/
example : ABC.TailBound 1 91 1 91 := by
  exact tailBound_of_targetRadTail_transport
    (u := 91)
    (v := 1)
    (htransport := by simp)
    (hγ_nonneg := by norm_num)
    (htail_target := by
      exact targetRadTailBound_of_channelCount_tail
        (F := primitiveWitnessFamilyPack_6_5_3)
        (htarget := by decide)
        (hdiff_ne := by decide)
        (hγ_nonneg := by norm_num)
        (by
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
              norm_num))

/--
The divisibility route supplies the radical transport automatically.
-/
example : ABC.TailBound 1 14 7 7 := by
  exact tailBound_of_channelCount_tail_dvd
    (F := primitiveWitnessFamilyPack_14_7_1)
    (u := 14)
    (v := 7)
    (htarget := by decide)
    (huv_ne := by decide)
    (hcdvd := by decide)
    (hdiff_ne := by decide)
    (hγ_nonneg := by norm_num)
    (by
      have htail_count :
          (ABC.twoTail 7 : ℝ) ≤
            ((2 ^ primitiveWitnessFamilyPack_14_7_1.channelCount : ℕ) : ℝ) ^ (1 : ℝ) := by
        have hsqtail_one : ABC.sqTail 7 = 1 := by
          exact ABC.sqTail_eq_one_of_squarefree
            (by decide)
            ((show Nat.Prime 7 by decide).squarefree)
        have htwoTail_le : (ABC.twoTail 7 : ℝ) ≤ (ABC.sqTail 7 : ℝ) := by
          exact ABC.twoTail_le_sqTail_real 7 (by decide)
        have hcount : primitiveWitnessFamilyPack_14_7_1.channelCount = 1 := by
          simp [PrimitiveWitnessFamily.channelCount, primitiveWitnessFamilyPack_14_7_1]
        calc
          (ABC.twoTail 7 : ℝ) ≤ (ABC.sqTail 7 : ℝ) := htwoTail_le
          _ = 1 := by norm_num [hsqtail_one]
          _ ≤ ((2 ^ primitiveWitnessFamilyPack_14_7_1.channelCount : ℕ) : ℝ) ^ (1 : ℝ) := by
            rw [hcount]
            norm_num
      exact htail_count)

/--
The `rad(abc)` analytic route already yields a concrete quality bound.
-/
example :
    ABC.quality triple_6_1_7 ≤ 2 := by
  have hpi : (ABC.piSqRad 7 : ℝ) ≤ (ABC.rad (6 * 1) : ℝ) ^ (0 : ℝ) := by
    rw [ABC.piSqRad_eq_one_of_squarefree (by decide) ((show Nat.Prime 7 by decide).squarefree),
      Real.rpow_zero]
    norm_num
  have hrad_gt_one : 1 < (ABC.rad (6 * 1 * 7) : ℝ) := by
    have hsqf6 : Squarefree 6 := by
      have hsq2 : Squarefree 2 := (show Nat.Prime 2 by decide).squarefree
      have hsq3 : Squarefree 3 := (show Nat.Prime 3 by decide).squarefree
      have hcop23 : Nat.Coprime 2 3 := by
        decide
      simpa using (Nat.squarefree_mul hcop23).2 ⟨hsq2, hsq3⟩
    have hsqf42 : Squarefree 42 := by
      have hsq7 : Squarefree 7 := (show Nat.Prime 7 by decide).squarefree
      have hcop6_7 : Nat.Coprime 6 7 := by
        decide
      simpa using (Nat.squarefree_mul hcop6_7).2 ⟨hsqf6, hsq7⟩
    have hrad42 : ABC.rad (6 * 1 * 7) = 42 := by
      simpa [ABC.squarefree] using
        (ABC.rad_eq_self_of_squarefree (n := 42) (by decide) hsqf42)
    norm_num [hrad42]
  have hq :
      ABC.quality triple_6_1_7 ≤ 1 + 1 :=
    quality_le_of_pi_targetRadTail_of_radAbc
      (a := 6)
      (b := 1)
      (c := 7)
      (ε := 1)
      (δ := 0)
      (γ := 1)
      (by norm_num)
      (by decide)
      (by decide)
      hpi
      targetRadTailBound_7
      (by norm_num)
      (by norm_num)
      (by norm_num)
      hrad_gt_one
  norm_num at hq
  exact hq

/--
The same concrete sample now lands directly in the `ABC038` convenience
theorem group under `ABC.Chernoff`.
-/
example :
    ABC.quality triple_6_1_7 ≤ 2 := by
  have hrad_gt_one : 1 < (ABC.rad (6 * 1 * 7) : ℝ) := by
    have hsqf6 : Squarefree 6 := by
      have hsq2 : Squarefree 2 := (show Nat.Prime 2 by decide).squarefree
      have hsq3 : Squarefree 3 := (show Nat.Prime 3 by decide).squarefree
      have hcop23 : Nat.Coprime 2 3 := by
        decide
      simpa using (Nat.squarefree_mul hcop23).2 ⟨hsq2, hsq3⟩
    have hsqf42 : Squarefree 42 := by
      have hsq7 : Squarefree 7 := (show Nat.Prime 7 by decide).squarefree
      have hcop6_7 : Nat.Coprime 6 7 := by
        decide
      simpa using (Nat.squarefree_mul hcop6_7).2 ⟨hsqf6, hsq7⟩
    have hrad42 : ABC.rad (6 * 1 * 7) = 42 := by
      simpa [ABC.squarefree] using
        (ABC.rad_eq_self_of_squarefree (n := 42) (by decide) hsqf42)
    norm_num [hrad42]
  have hq :
      ABC.quality triple_6_1_7 ≤ 1 + 1 :=
    ABC.Chernoff.quality_le_of_not_bad_with_channelCount_tail_on_radAbc
      (F := primitiveWitnessFamilyPack_14_7_1)
      (htarget := by decide)
      (hdiff_ne := by decide)
      (hγ_nonneg := by norm_num)
      (huv_sum := triple_6_1_7.hsum)
      (huv_cop := triple_6_1_7.hcop)
      (hε_pos := by norm_num)
      not_bad_6_1_7
      channelCountTailBound_7
      (by norm_num)
      (by norm_num)
      hrad_gt_one
  norm_num at hq
  exact hq

end DkMath.ABC.ABC038BridgeExamples
