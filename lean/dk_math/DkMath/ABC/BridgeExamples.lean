/- 
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Tactic.IntervalCases
import DkMath.ABC.Bridge

#print "file: DkMath.ABC.BridgeExamples"

namespace DkMath.ABC.BridgeExamples

open DkMath.ABC
open DkMath.NumberTheory.ValuationFlow

/-- Public aggregator sample for the support-mass family lower bound. -/
example : ({2, 3} : Finset ℕ).prod id ≤ supportMass 12 := by
  exact supportMass_ge_prod_of_prime_channel_family
    (n := 12)
    (S := ({2, 3} : Finset ℕ))
    (by decide)
    (by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact ⟨by decide, by decide⟩
      · exact ⟨by decide, by decide⟩)

/-- A minimal packaged primitive witness family available through `DkMath.ABC.Bridge`. -/
private def primitiveWitnessFamilyPack_8_1_1 : PrimitiveWitnessFamily 8 1 1 where
  support := ({7} : Finset ℕ)
  witness q hq := by
    have hq7 : q = 7 := by
      simpa only [Finset.mem_singleton] using hq
    subst hq7
    refine ⟨by decide, by decide, ?_⟩
    intro k hk_pos hk_lt
    omega

/-- A two-channel public sample: `6^3 - 5^3 = 91 = 7 * 13`. -/
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

/-- A transport-friendly sample: `14^1 - 7^1 = 7` and `rad 7 ≤ rad (14 * 7)`. -/
private def primitiveWitnessFamilyPack_14_7_1 : PrimitiveWitnessFamily 14 7 1 where
  support := ({7} : Finset ℕ)
  witness q hq := by
    have hq7 : q = 7 := by
      simpa only [Finset.mem_singleton] using hq
    subst hq7
    refine ⟨by decide, by decide, ?_⟩
    intro k hk_pos hk_lt
    omega

/-- The packaged bridge API exposes prime channels through the public aggregator. -/
example : Nat.Prime 7 ∧ 7 ∣ 8 ^ 1 - 1 ^ 1 := by
  exact PrimitiveWitnessFamily.primeChannelFamily
    primitiveWitnessFamilyPack_8_1_1
    7
    (by simp [primitiveWitnessFamilyPack_8_1_1])

/-- The packaged bridge API also exposes the diff support-mass lower bound. -/
example :
    primitiveWitnessFamilyPack_8_1_1.support.prod id ≤
      supportMass (8 ^ 1 - 1 ^ 1) := by
  exact PrimitiveWitnessFamily.supportMassLowerBound
    primitiveWitnessFamilyPack_8_1_1
    (by decide)

/-- The public package API exposes the channel product alias. -/
example : primitiveWitnessFamilyPack_8_1_1.channelProduct = 7 := by
  simp [PrimitiveWitnessFamily.channelProduct, primitiveWitnessFamilyPack_8_1_1]

/-- The public package API also exposes the channel-count alias. -/
example : primitiveWitnessFamilyPack_8_1_1.channelCount = 1 := by
  simp [PrimitiveWitnessFamily.channelCount, primitiveWitnessFamilyPack_8_1_1]

/-- The channel-product alias carries the same public lower bound. -/
example :
    primitiveWitnessFamilyPack_8_1_1.channelProduct ≤
      supportMass (8 ^ 1 - 1 ^ 1) := by
  exact PrimitiveWitnessFamily.channelProduct_le_supportMass
    primitiveWitnessFamilyPack_8_1_1
    (by decide)

/-- Public extraction API: support members are prime diff channels. -/
example :
    Nat.Prime 7 ∧ 7 ∣ 8 ^ 1 - 1 ^ 1 := by
  exact PrimitiveWitnessFamily.mem_support_implies_prime_and_dvd_diff
    primitiveWitnessFamilyPack_8_1_1
    (by simp [primitiveWitnessFamilyPack_8_1_1])

/-- Public extraction API: support members are prime. -/
example : Nat.Prime 7 := by
  exact PrimitiveWitnessFamily.mem_support_implies_prime_channel
    primitiveWitnessFamilyPack_8_1_1
    (by simp [primitiveWitnessFamilyPack_8_1_1])

/-- Public extraction API: support members divide the diff. -/
example : 7 ∣ 8 ^ 1 - 1 ^ 1 := by
  exact PrimitiveWitnessFamily.mem_support_implies_dvd_diff
    primitiveWitnessFamilyPack_8_1_1
    (by simp [primitiveWitnessFamilyPack_8_1_1])

/-- Counting API: channel count forces a lower bound on the channel product. -/
example :
    2 ^ primitiveWitnessFamilyPack_8_1_1.channelCount ≤
      primitiveWitnessFamilyPack_8_1_1.channelProduct := by
  exact PrimitiveWitnessFamily.pow_channelCount_le_channelProduct
    primitiveWitnessFamilyPack_8_1_1

/-- Counting API: channel count also forces a support-mass lower bound. -/
example :
    2 ^ primitiveWitnessFamilyPack_8_1_1.channelCount ≤
      supportMass (8 ^ 1 - 1 ^ 1) := by
  exact PrimitiveWitnessFamily.pow_channelCount_le_supportMass
    primitiveWitnessFamilyPack_8_1_1
    (by decide)

/-- The two-channel sample exposes a nontrivial channel count. -/
example : primitiveWitnessFamilyPack_6_5_3.channelCount = 2 := by
  simp [PrimitiveWitnessFamily.channelCount, primitiveWitnessFamilyPack_6_5_3]

/-- The two-channel sample exposes the expected channel product. -/
example : primitiveWitnessFamilyPack_6_5_3.channelProduct = 7 * 13 := by
  simp [PrimitiveWitnessFamily.channelProduct, primitiveWitnessFamilyPack_6_5_3]

/-- Counting API on the two-channel sample: `2 ^ count ≤ product`. -/
example :
    2 ^ primitiveWitnessFamilyPack_6_5_3.channelCount ≤
      primitiveWitnessFamilyPack_6_5_3.channelProduct := by
  exact PrimitiveWitnessFamily.pow_channelCount_le_channelProduct
    primitiveWitnessFamilyPack_6_5_3

/-- Counting API on the two-channel sample: `2 ^ count ≤ supportMass`. -/
example :
    2 ^ primitiveWitnessFamilyPack_6_5_3.channelCount ≤
      supportMass (6 ^ 3 - 5 ^ 3) := by
  exact PrimitiveWitnessFamily.pow_channelCount_le_supportMass
    primitiveWitnessFamilyPack_6_5_3
    (by decide)

/-- ABC-core-facing alias: the channel product is bounded by the radical. -/
example :
    primitiveWitnessFamilyPack_6_5_3.channelProduct ≤
      ABC.rad (6 ^ 3 - 5 ^ 3) := by
  exact PrimitiveWitnessFamily.channelProduct_le_abc_rad_diff
    primitiveWitnessFamilyPack_6_5_3
    (by decide)

/-- ABC-core-facing alias: the counting spine lands directly in `ABC.rad`. -/
example :
    2 ^ primitiveWitnessFamilyPack_6_5_3.channelCount ≤
      ABC.rad (6 ^ 3 - 5 ^ 3) := by
  exact PrimitiveWitnessFamily.pow_channelCount_le_abc_rad_diff
    primitiveWitnessFamilyPack_6_5_3
    (by decide)

/-- Target rename layer: the diff radical lower bound can be read on a named target. -/
example :
    2 ^ primitiveWitnessFamilyPack_6_5_3.channelCount ≤
      ABC.rad 91 := by
  exact PrimitiveWitnessFamily.primitive_witness_family_gives_abc_rad_target_lower_bound
    primitiveWitnessFamilyPack_6_5_3
    (by decide)
    (by decide)

/--
Quality-input layer: if the target radical transports forward, the count forces
the quality input radical.
-/
example :
    2 ^ primitiveWitnessFamilyPack_14_7_1.channelCount ≤
      ABC.rad (14 * 7) := by
  have hrad7 : ABC.rad 7 = 7 := by
    simpa [ABC.squarefree] using
      (ABC.rad_eq_self_of_squarefree (n := 7) (by decide)
        ((show Nat.Prime 7 by decide).squarefree))
  have htransport7 : 7 ≤ ABC.rad (14 * 7) := by
    have h7dvd : 7 ∣ ABC.rad (14 * 7) := by
      rw [← supportMass_eq_abc_rad]
      exact supportMass_dvd_of_prime_channel
        (n := 14 * 7)
        (p := 7)
        (by decide)
        (by decide)
        (by decide)
    have hpos : 0 < ABC.rad (14 * 7) := by
      rw [← supportMass_eq_abc_rad]
      exact supportMass_pos (14 * 7)
    exact Nat.le_of_dvd hpos h7dvd
  exact PrimitiveWitnessFamily.primitive_channel_count_forces_quality_rad_input
    primitiveWitnessFamilyPack_14_7_1
    (c := 7)
    (htarget := by decide)
    (htransport := by simpa [hrad7] using htransport7)
    (hdiff_ne := by decide)

/-- RatioBound-facing bridge: the `rad` class shrinks by the counting spine. -/
example :
    ((Finset.range (100 + 1)).filter fun n =>
      n ≤ 100 ∧ ABC.rad n = ABC.rad (6 ^ 3 - 5 ^ 3)).card
        ≤ (100 / (2 ^ primitiveWitnessFamilyPack_6_5_3.channelCount)) + 1 := by
  exact PrimitiveWitnessFamily.count_class_with_same_rad_as_diff_le_of_channelCount
    (X := 100)
    primitiveWitnessFamilyPack_6_5_3
    (by decide)

end DkMath.ABC.BridgeExamples
