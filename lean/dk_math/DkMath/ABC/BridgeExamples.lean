/- 
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

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

end DkMath.ABC.BridgeExamples
