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

/-- The channel-product alias carries the same public lower bound. -/
example :
    primitiveWitnessFamilyPack_8_1_1.channelProduct ≤
      supportMass (8 ^ 1 - 1 ^ 1) := by
  exact PrimitiveWitnessFamily.channelProduct_le_supportMass
    primitiveWitnessFamilyPack_8_1_1
    (by decide)

end DkMath.ABC.BridgeExamples
