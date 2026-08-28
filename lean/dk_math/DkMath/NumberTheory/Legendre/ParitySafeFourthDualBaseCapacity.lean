/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeNearFirstPrimeWaveCapacity

#print "file: DkMath.NumberTheory.Legendre.ParitySafeFourthDualBaseCapacity"

/-!
## ParitySafeFourthDualBaseCapacity

PRIM-L064 places the exact fourth-direction branch inside a finite
dual-base universe carrying the existing FourDirectionGate witness.  This
gives the raw Fourth cardinality an explicit gated upper capacity and closes
the corresponding LowCost upper-control estimate.

The construction is only an inclusion and cardinality refinement.  It does
not assert equality with the exact fourth branch, fourth-prime injectivity,
new factorization infrastructure, asymptotic estimates, descent, or a
Legendre/RH conclusion.
-/

namespace DkMath.NumberTheory.Legendre

noncomputable section
local instance classicalDecidableFourth (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-! ### PRIM-L064.1: the gated dual-base upper universe -/

/-- Prime-admissible dual-base pairs carrying a FourDirectionGate witness. -/
noncomputable def paritySafeFourthGateDualBasePairs
    (n : ℕ) : Finset (ℕ × ℕ) :=
  (paritySafeRechargePrimeAdmissibleDualBasePairs n).filter
    (fun bt =>
      ∃ p q,
        ParitySafeRechargeExactPairWitness n bt.1 bt.2 p q ∧
        p ∈ paritySafeFourDirectionGatePrimes n)

@[simp] theorem mem_paritySafeFourthGateDualBasePairs
    {n b t : ℕ} :
    (b, t) ∈ paritySafeFourthGateDualBasePairs n ↔
      (b, t) ∈ paritySafeRechargePrimeAdmissibleDualBasePairs n ∧
      ∃ p q,
        ParitySafeRechargeExactPairWitness n b t p q ∧
        p ∈ paritySafeFourDirectionGatePrimes n := by
  simp [paritySafeFourthGateDualBasePairs]

/-! ### PRIM-L064.2: exact Fourth inclusion -/

/-- Every exact fourth-direction pair lies in the gated upper universe. -/
theorem paritySafeRechargeExactFourthDirectionPairs_subset_fourthGateDualBase
    (n : ℕ) :
    paritySafeRechargeExactFourthDirectionPairs n ⊆
      paritySafeFourthGateDualBasePairs n := by
  intro bt hbt
  have hfourth := mem_paritySafeRechargeExactFourthDirectionPairs.mp hbt
  have hexact := hfourth.1
  rcases mem_paritySafeRechargeExactDualBasePairs.mp hexact with
    ⟨hprime, p, q, hwitness⟩
  apply mem_paritySafeFourthGateDualBasePairs.mpr
  exact ⟨hprime, p, q, hwitness,
    paritySafeRechargeExactFourth_firstPrime_mem_fourDirectionGate hbt hwitness⟩

/-! ### PRIM-L064.3: refinement chain and finite cardinal capacity -/

/-- The gated upper universe is contained in the exact dual-base universe. -/
theorem paritySafeFourthGateDualBasePairs_subset_exactDualBase
    (n : ℕ) :
    paritySafeFourthGateDualBasePairs n ⊆
      paritySafeRechargeExactDualBasePairs n := by
  intro bt hbt
  rcases mem_paritySafeFourthGateDualBasePairs.mp hbt with
    ⟨hprime, p, q, hwitness, _⟩
  exact mem_paritySafeRechargeExactDualBasePairs.mpr
    ⟨hprime, p, q, hwitness⟩

/-- The gated upper universe refines the prime-admissible universe. -/
theorem paritySafeFourthGateDualBasePairs_subset_primeAdmissible
    (n : ℕ) :
    paritySafeFourthGateDualBasePairs n ⊆
      paritySafeRechargePrimeAdmissibleDualBasePairs n := by
  intro bt hbt
  exact (mem_paritySafeFourthGateDualBasePairs.mp hbt).1

/-- Exact Fourth cardinality is bounded by the gated dual-base capacity. -/
theorem paritySafeRechargeExactFourthDirectionPairs_card_le_fourthGateDualBase
    (n : ℕ) :
    (paritySafeRechargeExactFourthDirectionPairs n).card ≤
      (paritySafeFourthGateDualBasePairs n).card := by
  exact Finset.card_le_card
    (paritySafeRechargeExactFourthDirectionPairs_subset_fourthGateDualBase n)

/-- The gated universe is no larger than the prime-admissible universe. -/
theorem paritySafeFourthGateDualBasePairs_card_le_primeAdmissible
    (n : ℕ) :
    (paritySafeFourthGateDualBasePairs n).card ≤
      (paritySafeRechargePrimeAdmissibleDualBasePairs n).card := by
  exact Finset.card_le_card
    (paritySafeFourthGateDualBasePairs_subset_primeAdmissible n)

/-! ### PRIM-L064.4: LowCost capacity closure -/

/-- Finite upper capacity for the three L062 LowCost branches. -/
noncomputable def paritySafeLowCostResidualCapacity (n : ℕ) : ℕ :=
  paritySafeNearFirstPrimeWaveBudget n +
    squareAnchorCoprimePrimeSquareDepthBudget n +
    (paritySafeFourthGateDualBasePairs n).card

/-- LowCost is bounded by Near waves, L018 depth, and gated Fourth. -/
theorem paritySafeLowCostResidualMass_le_nearWaveBudget_add_L018Depth_add_fourthGateDualBase
    (n : ℕ) :
    paritySafeLowCostResidualMass n ≤
      paritySafeNearFirstPrimeWaveBudget n +
      squareAnchorCoprimePrimeSquareDepthBudget n +
      (paritySafeFourthGateDualBasePairs n).card := by
  have hlow := paritySafeLowCostResidualMass_le_nearWaveBudget_add_L018Depth_add_fourth n
  have hfourth := paritySafeRechargeExactFourthDirectionPairs_card_le_fourthGateDualBase n
  omega

/-- The LowCost residual is bounded by the named finite capacity. -/
theorem paritySafeLowCostResidualMass_le_capacity (n : ℕ) :
    paritySafeLowCostResidualMass n ≤ paritySafeLowCostResidualCapacity n := by
  exact paritySafeLowCostResidualMass_le_nearWaveBudget_add_L018Depth_add_fourthGateDualBase n

end
end DkMath.NumberTheory.Legendre
