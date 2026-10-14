/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeIncidenceUpper

#print "file: DkMath.NumberTheory.Legendre.ParitySafeExcessCertificate"

/-!
## Local certificates for the existing support-excess ledger

Only a finite subset of candidate seats and finite subsets of their actual
active supports are needed. Distinct seats pay additive excess; a repeated
prime at different seats is allowed by the existing incidence semantics.
All providers below are independent of full cover.
-/

namespace DkMath.NumberTheory.Legendre

open scoped BigOperators

/-- A local support lower bound pays its multiplicity beyond the first hit. -/
theorem local_support_excess_ge_of_card_ge {n r k : ℕ}
    (hcard : k + 1 ≤ (paritySafeActiveSupport n r).card) :
    k ≤ (paritySafeActiveSupport n r).card - 1 := by
  omega

/-- Lower costs on a finite subset of distinct candidates embed into the existing excess sum. -/
theorem sum_local_cost_le_supportExcess {n : ℕ} (R : Finset ℕ) (cost : ℕ → ℕ)
    (hR : R ⊆ squareAnchorOddPointCoprimeOffsets n)
    (hcost : ∀ r ∈ R, cost r ≤ (paritySafeActiveSupport n r).card - 1) :
    (∑ r ∈ R, cost r) ≤ paritySafeSupportExcess n := by
  calc
    (∑ r ∈ R, cost r) ≤ ∑ r ∈ R, ((paritySafeActiveSupport n r).card - 1) :=
      Finset.sum_le_sum hcost
    _ ≤ paritySafeSupportExcess n :=
      Finset.sum_le_sum_of_subset_of_nonneg hR (by intros; omega)

/-- Witness prime sets need only be subsets of actual support, not complete factorizations. -/
theorem sum_witness_support_excess_le_supportExcess {n : ℕ}
    (R : Finset ℕ) (witness : ℕ → Finset ℕ)
    (hR : R ⊆ squareAnchorOddPointCoprimeOffsets n)
    (hw : ∀ r ∈ R, witness r ⊆ paritySafeActiveSupport n r) :
    (∑ r ∈ R, ((witness r).card - 1)) ≤ paritySafeSupportExcess n := by
  apply sum_local_cost_le_supportExcess R (fun r => (witness r).card - 1) hR
  intro r hr
  exact Nat.sub_le_sub_right (Finset.card_le_card (hw r hr)) 1

/-- Two distinct certified seats pay their lower excess costs additively. -/
theorem two_seat_support_card_lower_le_supportExcess {n r s k l : ℕ}
    (hr : r ∈ squareAnchorOddPointCoprimeOffsets n)
    (hs : s ∈ squareAnchorOddPointCoprimeOffsets n) (hne : r ≠ s)
    (hkr : k + 1 ≤ (paritySafeActiveSupport n r).card)
    (hls : l + 1 ≤ (paritySafeActiveSupport n s).card) :
    k + l ≤ paritySafeSupportExcess n := by
  let cost := fun x => if x = r then k else l
  have hR : ({r, s} : Finset ℕ) ⊆ squareAnchorOddPointCoprimeOffsets n := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hr
    · have hx' := Finset.mem_singleton.mp hx
      subst x
      exact hs
  have hcost : ∀ x ∈ ({r, s} : Finset ℕ), cost x ≤ (paritySafeActiveSupport n x).card - 1 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · simpa [cost] using local_support_excess_ge_of_card_ge hkr
    · have hx' := Finset.mem_singleton.mp hx
      subst x
      simpa [cost, hne.symm] using local_support_excess_ge_of_card_ge hls
  have h := sum_local_cost_le_supportExcess {r, s} cost hR hcost
  simpa [cost, hne, hne.symm] using h

/-- General deficit consumer for the pairwise incidence cap and independent excess evidence. -/
theorem paritySafeUncovered_card_ge_candidate_add_excess_sub_twoPrimeUpper
    (n e : ℕ) (he : e ≤ paritySafeSupportExcess n) :
    (squareAnchorOddPointCoprimeOffsets n).card + e - paritySafeTwoPrimeIncidenceUpper n ≤
      (paritySafeUncoveredCandidates n).card := by
  have hu := paritySafeIncidenceCount_le_twoPrimeUpper n
  have hc := paritySafeCoveredCandidates_card_add_uncoveredCandidates_card_eq_candidate_card n
  have hb := paritySafeCoveredCandidates_card_add_supportExcess_eq_incidence n
  omega

theorem paritySafeUncovered_nonempty_of_twoPrimeUpper_lt_candidate_add_excess
    {n e : ℕ} (he : e ≤ paritySafeSupportExcess n)
    (hlt : paritySafeTwoPrimeIncidenceUpper n < (squareAnchorOddPointCoprimeOffsets n).card + e) :
    (paritySafeUncoveredCandidates n).Nonempty := by
  apply Finset.card_pos.mp
  have h := paritySafeUncovered_card_ge_candidate_add_excess_sub_twoPrimeUpper n e he
  omega

/-- The hybrid provider verifies only the specified local support witnesses. -/
theorem paritySafeUncovered_nonempty_of_local_witnesses {n : ℕ}
    (R : Finset ℕ) (witness : ℕ → Finset ℕ)
    (hR : R ⊆ squareAnchorOddPointCoprimeOffsets n)
    (hw : ∀ r ∈ R, witness r ⊆ paritySafeActiveSupport n r)
    (hlt : paritySafeTwoPrimeIncidenceUpper n <
      (squareAnchorOddPointCoprimeOffsets n).card + (∑ r ∈ R, ((witness r).card - 1))) :
    (paritySafeUncoveredCandidates n).Nonempty :=
  paritySafeUncovered_nonempty_of_twoPrimeUpper_lt_candidate_add_excess
    (sum_witness_support_excess_le_supportExcess R witness hR hw) hlt

theorem exists_prime_squareCell_of_local_witnesses {n : ℕ} (hn : 0 < n)
    (R : Finset ℕ) (witness : ℕ → Finset ℕ)
    (hR : R ⊆ squareAnchorOddPointCoprimeOffsets n)
    (hw : ∀ r ∈ R, witness r ⊆ paritySafeActiveSupport n r)
    (hlt : paritySafeTwoPrimeIncidenceUpper n <
      (squareAnchorOddPointCoprimeOffsets n).card + (∑ r ∈ R, ((witness r).card - 1))) :
    ∃ p, Nat.Prime p ∧ SquareCell n p :=
  exists_prime_squareCell_of_paritySafeUncoveredCandidates_nonempty hn
    (paritySafeUncovered_nonempty_of_local_witnesses R witness hR hw hlt)

end DkMath.NumberTheory.Legendre
