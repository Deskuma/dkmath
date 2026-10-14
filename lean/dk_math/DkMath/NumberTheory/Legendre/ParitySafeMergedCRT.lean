/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeCRTSeat

#print "file: DkMath.NumberTheory.Legendre.ParitySafeMergedCRT"

/-!
## Witness unions at actual seats

Family indices can collide. Union their prime labels at each actual offset,
then charge that offset once in the existing support-excess ledger.
-/

namespace DkMath.NumberTheory

/-- The overlap correction for two nonempty local witness sets. -/
theorem union_excess_add_inter_card {α : Type*} [DecidableEq α]
    (P Q : Finset α) (hP : P.Nonempty) (hQ : Q.Nonempty) :
    (P ∪ Q).card - 1 + (P ∩ Q).card = (P.card - 1) + (Q.card - 1) + 1 := by
  have hp := Finset.card_pos.mpr hP
  have hq := Finset.card_pos.mpr hQ
  have hu := Finset.card_le_card (Finset.subset_union_left : P ⊆ P ∪ Q)
  have hc := Finset.card_union_add_card_inter P Q
  omega

/-- At most one common label permits addition of the two local charges, even at a shared seat. -/
theorem add_excess_le_union_excess_of_inter_card_le_one {α : Type*} [DecidableEq α]
    (P Q : Finset α) (hinter : (P ∩ Q).card ≤ 1) :
    (P.card - 1) + (Q.card - 1) ≤ (P ∪ Q).card - 1 := by
  have hp := Finset.card_le_card (Finset.subset_union_left : P ⊆ P ∪ Q)
  have hq := Finset.card_le_card (Finset.subset_union_right : Q ⊆ P ∪ Q)
  have hc := Finset.card_union_add_card_inter P Q
  omega

end DkMath.NumberTheory

namespace DkMath.NumberTheory.Legendre

open scoped BigOperators

/-- All supplied witness labels whose family index lands at this actual offset. -/
def mergedSeatWitness {ι : Type*} (J : Finset ι) (seat : ι → ℕ)
    (Q : ι → Finset ℕ) (r : ℕ) : Finset ℕ :=
  (J.filter (fun j => seat j = r)).biUnion Q

/-- Guaranteed witness excess, counted once per actual image seat. -/
def mergedSeatCharge {ι : Type*} (J : Finset ι) (seat : ι → ℕ)
    (Q : ι → Finset ℕ) : ℕ :=
  ∑ r ∈ J.image seat, ((mergedSeatWitness J seat Q r).card - 1)

theorem mergedSeatWitness_subset_activeSupport {ι : Type*} {n : ℕ}
    (J : Finset ι) (seat : ι → ℕ) (Q : ι → Finset ℕ)
    (hw : ∀ j ∈ J, Q j ⊆ paritySafeActiveSupport n (seat j)) (r : ℕ) :
    mergedSeatWitness J seat Q r ⊆ paritySafeActiveSupport n r := by
  intro q hq
  obtain ⟨j, hj, hqj⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨hj, heq⟩ := Finset.mem_filter.mp hj
  simpa only [heq] using hw j hj hqj

/-- No injectivity hypothesis: shared seats and repeated witness labels are merged first. -/
theorem mergedSeatCharge_le_supportExcess {ι : Type*} {n : ℕ}
    (J : Finset ι) (seat : ι → ℕ) (Q : ι → Finset ℕ)
    (hcandidate : ∀ j ∈ J, seat j ∈ squareAnchorOddPointCoprimeOffsets n)
    (hw : ∀ j ∈ J, Q j ⊆ paritySafeActiveSupport n (seat j)) :
    mergedSeatCharge J seat Q ≤ paritySafeSupportExcess n := by
  apply sum_witness_support_excess_le_supportExcess (J.image seat) (mergedSeatWitness J seat Q)
  · intro r hr
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
    exact hcandidate j hj
  · exact fun r _ => mergedSeatWitness_subset_activeSupport J seat Q hw r

theorem mergedSeatCharge_le_supportExcess_of_modEq {ι : Type*} {n : ℕ}
    (J : Finset ι) (seat : ι → ℕ) (Q : ι → Finset ℕ)
    (hcandidate : ∀ j ∈ J, seat j ∈ squareAnchorOddPointCoprimeOffsets n)
    (hQ : ∀ j ∈ J, Q j ⊆ squareAnchorOddActivePrimes n)
    (hmod : ∀ j ∈ J, ∀ q ∈ Q j, Nat.ModEq q (n ^ 2 + seat j) 0) :
    mergedSeatCharge J seat Q ≤ paritySafeSupportExcess n :=
  mergedSeatCharge_le_supportExcess J seat Q hcandidate
    (fun j hj => activeSupport_contains_of_point_modEq (Q j) (hQ j hj) (hmod j hj))

theorem mergedSeatWitness_eq_of_injOn {ι : Type*} (J : Finset ι) (seat : ι → ℕ)
    (Q : ι → Finset ℕ) (hinj : Set.InjOn seat J) {j : ι} (hj : j ∈ J) :
    mergedSeatWitness J seat Q (seat j) = Q j := by
  ext q
  constructor
  · intro hq
    obtain ⟨k, hk, hqk⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨hk, heq⟩ := Finset.mem_filter.mp hk
    have heqj := hinj hk hj heq
    simpa only [heqj] using hqk
  · intro hq
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, rfl⟩, hq⟩

/-- The old injective charge is exactly the merged charge when actual seats are injective. -/
theorem mergedSeatCharge_eq_indexed_of_injOn {ι : Type*} (J : Finset ι) (seat : ι → ℕ)
    (Q : ι → Finset ℕ) (hinj : Set.InjOn seat J) :
    mergedSeatCharge J seat Q = ∑ j ∈ J, ((Q j).card - 1) := by
  unfold mergedSeatCharge
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mergedSeatWitness_eq_of_injOn J seat Q hinj hj]

theorem uncovered_nonempty_of_merged_certificates {ι : Type*} {n : ℕ}
    (J : Finset ι) (seat : ι → ℕ) (Q : ι → Finset ℕ)
    (hcandidate : ∀ j ∈ J, seat j ∈ squareAnchorOddPointCoprimeOffsets n)
    (hw : ∀ j ∈ J, Q j ⊆ paritySafeActiveSupport n (seat j))
    (hgap : paritySafeTwoPrimeIncidenceUpper n <
      (squareAnchorOddPointCoprimeOffsets n).card + mergedSeatCharge J seat Q) :
    (paritySafeUncoveredCandidates n).Nonempty :=
  paritySafeUncovered_nonempty_of_twoPrimeUpper_lt_candidate_add_excess
    (mergedSeatCharge_le_supportExcess J seat Q hcandidate hw) hgap

theorem prime_squareCell_of_merged_certificates {ι : Type*} {n : ℕ} (hn : 0 < n)
    (J : Finset ι) (seat : ι → ℕ) (Q : ι → Finset ℕ)
    (hcandidate : ∀ j ∈ J, seat j ∈ squareAnchorOddPointCoprimeOffsets n)
    (hw : ∀ j ∈ J, Q j ⊆ paritySafeActiveSupport n (seat j))
    (hgap : paritySafeTwoPrimeIncidenceUpper n <
      (squareAnchorOddPointCoprimeOffsets n).card + mergedSeatCharge J seat Q) :
    ∃ p, Nat.Prime p ∧ SquareCell n p :=
  exists_prime_squareCell_of_paritySafeUncoveredCandidates_nonempty hn
    (uncovered_nonempty_of_merged_certificates J seat Q hcandidate hw hgap)

/-- Two fixed witness families can add their charges if shared seats have at most one common label. -/
theorem two_family_charge_le_supportExcess {n : ℕ} (R S P Q : Finset ℕ)
    (hR : R ⊆ squareAnchorOddPointCoprimeOffsets n)
    (hS : S ⊆ squareAnchorOddPointCoprimeOffsets n)
    (hP : ∀ r ∈ R, P ⊆ paritySafeActiveSupport n r)
    (hQ : ∀ r ∈ S, Q ⊆ paritySafeActiveSupport n r)
    (hinter : (P ∩ Q).card ≤ 1) :
    R.card * (P.card - 1) + S.card * (Q.card - 1) ≤ paritySafeSupportExcess n := by
  classical
  let cost := fun r => (if r ∈ R then P.card - 1 else 0) + (if r ∈ S then Q.card - 1 else 0)
  have hcost : ∀ r ∈ R ∪ S, cost r ≤ (paritySafeActiveSupport n r).card - 1 := by
    intro r _
    by_cases hr : r ∈ R <;> by_cases hs : r ∈ S
    · have hu := Finset.union_subset (hP r hr) (hQ r hs)
      simpa [cost, hr, hs] using
        (DkMath.NumberTheory.add_excess_le_union_excess_of_inter_card_le_one P Q hinter).trans
          (Nat.sub_le_sub_right (Finset.card_le_card hu) 1)
    · simpa [cost, hr, hs] using Nat.sub_le_sub_right (Finset.card_le_card (hP r hr)) 1
    · simpa [cost, hr, hs] using Nat.sub_le_sub_right (Finset.card_le_card (hQ r hs)) 1
    · simp [cost, hr, hs]
  have h := sum_local_cost_le_supportExcess (R ∪ S) cost (Finset.union_subset hR hS) hcost
  have hRR : (R ∪ S) ∩ R = R := Finset.inter_eq_right.mpr Finset.subset_union_left
  have hSS : (R ∪ S) ∩ S = S := Finset.inter_eq_right.mpr Finset.subset_union_right
  simpa [cost, Finset.sum_add_distrib, Finset.sum_ite_mem, hRR, hSS] using h

end DkMath.NumberTheory.Legendre
