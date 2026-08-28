/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOffsetFreshPrimeFirstHitTransport
import Mathlib.Tactic

/-!
# Fresh-prime transport at a successor-pair minimizer

This provider-side module combines the successor-pair statistic with the
fresh-prime first-hit transport.  A pair persists when at least one old
minimizing side survives the new prime.  In the tied case, delaying the pair
requires simultaneous deletion of two raw seats, forcing divisibility of the
intrinsic successor increment `2 * n + 1`.

The results are finite reservation statements only.  They do not introduce a
shell-width theorem, a Legendre consumer, a universal coverage bound, or an
analytic claim.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

/-! ## Pair minimizers and persistence -/

/-- An old left first-hit side is a minimizer of its successor pair. -/
def IsLeftPairMinimizer
    (S : Finset ℕ) (n : ℕ)
    (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty) : Prop :=
  squareAnchorFirstPositiveUnreservedOffset S n hS hSne =
    squareAnchorSuccessorPairPositiveFirstHit S n hS hSne

/-- An old right first-hit side is a minimizer of its successor pair. -/
def IsRightPairMinimizer
    (S : Finset ℕ) (n : ℕ)
    (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty) : Prop :=
  squareAnchorFirstPositiveUnreservedOffset S (n + 1) hS hSne =
    squareAnchorSuccessorPairPositiveFirstHit S n hS hSne

/-- Fresh insertion cannot move a successor-pair first hit backwards. -/
theorem squareAnchorSuccessorPairPositiveFirstHit_le_insert_fresh_transport
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n : ℕ) :
    squareAnchorSuccessorPairPositiveFirstHit S n hS hSne ≤
      squareAnchorSuccessorPairPositiveFirstHit (insert q S) n
        (isFinitePrimeBasis_insert_fresh hS hq hqS) (by simp) := by
  exact squareAnchorSuccessorPairPositiveFirstHit_le_insert_fresh
    hS hSne hq hqS n

/-- A successor pair persists exactly when one old minimizing side survives
the fresh-prime insertion. -/
theorem squareAnchorSuccessorPairPositiveFirstHit_insert_fresh_eq_iff
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n : ℕ) :
    squareAnchorSuccessorPairPositiveFirstHit (insert q S) n
        (isFinitePrimeBasis_insert_fresh hS hq hqS) (by simp) =
      squareAnchorSuccessorPairPositiveFirstHit S n hS hSne ↔
    (squareAnchorFirstPositiveUnreservedOffset S n hS hSne =
        squareAnchorSuccessorPairPositiveFirstHit S n hS hSne ∧
      ¬ q ∣ (n ^ 2 + squareAnchorFirstPositiveUnreservedOffset S n hS hSne)) ∨
    (squareAnchorFirstPositiveUnreservedOffset S (n + 1) hS hSne =
        squareAnchorSuccessorPairPositiveFirstHit S n hS hSne ∧
      ¬ q ∣ ((n + 1) ^ 2 +
        squareAnchorFirstPositiveUnreservedOffset S (n + 1) hS hSne)) := by
  let hS' := isFinitePrimeBasis_insert_fresh hS hq hqS
  let hSne' : (insert q S).Nonempty := by simp
  let H0 := squareAnchorFirstPositiveUnreservedOffset S n hS hSne
  let H1 := squareAnchorFirstPositiveUnreservedOffset S (n + 1) hS hSne
  let P := squareAnchorSuccessorPairPositiveFirstHit S n hS hSne
  let N0 := squareAnchorFirstPositiveUnreservedOffset (insert q S) n hS' hSne'
  let N1 := squareAnchorFirstPositiveUnreservedOffset (insert q S) (n + 1) hS' hSne'
  let P' := squareAnchorSuccessorPairPositiveFirstHit (insert q S) n hS' hSne'
  have hmono0 : H0 ≤ N0 := by
    exact squareAnchorFirstPositiveUnreservedOffset_le_insert_fresh
      hS hSne hq hqS n
  have hmono1 : H1 ≤ N1 := by
    exact squareAnchorFirstPositiveUnreservedOffset_le_insert_fresh
      hS hSne hq hqS (n + 1)
  have hpmono : P ≤ P' := by
    exact squareAnchorSuccessorPairPositiveFirstHit_le_insert_fresh
      hS hSne hq hqS n
  constructor
  · intro hEq
    by_cases hOld : H0 ≤ H1
    · have hP0 : P = H0 := min_eq_left hOld
      by_cases hNew : N0 ≤ N1
      · left
        refine ⟨hP0.symm, ?_⟩
        have hN0 : N0 = H0 := by
          have hP' : P' = N0 := min_eq_left hNew
          calc
            N0 = P' := hP'.symm
            _ = P := hEq
            _ = H0 := hP0
        exact (squareAnchorFirstPositiveUnreservedOffset_insert_fresh_eq_iff
          hS hSne hq hqS n).mp hN0
      · right
        have hP' : P' = N1 := min_eq_right (Nat.le_of_not_ge hNew)
        have hN1 : N1 = P := hP'.symm.trans hEq
        have hH1 : H1 = P := by
          apply le_antisymm
          · exact hmono1.trans_eq hN1
          · exact hP0 ▸ hOld
        refine ⟨hH1, ?_⟩
        have hN1old : N1 = H1 := hN1.trans hH1.symm
        exact (squareAnchorFirstPositiveUnreservedOffset_insert_fresh_eq_iff
          hS hSne hq hqS (n + 1)).mp hN1old
    · have hOld' : H1 ≤ H0 := Nat.le_of_not_ge hOld
      have hP1 : P = H1 := min_eq_right hOld'
      by_cases hNew : N0 ≤ N1
      · left
        have hP' : P' = N0 := min_eq_left hNew
        have hN0 : N0 = P := hP'.symm.trans hEq
        have hH0 : H0 = P := by
          apply le_antisymm
          · exact hmono0.trans_eq hN0
          · exact hP1 ▸ hOld'
        refine ⟨hH0, ?_⟩
        have hN0old : N0 = H0 := hN0.trans hH0.symm
        exact (squareAnchorFirstPositiveUnreservedOffset_insert_fresh_eq_iff
          hS hSne hq hqS n).mp hN0old
      · right
        refine ⟨hP1.symm, ?_⟩
        have hP' : P' = N1 := min_eq_right (Nat.le_of_not_ge hNew)
        have hN1 : N1 = H1 := by
          calc
            N1 = P' := hP'.symm
            _ = P := hEq
            _ = H1 := hP1
        exact (squareAnchorFirstPositiveUnreservedOffset_insert_fresh_eq_iff
          hS hSne hq hqS (n + 1)).mp hN1
  · rintro (hleft | hright)
    · have hN0 : N0 = H0 :=
        (squareAnchorFirstPositiveUnreservedOffset_insert_fresh_eq_iff
          hS hSne hq hqS n).mpr hleft.2
      have hP0 : P = H0 := hleft.1.symm
      apply le_antisymm
      · change min N0 N1 ≤ P
        rw [hN0, hP0]
        exact min_le_left _ _
      · exact hpmono
    · have hN1 : N1 = H1 :=
        (squareAnchorFirstPositiveUnreservedOffset_insert_fresh_eq_iff
          hS hSne hq hqS (n + 1)).mpr hright.2
      have hP1 : P = H1 := hright.1.symm
      apply le_antisymm
      · change min N0 N1 ≤ P
        rw [hN1, hP1]
        exact min_le_right _ _
      · exact hpmono

/-- A successor pair is strictly delayed exactly when every old minimizing
side is deleted by the fresh prime. -/
theorem squareAnchorSuccessorPairPositiveFirstHit_insert_fresh_lt_iff
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n : ℕ) :
    squareAnchorSuccessorPairPositiveFirstHit S n hS hSne <
      squareAnchorSuccessorPairPositiveFirstHit (insert q S) n
        (isFinitePrimeBasis_insert_fresh hS hq hqS) (by simp) ↔
    (squareAnchorFirstPositiveUnreservedOffset S n hS hSne =
        squareAnchorSuccessorPairPositiveFirstHit S n hS hSne →
      q ∣ (n ^ 2 + squareAnchorFirstPositiveUnreservedOffset S n hS hSne)) ∧
    (squareAnchorFirstPositiveUnreservedOffset S (n + 1) hS hSne =
        squareAnchorSuccessorPairPositiveFirstHit S n hS hSne →
      q ∣ ((n + 1) ^ 2 +
        squareAnchorFirstPositiveUnreservedOffset S (n + 1) hS hSne)) := by
  have hmono := squareAnchorSuccessorPairPositiveFirstHit_le_insert_fresh
    hS hSne hq hqS n
  constructor
  · intro hlt
    constructor
    · intro hmin
      by_contra hnot
      have hpersist := (squareAnchorSuccessorPairPositiveFirstHit_insert_fresh_eq_iff
        hS hSne hq hqS n).mpr (Or.inl ⟨hmin, hnot⟩)
      omega
    · intro hmin
      by_contra hnot
      have hpersist := (squareAnchorSuccessorPairPositiveFirstHit_insert_fresh_eq_iff
        hS hSne hq hqS n).mpr (Or.inr ⟨hmin, hnot⟩)
      omega
  · rintro ⟨hleft, hright⟩
    have hnotpersist : ¬ squareAnchorSuccessorPairPositiveFirstHit (insert q S) n
        (isFinitePrimeBasis_insert_fresh hS hq hqS) (by simp) =
      squareAnchorSuccessorPairPositiveFirstHit S n hS hSne := by
      intro heq
      rcases (squareAnchorSuccessorPairPositiveFirstHit_insert_fresh_eq_iff
        hS hSne hq hqS n).mp heq with h | h
      · exact h.2 (hleft h.1)
      · exact h.2 (hright h.1)
    exact lt_of_le_of_ne hmono (by
      intro heq
      exact hnotpersist heq.symm)

/-! ## Tied-pair obstruction -/

/-- If an equal-minimum successor pair is delayed, the fresh prime divides
both old minimizing raw seats. -/
theorem freshPrime_dvd_both_tied_pair_seats_of_delay
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n h : ℕ)
    (htie0 : squareAnchorFirstPositiveUnreservedOffset S n hS hSne = h)
    (htie1 : squareAnchorFirstPositiveUnreservedOffset S (n + 1) hS hSne = h)
    (hdelay : squareAnchorSuccessorPairPositiveFirstHit S n hS hSne <
      squareAnchorSuccessorPairPositiveFirstHit (insert q S) n
        (isFinitePrimeBasis_insert_fresh hS hq hqS) (by simp)) :
    q ∣ n ^ 2 + h ∧ q ∣ (n + 1) ^ 2 + h := by
  have hpair : squareAnchorSuccessorPairPositiveFirstHit S n hS hSne = h := by
    unfold squareAnchorSuccessorPairPositiveFirstHit
    rw [htie0, htie1]
    exact min_self h
  have hdual := (squareAnchorSuccessorPairPositiveFirstHit_insert_fresh_lt_iff
    hS hSne hq hqS n).mp hdelay
  constructor
  · have h0 := hdual.1 (htie0.trans hpair.symm)
    simpa only [htie0] using h0
  · have h1 := hdual.2 (htie1.trans hpair.symm)
    simpa only [htie1] using h1

/-- A delayed tied pair forces the fresh prime to divide the successor
increment `2*n+1`. -/
theorem freshPrime_dvd_successor_increment_of_tied_pair_delay
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n h : ℕ)
    (htie0 : squareAnchorFirstPositiveUnreservedOffset S n hS hSne = h)
    (htie1 : squareAnchorFirstPositiveUnreservedOffset S (n + 1) hS hSne = h)
    (hdelay : squareAnchorSuccessorPairPositiveFirstHit S n hS hSne <
      squareAnchorSuccessorPairPositiveFirstHit (insert q S) n
        (isFinitePrimeBasis_insert_fresh hS hq hqS) (by simp)) :
    q ∣ 2 * n + 1 := by
  obtain ⟨h0, h1⟩ := freshPrime_dvd_both_tied_pair_seats_of_delay
    hS hSne hq hqS n h htie0 htie1 hdelay
  have hsub : q ∣ ((n + 1) ^ 2 + h) - (n ^ 2 + h) := Nat.dvd_sub h1 h0
  have hcalc : ((n + 1) ^ 2 + h) - (n ^ 2 + h) = 2 * n + 1 := by
    have hsquare : (n + 1) ^ 2 = n ^ 2 + (2 * n + 1) := by ring
    rw [hsquare]
    omega
  rw [hcalc] at hsub
  exact hsub

/-- If an equal-minimum pair has a fresh prime missing from `2*n+1`, the pair
persists. -/
theorem squareAnchorSuccessorPairPositiveFirstHit_eq_insert_fresh_of_tied_and_increment_not_dvd
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n h : ℕ)
    (htie0 : squareAnchorFirstPositiveUnreservedOffset S n hS hSne = h)
    (htie1 : squareAnchorFirstPositiveUnreservedOffset S (n + 1) hS hSne = h)
    (hqnot : ¬ q ∣ 2 * n + 1) :
    squareAnchorSuccessorPairPositiveFirstHit (insert q S) n
        (isFinitePrimeBasis_insert_fresh hS hq hqS) (by simp) =
      squareAnchorSuccessorPairPositiveFirstHit S n hS hSne := by
  have hpair : squareAnchorSuccessorPairPositiveFirstHit S n hS hSne = h := by
    unfold squareAnchorSuccessorPairPositiveFirstHit
    rw [htie0, htie1]
    exact min_self h
  have hH0 : squareAnchorFirstPositiveUnreservedOffset S n hS hSne =
      squareAnchorSuccessorPairPositiveFirstHit S n hS hSne :=
    htie0.trans hpair.symm
  have hH1 : squareAnchorFirstPositiveUnreservedOffset S (n + 1) hS hSne =
      squareAnchorSuccessorPairPositiveFirstHit S n hS hSne :=
    htie1.trans hpair.symm
  apply (squareAnchorSuccessorPairPositiveFirstHit_insert_fresh_eq_iff
    hS hSne hq hqS n).mpr
  by_cases h0 : q ∣ n ^ 2 + squareAnchorFirstPositiveUnreservedOffset S n hS hSne
  · right
    refine ⟨hH1, ?_⟩
    intro h1
    apply hqnot
    have hsub : q ∣ ((n + 1) ^ 2 + h) - (n ^ 2 + h) :=
      Nat.dvd_sub (by simpa [htie1] using h1) (by simpa [htie0] using h0)
    have hsquare : (n + 1) ^ 2 = n ^ 2 + (2 * n + 1) := by ring
    have hcalc : ((n + 1) ^ 2 + h) - (n ^ 2 + h) = 2 * n + 1 := by
      rw [hsquare]
      omega
    rw [hcalc] at hsub
    exact hsub
  · left
    exact ⟨hH0, h0⟩

/-- A tied pair persists whenever its successor increment is smaller than the
fresh prime. -/
theorem squareAnchorSuccessorPairPositiveFirstHit_eq_insert_fresh_of_tied_and_increment_lt
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n h : ℕ)
    (htie0 : squareAnchorFirstPositiveUnreservedOffset S n hS hSne = h)
    (htie1 : squareAnchorFirstPositiveUnreservedOffset S (n + 1) hS hSne = h)
    (hincrement : 2 * n + 1 < q) :
    squareAnchorSuccessorPairPositiveFirstHit (insert q S) n
        (isFinitePrimeBasis_insert_fresh hS hq hqS) (by simp) =
      squareAnchorSuccessorPairPositiveFirstHit S n hS hSne := by
  apply squareAnchorSuccessorPairPositiveFirstHit_eq_insert_fresh_of_tied_and_increment_not_dvd
    hS hSne hq hqS n h htie0 htie1
  intro hdiv
  exact (Nat.not_lt_of_ge (Nat.le_of_dvd (by omega) hdiv)) hincrement

/-! ## Untied boundary -/

/-- In the untied case, the old successor pair has a unique minimizer. -/
theorem squareAnchorSuccessorPairPositiveFirstHit_unique_minimizer_left
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    {n : ℕ}
    (hleft : squareAnchorFirstPositiveUnreservedOffset S n hS hSne <
      squareAnchorFirstPositiveUnreservedOffset S (n + 1) hS hSne) :
    IsLeftPairMinimizer S n hS hSne ∧ ¬ IsRightPairMinimizer S n hS hSne := by
  unfold IsLeftPairMinimizer IsRightPairMinimizer
  constructor
  · unfold squareAnchorSuccessorPairPositiveFirstHit
    exact (min_eq_left (Nat.le_of_lt hleft)).symm
  · intro hright
    unfold squareAnchorSuccessorPairPositiveFirstHit at hright
    have hle : squareAnchorFirstPositiveUnreservedOffset S (n + 1) hS hSne ≤
        squareAnchorFirstPositiveUnreservedOffset S n hS hSne := by
      calc
        squareAnchorFirstPositiveUnreservedOffset S (n + 1) hS hSne =
            min (squareAnchorFirstPositiveUnreservedOffset S n hS hSne)
              (squareAnchorFirstPositiveUnreservedOffset S (n + 1) hS hSne) := hright
        _ ≤ squareAnchorFirstPositiveUnreservedOffset S n hS hSne := min_le_left _ _
    exact (Nat.not_lt_of_ge hle) hleft

/-! ## Visible symbolic regression -/

/-- A small symbolic regression exercises the tied-pair persistence theorem:
the hypotheses themselves provide equal first hits and a fresh prime missing
from the successor increment. -/
theorem tied_pair_increment_miss_persistence_regression
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n h : ℕ)
    (htie0 : squareAnchorFirstPositiveUnreservedOffset S n hS hSne = h)
    (htie1 : squareAnchorFirstPositiveUnreservedOffset S (n + 1) hS hSne = h)
    (hqnot : ¬ q ∣ 2 * n + 1) :
    squareAnchorSuccessorPairPositiveFirstHit (insert q S) n
        (isFinitePrimeBasis_insert_fresh hS hq hqS) (by simp) =
      squareAnchorSuccessorPairPositiveFirstHit S n hS hSne :=
  squareAnchorSuccessorPairPositiveFirstHit_eq_insert_fresh_of_tied_and_increment_not_dvd
    hS hSne hq hqS n h htie0 htie1 hqnot

end DkMath.NumberTheory.PrimorialUniverse
