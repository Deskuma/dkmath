/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.NumberTheory.Goldbach.Capacity
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.Goldbach.Overlap"

/-!
# Goldbach obstruction overlap ledger

For each offset, the obstruction support records the small primes producing a
proper obstruction.  Its cardinality contributes one covered seat plus the
remaining overlap excess.  The resulting identities are finite bookkeeping
theorems; they do not assert that every offset is covered or that Goldbach has
an unconditional escape provider.
-/

namespace DkMath.NumberTheory

open scoped BigOperators

/-- Small primes giving a proper obstruction at one fixed offset. -/
def goldbachObstructionSupport (n u : ℕ) : Finset ℕ :=
  (goldbachSmallPrimes n).filter
    (fun r => GoldbachProperObstructed n r u)

@[simp] theorem mem_goldbachObstructionSupport {n u r : ℕ} :
    r ∈ goldbachObstructionSupport n u ↔
      r ∈ goldbachSmallPrimes n ∧ GoldbachProperObstructed n r u := by
  simp [goldbachObstructionSupport]

/-- One seat's repeated obstruction count after paying for its first obstruction. -/
def goldbachLocalOverlapExcess (n u : ℕ) : ℕ :=
  (goldbachObstructionSupport n u).card - 1

/-- Total repeated-obstruction excess over the finite Goldbach offset fiber. -/
def goldbachOverlapExcess (n : ℕ) : ℕ :=
  ∑ u ∈ goldbachOffsets n, goldbachLocalOverlapExcess n u

/-- A seat is covered exactly when its obstruction support is nonempty. -/
theorem goldbach_mem_covered_iff_support_nonempty {n u : ℕ} :
    u ∈ goldbachCoveredSeats n (goldbachSmallPrimes n) ↔
      u ∈ goldbachOffsets n ∧
        (goldbachObstructionSupport n u).Nonempty := by
  rw [goldbachCoveredSeats_eq_filter]
  constructor
  · intro h
    have hmem := Finset.mem_filter.mp h
    refine ⟨hmem.1, ?_⟩
    have hnot : ¬ GoldbachSurvives n (goldbachSmallPrimes n) u := hmem.2
    have hex : ∃ r, r ∈ goldbachSmallPrimes n ∧
        GoldbachProperObstructed n r u := by
      by_contra hnone
      apply hnot
      intro r hr ho
      apply hnone
      exact ⟨r, hr, ho⟩
    obtain ⟨r, hr, ho⟩ := hex
    exact ⟨r, mem_goldbachObstructionSupport.mpr ⟨hr, ho⟩⟩
  · rintro ⟨hu, hs⟩
    apply Finset.mem_filter.mpr
    refine ⟨hu, ?_⟩
    intro hsurv
    obtain ⟨r, hr⟩ := hs
    have hr' : r ∈ goldbachObstructionSupport n u := hr
    exact hsurv r (mem_goldbachObstructionSupport.mp hr').1
      (mem_goldbachObstructionSupport.mp hr').2

/-- Incidence counted from the wave side equals the sum of support cardinalities. -/
theorem goldbachIncidence_eq_sum_support_cards (n : ℕ) :
    goldbachIncidence n (goldbachSmallPrimes n) =
      ∑ u ∈ goldbachOffsets n, (goldbachObstructionSupport n u).card := by
  classical
  unfold goldbachIncidence goldbachBlockedSeats goldbachObstructionSupport
  calc
    (∑ r ∈ goldbachSmallPrimes n,
        ((goldbachOffsets n).filter (GoldbachProperObstructed n r)).card) =
        ∑ r ∈ goldbachSmallPrimes n,
          ∑ u ∈ goldbachOffsets n,
            if GoldbachProperObstructed n r u then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.card_filter]
    _ = ∑ u ∈ goldbachOffsets n,
          ∑ r ∈ goldbachSmallPrimes n,
            if GoldbachProperObstructed n r u then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ u ∈ goldbachOffsets n,
          ((goldbachSmallPrimes n).filter
            (fun r => GoldbachProperObstructed n r u)).card := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.card_filter]

/-- The covered-card count is the sum of one indicator per nonempty support. -/
private theorem goldbach_card_covered_eq_sum_support_nonempty (n : ℕ) :
    (goldbachCoveredSeats n (goldbachSmallPrimes n)).card =
      ∑ u ∈ goldbachOffsets n,
        if (goldbachObstructionSupport n u).Nonempty then 1 else 0 := by
  rw [goldbachCoveredSeats_eq_filter]
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hs : (goldbachObstructionSupport n u).Nonempty
  · have hcovered : ¬ GoldbachSurvives n (goldbachSmallPrimes n) u := by
      intro hsurv
      obtain ⟨r, hr⟩ := hs
      have hr' : r ∈ goldbachObstructionSupport n u := hr
      exact hsurv r (mem_goldbachObstructionSupport.mp hr').1
        (mem_goldbachObstructionSupport.mp hr').2
    simp [hcovered, hs]
  · have hsurv : GoldbachSurvives n (goldbachSmallPrimes n) u := by
      intro r hr ho
      exact hs ⟨r, mem_goldbachObstructionSupport.mpr ⟨hr, ho⟩⟩
    simp [hsurv, hs]

/-- One support of size `k` is one covered seat plus `k-1` repeated excess. -/
private theorem goldbach_support_card_eq_indicator_add_excess (n u : ℕ) :
    (goldbachObstructionSupport n u).card =
      (if (goldbachObstructionSupport n u).Nonempty then 1 else 0) +
        goldbachLocalOverlapExcess n u := by
  unfold goldbachLocalOverlapExcess
  by_cases hs : (goldbachObstructionSupport n u).Nonempty
  · have hpos : 0 < (goldbachObstructionSupport n u).card :=
      Finset.card_pos.mpr hs
    rw [if_pos hs]
    change (goldbachObstructionSupport n u).card =
      1 + ((goldbachObstructionSupport n u).card - 1)
    omega
  · have hempty : goldbachObstructionSupport n u = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hempty]

/-- Exact incidence = covered seats + overlap excess, without a full-cover assumption. -/
theorem goldbachIncidence_eq_covered_add_overlapExcess (n : ℕ) :
    goldbachIncidence n (goldbachSmallPrimes n) =
      (goldbachCoveredSeats n (goldbachSmallPrimes n)).card +
        goldbachOverlapExcess n := by
  rw [goldbachIncidence_eq_sum_support_cards]
  unfold goldbachOverlapExcess
  rw [goldbach_card_covered_eq_sum_support_nonempty]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  exact goldbach_support_card_eq_indicator_add_excess n u

/-- The survivor/incidence conservation law with overlap payment exposed. -/
theorem goldbachIncidenceConservation (n : ℕ) :
    (goldbachSurvivors n (goldbachSmallPrimes n)).card +
        goldbachIncidence n (goldbachSmallPrimes n) =
      (n - 1) + goldbachOverlapExcess n := by
  have hledger := goldbachIncidence_eq_covered_add_overlapExcess n
  have hseats := goldbach_survivors_add_covered n (goldbachSmallPrimes n)
  omega

/-- Goldbach is equivalent to incidence being below offsets plus overlap excess.

This is a reformulation of the fixed-center finite criterion.  The theorem
does not prove the inequality for every center; it only identifies the exact
amount paid by obstruction overlap.
-/
theorem goldbachPairAt_iff_incidence_lt_offsets_add_overlap (n : ℕ) :
    GoldbachPairAt n ↔
      goldbachIncidence n (goldbachSmallPrimes n) <
        (n - 1) + goldbachOverlapExcess n := by
  rw [goldbachPairAt_iff_survivors_nonempty, ← Finset.card_pos]
  have h := goldbachIncidenceConservation n
  omega

end DkMath.NumberTheory
