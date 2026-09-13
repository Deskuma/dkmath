/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/

import DkMath.NumberTheory.Goldbach.BalancedReflection
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.Goldbach.BalancedCapacity"

/-!
# Balanced-window capacity and first-overlap ledger

This module bounds each obstruction wave by the width of a balanced window and
separates repeated obstruction incidences from covered seats.  The resulting
shortfall criteria are provider interfaces; no universal survivor theorem is
asserted.
-/

namespace DkMath.NumberTheory

open DkMath.NumberTheory.Primitive

open scoped BigOperators

/-- Incidence counts restricted blocked seats, once for each prime in `S`. -/
def goldbachWindowIncidence (n w : ℕ) (S : Finset ℕ) : ℕ :=
  ∑ r ∈ S, (goldbachWindowBlockedSeats n w r).card

/-- Window covered seats are bounded by their obstruction incidences. -/
theorem goldbachWindow_covered_le_incidence (n w : ℕ) (S : Finset ℕ) :
    (goldbachWindowCoveredSeats n w S).card ≤ goldbachWindowIncidence n w S := by
  unfold goldbachWindowIncidence
  rw [goldbachWindowCoveredSeats_eq_biUnion]
  exact Finset.card_biUnion_le

/-- A blocked window seat injects into its forbidden residue and quotient. -/
theorem goldbachWindow_blocked_card_le_residue_capacity (n w r : ℕ) :
    (goldbachWindowBlockedSeats n w r).card ≤
      (if r ∣ 2 * n then 1 else 2) * (w / r + 1) := by
  let T := (goldbachForbiddenResidues n r).product (Finset.range (w / r + 1))
  have hcard : (goldbachWindowBlockedSeats n w r).card ≤ T.card := by
    apply Finset.card_le_card_of_injOn (fun t : ℕ => ((t : ZMod r), t / r))
    · intro t ht
      rcases mem_goldbachWindowBlockedSeats.mp ht with ⟨hblocked, hwindow⟩
      rcases Finset.mem_filter.mp hblocked with ⟨hoffset, hobs⟩
      have hb := goldbachOffset_bounds hoffset
      have htw := (mem_goldbachBalancedOffsets.mp hwindow).2
      refine Finset.mem_product.mpr ⟨?_, Finset.mem_range.mpr ?_⟩
      · apply (goldbach_obstructed_iff_mem_forbidden hb.1).mp
        exact hobs.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
      · change t / r < w / r + 1
        exact Nat.lt_succ_of_le (Nat.div_le_div_right htw)
    · intro t _ s _ heq
      have hmod := (ZMod.natCast_eq_natCast_iff' t s r).mp
        (congrArg Prod.fst heq)
      have hdiv : t / r = s / r := congrArg Prod.snd heq
      calc
        t = t % r + r * (t / r) := (Nat.mod_add_div t r).symm
        _ = s % r + r * (s / r) := by rw [hmod, hdiv]
        _ = s := Nat.mod_add_div s r
  simpa [T, Finset.card_product, goldbach_card_forbidden] using hcard

/-- Summing the width-local wave bounds gives a window incidence capacity. -/
theorem goldbachWindow_incidence_le_residue_capacity (n w : ℕ) (S : Finset ℕ) :
    goldbachWindowIncidence n w S ≤
      ∑ r ∈ S, (if r ∣ 2 * n then 1 else 2) * (w / r + 1) := by
  unfold goldbachWindowIncidence
  exact Finset.sum_le_sum
    (fun r hr => goldbachWindow_blocked_card_le_residue_capacity n w r)

/-- Generic obstruction support inside an arbitrary finite prime world. -/
def goldbachObstructionSupportIn (n t : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.filter (fun r => GoldbachProperObstructed n r t)

@[simp] theorem mem_goldbachObstructionSupportIn {n t : ℕ} {S : Finset ℕ} {r : ℕ} :
    r ∈ goldbachObstructionSupportIn n t S ↔
      r ∈ S ∧ GoldbachProperObstructed n r t := by
  simp [goldbachObstructionSupportIn]

/-- Repeated obstruction mass at one window seat, after paying for first cover. -/
def goldbachWindowLocalOverlapExcess (n _w : ℕ) (S : Finset ℕ) (t : ℕ) : ℕ :=
  (goldbachObstructionSupportIn n t S).card - 1

/-- Total repeated-obstruction mass over the balanced window.

This is overlap payment: it counts incidences beyond the first obstruction at
each already-covered seat; it does not remove or negate any obstruction. -/
def goldbachWindowOverlapExcess (n w : ℕ) (S : Finset ℕ) : ℕ :=
  ∑ t ∈ goldbachBalancedOffsets n w,
    goldbachWindowLocalOverlapExcess n w S t

theorem goldbachWindowBlockedSeats_eq_filter_balanced
    (n w r : ℕ) :
    goldbachWindowBlockedSeats n w r =
      (goldbachBalancedOffsets n w).filter (GoldbachProperObstructed n r) := by
  ext t
  simp [goldbachWindowBlockedSeats, goldbachBlockedSeats,
    goldbachBalancedOffsets, goldbachOffsets, and_assoc, and_left_comm,
    and_comm]

private theorem goldbachWindowIncidence_eq_sum_support_cards
    (n w : ℕ) (S : Finset ℕ) :
    goldbachWindowIncidence n w S =
      ∑ t ∈ goldbachBalancedOffsets n w,
        (goldbachObstructionSupportIn n t S).card := by
  unfold goldbachWindowIncidence
  calc
    (∑ r ∈ S, (goldbachWindowBlockedSeats n w r).card) =
        ∑ r ∈ S, ∑ t ∈ goldbachBalancedOffsets n w,
          if GoldbachProperObstructed n r t then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [goldbachWindowBlockedSeats_eq_filter_balanced,
        Finset.card_filter]
    _ = ∑ t ∈ goldbachBalancedOffsets n w, ∑ r ∈ S,
          if GoldbachProperObstructed n r t then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ t ∈ goldbachBalancedOffsets n w,
          (goldbachObstructionSupportIn n t S).card := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [goldbachObstructionSupportIn, Finset.card_filter]

private theorem goldbachWindow_card_covered_eq_sum_support_nonempty
    (n w : ℕ) (S : Finset ℕ) :
    (goldbachWindowCoveredSeats n w S).card =
      ∑ t ∈ goldbachBalancedOffsets n w,
        if (goldbachObstructionSupportIn n t S).Nonempty then 1 else 0 := by
  rw [goldbachWindowCoveredSeats_eq_filter, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hs : (goldbachObstructionSupportIn n t S).Nonempty
  · have hcovered : ¬ GoldbachSurvives n S t := by
      intro hsurv
      obtain ⟨r, hr⟩ := hs
      exact hsurv r (mem_goldbachObstructionSupportIn.mp hr).1
        (mem_goldbachObstructionSupportIn.mp hr).2
    simp [hcovered, hs]
  · have hsurv : GoldbachSurvives n S t := by
      intro r hr ho
      exact hs ⟨r, mem_goldbachObstructionSupportIn.mpr ⟨hr, ho⟩⟩
    simp [hsurv, hs]

private theorem goldbachWindow_support_card_eq_indicator_add_excess
    (n w : ℕ) (S : Finset ℕ) (t : ℕ) :
    (goldbachObstructionSupportIn n t S).card =
      (if (goldbachObstructionSupportIn n t S).Nonempty then 1 else 0) +
        goldbachWindowLocalOverlapExcess n w S t := by
  unfold goldbachWindowLocalOverlapExcess
  by_cases hs : (goldbachObstructionSupportIn n t S).Nonempty
  · have hpos : 0 < (goldbachObstructionSupportIn n t S).card :=
      Finset.card_pos.mpr hs
    rw [if_pos hs]
    change (goldbachObstructionSupportIn n t S).card =
      1 + ((goldbachObstructionSupportIn n t S).card - 1)
    omega
  · have hempty : goldbachObstructionSupportIn n t S = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hempty]

/-- Exact incidence equals covered seats plus repeated-obstruction payment. -/
theorem goldbachWindowIncidence_eq_covered_add_overlapExcess
    (n w : ℕ) (S : Finset ℕ) :
    goldbachWindowIncidence n w S =
      (goldbachWindowCoveredSeats n w S).card +
        goldbachWindowOverlapExcess n w S := by
  rw [goldbachWindowIncidence_eq_sum_support_cards]
  unfold goldbachWindowOverlapExcess
  rw [goldbachWindow_card_covered_eq_sum_support_nonempty]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  exact goldbachWindow_support_card_eq_indicator_add_excess n w S t

/-- Exact survivor/incidence conservation with the overlap payment exposed. -/
theorem goldbachWindowIncidenceConservation (n w : ℕ) (S : Finset ℕ) :
    (goldbachWindowSurvivors n w S).card +
        goldbachWindowIncidence n w S =
      (goldbachBalancedOffsets n w).card +
        goldbachWindowOverlapExcess n w S := by
  have hledger := goldbachWindowIncidence_eq_covered_add_overlapExcess n w S
  have hseats := goldbachWindow_survivors_add_covered n w S
  omega

/-- Window survivor existence in exact incidence normal form. -/
theorem goldbachWindowSurvivors_nonempty_iff_incidence_lt
    (n w : ℕ) (S : Finset ℕ) :
    (goldbachWindowSurvivors n w S).Nonempty ↔
      goldbachWindowIncidence n w S <
        (goldbachBalancedOffsets n w).card +
          goldbachWindowOverlapExcess n w S := by
  rw [← Finset.card_pos]
  have hconservation := goldbachWindowIncidenceConservation n w S
  omega

/-- Supplied incidence and overlap bounds imply a window survivor. -/
theorem goldbachWindowSurvivor_of_incidence_le_of_overlap_le
    {n w : ℕ} {S : Finset ℕ} {C e : ℕ}
    (hincidence : goldbachWindowIncidence n w S ≤ C)
    (hoverlap : e ≤ goldbachWindowOverlapExcess n w S)
    (hbudget : C < (goldbachBalancedOffsets n w).card + e) :
    (goldbachWindowSurvivors n w S).Nonempty := by
  apply (goldbachWindowSurvivors_nonempty_iff_incidence_lt n w S).mpr
  omega

/-- Width-local capacity plus supplied overlap payment yields a survivor. -/
theorem goldbachWindowSurvivor_of_residue_capacity_of_overlap_lower
    {n w : ℕ} {S : Finset ℕ} {e : ℕ}
    (hoverlap : e ≤ goldbachWindowOverlapExcess n w S)
    (hbudget :
      (∑ r ∈ S, (if r ∣ 2 * n then 1 else 2) * (w / r + 1)) <
        (goldbachBalancedOffsets n w).card + e) :
    (goldbachWindowSurvivors n w S).Nonempty := by
  apply goldbachWindowSurvivor_of_incidence_le_of_overlap_le
    (C := ∑ r ∈ S, (if r ∣ 2 * n then 1 else 2) * (w / r + 1))
  · exact goldbachWindow_incidence_le_residue_capacity n w S
  · exact hoverlap
  · exact hbudget

/-- Anchor-local conditional Goldbach closure from capacity and overlap input. -/
theorem goldbachPairAt_of_goldbachWindow_residue_capacity_of_overlap_lower
    {n w P e : ℕ}
    (hw : w ≤ n)
    (hanchor : P < n - w)
    (hhorizon : n + w ≤ squareBody P)
    (hoverlap : e ≤
      goldbachWindowOverlapExcess n w (primeScalesUpTo P))
    (hbudget :
      (∑ r ∈ primeScalesUpTo P,
        (if r ∣ 2 * n then 1 else 2) * (w / r + 1)) <
        (goldbachBalancedOffsets n w).card + e) :
    GoldbachPairAt n := by
  have hsurvivor := goldbachWindowSurvivor_of_residue_capacity_of_overlap_lower
    (S := primeScalesUpTo P) hoverlap hbudget
  obtain ⟨t, ht⟩ := hsurvivor
  exact goldbachPairAt_of_goldbachWindowSurvivor hw
    (mem_goldbachWindowSurvivors.mp ht).1 hanchor hhorizon
    (mem_goldbachWindowSurvivors.mp ht).2

end DkMath.NumberTheory
