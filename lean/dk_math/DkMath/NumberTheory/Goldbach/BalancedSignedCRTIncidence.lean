/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.Goldbach.BalancedSignedCRTExact
import Mathlib.Data.Finset.Sigma
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.Goldbach.BalancedSignedCRTIncidence"

/-!
# The exact single-prime signed CRT incidence layer

The single-prime residue family is the canonical finite set of representatives
of the two forbidden classes modulo one prime.  Its progression lift is
identified exactly with the blocked seats in the balanced window.  This is a
finite incidence identity and a provider interface; it does not assert a
universal survivor inequality or Strong Goldbach.
-/

namespace DkMath.NumberTheory

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open scoped BigOperators

/-! ## Single-prime residue families -/

/-- Canonical representatives of the signed single-prime forbidden classes. -/
def signedSingleResidues (n r : ℕ) : Finset ℕ :=
  (Finset.range r).filter (fun t =>
    (t : ZMod r) ∈ goldbachForbiddenResidues n r)

@[simp] theorem mem_signedSingleResidues {n r t : ℕ} :
    t ∈ signedSingleResidues n r ↔
      t < r ∧ (t : ZMod r) ∈ goldbachForbiddenResidues n r := by
  simp [signedSingleResidues]

private theorem natCast_mod_eq {r t : ℕ} [NeZero r] :
    ((t % r : ℕ) : ZMod r) = (t : ZMod r) := by
  apply (ZMod.natCast_eq_natCast_iff' (t % r) t r).mpr
  simp

/-- The canonical single-prime representatives have exactly the forbidden
residue cardinality when the modulus is prime. -/
theorem signedSingleResidues_card_eq_forbidden
    {n r : ℕ} (hr : Nat.Prime r) :
    (signedSingleResidues n r).card =
      (goldbachForbiddenResidues n r).card := by
  classical
  letI : NeZero r := ⟨Nat.ne_of_gt hr.pos⟩
  refine Finset.card_bij (s := signedSingleResidues n r)
    (t := goldbachForbiddenResidues n r) (fun t _ => (t : ZMod r)) ?_ ?_ ?_
  · intro t ht
    exact (mem_signedSingleResidues.mp ht).2
  · intro t ht s hs heq
    have hmod := (ZMod.natCast_eq_natCast_iff' t s r).mp heq
    have ht' := mem_signedSingleResidues.mp ht
    have hs' := mem_signedSingleResidues.mp hs
    simpa [Nat.mod_eq_of_lt ht'.1, Nat.mod_eq_of_lt hs'.1] using hmod
  · intro x hx
    refine ⟨x.val, ?_, ?_⟩
    · apply mem_signedSingleResidues.mpr
      exact ⟨ZMod.val_lt x, by simpa using hx⟩
    · exact ZMod.natCast_zmod_val x

/-! ## Exact single-prime progression counts -/

/-- The progression lift of the signed single-prime residue family. -/
def goldbachSignedSingleCRTCount (n w r : ℕ) : ℕ :=
  ∑ t₀ ∈ signedSingleResidues n r,
    goldbachProgressionWindowCount (min (n - 2) w) t₀ r

theorem goldbach_signed_single_count_eq_progression_sum
    {n w r : ℕ} (hr : 0 < r) :
    goldbachSignedSingleCRTCount n w r =
      ∑ t₀ ∈ signedSingleResidues n r,
        (goldbachProgressionSeats (min (n - 2) w) t₀ r).card := by
  unfold goldbachSignedSingleCRTCount
  apply Finset.sum_congr rfl
  intro t₀ ht₀
  exact goldbachProgressionWindowCount_eq_card hr

/-- The single-prime CRT progression lift is exactly the blocked-seat set. -/
theorem goldbachSignedSingleCRTCount_eq_windowBlockedSeats_card
    {n w P : ℕ} {S : Finset ℕ}
    (hn : 2 ≤ n) (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P)
    (hanchor : P < n - w) {r : ℕ} (hr : r ∈ S) :
    goldbachSignedSingleCRTCount n w r =
      (goldbachWindowBlockedSeats n w r).card := by
  classical
  letI : NeZero r := ⟨Nat.ne_of_gt (hS hr).pos⟩
  let L : Finset (Σ _ : ℕ, ℕ) :=
    (signedSingleResidues n r).sigma
      (fun t₀ => goldbachProgressionSeats (min (n - 2) w) t₀ r)
  have hL : L.card = (goldbachWindowBlockedSeats n w r).card := by
    apply Nat.le_antisymm
    · apply Finset.card_le_card_of_injOn (s := L)
        (t := goldbachWindowBlockedSeats n w r)
        (fun z : (Σ _ : ℕ, ℕ) => z.2)
      · intro z hz
        change z ∈ (signedSingleResidues n r).sigma
          (fun t₀ => goldbachProgressionSeats (min (n - 2) w) t₀ r) at hz
        have hz' := Finset.mem_sigma.mp hz
        have ht₀ := hz'.1
        have ht := hz'.2
        have hprog := mem_goldbachProgressionSeats_iff_balanced_modEq
          (n := n) (w := w) (t₀ := z.1) (M := r) (t := z.2) hn
          (hS hr).pos (mem_signedSingleResidues.mp ht₀).1
        have hprog' := hprog.mp ht
        have htw := hprog'.1
        have hforbid : (z.2 : ZMod r) ∈ goldbachForbiddenResidues n r := by
          have hmod := natCast_mod_eq (r := r) (t := z.2)
          rw [← hmod, hprog'.2]
          exact (mem_signedSingleResidues.mp ht₀).2
        have hproper : GoldbachProperObstructed n r z.2 := by
          have hs := (goldbach_signed_pair_raw_iff_support hS hbound hanchor
            htw hr).mp hforbid
          exact (mem_goldbachObstructionSupportIn.mp hs).2
        rw [goldbachWindowBlockedSeats_eq_filter_balanced]
        exact Finset.mem_filter.mpr ⟨htw, hproper⟩
      · intro a ha b hb hab
        have ha' := Finset.mem_sigma.mp ha
        have hb' := Finset.mem_sigma.mp hb
        have hpa := (mem_goldbachProgressionSeats_iff_balanced_modEq hn
          (hS hr).pos (mem_signedSingleResidues.mp ha'.1).1).mp ha'.2
        have hpb := (mem_goldbachProgressionSeats_iff_balanced_modEq hn
          (hS hr).pos (mem_signedSingleResidues.mp hb'.1).1).mp hb'.2
        have hsnd : a.2 = b.2 := hab
        apply Sigma.ext
        · calc
            a.1 = a.2 % r := hpa.2.symm
            _ = b.2 % r := by rw [hsnd]
            _ = b.1 := hpb.2
        · simp [hab]
    · apply Finset.card_le_card_of_injOn (s := goldbachWindowBlockedSeats n w r)
        (t := L) (fun t : ℕ => ⟨t % r, t⟩)
      · intro t ht
        have ht' := mem_goldbachWindowBlockedSeats.mp ht
        have htw := ht'.2
        have hforbid : (t : ZMod r) ∈ goldbachForbiddenResidues n r := by
          have hproper :=
            (Finset.mem_filter.mp
              (goldbachWindowBlockedSeats_eq_filter_balanced n w r ▸ ht)).2
          exact (goldbach_obstructed_iff_mem_forbidden
            (reflection_offset_le_center htw)).mp
            (hproper.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))
        dsimp [L]
        change (⟨t % r, t⟩ : (Σ _ : ℕ, ℕ)) ∈
          (signedSingleResidues n r).sigma
            (fun t₀ => goldbachProgressionSeats (min (n - 2) w) t₀ r)
        rw [Finset.mem_sigma]
        constructor
        · exact mem_signedSingleResidues.mpr ⟨Nat.mod_lt t (hS hr).pos,
            by simpa [natCast_mod_eq (r := r) (t := t)] using hforbid⟩
        · exact (mem_goldbachProgressionSeats_iff_balanced_modEq hn
            (hS hr).pos (Nat.mod_lt t (hS hr).pos)).mpr ⟨htw, rfl⟩
      · intro a ha b hb hab
        exact congrArg (fun z : (Σ _ : ℕ, ℕ) => z.2) hab
  calc
    goldbachSignedSingleCRTCount n w r = L.card := by
      unfold goldbachSignedSingleCRTCount L
      rw [Finset.card_sigma]
      apply Finset.sum_congr rfl
      intro t₀ ht₀
      exact goldbachProgressionWindowCount_eq_card (hS hr).pos
    _ = (goldbachWindowBlockedSeats n w r).card := hL

/-! ## Global exact single incidence -/

/-- Sum of the exact single-prime CRT counts over a finite prime world. -/
def goldbachSignedSingleCRTSum (n w : ℕ) (S : Finset ℕ) : ℕ :=
  ∑ r ∈ S, goldbachSignedSingleCRTCount n w r

theorem goldbachSignedSingleCRTSum_eq_windowIncidence
    {n w P : ℕ} {S : Finset ℕ}
    (hn : 2 ≤ n) (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P)
    (hanchor : P < n - w) :
    goldbachSignedSingleCRTSum n w S = goldbachWindowIncidence n w S := by
  unfold goldbachSignedSingleCRTSum goldbachWindowIncidence
  apply Finset.sum_congr rfl
  intro r hr
  exact goldbachSignedSingleCRTCount_eq_windowBlockedSeats_card
    hn hS hbound hanchor hr

/-! ## Provider bridges and the anchor-local wrapper -/

/-- Exact single/pair/triple signed counts feed the existing Pascal provider. -/
theorem goldbachWindowSurvivor_of_exact_signed_crt_budget
    {n w P : ℕ} {S : Finset ℕ}
    (hn : 2 ≤ n) (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P) (hanchor : P < n - w)
    (hbudget : goldbachSignedSingleCRTSum n w S <
      (goldbachBalancedOffsets n w).card +
        (goldbachSignedPairCRTSum n w S - goldbachSignedTripleCRTSum n w S)) :
    (goldbachWindowSurvivors n w S).Nonempty := by
  apply goldbachWindowSurvivor_of_signed_crt_budget_exact
    hn hS hbound hanchor
    (C := goldbachWindowIncidence n w S)
  · exact le_rfl
  · rw [← goldbachSignedSingleCRTSum_eq_windowIncidence hn hS hbound hanchor]
    exact hbudget

/-- An exact single/pair/triple budget closes a fixed target once the
anchor-local prime horizon is supplied. -/
theorem goldbachPairAt_of_exact_signed_crt_budget
    {n w P : ℕ}
    (hn : 2 ≤ n) (hw : w ≤ n) (hanchor : P < n - w)
    (hhorizon : n + w ≤ squareBody P)
    (hbudget : goldbachSignedSingleCRTSum n w (primeScalesUpTo P) <
      (goldbachBalancedOffsets n w).card +
        (goldbachSignedPairCRTSum n w (primeScalesUpTo P) -
          goldbachSignedTripleCRTSum n w (primeScalesUpTo P))) :
    GoldbachPairAt n := by
  have hsurv := goldbachWindowSurvivor_of_exact_signed_crt_budget
    (n := n) (w := w) (P := P) (S := primeScalesUpTo P)
    hn (knownPrimeScales_primeScalesUpTo P)
    (hbound := fun {_} hr => (mem_primeScalesUpTo.mp hr).2)
    hanchor hbudget
  obtain ⟨t, ht⟩ := hsurv
  exact goldbachPairAt_of_goldbachWindowSurvivor hw
    (mem_goldbachWindowSurvivors.mp ht).1 hanchor hhorizon
    (mem_goldbachWindowSurvivors.mp ht).2

end DkMath.NumberTheory
