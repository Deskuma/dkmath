/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.Goldbach.BalancedSignedCRTParityTail
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.Goldbach.BalancedSignedCRTMargin"

/-!
# Exact signed parity margin and maximal anchor window

This module packages the finite CGE-011 ledger as an exact nonnegative margin
and transports it across balanced windows in a fixed finite prime world.  All
endpoint statements remain conditional on the explicit finite anchor.
-/

namespace DkMath.NumberTheory

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open scoped BigOperators

/-- The raw finite slack of the exact signed parity budget. -/
def goldbachSignedParityMargin (n w : ℕ) (S : Finset ℕ) : ℕ :=
  (goldbachBalancedOffsets n w).card +
      goldbachSignedEvenTailCRTSum n w S -
    (goldbachSignedSingleCRTSum n w S +
      goldbachSignedOddTailCRTSum n w S)

theorem goldbachSignedParityMargin_eq_survivors_card
    {n w P : ℕ} {S : Finset ℕ}
    (hn : 2 ≤ n) (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P)
    (hanchor : P < n - w) :
    goldbachSignedParityMargin n w S =
      (goldbachWindowSurvivors n w S).card := by
  have hsingle := goldbachSignedSingleCRTSum_eq_windowIncidence
    (n := n) (w := w) (P := P) (S := S) hn hS hbound hanchor
  have heven := goldbachSignedEvenTailCRTSum_eq_overlapExcess_add_oddTailCRT
    (n := n) (w := w) (P := P) (S := S) hn hS hbound hanchor
  have hconservation := goldbachWindowIncidenceConservation n w S
  unfold goldbachSignedParityMargin
  rw [hsingle, heven]
  omega

theorem goldbachSignedParityMargin_pos_iff_survivors_nonempty
    {n w P : ℕ} {S : Finset ℕ}
    (hn : 2 ≤ n) (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P)
    (hanchor : P < n - w) :
    0 < goldbachSignedParityMargin n w S ↔
      (goldbachWindowSurvivors n w S).Nonempty := by
  rw [goldbachSignedParityMargin_eq_survivors_card hn hS hbound hanchor]
  exact Finset.card_pos

theorem goldbachWindowSurvivors_subset_of_window_le
    {n w₁ w₂ : ℕ} {S : Finset ℕ} (hw : w₁ ≤ w₂) :
    goldbachWindowSurvivors n w₁ S ⊆ goldbachWindowSurvivors n w₂ S := by
  intro t ht
  have ht' := mem_goldbachWindowSurvivors.mp ht
  have htw := mem_goldbachBalancedOffsets.mp ht'.1
  apply mem_goldbachWindowSurvivors.mpr
  exact ⟨mem_goldbachBalancedOffsets.mpr
    ⟨htw.1, htw.2.trans hw⟩, ht'.2⟩

theorem goldbachWindowSurvivors_card_mono_window
    {n w₁ w₂ : ℕ} {S : Finset ℕ} (hw : w₁ ≤ w₂) :
    (goldbachWindowSurvivors n w₁ S).card ≤
      (goldbachWindowSurvivors n w₂ S).card := by
  exact Finset.card_le_card (goldbachWindowSurvivors_subset_of_window_le hw)

theorem goldbachSignedParityMargin_mono_window
    {n P w₁ w₂ : ℕ} {S : Finset ℕ}
    (hn : 2 ≤ n) (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P)
    (hw : w₁ ≤ w₂) (hanchor₂ : P < n - w₂) :
    goldbachSignedParityMargin n w₁ S ≤
      goldbachSignedParityMargin n w₂ S := by
  have hanchor₁ : P < n - w₁ := by omega
  rw [goldbachSignedParityMargin_eq_survivors_card hn hS hbound hanchor₁,
    goldbachSignedParityMargin_eq_survivors_card hn hS hbound hanchor₂]
  exact goldbachWindowSurvivors_card_mono_window hw

/-- The largest natural balanced window satisfying the two anchor bounds. -/
def goldbachMaxAnchorWindow (n P : ℕ) : ℕ :=
  min (n - (P + 1)) (squareBody P - n)

theorem goldbachMaxAnchorWindow_le_n
    {n P : ℕ} (hP : P < n) (hbody : n ≤ squareBody P) :
    goldbachMaxAnchorWindow n P ≤ n := by
  unfold goldbachMaxAnchorWindow
  omega

theorem goldbachMaxAnchorWindow_safe
    {n P : ℕ} (hP : P < n) (hbody : n ≤ squareBody P) :
    let wMax := goldbachMaxAnchorWindow n P
    wMax ≤ n ∧ P < n - wMax ∧ n + wMax ≤ squareBody P := by
  dsimp
  unfold goldbachMaxAnchorWindow
  omega

theorem goldbachMaxAnchorWindow_maximal
    {n P w : ℕ}
    (hanchor : P < n - w) (hhorizon : n + w ≤ squareBody P) :
    w ≤ goldbachMaxAnchorWindow n P := by
  unfold goldbachMaxAnchorWindow
  omega

theorem goldbachSignedParityMargin_le_maxAnchorWindow
    {n P w : ℕ} {S : Finset ℕ}
    (hn : 2 ≤ n) (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P)
    (hP : P < n) (hbody : n ≤ squareBody P)
    (hanchor : P < n - w) (hhorizon : n + w ≤ squareBody P) :
    goldbachSignedParityMargin n w S ≤
      goldbachSignedParityMargin n (goldbachMaxAnchorWindow n P) S := by
  apply goldbachSignedParityMargin_mono_window hn hS hbound
    (goldbachMaxAnchorWindow_maximal hanchor hhorizon)
  · exact (goldbachMaxAnchorWindow_safe hP hbody).2.1

theorem goldbachSignedParityMargin_exists_admissible_iff_max_positive
    {n P : ℕ} {S : Finset ℕ}
    (hn : 2 ≤ n) (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P)
    (hP : P < n) (hbody : n ≤ squareBody P) :
    (∃ w, P < n - w ∧ n + w ≤ squareBody P ∧
      0 < goldbachSignedParityMargin n w S) ↔
      0 < goldbachSignedParityMargin n (goldbachMaxAnchorWindow n P) S := by
  constructor
  · rintro ⟨w, hanchor, hhorizon, hpos⟩
    have hle := goldbachSignedParityMargin_le_maxAnchorWindow
      hn hS hbound hP hbody hanchor hhorizon
    exact lt_of_lt_of_le hpos hle
  · intro hpos
    refine ⟨goldbachMaxAnchorWindow n P, ?_, ?_, hpos⟩
    · exact (goldbachMaxAnchorWindow_safe hP hbody).2.1
    · exact (goldbachMaxAnchorWindow_safe hP hbody).2.2

theorem goldbachPairAt_of_maxAnchorWindow_margin_pos
    {n P : ℕ} (hn : 2 ≤ n) (hP : P < n) (hbody : n ≤ squareBody P)
    (hpos : 0 < goldbachSignedParityMargin n (goldbachMaxAnchorWindow n P)
      (primeScalesUpTo P)) :
    GoldbachPairAt n := by
  have hsafe := goldbachMaxAnchorWindow_safe hP hbody
  have hsurv :
      (goldbachWindowSurvivors n (goldbachMaxAnchorWindow n P)
        (primeScalesUpTo P)).Nonempty :=
    (goldbachSignedParityMargin_pos_iff_survivors_nonempty
      (n := n) (w := goldbachMaxAnchorWindow n P) (P := P)
      (S := primeScalesUpTo P) hn (knownPrimeScales_primeScalesUpTo P)
      (fun {_} hr => (mem_primeScalesUpTo.mp hr).2) hsafe.2.1).mp hpos
  obtain ⟨t, ht⟩ := hsurv
  exact goldbachPairAt_of_goldbachWindowSurvivor hsafe.1
    (mem_goldbachWindowSurvivors.mp ht).1 hsafe.2.1 hsafe.2.2
    (mem_goldbachWindowSurvivors.mp ht).2

end DkMath.NumberTheory
