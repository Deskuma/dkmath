/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Goldbach.Capacity
import DkMath.NumberTheory.Goldbach.CrossGapSquareCertification
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.Goldbach.BalancedReflection"

/-!
# Balanced reflection windows

This module restricts the existing finite Goldbach offset fiber to a central
window.  It records exact window bookkeeping and the canonical reflection
projection of a Cross-Gap pair.  The anchor-local prime bridge is conditional
on a window survivor; no universal survivor provider is asserted.
-/

namespace DkMath.NumberTheory

open DkMath.NumberTheory.GoldbachCrossGapExchange
open DkMath.NumberTheory.GoldbachCrossGapEscape
open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic

/-- The offsets in `goldbachOffsets n` lying within distance `w` of the center. -/
def goldbachBalancedOffsets (n w : ℕ) : Finset ℕ :=
  (goldbachOffsets n).filter (fun t => t ≤ w)

@[simp] theorem mem_goldbachBalancedOffsets {n w t : ℕ} :
    t ∈ goldbachBalancedOffsets n w ↔
      t ∈ goldbachOffsets n ∧ t ≤ w := by
  simp [goldbachBalancedOffsets]

/-- The balanced window is a restriction of the complete admissible fiber. -/
theorem goldbachBalancedOffsets_subset (n w : ℕ) :
    goldbachBalancedOffsets n w ⊆ goldbachOffsets n := by
  exact Finset.filter_subset _ _

/-- The filter form of the balanced window is an explicit range intersection. -/
theorem goldbachBalancedOffsets_eq_range (n w : ℕ) :
    goldbachBalancedOffsets n w = Finset.range (min (n - 1) (w + 1)) := by
  ext t
  simp [goldbachBalancedOffsets, goldbachOffsets]

/-- Exact cardinality of the balanced offset window. -/
theorem card_goldbachBalancedOffsets (n w : ℕ) :
    (goldbachBalancedOffsets n w).card = min (n - 1) (w + 1) := by
  rw [goldbachBalancedOffsets_eq_range]
  simp

/-- The lower and upper members of a canonical reflection pair. -/
def reflectionLeft (n t : ℕ) : ℕ := n - t

def reflectionRight (n t : ℕ) : ℕ := n + t

theorem reflection_endpoints_add {n t : ℕ} (ht : t ≤ n) :
    reflectionLeft n t + reflectionRight n t = 2 * n := by
  simp [reflectionLeft, reflectionRight]
  omega

/-- Balanced membership supplies the offset bound needed by reflection arithmetic. -/
theorem reflection_offset_le_center {n w t : ℕ}
    (ht : t ∈ goldbachBalancedOffsets n w) : t ≤ n := by
  exact (goldbachOffset_bounds (mem_goldbachBalancedOffsets.mp ht).1).1

theorem reflectionLeft_ge_sub_of_balanced {n w t : ℕ} (_hw : w ≤ n)
    (ht : t ∈ goldbachBalancedOffsets n w) :
    n - w ≤ reflectionLeft n t := by
  have htw := (mem_goldbachBalancedOffsets.mp ht).2
  simp [reflectionLeft]
  omega

theorem reflectionRight_le_add_of_balanced {n w t : ℕ}
    (ht : t ∈ goldbachBalancedOffsets n w) :
    reflectionRight n t ≤ n + w := by
  have htw := (mem_goldbachBalancedOffsets.mp ht).2
  simp [reflectionRight]
  omega

theorem reflection_pair_in_balanced_window {n w t : ℕ} (_hw : w ≤ n)
    (ht : t ∈ goldbachBalancedOffsets n w) :
    n - w ≤ reflectionLeft n t ∧
      reflectionLeft n t ≤ n + w ∧
      n - w ≤ reflectionRight n t ∧
      reflectionRight n t ≤ n + w := by
  have htw := (mem_goldbachBalancedOffsets.mp ht).2
  have htn := reflection_offset_le_center ht
  constructor <;> simp [reflectionLeft, reflectionRight] <;> omega

/-- The canonical offset of a Cross-Gap pair, independent of its labels. -/
def crossGapReflectionOffset
    (n d₁ x₁ u₁ d₂ x₂ u₂ : ℕ) : ℕ :=
  n - min (crossLeft d₁ x₁ u₁ d₂ x₂ u₂)
    (crossRight d₁ x₁ u₁ d₂ x₂ u₂)

/-- The canonical offset identifies the unordered Cross-Gap endpoints. -/
theorem crossGapReflectionOffset_min_max
    {n d₁ x₁ u₁ d₂ x₂ u₂ : ℕ}
    (hfiber : CrossGapEvenFiberAt n d₁ x₁ u₁ d₂ x₂ u₂) :
    min (crossLeft d₁ x₁ u₁ d₂ x₂ u₂)
        (crossRight d₁ x₁ u₁ d₂ x₂ u₂) =
        n - crossGapReflectionOffset n d₁ x₁ u₁ d₂ x₂ u₂ ∧
      max (crossLeft d₁ x₁ u₁ d₂ x₂ u₂)
        (crossRight d₁ x₁ u₁ d₂ x₂ u₂) =
        n + crossGapReflectionOffset n d₁ x₁ u₁ d₂ x₂ u₂ := by
  let L := crossLeft d₁ x₁ u₁ d₂ x₂ u₂
  let R := crossRight d₁ x₁ u₁ d₂ x₂ u₂
  have hsum : L + R = 2 * n := by
    dsimp [L, R]
    exact (crossLeft_add_crossRight_eq_pairedBig d₁ x₁ u₁ d₂ x₂ u₂).trans
      hfiber.1
  by_cases hLR : L ≤ R
  · have hL : L ≤ n := by omega
    simp [crossGapReflectionOffset, L, R, hLR]
    omega
  · have hRL : R ≤ L := by omega
    have hR : R ≤ n := by omega
    simp [crossGapReflectionOffset, L, R, hRL]
    omega

/-- Reflection endpoints are the sorted Cross-Gap endpoints. -/
theorem crossGapReflectionOffset_endpoints
    {n d₁ x₁ u₁ d₂ x₂ u₂ : ℕ}
    (hfiber : CrossGapEvenFiberAt n d₁ x₁ u₁ d₂ x₂ u₂) :
    reflectionLeft n (crossGapReflectionOffset n d₁ x₁ u₁ d₂ x₂ u₂) =
        min (crossLeft d₁ x₁ u₁ d₂ x₂ u₂)
          (crossRight d₁ x₁ u₁ d₂ x₂ u₂) ∧
      reflectionRight n (crossGapReflectionOffset n d₁ x₁ u₁ d₂ x₂ u₂) =
        max (crossLeft d₁ x₁ u₁ d₂ x₂ u₂)
          (crossRight d₁ x₁ u₁ d₂ x₂ u₂) := by
  have hspec := crossGapReflectionOffset_min_max hfiber
  have hmin : min (crossLeft d₁ x₁ u₁ d₂ x₂ u₂)
      (crossRight d₁ x₁ u₁ d₂ x₂ u₂) ≤ n := by
    have hsum := (crossLeft_add_crossRight_eq_pairedBig
      d₁ x₁ u₁ d₂ x₂ u₂).trans hfiber.1
    omega
  constructor <;> simp [reflectionLeft, reflectionRight] <;> omega

/-- A Cross-Gap even fiber has an admissible canonical reflection offset. -/
theorem crossGapReflectionOffset_mem_goldbachOffsets
    {n d₁ x₁ u₁ d₂ x₂ u₂ : ℕ}
    (hfiber : CrossGapEvenFiberAt n d₁ x₁ u₁ d₂ x₂ u₂) :
    crossGapReflectionOffset n d₁ x₁ u₁ d₂ x₂ u₂ ∈ goldbachOffsets n := by
  have hspec := crossGapReflectionOffset_min_max hfiber
  have hmin : 2 ≤ min (crossLeft d₁ x₁ u₁ d₂ x₂ u₂)
      (crossRight d₁ x₁ u₁ d₂ x₂ u₂) :=
    le_min hfiber.2.1 hfiber.2.2
  simp only [goldbachOffsets, Finset.mem_range]
  omega

theorem crossGapReflectionOffset_mem_goldbachBalancedOffsets
    {n w d₁ x₁ u₁ d₂ x₂ u₂ : ℕ}
    (hfiber : CrossGapEvenFiberAt n d₁ x₁ u₁ d₂ x₂ u₂)
    (hw : crossGapReflectionOffset n d₁ x₁ u₁ d₂ x₂ u₂ ≤ w) :
    crossGapReflectionOffset n d₁ x₁ u₁ d₂ x₂ u₂ ∈
      goldbachBalancedOffsets n w := by
  apply mem_goldbachBalancedOffsets.mpr
  exact ⟨crossGapReflectionOffset_mem_goldbachOffsets hfiber, hw⟩

/-- Obstructions restricted to one balanced window. -/
def goldbachWindowBlockedSeats (n w r : ℕ) : Finset ℕ :=
  goldbachBlockedSeats n r ∩ goldbachBalancedOffsets n w

/-- The existing obstruction cover restricted to one balanced window. -/
def goldbachWindowCoveredSeats (n w : ℕ) (S : Finset ℕ) : Finset ℕ :=
  goldbachCoveredSeats n S ∩ goldbachBalancedOffsets n w

/-- Survivors in a balanced window for an arbitrary finite obstruction world. -/
def goldbachWindowSurvivors (n w : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (goldbachBalancedOffsets n w).filter (GoldbachSurvives n S)

@[simp] theorem mem_goldbachWindowBlockedSeats {n w r t : ℕ} :
    t ∈ goldbachWindowBlockedSeats n w r ↔
      t ∈ goldbachBlockedSeats n r ∧
        t ∈ goldbachBalancedOffsets n w := by
  simp [goldbachWindowBlockedSeats]

@[simp] theorem mem_goldbachWindowCoveredSeats {n w : ℕ} {S : Finset ℕ} {t : ℕ} :
    t ∈ goldbachWindowCoveredSeats n w S ↔
      t ∈ goldbachCoveredSeats n S ∧
        t ∈ goldbachBalancedOffsets n w := by
  simp [goldbachWindowCoveredSeats]

@[simp] theorem mem_goldbachWindowSurvivors {n w : ℕ} {S : Finset ℕ} {t : ℕ} :
    t ∈ goldbachWindowSurvivors n w S ↔
      t ∈ goldbachBalancedOffsets n w ∧ GoldbachSurvives n S t := by
  simp [goldbachWindowSurvivors]

theorem goldbachWindowBlockedSeats_subset (n w r : ℕ) :
    goldbachWindowBlockedSeats n w r ⊆ goldbachBlockedSeats n r := by
  exact Finset.inter_subset_left

theorem goldbachWindowCoveredSeats_subset (n w : ℕ) (S : Finset ℕ) :
    goldbachWindowCoveredSeats n w S ⊆ goldbachCoveredSeats n S := by
  exact Finset.inter_subset_left

/-- The window cover is the bi-union of the restricted per-prime blocks. -/
theorem goldbachWindowCoveredSeats_eq_biUnion (n w : ℕ) (S : Finset ℕ) :
    goldbachWindowCoveredSeats n w S =
      S.biUnion (goldbachWindowBlockedSeats n w) := by
  ext t
  simp [goldbachWindowCoveredSeats, goldbachWindowBlockedSeats,
    goldbachCoveredSeats, goldbachBlockedSeats, and_assoc, and_left_comm,
    and_comm]

/-- The window cover is exactly the balanced seats that do not survive. -/
theorem goldbachWindowCoveredSeats_eq_filter (n w : ℕ) (S : Finset ℕ) :
    goldbachWindowCoveredSeats n w S =
      (goldbachBalancedOffsets n w).filter
        (fun t => ¬ GoldbachSurvives n S t) := by
  ext t
  simp [goldbachWindowCoveredSeats, goldbachCoveredSeats_eq_filter,
    and_left_comm, and_comm]

/-- Exact survivor-plus-cover conservation inside the balanced window. -/
theorem goldbachWindow_survivors_add_covered (n w : ℕ) (S : Finset ℕ) :
    (goldbachWindowSurvivors n w S).card +
        (goldbachWindowCoveredSeats n w S).card =
      (goldbachBalancedOffsets n w).card := by
  rw [goldbachWindowCoveredSeats_eq_filter, goldbachWindowSurvivors]
  exact Finset.card_filter_add_card_filter_not (GoldbachSurvives n S)

/-- A strict window-cover shortfall is exactly window survivor existence. -/
theorem goldbachWindowSurvivors_nonempty_iff_covered_card_lt
    (n w : ℕ) (S : Finset ℕ) :
    (goldbachWindowSurvivors n w S).Nonempty ↔
      (goldbachWindowCoveredSeats n w S).card <
        (goldbachBalancedOffsets n w).card := by
  rw [← Finset.card_pos]
  have hledger := goldbachWindow_survivors_add_covered n w S
  omega

/-- A window survivor supplies the anchor-local support disjointness for the left endpoint. -/
theorem goldbachSurvives_supportDisjoint_left_of_window
    {n w P t : ℕ}
    (hw : w ≤ n)
    (ht : t ∈ goldbachBalancedOffsets n w)
    (hanchor : P < n - w)
    (hsurv : GoldbachSurvives n (primeScalesUpTo P) t) :
    SupportDisjointFrom (primeScalesUpTo P) (reflectionLeft n t) := by
  intro q hq hqd hqmem
  have htw := (mem_goldbachBalancedOffsets.mp ht).2
  have hqle : q ≤ P := (mem_primeScalesUpTo.mp hqmem).2
  have hproper : reflectionLeft n t ≠ q := by
    simp [reflectionLeft]
    have hlow : n - w ≤ n - t := by omega
    omega
  exact hsurv q hqmem (Or.inl ⟨hqd, hproper⟩)

/-- A window survivor supplies the anchor-local support disjointness for the right endpoint. -/
theorem goldbachSurvives_supportDisjoint_right_of_window
    {n w P t : ℕ}
    (hw : w ≤ n)
    (ht : t ∈ goldbachBalancedOffsets n w)
    (hanchor : P < n - w)
    (hsurv : GoldbachSurvives n (primeScalesUpTo P) t) :
    SupportDisjointFrom (primeScalesUpTo P) (reflectionRight n t) := by
  intro q hq hqd hqmem
  have htw := (mem_goldbachBalancedOffsets.mp ht).2
  have hqle : q ≤ P := (mem_primeScalesUpTo.mp hqmem).2
  have hproper : reflectionRight n t ≠ q := by
    simp [reflectionRight]
    omega
  exact hsurv q hqmem (Or.inr ⟨hqd, hproper⟩)

/-- An anchor-local window survivor certifies both reflection endpoints as prime. -/
theorem prime_pair_of_goldbachWindowSurvivor
    {n w P t : ℕ}
    (hw : w ≤ n)
    (ht : t ∈ goldbachBalancedOffsets n w)
    (hanchor : P < n - w)
    (hhorizon : n + w ≤ squareBody P)
    (hsurv : GoldbachSurvives n (primeScalesUpTo P) t) :
    Nat.Prime (reflectionLeft n t) ∧ Nat.Prime (reflectionRight n t) := by
  have htw := (mem_goldbachBalancedOffsets.mp ht).2
  have htlower := reflectionLeft_ge_sub_of_balanced hw ht
  have htn := reflection_offset_le_center ht
  have hleft_upper : reflectionLeft n t ≤ squareBody P := by
    simp [reflectionLeft]
    omega
  have hright_upper : reflectionRight n t ≤ squareBody P := by
    exact (reflectionRight_le_add_of_balanced ht).trans hhorizon
  exact ⟨
    (DkMath.NumberTheory.FixedBigGauge.prime_iff_supportDisjointFrom_in_squareShell
      (by simp [reflectionLeft]; omega) hleft_upper).2
      (goldbachSurvives_supportDisjoint_left_of_window hw ht hanchor hsurv),
    (DkMath.NumberTheory.FixedBigGauge.prime_iff_supportDisjointFrom_in_squareShell
      (by simp [reflectionRight]; omega) hright_upper).2
      (goldbachSurvives_supportDisjoint_right_of_window hw ht hanchor hsurv)⟩

/-- The anchor-local survivor bridge closes one fixed even target. -/
theorem goldbachPairAt_of_goldbachWindowSurvivor
    {n w P t : ℕ}
    (hw : w ≤ n)
    (ht : t ∈ goldbachBalancedOffsets n w)
    (hanchor : P < n - w)
    (hhorizon : n + w ≤ squareBody P)
    (hsurv : GoldbachSurvives n (primeScalesUpTo P) t) :
    GoldbachPairAt n := by
  have hprime := prime_pair_of_goldbachWindowSurvivor
    hw ht hanchor hhorizon hsurv
  exact ⟨reflectionLeft n t, reflectionRight n t, hprime.1, hprime.2,
    reflection_endpoints_add (reflection_offset_le_center ht)⟩

/-- Strict window cover shortfall is the provider interface for the local bridge. -/
theorem goldbachPairAt_of_goldbachWindow_cover_shortfall
    {n w P : ℕ}
    (hw : w ≤ n)
    (hanchor : P < n - w)
    (hhorizon : n + w ≤ squareBody P)
    (hshort :
      (goldbachWindowCoveredSeats n w (primeScalesUpTo P)).card <
        (goldbachBalancedOffsets n w).card) :
    GoldbachPairAt n := by
  have hnonempty :=
    (goldbachWindowSurvivors_nonempty_iff_covered_card_lt n w
      (primeScalesUpTo P)).mpr hshort
  obtain ⟨t, ht⟩ := hnonempty
  exact goldbachPairAt_of_goldbachWindowSurvivor hw
    (mem_goldbachWindowSurvivors.mp ht).1 hanchor hhorizon
    (mem_goldbachWindowSurvivors.mp ht).2

end DkMath.NumberTheory
