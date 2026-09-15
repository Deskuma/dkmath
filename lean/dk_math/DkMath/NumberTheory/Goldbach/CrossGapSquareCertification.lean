/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.FixedBigGauge.SquareCertificate
import DkMath.NumberTheory.Goldbach.CrossGapEscape

#print "file: DkMath.NumberTheory.Goldbach.CrossGapSquareCertification"

/-!
# Cross-Gap square-shell certification

This module connects arbitrary-degree Cross-Gap generators to the existing
degree-two SquareBody certification envelope.  The generator degrees remain
unrestricted, and no survivor-existence theorem is asserted.
-/

namespace DkMath.NumberTheory.GoldbachCrossGapSquareCertification

open DkMath.NumberTheory.GoldbachCrossGapExchange
open DkMath.NumberTheory.GoldbachCrossGapEscape
open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic

/-- The pair-local upper horizon of the two Cross-Gap endpoints. -/
def crossPairHeight (d₁ x₁ u₁ d₂ x₂ u₂ : ℕ) : ℕ :=
  max (crossLeft d₁ x₁ u₁ d₂ x₂ u₂)
    (crossRight d₁ x₁ u₁ d₂ x₂ u₂)

theorem crossLeft_le_crossPairHeight (d₁ x₁ u₁ d₂ x₂ u₂ : ℕ) :
    crossLeft d₁ x₁ u₁ d₂ x₂ u₂ ≤
      crossPairHeight d₁ x₁ u₁ d₂ x₂ u₂ := by
  exact le_max_left _ _

theorem crossRight_le_crossPairHeight (d₁ x₁ u₁ d₂ x₂ u₂ : ℕ) :
    crossRight d₁ x₁ u₁ d₂ x₂ u₂ ≤
      crossPairHeight d₁ x₁ u₁ d₂ x₂ u₂ := by
  exact le_max_right _ _

/-- A Cross-Gap pair lies in one anchored square shell and avoids its old support. -/
def CrossGapSquareCertified
    (P d₁ x₁ u₁ d₂ x₂ u₂ : ℕ) : Prop :=
  P < crossLeft d₁ x₁ u₁ d₂ x₂ u₂ ∧
    crossLeft d₁ x₁ u₁ d₂ x₂ u₂ ≤ squareBody P ∧
    P < crossRight d₁ x₁ u₁ d₂ x₂ u₂ ∧
    crossRight d₁ x₁ u₁ d₂ x₂ u₂ ≤ squareBody P ∧
    SupportDisjointFrom (primeScalesUpTo P)
      (crossLeft d₁ x₁ u₁ d₂ x₂ u₂) ∧
    SupportDisjointFrom (primeScalesUpTo P)
      (crossRight d₁ x₁ u₁ d₂ x₂ u₂)

/-- Square-shell certification proves primality of both Cross-Gap endpoints. -/
theorem prime_pair_of_crossGapSquareCertified
    {P d₁ x₁ u₁ d₂ x₂ u₂ : ℕ}
    (hcert : CrossGapSquareCertified P d₁ x₁ u₁ d₂ x₂ u₂) :
    Nat.Prime (crossLeft d₁ x₁ u₁ d₂ x₂ u₂) ∧
      Nat.Prime (crossRight d₁ x₁ u₁ d₂ x₂ u₂) := by
  rcases hcert with ⟨hleft_lower, hleft_upper, hright_lower, hright_upper,
    hleft_disjoint, hright_disjoint⟩
  exact ⟨
    (DkMath.NumberTheory.FixedBigGauge.prime_iff_supportDisjointFrom_in_squareShell
      hleft_lower hleft_upper).2 hleft_disjoint,
    (DkMath.NumberTheory.FixedBigGauge.prime_iff_supportDisjointFrom_in_squareShell
      hright_lower hright_upper).2 hright_disjoint⟩

/-- A balanced even Cross-Gap pair has both endpoints above `n - w`. -/
theorem crossPair_lower_bounds_of_balanced_window
    {n w d₁ x₁ u₁ d₂ x₂ u₂ : ℕ}
    (hfiber : CrossGapEvenFiberAt n d₁ x₁ u₁ d₂ x₂ u₂)
    (hw : w ≤ n)
    (hleft_window : crossLeft d₁ x₁ u₁ d₂ x₂ u₂ ≤ n + w)
    (hright_window : crossRight d₁ x₁ u₁ d₂ x₂ u₂ ≤ n + w) :
    n - w ≤ crossLeft d₁ x₁ u₁ d₂ x₂ u₂ ∧
      n - w ≤ crossRight d₁ x₁ u₁ d₂ x₂ u₂ := by
  rcases hfiber with ⟨hpaired, hleft, hright⟩
  have htotal :=
    crossLeft_add_crossRight_eq_pairedBig d₁ x₁ u₁ d₂ x₂ u₂
  constructor <;> omega

/-- A balanced pair is transported into one common SquareBody shell. -/
theorem crossPair_in_squareShell_of_balanced_window
    {n w P d₁ x₁ u₁ d₂ x₂ u₂ : ℕ}
    (hfiber : CrossGapEvenFiberAt n d₁ x₁ u₁ d₂ x₂ u₂)
    (hw : w ≤ n)
    (hleft_window : crossLeft d₁ x₁ u₁ d₂ x₂ u₂ ≤ n + w)
    (hright_window : crossRight d₁ x₁ u₁ d₂ x₂ u₂ ≤ n + w)
    (hanchor : P < n - w)
    (hhorizon : n + w ≤ squareBody P) :
    P < crossLeft d₁ x₁ u₁ d₂ x₂ u₂ ∧
      crossLeft d₁ x₁ u₁ d₂ x₂ u₂ ≤ squareBody P ∧
      P < crossRight d₁ x₁ u₁ d₂ x₂ u₂ ∧
      crossRight d₁ x₁ u₁ d₂ x₂ u₂ ≤ squareBody P := by
  have hlower := crossPair_lower_bounds_of_balanced_window
    hfiber hw hleft_window hright_window
  exact ⟨by omega, hleft_window.trans hhorizon, by omega,
    hright_window.trans hhorizon⟩

/-- Balanced-window bounds plus support disjointness produce a square-certified pair. -/
theorem crossGapSquareCertified_of_balanced_window
    {n w P d₁ x₁ u₁ d₂ x₂ u₂ : ℕ}
    (hfiber : CrossGapEvenFiberAt n d₁ x₁ u₁ d₂ x₂ u₂)
    (hw : w ≤ n)
    (hleft_window : crossLeft d₁ x₁ u₁ d₂ x₂ u₂ ≤ n + w)
    (hright_window : crossRight d₁ x₁ u₁ d₂ x₂ u₂ ≤ n + w)
    (hanchor : P < n - w)
    (hhorizon : n + w ≤ squareBody P)
    (hleft_disjoint : SupportDisjointFrom (primeScalesUpTo P)
      (crossLeft d₁ x₁ u₁ d₂ x₂ u₂))
    (hright_disjoint : SupportDisjointFrom (primeScalesUpTo P)
      (crossRight d₁ x₁ u₁ d₂ x₂ u₂)) :
    CrossGapSquareCertified P d₁ x₁ u₁ d₂ x₂ u₂ := by
  rcases crossPair_in_squareShell_of_balanced_window
    hfiber hw hleft_window hright_window hanchor hhorizon with
    ⟨hleft_lower, hleft_upper, hright_lower, hright_upper⟩
  exact ⟨hleft_lower, hleft_upper, hright_lower, hright_upper,
    hleft_disjoint, hright_disjoint⟩

/-- A square-certified Cross-Gap configuration on an even fiber yields Goldbach. -/
theorem goldbachPairAt_of_crossGapSquareCertified
    {n P d₁ x₁ u₁ d₂ x₂ u₂ : ℕ}
    (hfiber : CrossGapEvenFiberAt n d₁ x₁ u₁ d₂ x₂ u₂)
    (hcert : CrossGapSquareCertified P d₁ x₁ u₁ d₂ x₂ u₂) :
    GoldbachPairAt n := by
  have hprime := prime_pair_of_crossGapSquareCertified hcert
  rcases hfiber with ⟨hpaired, hleft, hright⟩
  have htotal :=
    crossLeft_add_crossRight_eq_pairedBig d₁ x₁ u₁ d₂ x₂ u₂
  exact ⟨crossLeft d₁ x₁ u₁ d₂ x₂ u₂,
    crossRight d₁ x₁ u₁ d₂ x₂ u₂, hprime.1, hprime.2, by omega⟩

end DkMath.NumberTheory.GoldbachCrossGapSquareCertification
