/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.PrimorialWheelTwinThreshold
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.Legendre.PrimorialWheelOldEscapeFrontier"

/-!
# Old-escape frontier equivalence audit

This module packages the exact successor criterion supplied by the old-basis
and twin-threshold classifications.  It then compares that criterion with
the existing escaping-square-offset and prime-in-a-square-cell statements.
The comparison is deliberately an audit: it does not prove the provider or
any lower bound for the old-basis escape set.
-/

namespace DkMath.NumberTheory.Legendre

/-! ## Local criterion -/

/--
The exact old-basis condition for an actual escape in the successor shell.

For a composite successor, or a prime successor which is not followed by a
prime at distance two, one old escape suffices.  In the twin-prime branch the
second threshold seat may be deleted, so two old escapes are required.
-/
def SuccessorOldEscapeCriterion (n : ℕ) : Prop :=
  if Nat.Prime (n + 1) ∧ Nat.Prime (n + 3) then
    2 ≤ (successorOldBasisEscapingOffsets n).card
  else
    (successorOldBasisEscapingOffsets n).Nonempty

/-! ## Identification with the actual escape set -/

/-- The old-escape criterion is equivalent to nonempty actual escape. -/
theorem successorOldEscapeCriterion_iff_escapingSquareOffsets_nonempty
    {n : ℕ} (hn : 2 ≤ n) :
    SuccessorOldEscapeCriterion n ↔
      (escapingSquareOffsets (n + 1)).Nonempty := by
  have hident :
      successorProjectedEscapingOffsets n =
        escapingSquareOffsets (n + 1) :=
    successorProjectedEscapingOffsets_eq_escapingSquareOffsets (by omega)
  have hprojEsc :
      (successorProjectedEscapingOffsets n).Nonempty ↔
        (escapingSquareOffsets (n + 1)).Nonempty := by
    rw [hident]
  by_cases hq : Nat.Prime (n + 1)
  · by_cases htwin : Nat.Prime (n + 3)
    · have hbranch :
          (successorProjectedEscapingOffsets n).Nonempty ↔
            2 ≤ (successorOldBasisEscapingOffsets n).card :=
        successorProjectedEscapingOffsets_nonempty_iff_two_oldEscape_of_twinPrime
          hn hq htwin
      have hlocal :
          SuccessorOldEscapeCriterion n ↔
            (successorProjectedEscapingOffsets n).Nonempty := by
        simpa [SuccessorOldEscapeCriterion, hq, htwin] using hbranch.symm
      exact hlocal.trans hprojEsc
    · have hbranch :
          (successorProjectedEscapingOffsets n).Nonempty ↔
            (successorOldBasisEscapingOffsets n).Nonempty :=
        successorProjectedEscapingOffsets_nonempty_iff_old_of_not_twinPrime
          hn hq htwin
      have hlocal :
          SuccessorOldEscapeCriterion n ↔
            (successorProjectedEscapingOffsets n).Nonempty := by
        simpa [SuccessorOldEscapeCriterion, hq, htwin] using hbranch.symm
      exact hlocal.trans hprojEsc
  · have hbranch :
        (successorProjectedEscapingOffsets n).Nonempty ↔
          (successorOldBasisEscapingOffsets n).Nonempty := by
      rw [successorProjectedEscapingOffsets_eq_old_of_composite (by omega) hq]
    have hlocal :
        SuccessorOldEscapeCriterion n ↔
          (successorProjectedEscapingOffsets n).Nonempty := by
      simpa [SuccessorOldEscapeCriterion, hq] using hbranch.symm
    exact hlocal.trans hprojEsc

/-! ## Prime-witness spelling -/

/-- Nonempty escaping offsets are equivalent to a prime in the square cell. -/
theorem escapingSquareOffsets_nonempty_iff_exists_prime_in_squareCell
    {n : ℕ} (hn : 2 ≤ n) :
    (escapingSquareOffsets n).Nonempty ↔
      ∃ p, Nat.Prime p ∧ SquareCell n p := by
  constructor
  · rintro ⟨r, hr⟩
    have hrdata := mem_escapingSquareOffsets.mp hr
    have hp : Nat.Prime (n ^ 2 + r) :=
      (squareOffset_prime_iff_not_covered (by omega) hrdata.1).mpr hrdata.2
    refine ⟨n ^ 2 + r, hp, ?_⟩
    exact (squareCell_iff_exists_squareOffset n (n ^ 2 + r)).mpr
      ⟨r, hrdata.1, rfl⟩
  · rintro ⟨p, hp, hcell⟩
    obtain ⟨r, hr, hrEq⟩ :=
      (squareCell_iff_exists_squareOffset n p).mp hcell
    have hp' : Nat.Prime (n ^ 2 + r) := by
      simpa [hrEq] using hp
    have hnot : ¬ SquareOffsetCovered n r :=
      (squareOffset_prime_iff_not_covered (by omega) hr).mp hp'
    exact ⟨r, mem_escapingSquareOffsets.mpr ⟨hr, hnot⟩⟩

/-- The old-escape criterion is equivalent to a prime in the successor cell. -/
theorem successorOldEscapeCriterion_iff_exists_prime_in_successor_squareCell
    {n : ℕ} (hn : 2 ≤ n) :
    SuccessorOldEscapeCriterion n ↔
      ∃ p, Nat.Prime p ∧ SquareCell (n + 1) p := by
  exact (successorOldEscapeCriterion_iff_escapingSquareOffsets_nonempty hn).trans
    (escapingSquareOffsets_nonempty_iff_exists_prime_in_squareCell (by omega))

/-! ## Global provider equivalences -/

/-- Global old-basis escape from the first nontrivial successor level. -/
def SuccessorOldEscapeProvider : Prop :=
  ∀ n : ℕ, 2 ≤ n → SuccessorOldEscapeCriterion n

/-- The provider is exactly the prime-in-cell statement from anchor `3` on. -/
theorem successorOldEscapeProvider_iff_legendre_from_three :
    SuccessorOldEscapeProvider ↔
      ∀ m : ℕ, 3 ≤ m → ∃ p, Nat.Prime p ∧ SquareCell m p := by
  constructor
  · intro h m hm
    have hcriterion := h (m - 1) (by omega)
    have hcell :=
      (successorOldEscapeCriterion_iff_exists_prime_in_successor_squareCell
        (n := m - 1) (by omega)).mp hcriterion
    have hsub : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
    simpa [hsub] using hcell
  · intro h n hn
    apply (successorOldEscapeCriterion_iff_exists_prime_in_successor_squareCell hn).mpr
    exact h (n + 1) (by omega)

/-! ## Full Legendre equivalence -/

/-- The global old-escape provider is equivalent to Legendre's conjecture. -/
theorem legendreConjecture_iff_successorOldEscapeProvider :
    LegendreConjecture ↔ SuccessorOldEscapeProvider := by
  constructor
  · intro h n hn
    exact (successorOldEscapeCriterion_iff_exists_prime_in_successor_squareCell hn).mpr
      (h (n + 1) (by omega))
  · intro h n hn
    by_cases hnOne : n = 1
    · subst n
      refine ⟨2, by norm_num, ?_⟩
      norm_num [SquareCell]
    · by_cases hnTwo : n = 2
      · subst n
        refine ⟨5, by norm_num, ?_⟩
        norm_num [SquareCell]
      · have hnThree : 3 ≤ n := by omega
        have hcriterion := h (n - 1) (by omega)
        have hcell :=
          (successorOldEscapeCriterion_iff_exists_prime_in_successor_squareCell
            (n := n - 1) (by omega)).mp hcriterion
        have hsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
        simpa [hsub] using hcell

/-- Diagnostic direction: a global old-escape proof would prove Legendre. -/
theorem oldEscapeProvider_is_not_weaker_than_legendre :
    SuccessorOldEscapeProvider → LegendreConjecture :=
  legendreConjecture_iff_successorOldEscapeProvider.mpr

/-- Diagnostic converse: Legendre supplies the global old-escape provider. -/
theorem legendre_is_not_weaker_than_oldEscapeProvider :
    LegendreConjecture → SuccessorOldEscapeProvider :=
  legendreConjecture_iff_successorOldEscapeProvider.mp

/-! ## Visible regressions -/

/-- At `n = 3`, composite successor `4` preserves old and projected escape. -/
theorem successorOldEscapeRegression_three_composite :
    ¬ Nat.Prime (3 + 1) ∧
      successorProjectedEscapingOffsets 3 =
        successorOldBasisEscapingOffsets 3 := by
  refine ⟨by norm_num, ?_⟩
  exact successorProjectedEscapingOffsets_eq_old_of_composite
    (by norm_num) (by norm_num)

/-- At `n = 4`, twin successor `5` deletes old escape seat `10`. -/
theorem successorOldEscapeRegression_four_twin :
    Nat.Prime (4 + 1) ∧ Nat.Prime (4 + 3) ∧
      10 ∈ successorOldBasisEscapingOffsets 4 ∧
      10 ∉ successorProjectedEscapingOffsets 4 ∧
      (SuccessorOldEscapeCriterion 4 ↔
        2 ≤ (successorOldBasisEscapingOffsets 4).card) := by
  have hreg := successorTwinThresholdRegression_four
  refine ⟨hreg.1, hreg.2.1, hreg.2.2.1, hreg.2.2.2, ?_⟩
  simp [SuccessorOldEscapeCriterion, hreg.1, hreg.2.1]

end DkMath.NumberTheory.Legendre
