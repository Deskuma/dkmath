/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.PrimorialWheelSuccessor
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.Legendre.PrimorialWheelSuccessorEscape"

/-!
# Successor old-basis escape and deletion capacity

This module packages the offsets escaping the old bounded prime basis in the
successor shell.  A prime threshold can remove only the second threshold seat
from that old-escape set: the first seat is already reserved by the old basis.
The resulting cardinality statement is a finite deletion-capacity theorem;
it does not assert that the shifted successor window contains any old escape.

The module reuses the PUU-L012 successor transition and projected-survivor
dictionary.  It does not introduce square-hole propagation, gap bounds,
PowerSwap, GN/CosmicFormula, PNT, or RH.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.PrimorialUniverse

/-! ## Successor-shell escape sets -/

/-- Successor-shell offsets escaping reservation by the old bounded basis. -/
noncomputable def successorOldBasisEscapingOffsets (n : ℕ) : Finset ℕ := by
  classical
  exact (squareOffsets (n + 1)).filter
    (fun r => ¬ SuccessorOldBasisReserved n r)

/-- Membership in the old-basis successor escape set. -/
@[simp] theorem mem_successorOldBasisEscapingOffsets
    {n r : ℕ} :
    r ∈ successorOldBasisEscapingOffsets n ↔
      SquareOffset (n + 1) r ∧ ¬ SuccessorOldBasisReserved n r := by
  classical
  simp [successorOldBasisEscapingOffsets]

/-- Successor-shell offsets surviving the enlarged projected prime basis. -/
noncomputable def successorProjectedEscapingOffsets (n : ℕ) : Finset ℕ := by
  classical
  exact (squareOffsets (n + 1)).filter
    (fun r =>
      IsPrimeBasisWheelSurvivor (primeScalesUpTo (n + 1))
        (squareShellWheelProjection
          (primeScalesUpTo (n + 1)) (n + 1) r))

/-- Membership in the projected successor escape set. -/
@[simp] theorem mem_successorProjectedEscapingOffsets
    {n r : ℕ} :
    r ∈ successorProjectedEscapingOffsets n ↔
      SquareOffset (n + 1) r ∧
        IsPrimeBasisWheelSurvivor (primeScalesUpTo (n + 1))
          (squareShellWheelProjection
            (primeScalesUpTo (n + 1)) (n + 1) r) := by
  classical
  simp [successorProjectedEscapingOffsets]

/-! ## The first threshold seat -/

/-- The first prime-threshold seat is already reserved by the old basis. -/
theorem successorOldBasisReserved_firstThreshold
    {n : ℕ}
    (hn : 2 ≤ n)
    (hq : Nat.Prime (n + 1)) :
    SuccessorOldBasisReserved n (n + 1) := by
  unfold SuccessorOldBasisReserved ReservedByPrimeBasis
  refine ⟨2, mem_primeScalesUpTo.mpr ⟨Nat.prime_two, hn⟩, ?_⟩
  rw [show (n + 1) ^ 2 + (n + 1) = (n + 1) * (n + 2) by ring]
  obtain ⟨k, hk⟩ := (hq.odd_iff).2 (by omega)
  refine ⟨(n + 1) * (k + 1), ?_⟩
  rw [show n + 2 = 2 * (k + 1) by omega]
  ring

/-- The first threshold seat is not an old-basis escaping offset. -/
theorem not_mem_successorOldBasisEscapingOffsets_firstThreshold
    {n : ℕ}
    (hn : 2 ≤ n)
    (hq : Nat.Prime (n + 1)) :
    n + 1 ∉ successorOldBasisEscapingOffsets n := by
  rw [mem_successorOldBasisEscapingOffsets]
  intro hmem
  exact hmem.2 (successorOldBasisReserved_firstThreshold hn hq)

/-! ## Prime-threshold deletion -/

/-- Prime-threshold projected escapes are old escapes with the second seat erased.

The theorem records only a possible deletion: it does not assert that the
second threshold seat belongs to the old escape set.
-/
theorem successorProjectedEscapingOffsets_eq_erase_secondThreshold
    {n : ℕ}
    (hn : 2 ≤ n)
    (hq : Nat.Prime (n + 1)) :
    successorProjectedEscapingOffsets n =
      (successorOldBasisEscapingOffsets n).erase (2 * (n + 1)) := by
  classical
  ext r
  by_cases hsq : SquareOffset (n + 1) r
  · rw [mem_successorProjectedEscapingOffsets, Finset.mem_erase,
      mem_successorOldBasisEscapingOffsets]
    constructor
    · rintro ⟨_, hsurv⟩
      have htransition :=
        (successorProjectedSurvivor_iff_primeThreshold hq hsq).mp hsurv
      exact ⟨htransition.2.2, ⟨hsq, htransition.1⟩⟩
    · rintro ⟨hsecond, ⟨_, hold⟩⟩
      have hfirst : r ≠ n + 1 := by
        intro hfirst
        subst r
        exact hold (successorOldBasisReserved_firstThreshold hn hq)
      exact ⟨hsq,
        (successorProjectedSurvivor_iff_primeThreshold hq hsq).mpr
          ⟨hold, hfirst, hsecond⟩⟩
  · simp [mem_successorProjectedEscapingOffsets,
      mem_successorOldBasisEscapingOffsets, hsq]

/-! ## Deletion capacity -/

/-- The fresh prime deletes at most one old-basis escaping offset. -/
theorem successorOldBasisEscapingOffsets_card_le_projected_add_one
    {n : ℕ}
    (hn : 2 ≤ n)
    (hq : Nat.Prime (n + 1)) :
    (successorOldBasisEscapingOffsets n).card ≤
      (successorProjectedEscapingOffsets n).card + 1 := by
  rw [successorProjectedEscapingOffsets_eq_erase_secondThreshold hn hq]
  by_cases hmem : 2 * (n + 1) ∈ successorOldBasisEscapingOffsets n
  · rw [Finset.card_erase_of_mem hmem]
    omega
  · simp [hmem]

/-- Two old-basis escapes force one actual projected successor escape. -/
theorem successorProjectedEscapingOffsets_nonempty_of_two_le_oldEscapeCard
    {n : ℕ}
    (hn : 2 ≤ n)
    (hq : Nat.Prime (n + 1))
    (hcard : 2 ≤ (successorOldBasisEscapingOffsets n).card) :
    (successorProjectedEscapingOffsets n).Nonempty := by
  apply Finset.card_pos.mp
  have hbound := successorOldBasisEscapingOffsets_card_le_projected_add_one hn hq
  omega

/-! ## Composite successor -/

/-- Composite successors preserve the old-basis successor escape set exactly. -/
theorem successorProjectedEscapingOffsets_eq_old_of_composite
    {n : ℕ}
    (hn : 1 ≤ n)
    (hq : ¬ Nat.Prime (n + 1)) :
    successorProjectedEscapingOffsets n =
      successorOldBasisEscapingOffsets n := by
  classical
  ext r
  by_cases hsq : SquareOffset (n + 1) r
  · rw [mem_successorProjectedEscapingOffsets,
      mem_successorOldBasisEscapingOffsets]
    constructor
    · rintro ⟨_, hsurv⟩
      exact ⟨hsq,
        (successorProjectedSurvivor_iff_composite hq hn hsq).mp hsurv⟩
    · rintro ⟨_, hold⟩
      exact ⟨hsq,
        (successorProjectedSurvivor_iff_composite hq hn hsq).mpr hold⟩
  · simp [mem_successorProjectedEscapingOffsets,
      mem_successorOldBasisEscapingOffsets, hsq]

/-- In the composite case, old-basis and projected escape nonemptiness agree. -/
theorem successorProjectedEscapingOffsets_nonempty_iff_old_of_composite
    {n : ℕ}
    (hn : 1 ≤ n)
    (hq : ¬ Nat.Prime (n + 1)) :
    (successorProjectedEscapingOffsets n).Nonempty ↔
      (successorOldBasisEscapingOffsets n).Nonempty := by
  rw [successorProjectedEscapingOffsets_eq_old_of_composite hn hq]

/-! ## Visible regression -/

/-- At `n = 4`, `5` is old-reserved while `10` is deleted by the new prime. -/
theorem successorEscapeDeletionRegression_four :
    5 ∉ successorOldBasisEscapingOffsets 4 ∧
      10 ∈ successorOldBasisEscapingOffsets 4 ∧
      10 ∉ successorProjectedEscapingOffsets 4 := by
  have hn : 2 ≤ (4 : ℕ) := by norm_num
  have hq : Nat.Prime (4 + 1) := by norm_num
  have hfirst := not_mem_successorOldBasisEscapingOffsets_firstThreshold hn hq
  have hold : ¬ SuccessorOldBasisReserved 4 10 :=
    successorThresholdRegression_four_ten.1
  have hsq : SquareOffset (4 + 1) 10 := by
    norm_num [SquareOffset]
  have hmem : 10 ∈ successorOldBasisEscapingOffsets 4 :=
    mem_successorOldBasisEscapingOffsets.mpr ⟨hsq, hold⟩
  refine ⟨by simpa using hfirst, hmem, ?_⟩
  rw [successorProjectedEscapingOffsets_eq_erase_secondThreshold hn hq]
  simp [hmem]

end DkMath.NumberTheory.Legendre
