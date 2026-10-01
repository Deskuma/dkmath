/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.GroupTheory.SpecificGroups.KleinFour

#print "file: DkMath.Tromino.State"

namespace DkMath.Tromino

/-!
# The four-state Tromino carrier

The state kernel is the additive Klein four-group `ZMod 2 × ZMod 2`.
Consequently every state is its own additive inverse, and the sum of two
states is the unique V4 translation carrying one to the other.  The zero
state is the distinguished current state; its three nonzero translates are
the three waiting states and the three nontrivial exchange choices.
-/

/-- The finite additive V4 carrier used by the Tromino exchange kernel.

Its two coordinates are binary residues, so addition is componentwise modulo
two. -/
abbrev TrominoState := ZMod 2 × ZMod 2

/-- The state carrier has four elements, one for each binary coordinate pair. -/
theorem card_state : Nat.card TrominoState = 4 := by
  exact IsAddKleinFour.card_four

/-- The waiting states at `x` are the complement of the current state in the
four-element carrier. -/
def waitingStates (x : TrominoState) : Finset TrominoState :=
  Finset.univ.erase x

/-- Membership in `waitingStates x` is equivalent to being different from `x`. -/
theorem mem_waitingStates_iff {x y : TrominoState} :
    y ∈ waitingStates x ↔ y ≠ x := by
  simp [waitingStates]

/-- Removing one current state from the four-state carrier leaves three waiting
states. -/
theorem card_waitingStates (x : TrominoState) :
    (waitingStates x).card = 3 := by
  rw [waitingStates, Finset.card_erase_of_mem (Finset.mem_univ x)]
  simp

/-- Characteristic two makes every state self-inverse: `x + x = 0`.

This identity is the algebraic reason that each exchange is involutive. -/
theorem state_add_self (x : TrominoState) : x + x = 0 := by
  apply Prod.ext
  · calc
      x.1 + x.1 = x.1 + -x.1 := by rw [ZMod.neg_eq_self_mod_two]
      _ = 0 := add_neg_cancel x.1
  · calc
      x.2 + x.2 = x.2 + -x.2 := by rw [ZMod.neg_eq_self_mod_two]
      _ = 0 := add_neg_cancel x.2

/-- The nonzero states are exactly the waiting states relative to zero, hence
the three possible nontrivial exchange deltas. -/
theorem nonzeroStates_eq_waitingStates_zero :
    Finset.filter (fun x : TrominoState => x ≠ 0) Finset.univ =
      waitingStates 0 := by
  ext x
  simp [waitingStates]

/-- There are exactly three nontrivial translations of the V4 carrier. -/
theorem card_nonzeroStates :
    (Finset.filter (fun x : TrominoState => x ≠ 0) Finset.univ).card = 3 := by
  rw [nonzeroStates_eq_waitingStates_zero]
  exact card_waitingStates 0

end DkMath.Tromino
