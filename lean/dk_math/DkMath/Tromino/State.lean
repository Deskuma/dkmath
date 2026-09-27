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

The state kernel is the additive Klein four-group already provided by Mathlib.
The zero state is the distinguished current/waiting state; its three translates
by nonzero elements are the three nontrivial exchange choices.
-/

/-- The four-state carrier used by the Tromino exchange kernel. -/
abbrev TrominoState := ZMod 2 × ZMod 2

/-- The carrier has exactly four states. -/
theorem card_state : Nat.card TrominoState = 4 := by
  exact IsAddKleinFour.card_four

/-- The waiting states are all states other than the current state. -/
def waitingStates (x : TrominoState) : Finset TrominoState :=
  Finset.univ.erase x

/-- Membership in the waiting set means being a distinct state. -/
theorem mem_waitingStates_iff {x y : TrominoState} :
    y ∈ waitingStates x ↔ y ≠ x := by
  simp [waitingStates]

/-- Every current state has three waiting states. -/
theorem card_waitingStates (x : TrominoState) :
    (waitingStates x).card = 3 := by
  rw [waitingStates, Finset.card_erase_of_mem (Finset.mem_univ x)]
  simp

/-- Every state is self-added to zero in the characteristic-two carrier. -/
theorem state_add_self (x : TrominoState) : x + x = 0 := by
  apply Prod.ext
  · calc
      x.1 + x.1 = x.1 + -x.1 := by rw [ZMod.neg_eq_self_mod_two]
      _ = 0 := add_neg_cancel x.1
  · calc
      x.2 + x.2 = x.2 + -x.2 := by rw [ZMod.neg_eq_self_mod_two]
      _ = 0 := add_neg_cancel x.2

/-- The three nonzero states are exactly the nontrivial exchange choices. -/
theorem nonzeroStates_eq_waitingStates_zero :
    Finset.filter (fun x : TrominoState => x ≠ 0) Finset.univ =
      waitingStates 0 := by
  ext x
  simp [waitingStates]

/-- There are exactly three nonzero exchange choices. -/
theorem card_nonzeroStates :
    (Finset.filter (fun x : TrominoState => x ≠ 0) Finset.univ).card = 3 := by
  rw [nonzeroStates_eq_waitingStates_zero]
  exact card_waitingStates 0

end DkMath.Tromino
