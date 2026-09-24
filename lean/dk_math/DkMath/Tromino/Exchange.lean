/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.State

#print "file: DkMath.Tromino.Exchange"

namespace DkMath.Tromino

/-!
# Additive Tromino exchange

An exchange is translation by a state delta.  The laws below are inherited
from the characteristic-two additive Klein four-group; no color names or
geometric solver state are built into this kernel.
-/

/-- Apply the exchange delta to a state. -/
def exchange (delta x : TrominoState) : TrominoState := x + delta

/-- The zero exchange leaves the state unchanged. -/
@[simp] theorem exchange_zero (x : TrominoState) :
    exchange 0 x = x := by
  simp [exchange]

/-- Every exchange is self-inverse. -/
theorem exchange_self_inverse (delta x : TrominoState) :
    exchange delta (exchange delta x) = x := by
  simp [exchange, add_assoc, state_add_self]

/-- Exchange composition is addition of deltas. -/
theorem exchange_comp (alpha beta x : TrominoState) :
    exchange alpha (exchange beta x) = exchange (alpha + beta) x := by
  simp [exchange, add_comm, add_left_comm]

/-- Exchanges commute. -/
theorem exchange_commute (alpha beta x : TrominoState) :
    exchange alpha (exchange beta x) = exchange beta (exchange alpha x) := by
  simp [exchange, add_comm, add_left_comm]

/-- A nonzero exchange changes every source state. -/
theorem exchange_ne_of_nonzero {delta x : TrominoState} (hdelta : delta ≠ 0) :
    exchange delta x ≠ x := by
  intro h
  apply hdelta
  apply add_left_cancel (a := x)
  simpa [exchange] using h

/-- A distinct target has a unique nonzero exchange delta from a source. -/
theorem existsUnique_nonzero_exchange_to {x y : TrominoState} (hxy : x ≠ y) :
    ∃! delta, delta ≠ 0 ∧ exchange delta x = y := by
  let delta : TrominoState := x + y
  have hdelta : delta ≠ 0 := by
    intro hzero
    apply hxy
    dsimp [delta] at hzero
    calc
      x = x + 0 := by simp
      _ = x + (x + y) := by rw [hzero]
      _ = (x + x) + y := by rw [add_assoc]
      _ = y := by rw [state_add_self, zero_add]
  have htarget : exchange delta x = y := by
    dsimp [exchange, delta]
    rw [← add_assoc, state_add_self, zero_add]
  refine ⟨delta, ⟨hdelta, htarget⟩, ?_⟩
  intro other hother
  rcases hother with ⟨_, hother_target⟩
  calc
    other = 0 + other := by simp
    _ = (x + x) + other := by rw [state_add_self]
    _ = x + (x + other) := by rw [add_assoc]
    _ = x + y := by rw [show x + other = y from hother_target]
    _ = delta := rfl

/-- The exchange delta is nonzero exactly when its source and target differ. -/
theorem exchange_delta_ne_zero_iff {delta x : TrominoState} :
    delta ≠ 0 ↔ exchange delta x ≠ x := by
  constructor
  · exact exchange_ne_of_nonzero
  · intro hdelta hzero
    apply hdelta
    apply add_left_cancel (a := x)
    simpa [exchange] using hzero

end DkMath.Tromino
