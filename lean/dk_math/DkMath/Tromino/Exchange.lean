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

An exchange is translation by a state delta in the additive V4 carrier.
The delta is the displacement between source and target states, so applying
the same exchange twice cancels it in characteristic two.  The laws below
are purely algebraic; no color names or geometric solver state are built into
this kernel.
-/

/-- Translate a state by an exchange delta.

The argument order is chosen so that `exchange delta x` is the target reached
from source state `x`. -/
def exchange (delta x : TrominoState) : TrominoState := x + delta

/-- The identity delta acts trivially on every source state. -/
@[simp] theorem exchange_zero (x : TrominoState) :
    exchange 0 x = x := by
  simp [exchange]

/-- Every exchange is an involution because its delta is self-added to zero. -/
theorem exchange_self_inverse (delta x : TrominoState) :
    exchange delta (exchange delta x) = x := by
  simp [exchange, add_assoc, state_add_self]

/-- Successive translations compose by adding their deltas.

This gives the exchange kernel its group-action interpretation. -/
theorem exchange_comp (alpha beta x : TrominoState) :
    exchange alpha (exchange beta x) = exchange (alpha + beta) x := by
  simp [exchange, add_comm, add_left_comm]

/-- Exchanges commute because the underlying V4 addition is commutative. -/
theorem exchange_commute (alpha beta x : TrominoState) :
    exchange alpha (exchange beta x) = exchange beta (exchange alpha x) := by
  simp [exchange, add_comm, add_left_comm]

/-- A nonzero delta has no fixed source state: it changes every state. -/
theorem exchange_ne_of_nonzero {delta x : TrominoState} (hdelta : delta ≠ 0) :
    exchange delta x ≠ x := by
  intro h
  apply hdelta
  apply add_left_cancel (a := x)
  simpa [exchange] using h

/-- For distinct source and target states, there is a unique nonzero delta
carrying the source to the target.  Explicitly, that delta is `x + y`. -/
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

/-- An exchange is nontrivial exactly when its source and target states differ. -/
theorem exchange_delta_ne_zero_iff {delta x : TrominoState} :
    delta ≠ 0 ↔ exchange delta x ≠ x := by
  constructor
  · exact exchange_ne_of_nonzero
  · intro hdelta hzero
    apply hdelta
    apply add_left_cancel (a := x)
    simpa [exchange] using hzero

/-- For a fixed source, translating by all deltas permutes the four target
states. -/
def exchangeEquiv (x : TrominoState) : TrominoState ≃ TrominoState :=
  Equiv.addRight x

@[simp] theorem exchangeEquiv_apply (x delta : TrominoState) :
    exchangeEquiv x delta = exchange delta x := by
  simp [exchangeEquiv, exchange, add_comm]

/-- Every target has a unique exchange delta from a fixed source, including
the identity delta when source and target coincide. -/
theorem existsUnique_exchange_to (x y : TrominoState) :
    ∃! delta, exchange delta x = y := by
  by_cases hxy : x = y
  · subst y
    refine ⟨0, exchange_zero x, ?_⟩
    intro delta hdelta
    apply add_left_cancel (a := x)
    simpa [exchange] using hdelta
  · rcases existsUnique_nonzero_exchange_to hxy with
      ⟨delta, ⟨hdelta, htarget⟩, hunique⟩
    refine ⟨delta, htarget, ?_⟩
    intro other hother
    apply hunique other
    refine ⟨?_, hother⟩
    intro hzero
    apply hxy
    subst other
    simpa using hother

end DkMath.Tromino
