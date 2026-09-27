/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.TransitionGraph

#print "file: DkMath.Tromino.TransitionXor"

namespace DkMath.Tromino

open scoped BigOperators

/-!
# XOR accumulated along a closed transition orbit

The transition graph supplies a finite label-preserving permutation.  This
module sums the labels along its iterates.  Since the V4 carrier has
characteristic two, the resulting sum depends only on the parity of the
number of steps once the label is known to be nonzero.
-/

/-- The label at iterate `j` is counted once for each transition step. -/
def transitionXor (N : ClosedBoundaryNetwork) (p : NetworkPort N.toBoundaryNetwork)
    (n : Nat) : TrominoState :=
  Finset.sum (Finset.range n) (fun j =>
    boundaryDelta (N.toBoundaryNetwork.signature ((transitionStep N)^[j] p).1)
      ((transitionStep N)^[j] p).2)

/-- Label preservation turns the transition XOR into an `n`-fold sum. -/
theorem transitionXor_eq_nsmul (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) (n : Nat) :
    transitionXor N p n = n •
      boundaryDelta (N.toBoundaryNetwork.signature p.1) p.2 := by
  induction n with
  | zero => simp [transitionXor]
  | succ n ih =>
    rw [transitionXor, Finset.sum_range_succ]
    change transitionXor N p n +
      boundaryDelta (N.toBoundaryNetwork.signature ((transitionStep N)^[n] p).1)
        ((transitionStep N)^[n] p).2 = _
    rw [ih, transitionStep_iterate_sameLabel, succ_nsmul]

/-- Transition XOR is additive when an orbit segment is split. -/
theorem transitionXor_add (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) (n m : Nat) :
    transitionXor N p (n + m) =
      transitionXor N p n +
        transitionXor N ((transitionStep N)^[n] p) m := by
  rw [transitionXor, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [show n + j = j + n by omega, Function.iterate_add_apply]

/-! ### Characteristic-two repeated labels -/

/-- Repeating one V4 state `n` times depends only on `n mod 2`. -/
theorem nsmul_state_eq_mod_two (n : Nat) (delta : TrominoState) :
    n • delta = if n % 2 = 0 then 0 else delta := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, ih]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have hsucc : (n + 1) % 2 = 1 := by omega
      simp [h, hsucc]
    · have hsucc : (n + 1) % 2 = 0 := by omega
      simp [h, hsucc, state_add_self]

/-- A repeated V4 state sums to zero iff it is zero or repeated evenly. -/
theorem nsmul_state_eq_zero_iff (n : Nat) (delta : TrominoState) :
    n • delta = 0 ↔ delta = 0 ∨ n % 2 = 0 := by
  rw [nsmul_state_eq_mod_two]
  by_cases hdelta : delta = 0
  · simp [hdelta]
  · by_cases hparity : n % 2 = 0
    · simp [hparity]
    · simp [hdelta, hparity]

/-- Transition XOR vanishes iff the initial label is zero or the length is even. -/
theorem transitionXor_eq_zero_iff (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) (n : Nat) :
    transitionXor N p n = 0 ↔
      boundaryDelta (N.toBoundaryNetwork.signature p.1) p.2 = 0 ∨ n % 2 = 0 := by
  rw [transitionXor_eq_nsmul, nsmul_state_eq_zero_iff]

/-- For a nowhere-zero network, vanishing transition XOR is even parity. -/
theorem transitionXor_nonzero_iff_even (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) (n : Nat) :
    transitionXor N p n = 0 ↔ n % 2 = 0 := by
  rw [transitionXor_eq_zero_iff]
  constructor
  · rintro (hzero | heven)
    · exact (boundaryDelta_ne_zero (N.toBoundaryNetwork.signature p.1) p.2 hzero).elim
    · exact heven
  · intro heven
    exact Or.inr heven

/-! ### Positive and primitive returns -/

/-- A positive return of the directed transition orbit. -/
def TransitionReturn (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) (n : Nat) : Prop :=
  0 < n ∧ (transitionStep N)^[n] p = p

/-- A return with no smaller positive return. -/
def PrimitiveTransitionReturn (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) (n : Nat) : Prop :=
  TransitionReturn N p n ∧
    ∀ m, 0 < m → m < n → (transitionStep N)^[m] p ≠ p

/-- The least positive return time of the transition. -/
def firstTransitionReturn (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) : Nat :=
  Nat.find (transitionStep_periodic N p)

/-- The first return time is a positive valid return. -/
theorem firstTransitionReturn_spec (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) :
    TransitionReturn N p (firstTransitionReturn N p) := by
  exact Nat.find_spec (transitionStep_periodic N p)

/-- Every positive return is at least the first return. -/
theorem firstTransitionReturn_min (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) {m : Nat}
    (hm : TransitionReturn N p m) : firstTransitionReturn N p ≤ m := by
  exact Nat.find_min' (transitionStep_periodic N p) hm

/-- The first return has no earlier positive return. -/
theorem firstTransitionReturn_primitive (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) :
    PrimitiveTransitionReturn N p (firstTransitionReturn N p) := by
  refine ⟨firstTransitionReturn_spec N p, ?_⟩
  intro m hmpos hmlt hreturn
  have hmin := firstTransitionReturn_min N p ⟨hmpos, hreturn⟩
  omega

/-- Every finite transition orbit has a primitive return. -/
theorem exists_primitiveTransitionReturn (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) : ∃ n, PrimitiveTransitionReturn N p n := by
  exact ⟨firstTransitionReturn N p, firstTransitionReturn_primitive N p⟩

/-- A primitive return is compatible when its accumulated XOR vanishes. -/
def PrimitiveCycleCompatible (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) (n : Nat) : Prop :=
  PrimitiveTransitionReturn N p n ∧ transitionXor N p n = 0

/-- Primitive-cycle XOR vanishing is equivalent to even return length. -/
theorem primitiveCycleXor_iff_even (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) (n : Nat)
    (_hprimitive : PrimitiveTransitionReturn N p n) :
    transitionXor N p n = 0 ↔ n % 2 = 0 :=
  transitionXor_nonzero_iff_even N p n

/-- Primitive-cycle compatibility is exactly the even-parity condition. -/
theorem primitiveCycleCompatible_iff_even (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) (n : Nat)
    (hprimitive : PrimitiveTransitionReturn N p n) :
    PrimitiveCycleCompatible N p n ↔ n % 2 = 0 := by
  constructor
  · rintro ⟨_, hxor⟩
    exact (primitiveCycleXor_iff_even N p n hprimitive).mp hxor
  · intro heven
    exact ⟨hprimitive, (primitiveCycleXor_iff_even N p n hprimitive).mpr heven⟩

/-! ### Prefix transport -/

/-- Transport a base state by the XOR accumulated along a prefix. -/
def transportState (base : TrominoState) (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) (n : Nat) : TrominoState :=
  base + transitionXor N p n

/-- Zero steps leave the transported state unchanged. -/
@[simp] theorem transportState_zero (base : TrominoState) (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) : transportState base N p 0 = base := by
  simp [transportState, transitionXor]

/-- Prefix transport composes over concatenated transition segments. -/
theorem transportState_add (base : TrominoState) (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) (n m : Nat) :
    transportState base N p (n + m) =
      transportState (transportState base N p n) N ((transitionStep N)^[n] p) m := by
  rw [transportState, transitionXor_add, transportState, transportState]
  rw [add_assoc]

/-- At a return, transport closure is equivalent to zero accumulated XOR. -/
theorem transportState_return_iff (base : TrominoState) (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) (n : Nat)
    (_hreturn : TransitionReturn N p n) :
    transportState base N p n = base ↔ transitionXor N p n = 0 := by
  constructor
  · intro h
    have h' : base + transitionXor N p n = base + 0 := by simpa [transportState] using h
    exact add_left_cancel h'
  · intro h
    simp [transportState, h]

/-- On a primitive cycle, transport closure is equivalent to even length. -/
theorem primitiveTransport_return_iff (base : TrominoState) (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) (n : Nat)
    (hprimitive : PrimitiveTransitionReturn N p n) :
    transportState base N p n = base ↔ n % 2 = 0 := by
  rw [transportState_return_iff base N p n hprimitive.1,
    primitiveCycleXor_iff_even N p n hprimitive]

end DkMath.Tromino
