/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.FlowTransition
import DkMath.Tromino.TransitionXor

#print "file: DkMath.Tromino.FlowTransitionXor"

namespace DkMath.Tromino

open scoped BigOperators

def flowTransitionXor (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) (n : Nat) : TrominoState :=
  Finset.sum (Finset.range n) (fun j =>
    (N.toFlowNetwork.signature ((flowTransitionStep N)^[j] p).1).label
      ((flowTransitionStep N)^[j] p).2)

theorem flowTransitionXor_eq_nsmul (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) (n : Nat) :
    flowTransitionXor N p n = n •
      (N.toFlowNetwork.signature p.1).label p.2 := by
  induction n with
  | zero => simp [flowTransitionXor]
  | succ n ih =>
    rw [flowTransitionXor, Finset.sum_range_succ]
    change flowTransitionXor N p n +
      (N.toFlowNetwork.signature ((flowTransitionStep N)^[n] p).1).label
        ((flowTransitionStep N)^[n] p).2 = _
    rw [ih, flowTransitionStep_iterate_sameLabel, succ_nsmul]

theorem flowTransitionXor_add (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) (n m : Nat) :
    flowTransitionXor N p (n + m) =
      flowTransitionXor N p n +
        flowTransitionXor N ((flowTransitionStep N)^[n] p) m := by
  rw [flowTransitionXor, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [show n + j = j + n by omega, Function.iterate_add_apply]

theorem flowTransitionXor_eq_zero_iff (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) (n : Nat) :
    flowTransitionXor N p n = 0 ↔
      (N.toFlowNetwork.signature p.1).label p.2 = 0 ∨ n % 2 = 0 := by
  rw [flowTransitionXor_eq_nsmul, nsmul_state_eq_zero_iff]

theorem flowTransitionXor_nonzero_iff_even (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) (n : Nat) :
    flowTransitionXor N p n = 0 ↔ n % 2 = 0 := by
  rw [flowTransitionXor_eq_zero_iff]
  constructor
  · rintro (hzero | heven)
    · exact ((N.toFlowNetwork.signature p.1).nonzero p.2 hzero).elim
    · exact heven
  · intro heven
    exact Or.inr heven

def FlowTransitionReturn (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) (n : Nat) : Prop :=
  0 < n ∧ (flowTransitionStep N)^[n] p = p

def FlowPrimitiveTransitionReturn (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) (n : Nat) : Prop :=
  FlowTransitionReturn N p n ∧
    ∀ m, 0 < m → m < n → (flowTransitionStep N)^[m] p ≠ p

def firstFlowTransitionReturn (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) : Nat :=
  Nat.find (flowTransitionStep_periodic N p)

theorem firstFlowTransitionReturn_spec (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    FlowTransitionReturn N p (firstFlowTransitionReturn N p) := by
  exact Nat.find_spec (flowTransitionStep_periodic N p)

theorem firstFlowTransitionReturn_min (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) {m : Nat}
    (hm : FlowTransitionReturn N p m) :
    firstFlowTransitionReturn N p ≤ m := by
  exact Nat.find_min' (flowTransitionStep_periodic N p) hm

theorem firstFlowTransitionReturn_primitive (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    FlowPrimitiveTransitionReturn N p (firstFlowTransitionReturn N p) := by
  refine ⟨firstFlowTransitionReturn_spec N p, ?_⟩
  intro m hmpos hmlt hreturn
  have hmin := firstFlowTransitionReturn_min N p ⟨hmpos, hreturn⟩
  omega

theorem exists_primitiveFlowTransitionReturn (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    ∃ n, FlowPrimitiveTransitionReturn N p n := by
  exact ⟨firstFlowTransitionReturn N p, firstFlowTransitionReturn_primitive N p⟩

def FlowPrimitiveCycleCompatible (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) (n : Nat) : Prop :=
  FlowPrimitiveTransitionReturn N p n ∧ flowTransitionXor N p n = 0

theorem flowPrimitiveCycleXor_iff_even (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) (n : Nat)
    (_hprimitive : FlowPrimitiveTransitionReturn N p n) :
    flowTransitionXor N p n = 0 ↔ n % 2 = 0 :=
  flowTransitionXor_nonzero_iff_even N p n

theorem flowPrimitiveCycleCompatible_iff_even (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) (n : Nat)
    (hprimitive : FlowPrimitiveTransitionReturn N p n) :
    FlowPrimitiveCycleCompatible N p n ↔ n % 2 = 0 := by
  constructor
  · rintro ⟨_, hxor⟩
    exact (flowPrimitiveCycleXor_iff_even N p n hprimitive).mp hxor
  · intro heven
    exact ⟨hprimitive, (flowPrimitiveCycleXor_iff_even N p n hprimitive).mpr heven⟩

def flowTransportState (base : TrominoState) (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) (n : Nat) : TrominoState :=
  base + flowTransitionXor N p n

@[simp] theorem flowTransportState_zero (base : TrominoState) (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    flowTransportState base N p 0 = base := by
  simp [flowTransportState, flowTransitionXor]

theorem flowTransportState_add (base : TrominoState) (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) (n m : Nat) :
    flowTransportState base N p (n + m) =
      flowTransportState (flowTransportState base N p n) N
        ((flowTransitionStep N)^[n] p) m := by
  rw [flowTransportState, flowTransitionXor_add, flowTransportState, flowTransportState]
  rw [add_assoc]

theorem flowTransportState_return_iff (base : TrominoState) (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) (n : Nat)
    (_hreturn : FlowTransitionReturn N p n) :
    flowTransportState base N p n = base ↔ flowTransitionXor N p n = 0 := by
  constructor
  · intro h
    have h' : base + flowTransitionXor N p n = base + 0 := by
      simpa [flowTransportState] using h
    exact add_left_cancel h'
  · intro h
    simp [flowTransportState, h]

theorem flowPrimitiveTransport_return_iff (base : TrominoState)
    (N : ClosedFlowNetwork) (p : FlowNetworkPort N.toFlowNetwork) (n : Nat)
    (hprimitive : FlowPrimitiveTransitionReturn N p n) :
    flowTransportState base N p n = base ↔ n % 2 = 0 := by
  rw [flowTransportState_return_iff base N p n hprimitive.1,
    flowPrimitiveCycleXor_iff_even N p n hprimitive]

theorem flowTransitionXor_toClosedFlowNetwork (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) (n : Nat) :
    flowTransitionXor N.toClosedFlowNetwork p n = transitionXor N p n := rfl

theorem flowTransportState_toClosedFlowNetwork (base : TrominoState)
    (N : ClosedBoundaryNetwork) (p : NetworkPort N.toBoundaryNetwork) (n : Nat) :
    flowTransportState base N.toClosedFlowNetwork p n = transportState base N p n := rfl

theorem flowTransitionReturn_toClosedFlowNetwork (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) (n : Nat) :
    FlowTransitionReturn N.toClosedFlowNetwork p n ↔ TransitionReturn N p n := Iff.rfl

theorem flowPrimitiveTransitionReturn_toClosedFlowNetwork
    (N : ClosedBoundaryNetwork) (p : NetworkPort N.toBoundaryNetwork) (n : Nat) :
    FlowPrimitiveTransitionReturn N.toClosedFlowNetwork p n ↔
      PrimitiveTransitionReturn N p n := Iff.rfl

theorem flowPrimitiveCycleCompatible_toClosedFlowNetwork
    (N : ClosedBoundaryNetwork) (p : NetworkPort N.toBoundaryNetwork) (n : Nat) :
    FlowPrimitiveCycleCompatible N.toClosedFlowNetwork p n ↔
      PrimitiveCycleCompatible N p n := Iff.rfl

theorem firstFlowTransitionReturn_toClosedFlowNetwork
    (N : ClosedBoundaryNetwork) (p : NetworkPort N.toBoundaryNetwork) :
    firstFlowTransitionReturn N.toClosedFlowNetwork p = firstTransitionReturn N p := rfl

end DkMath.Tromino
