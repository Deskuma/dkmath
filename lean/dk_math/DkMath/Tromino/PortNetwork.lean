/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.FlowTransition

#print "file: DkMath.Tromino.PortNetwork"

namespace DkMath.Tromino

structure PortNetwork where
  regionCount : Nat
  arity : Fin regionCount → Nat

abbrev PortNetworkPort (P : PortNetwork) :=
  Sigma (fun r : Fin P.regionCount => Fin (P.arity r))

def PortNetwork.portCount (P : PortNetwork) : Nat :=
  Fintype.card (PortNetworkPort P)

structure PortCrossing (P : PortNetwork) where
  cross : PortNetworkPort P → PortNetworkPort P
  involutive : Function.Involutive cross
  changesRegion : ∀ p, (cross p).1 ≠ p.1

theorem PortCrossing.cross_ne {P : PortNetwork} (C : PortCrossing P)
    (p : PortNetworkPort P) : C.cross p ≠ p := by
  intro h
  exact C.changesRegion p (congrArg Sigma.fst h)

def PortCrossing.crossEquiv {P : PortNetwork} (C : PortCrossing P) :
    PortNetworkPort P ≃ PortNetworkPort P where
  toFun := C.cross
  invFun := C.cross
  left_inv := C.involutive
  right_inv := C.involutive

@[simp] theorem PortCrossing.crossEquiv_apply {P : PortNetwork}
    (C : PortCrossing P) (p : PortNetworkPort P) :
    C.crossEquiv p = C.cross p := rfl

theorem PortCrossing.reverse_twice {P : PortNetwork} (C : PortCrossing P)
    (p : PortNetworkPort P) : C.cross (C.cross p) = p :=
  C.involutive p

structure V4FlowAssignment {P : PortNetwork} (C : PortCrossing P) where
  label : PortNetworkPort P → TrominoState
  nonzero : ∀ p, label p ≠ 0
  cross_sameLabel : ∀ p, label (C.cross p) = label p

def V4FlowAssignment.toFlowNetwork {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) : FlowNetwork where
  regionCount := P.regionCount
  signature := fun r =>
    { arity := P.arity r
      label := fun i => A.label ⟨r, i⟩
      nonzero := by
        intro i
        exact A.nonzero ⟨r, i⟩ }

@[simp] theorem V4FlowAssignment.toFlowNetwork_regionCount
    {P : PortNetwork} {C : PortCrossing P} (A : V4FlowAssignment C) :
    A.toFlowNetwork.regionCount = P.regionCount := rfl

@[simp] theorem V4FlowAssignment.toFlowNetwork_arity
    {P : PortNetwork} {C : PortCrossing P} (A : V4FlowAssignment C)
    (r : Fin P.regionCount) :
    (A.toFlowNetwork.signature r).arity = P.arity r := rfl

@[simp] theorem V4FlowAssignment.toFlowNetwork_label
    {P : PortNetwork} {C : PortCrossing P} (A : V4FlowAssignment C)
    (r : Fin P.regionCount) (i : Fin (A.toFlowNetwork.signature r).arity) :
    (A.toFlowNetwork.signature r).label i = A.label ⟨r, i⟩ := rfl

def V4FlowAssignment.toFlowCrossing {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) : FlowCrossing A.toFlowNetwork where
  cross := C.cross
  involutive := C.involutive
  changesRegion := C.changesRegion
  sameLabel := by
    intro p
    exact A.cross_sameLabel p

@[simp] theorem V4FlowAssignment.toFlowCrossing_cross
    {P : PortNetwork} {C : PortCrossing P} (A : V4FlowAssignment C)
    (p : FlowNetworkPort A.toFlowNetwork) :
    A.toFlowCrossing.cross p = C.cross p := rfl

def FlowNetwork.toPortNetwork (N : FlowNetwork) : PortNetwork where
  regionCount := N.regionCount
  arity := fun r => (N.signature r).arity

@[simp] theorem FlowNetwork.toPortNetwork_regionCount (N : FlowNetwork) :
    N.toPortNetwork.regionCount = N.regionCount := rfl

@[simp] theorem FlowNetwork.toPortNetwork_arity (N : FlowNetwork)
    (r : Fin N.regionCount) : N.toPortNetwork.arity r = (N.signature r).arity := rfl

def FlowCrossing.toPortCrossing {N : FlowNetwork} (C : FlowCrossing N) :
    PortCrossing N.toPortNetwork where
  cross := C.cross
  involutive := C.involutive
  changesRegion := C.changesRegion

@[simp] theorem FlowCrossing.toPortCrossing_cross {N : FlowNetwork}
    (C : FlowCrossing N) (p : PortNetworkPort N.toPortNetwork) :
    C.toPortCrossing.cross p = C.cross p := rfl

def FlowCrossing.toV4FlowAssignment {N : FlowNetwork} (C : FlowCrossing N) :
    V4FlowAssignment C.toPortCrossing where
  label := fun p => (N.signature p.1).label p.2
  nonzero := by
    intro p
    exact (N.signature p.1).nonzero p.2
  cross_sameLabel := by
    intro p
    exact C.sameLabel p

@[simp] theorem FlowCrossing.toV4FlowAssignment_label {N : FlowNetwork}
    (C : FlowCrossing N) (p : PortNetworkPort N.toPortNetwork) :
    C.toV4FlowAssignment.label p = (N.signature p.1).label p.2 := rfl

@[simp] theorem FlowCrossing.toV4FlowAssignment_toFlowNetwork_regionCount
    {N : FlowNetwork} (C : FlowCrossing N) :
    C.toV4FlowAssignment.toFlowNetwork.regionCount = N.regionCount := rfl

@[simp] theorem FlowCrossing.toV4FlowAssignment_toFlowNetwork_arity
    {N : FlowNetwork} (C : FlowCrossing N) (r : Fin N.regionCount) :
    (C.toV4FlowAssignment.toFlowNetwork.signature r).arity =
      (N.signature r).arity := rfl

@[simp] theorem FlowCrossing.toV4FlowAssignment_toFlowNetwork_label
    {N : FlowNetwork} (C : FlowCrossing N) (r : Fin N.regionCount)
    (i : Fin (N.signature r).arity) :
    (C.toV4FlowAssignment.toFlowNetwork.signature r).label i =
      (N.signature r).label i := rfl

@[simp] theorem FlowCrossing.toV4FlowAssignment_toFlowCrossing_cross
    {N : FlowNetwork} (C : FlowCrossing N)
    (p : PortNetworkPort N.toPortNetwork) :
    C.toV4FlowAssignment.toFlowCrossing.cross p = C.cross p := rfl

@[simp] theorem V4FlowAssignment.toFlowNetwork_toPortNetwork_regionCount
    {P : PortNetwork} {C : PortCrossing P} (A : V4FlowAssignment C) :
    A.toFlowNetwork.toPortNetwork.regionCount = P.regionCount := rfl

@[simp] theorem V4FlowAssignment.toFlowNetwork_toPortNetwork_arity
    {P : PortNetwork} {C : PortCrossing P} (A : V4FlowAssignment C)
    (r : Fin P.regionCount) :
    A.toFlowNetwork.toPortNetwork.arity r = P.arity r := rfl

@[simp] theorem V4FlowAssignment.toFlowCrossing_toPortCrossing_cross
    {P : PortNetwork} {C : PortCrossing P} (A : V4FlowAssignment C)
    (p : PortNetworkPort P) :
    A.toFlowCrossing.toPortCrossing.cross p = C.cross p := rfl

@[simp] theorem V4FlowAssignment.reextracted_label
    {P : PortNetwork} {C : PortCrossing P} (A : V4FlowAssignment C)
    (p : PortNetworkPort P) :
    A.toFlowCrossing.toV4FlowAssignment.label p = A.label p := rfl

end DkMath.Tromino
