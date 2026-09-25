/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortNetwork
import DkMathTest.Tromino.FlowTransitionXorAxiomAudit

#print "file: DkMathTest.Tromino.PortNetworkAxiomAudit"

namespace DkMathTest.Tromino.PortNetworkAxiomAudit

open DkMath.Tromino
open DkMathTest.Tromino.FlowTransitionXorAxiomAudit

def twoByTwoPortNetwork : PortNetwork :=
  twoRegionFlowNetwork.toPortNetwork

def twoByTwoPortCrossing : PortCrossing twoByTwoPortNetwork :=
  twoRegionFlowCrossing.toPortCrossing

def port00 : PortNetworkPort twoByTwoPortNetwork :=
  ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩

def allDeltaAAssignment : V4FlowAssignment twoByTwoPortCrossing :=
  twoRegionFlowCrossing.toV4FlowAssignment

def allDeltaBAssignment : V4FlowAssignment twoByTwoPortCrossing where
  label := fun _ => deltaB
  nonzero := by
    intro p
    exact deltaB_ne_zero
  cross_sameLabel := by
    intro p
    rfl

theorem allDeltaA_label (p : PortNetworkPort twoByTwoPortNetwork) :
    allDeltaAAssignment.label p = deltaA := by
  cases p with
  | mk r i =>
    fin_cases r <;> fin_cases i <;> rfl

theorem allDeltaB_label (p : PortNetworkPort twoByTwoPortNetwork) :
    allDeltaBAssignment.label p = deltaB := by
  rfl

example : twoByTwoPortNetwork.regionCount = 2 := by decide
example : twoByTwoPortNetwork.portCount = 4 := by decide
example (r : Fin twoByTwoPortNetwork.regionCount) :
    twoByTwoPortNetwork.arity r = 2 := by
  fin_cases r <;> rfl

example (p : PortNetworkPort twoByTwoPortNetwork) :
    twoByTwoPortCrossing.cross (twoByTwoPortCrossing.cross p) = p :=
  twoByTwoPortCrossing.involutive p

example (p : PortNetworkPort twoByTwoPortNetwork) :
    twoByTwoPortCrossing.cross p ≠ p :=
  twoByTwoPortCrossing.cross_ne p

example (p : PortNetworkPort twoByTwoPortNetwork) :
    twoByTwoPortCrossing.crossEquiv p = twoByTwoPortCrossing.cross p := rfl

example : allDeltaAAssignment ≠ allDeltaBAssignment := by
  intro h
  have hp := congrArg
    (fun A : V4FlowAssignment twoByTwoPortCrossing => A.label port00) h
  rw [allDeltaA_label, allDeltaB_label] at hp
  exact deltaA_ne_deltaB hp

example (r : Fin twoByTwoPortNetwork.regionCount)
    (_i : Fin (twoByTwoPortNetwork.arity r)) :
    (allDeltaBAssignment.toFlowNetwork.signature r).arity =
      twoByTwoPortNetwork.arity r := by
  rfl

example (r : Fin twoByTwoPortNetwork.regionCount)
    (i : Fin (twoByTwoPortNetwork.arity r)) :
    (allDeltaBAssignment.toFlowNetwork.signature r).label i = deltaB := by
  rfl

example (p : PortNetworkPort twoByTwoPortNetwork) :
    allDeltaBAssignment.toFlowCrossing.cross p =
      twoByTwoPortCrossing.cross p := by
  rfl

example :
    allDeltaBAssignment.toFlowNetwork.toPortNetwork.regionCount =
      twoByTwoPortNetwork.regionCount := by
  rfl

example (r : Fin twoByTwoPortNetwork.regionCount) :
    allDeltaBAssignment.toFlowNetwork.toPortNetwork.arity r =
      twoByTwoPortNetwork.arity r := by
  rfl

example :
    twoRegionFlowNetwork.toPortNetwork.regionCount =
      twoRegionFlowNetwork.regionCount := by
  exact FlowNetwork.toPortNetwork_regionCount twoRegionFlowNetwork

example (r : Fin twoRegionFlowNetwork.regionCount) :
    twoRegionFlowNetwork.toPortNetwork.arity r =
      (twoRegionFlowNetwork.signature r).arity := by
  exact FlowNetwork.toPortNetwork_arity twoRegionFlowNetwork r

example (p : PortNetworkPort twoRegionFlowNetwork.toPortNetwork) :
    twoRegionFlowCrossing.toPortCrossing.cross p =
      twoRegionFlowCrossing.cross p := by
  exact FlowCrossing.toPortCrossing_cross twoRegionFlowCrossing p

example (p : PortNetworkPort twoRegionFlowNetwork.toPortNetwork) :
    twoRegionFlowCrossing.toV4FlowAssignment.label p =
      (twoRegionFlowNetwork.signature p.1).label p.2 := by
  exact FlowCrossing.toV4FlowAssignment_label twoRegionFlowCrossing p

example :
    twoRegionFlowCrossing.toV4FlowAssignment.toFlowNetwork.regionCount =
      twoRegionFlowNetwork.regionCount := by
  exact FlowCrossing.toV4FlowAssignment_toFlowNetwork_regionCount
    twoRegionFlowCrossing

example (r : Fin twoRegionFlowNetwork.regionCount) :
    (twoRegionFlowCrossing.toV4FlowAssignment.toFlowNetwork.signature r).arity =
      (twoRegionFlowNetwork.signature r).arity := by
  exact FlowCrossing.toV4FlowAssignment_toFlowNetwork_arity
    twoRegionFlowCrossing r

example (r : Fin twoRegionFlowNetwork.regionCount)
    (i : Fin (twoRegionFlowNetwork.signature r).arity) :
    (twoRegionFlowCrossing.toV4FlowAssignment.toFlowNetwork.signature r).label i =
      (twoRegionFlowNetwork.signature r).label i := by
  exact FlowCrossing.toV4FlowAssignment_toFlowNetwork_label
    twoRegionFlowCrossing r i

example (p : PortNetworkPort twoRegionFlowNetwork.toPortNetwork) :
    twoRegionFlowCrossing.toV4FlowAssignment.toFlowCrossing.cross p =
      twoRegionFlowCrossing.cross p := by
  exact FlowCrossing.toV4FlowAssignment_toFlowCrossing_cross
    twoRegionFlowCrossing p

example (p : PortNetworkPort twoByTwoPortNetwork) :
    allDeltaBAssignment.toFlowCrossing.toPortCrossing.cross p =
      twoByTwoPortCrossing.cross p := by
  exact V4FlowAssignment.toFlowCrossing_toPortCrossing_cross
    allDeltaBAssignment p

example (p : PortNetworkPort twoByTwoPortNetwork) :
    allDeltaBAssignment.toFlowCrossing.toV4FlowAssignment.label p =
      allDeltaBAssignment.label p := by
  exact V4FlowAssignment.reextracted_label allDeltaBAssignment p

#print axioms DkMath.Tromino.PortCrossing.cross_ne
#print axioms DkMath.Tromino.PortCrossing.crossEquiv
#print axioms DkMath.Tromino.V4FlowAssignment.toFlowNetwork
#print axioms DkMath.Tromino.V4FlowAssignment.toFlowCrossing
#print axioms DkMath.Tromino.FlowNetwork.toPortNetwork
#print axioms DkMath.Tromino.FlowCrossing.toPortCrossing
#print axioms DkMath.Tromino.FlowCrossing.toV4FlowAssignment
#print axioms DkMath.Tromino.V4FlowAssignment.reextracted_label

end DkMathTest.Tromino.PortNetworkAxiomAudit
