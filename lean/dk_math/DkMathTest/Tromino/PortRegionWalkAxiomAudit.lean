/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortRegionWalk
import DkMathTest.Tromino.PortRotationSystemAxiomAudit

#print "file: DkMathTest.Tromino.PortRegionWalkAxiomAudit"

namespace DkMathTest.Tromino.PortRegionWalkAxiomAudit

open DkMath.Tromino
open DkMathTest.Tromino.PortRotationSystemAxiomAudit
open DkMathTest.Tromino.RotationSystemAxiomAudit

example : PortRegionWalk.Valid portTwoCrossing ⟨0, by decide⟩
    ⟨0, by decide⟩ [] := rfl

example : PortRegionWalk.Valid portTwoCrossing ⟨0, by decide⟩
    ⟨1, by decide⟩ [p22_00] := by
  change p22_00.1 = ⟨0, by decide⟩ ∧
    (portTwoCrossing.cross p22_00).1 = ⟨1, by decide⟩
  exact ⟨rfl, rfl⟩

example : (PortRegionWalk.singleton portTwoCrossing p22_00).length = 1 := rfl

example : (PortRegionWalk.append
    (PortRegionWalk.singleton portTwoCrossing p22_00)
    (PortRegionWalk.singleton portTwoCrossing p22_11)).length = 2 := by
  rfl

example : PortRegionWalk.reverse
    (PortRegionWalk.reverse (PortRegionWalk.singleton portTwoCrossing p22_00)) =
      PortRegionWalk.singleton portTwoCrossing p22_00 := by
  exact PortRegionWalk.reverse_reverse _

example : PortRegionReachable portTwoCrossing ⟨0, by decide⟩
    ⟨1, by decide⟩ := by
  exact ⟨PortRegionWalk.singleton portTwoCrossing p22_00⟩

example : PortRegionReachable portTwoCrossing ⟨1, by decide⟩
    ⟨0, by decide⟩ := by
  exact ⟨PortRegionWalk.singleton portTwoCrossing p22_10⟩

example {r s : Fin portTwoNetwork.regionCount}
    (h : PortRegionReachable portTwoCrossing r s) :
    PortRegionReachable portTwoCrossing s r :=
  portRegionReachable_symm _ h

example {r s t : Fin portTwoNetwork.regionCount}
    (h₁ : PortRegionReachable portTwoCrossing r s)
    (h₂ : PortRegionReachable portTwoCrossing s t) :
    PortRegionReachable portTwoCrossing r t :=
  portRegionReachable_trans _ h₁ h₂

theorem portTwo_region_connected : PortRegionConnected portTwoCrossing := by
  intro r s
  fin_cases r <;> fin_cases s
  · exact ⟨PortRegionWalk.nil portTwoCrossing _⟩
  · exact ⟨PortRegionWalk.singleton portTwoCrossing p22_00⟩
  · exact ⟨PortRegionWalk.singleton portTwoCrossing p22_10⟩
  · exact ⟨PortRegionWalk.nil portTwoCrossing _⟩

theorem portThree_region_connected :
    PortRegionConnected portThreeCrossing := by
  intro r s
  fin_cases r <;> fin_cases s
  · exact ⟨PortRegionWalk.nil portThreeCrossing _⟩
  · exact ⟨PortRegionWalk.singleton portThreeCrossing p30⟩
  · exact ⟨PortRegionWalk.singleton portThreeCrossing p33⟩
  · exact ⟨PortRegionWalk.nil portThreeCrossing _⟩

def disconnectedNetwork : PortNetwork where
  regionCount := 4
  arity := fun _ => 1

def disconnectedRegion (r : Fin 4) : Fin 4 :=
  if h : r.val < 2 then ⟨1 - r.val, by omega⟩
  else ⟨5 - r.val, by omega⟩

theorem disconnectedRegion_involutive (r : Fin 4) :
    disconnectedRegion (disconnectedRegion r) = r := by
  fin_cases r <;> rfl

theorem disconnectedRegion_ne (r : Fin 4) : disconnectedRegion r ≠ r := by
  fin_cases r <;> decide

def disconnectedCrossing : PortCrossing disconnectedNetwork where
  cross := fun p => ⟨disconnectedRegion p.1, p.2⟩
  involutive := by
    intro p
    apply Sigma.ext
    · exact disconnectedRegion_involutive p.1
    · exact heq_of_eq rfl
  changesRegion := by
    intro p
    exact disconnectedRegion_ne p.1

def pd0 : PortNetworkPort disconnectedNetwork :=
  ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
def pd1 : PortNetworkPort disconnectedNetwork :=
  ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
def pd2 : PortNetworkPort disconnectedNetwork :=
  ⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩
def pd3 : PortNetworkPort disconnectedNetwork :=
  ⟨⟨3, by decide⟩, ⟨0, by decide⟩⟩

theorem disconnected_component_cross (p : PortNetworkPort disconnectedNetwork) :
    (p.1.val < 2 ↔ (disconnectedCrossing.cross p).1.val < 2) := by
  rcases p with ⟨r, i⟩
  fin_cases r <;> fin_cases i <;> decide

theorem disconnected_valid_component {r s : Fin 4}
    {xs : List (PortNetworkPort disconnectedNetwork)}
    (h : PortRegionWalk.Valid disconnectedCrossing r s xs) :
    (r.val < 2 ↔ s.val < 2) := by
  induction xs generalizing r s with
  | nil =>
    simp only [PortRegionWalk.Valid] at h
    subst s
    rfl
  | cons p xs ih =>
    simp only [PortRegionWalk.Valid] at h
    have hp : p.1 = r := h.1
    have htail := ih h.2
    have hcross := disconnected_component_cross p
    simpa [hp] using hcross.trans htail

example : PortRegionReachable disconnectedCrossing ⟨0, by decide⟩
    ⟨1, by decide⟩ := by
  exact ⟨PortRegionWalk.singleton disconnectedCrossing pd0⟩

example : PortRegionReachable disconnectedCrossing ⟨2, by decide⟩
    ⟨3, by decide⟩ := by
  exact ⟨PortRegionWalk.singleton disconnectedCrossing pd2⟩

example : ¬ PortRegionReachable disconnectedCrossing ⟨0, by decide⟩
    ⟨2, by decide⟩ := by
  rintro ⟨W⟩
  have hcomponent := disconnected_valid_component W.valid
  norm_num at hcomponent

example : ¬ PortRegionConnected disconnectedCrossing := by
  intro h
  exact (show ¬ PortRegionReachable disconnectedCrossing
      ⟨0, by decide⟩ ⟨2, by decide⟩ from by
        intro h02
        rcases h02 with ⟨W⟩
        have hcomponent := disconnected_valid_component W.valid
        norm_num at hcomponent) (h _ _)

example {N : FlowNetwork} (C : FlowCrossing N)
    {r s : Fin N.regionCount} (W : FlowRegionWalk C r s) :
    W.toPortRegionWalk.edges = W.edges := rfl

example {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) {r s : Fin P.regionCount}
    (W : PortRegionWalk C r s) :
    (W.toFlowRegionWalk A).edges = W.edges := rfl

example {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (r : Fin P.regionCount) :
    (PortRegionWalk.nil C r).toFlowRegionWalk A =
      FlowRegionWalk.nil A.toFlowCrossing r := by
  exact PortRegionWalk.toFlowRegionWalk_nil A r

example {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) {r s : Fin P.regionCount}
    (W : PortRegionWalk C r s) :
    (W.toFlowRegionWalk A).toPortRegionWalk = W :=
  PortRegionWalk.toFlowRegionWalk_toPortRegionWalk A W

example {N : FlowNetwork} (C : FlowCrossing N)
    {r s : Fin N.regionCount} :
    RegionReachable C r s →
      PortRegionReachable C.toPortCrossing r s :=
  flowRegionReachable_imp_port C

example {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) {r s : Fin P.regionCount} :
    PortRegionReachable C r s ↔
      RegionReachable A.toFlowCrossing r s :=
  portRegionReachable_iff_flow_lift A

example {P : PortNetwork} {C : PortCrossing P}
    (A B : V4FlowAssignment C) {r s : Fin P.regionCount} :
    RegionReachable A.toFlowCrossing r s ↔
      RegionReachable B.toFlowCrossing r s :=
  regionReachable_assignment_independent A B

example : PortRegionConnected twoThreeCrossing.toPortCrossing := by
  apply (portRegionConnected_iff_flow_lift
    twoThreeCrossing.toV4FlowAssignment).mpr
  intro r s
  fin_cases r <;> fin_cases s
  · exact ⟨FlowRegionWalk.nil twoThreeCrossing _⟩
  · exact ⟨FlowRegionWalk.singleton twoThreeCrossing p23⟩
  · exact ⟨FlowRegionWalk.singleton twoThreeCrossing
      ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩⟩
  · exact ⟨FlowRegionWalk.nil twoThreeCrossing _⟩

example :
    (∀ r s, RegionReachable portDeltaAAssignment.toFlowCrossing r s) ↔
      (∀ r s, RegionReachable portDeltaBAssignment.toFlowCrossing r s) :=
  regionConnected_assignment_independent portDeltaAAssignment
    portDeltaBAssignment

#print axioms DkMath.Tromino.PortRegionWalk.Valid
#print axioms DkMath.Tromino.PortRegionWalk.append
#print axioms DkMath.Tromino.PortRegionWalk.reverse
#print axioms DkMath.Tromino.PortRegionWalk.reverse_reverse
#print axioms DkMath.Tromino.PortRegionReachable
#print axioms DkMath.Tromino.portRegionReachable_trans
#print axioms DkMath.Tromino.PortRegionConnected
#print axioms DkMath.Tromino.flowRegionReachable_imp_port
#print axioms DkMath.Tromino.portRegionReachable_iff_flow_lift
#print axioms DkMath.Tromino.regionReachable_assignment_independent
#print axioms DkMath.Tromino.FlowRegionWalk.toPortRegionWalk_toFlowRegionWalk
#print axioms DkMath.Tromino.PortRegionWalk.toFlowRegionWalk_toPortRegionWalk

end DkMathTest.Tromino.PortRegionWalkAxiomAudit
