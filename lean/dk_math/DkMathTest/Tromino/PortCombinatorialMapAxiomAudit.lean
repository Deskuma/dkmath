/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortCombinatorialMap
import DkMathTest.Tromino.PortRegionWalkAxiomAudit
import DkMathTest.Tromino.PortEulerCountAxiomAudit
import DkMathTest.Tromino.CombinatorialMapAxiomAudit

#print "file: DkMathTest.Tromino.PortCombinatorialMapAxiomAudit"

namespace DkMathTest.Tromino.PortCombinatorialMapAxiomAudit

open DkMath.Tromino
open DkMathTest.Tromino.PortEulerCountAxiomAudit
open DkMathTest.Tromino.PortRegionWalkAxiomAudit
open DkMathTest.Tromino.PortRotationSystemAxiomAudit
open DkMathTest.Tromino.CombinatorialMapAxiomAudit
open DkMathTest.Tromino.FlowTransitionXorAxiomAudit

def portTwoMap : PortCombinatorialMap portTwoNetwork where
  crossing := portTwoCrossing
  rotation := portTwoRotationSystem
  nonemptyRegions := by decide
  connected := portTwo_region_connected

def portThreeMap : PortCombinatorialMap portThreeNetwork where
  crossing := portThreeCrossing
  rotation := portThreeRotationSystem
  nonemptyRegions := by decide
  connected := portThree_region_connected

example : portTwoMap.vertexCount = 2 := by decide
example : portTwoMap.edgeCount = 2 := by decide
example : portTwoMap.faceCount = 2 := by
  change portFaceCount portTwoRotation portTwoCrossing = 2
  exact portFaceCount_22
example : portTwoMap.portCount = 4 := by decide

theorem portTwoMap_eulerCharacteristic : portTwoMap.eulerCharacteristic = 2 := by
  change portCombinatorialEulerCharacteristic portTwoRotation portTwoCrossing = 2
  have he : portCrossingEdgeCount portTwoCrossing = 2 := by decide
  unfold portCombinatorialEulerCharacteristic
  rw [he, portFaceCount_22]
  norm_num [portRegionVertexCount, portTwoNetwork]

example : portThreeMap.vertexCount = 2 := by decide
example : portThreeMap.edgeCount = 3 := by decide
example : portThreeMap.faceCount = 1 := by
  change portFaceCount portThreeRotation portThreeCrossing = 1
  exact portFaceCount_23
example : portThreeMap.portCount = 6 := by decide

theorem portThreeMap_eulerCharacteristic : portThreeMap.eulerCharacteristic = 0 := by
  change portCombinatorialEulerCharacteristic portThreeRotation portThreeCrossing = 0
  have he : portCrossingEdgeCount portThreeCrossing = 3 := by decide
  unfold portCombinatorialEulerCharacteristic
  rw [he, portFaceCount_23]
  norm_num [portRegionVertexCount, portThreeNetwork]

example : PortHasCombinatorialGenus portTwoMap 0 := by
  rw [portCombinatorialGenus_zero_iff, portTwoMap_eulerCharacteristic]

example : PortHasSphereCharacteristic portTwoMap := by
  rw [PortHasSphereCharacteristic, portTwoMap_eulerCharacteristic]

def portTwoGenusZero : PortGenusZeroCombinatorialMap portTwoNetwork where
  map := portTwoMap
  genusZero := by
    rw [portCombinatorialGenus_zero_iff, portTwoMap_eulerCharacteristic]

example : PortHasSphereCharacteristic portTwoGenusZero.map :=
  portTwoGenusZero.hasSphereCharacteristic

example : PortHasCombinatorialGenus portThreeMap 1 := by
  rw [portCombinatorialGenus_one_iff, portThreeMap_eulerCharacteristic]

example : ¬ PortHasSphereCharacteristic portThreeMap := by
  rw [PortHasSphereCharacteristic, portThreeMap_eulerCharacteristic]
  decide

example : ¬ PortRegionConnected disconnectedCrossing := by
  intro h
  have h02 := h ⟨0, by decide⟩ ⟨2, by decide⟩
  rcases h02 with ⟨W⟩
  have hcomponent := disconnected_valid_component W.valid
  norm_num at hcomponent

example (p q : PortNetworkPort portTwoNetwork) (hregion : p.1 = q.1) :
    SamePortVertexRotationOrbit portTwoMap p q :=
  portTwoMap.sameVertexRotationOrbit_of_same_region p q hregion

example : PortRegionReachable portTwoCrossing ⟨0, by decide⟩ ⟨1, by decide⟩ :=
  portTwoMap.connected_regions _ _

example : (portTwoMap.toFlowCombinatorialMap portDeltaAAssignment).vertexCount =
    portTwoMap.vertexCount :=
  portTwoMap.toFlowCombinatorialMap_vertexCount portDeltaAAssignment

example : (portTwoMap.toFlowCombinatorialMap portDeltaAAssignment).edgeCount =
    portTwoMap.edgeCount :=
  portTwoMap.toFlowCombinatorialMap_edgeCount portDeltaAAssignment

example : (portTwoMap.toFlowCombinatorialMap portDeltaAAssignment).faceCount =
    portTwoMap.faceCount :=
  portTwoMap.toFlowCombinatorialMap_faceCount portDeltaAAssignment

example : (portTwoMap.toFlowCombinatorialMap portDeltaAAssignment).portCount =
    portTwoMap.portCount :=
  portTwoMap.toFlowCombinatorialMap_portCount portDeltaAAssignment

example : (portTwoMap.toFlowCombinatorialMap portDeltaAAssignment).eulerCharacteristic =
    portTwoMap.eulerCharacteristic :=
  portTwoMap.toFlowCombinatorialMap_eulerCharacteristic portDeltaAAssignment

example : twoTwoMap.toPortCombinatorialMap.vertexCount = twoTwoMap.vertexCount :=
  twoTwoMap.toPortCombinatorialMap_vertexCount

example : twoTwoMap.toPortCombinatorialMap.edgeCount = twoTwoMap.edgeCount :=
  twoTwoMap.toPortCombinatorialMap_edgeCount

example : twoTwoMap.toPortCombinatorialMap.faceCount = twoTwoMap.faceCount :=
  twoTwoMap.toPortCombinatorialMap_faceCount

example : twoTwoMap.toPortCombinatorialMap.portCount = twoTwoMap.portCount :=
  twoTwoMap.toPortCombinatorialMap_portCount

example : twoTwoMap.toPortCombinatorialMap.eulerCharacteristic =
    twoTwoMap.eulerCharacteristic :=
  twoTwoMap.toPortCombinatorialMap_eulerCharacteristic

example : HasCombinatorialGenus twoTwoMap 0 ↔
    PortHasCombinatorialGenus twoTwoMap.toPortCombinatorialMap 0 :=
  twoTwoMap.toPortCombinatorialMap_genus_iff 0

example : HasSphereCharacteristic twoTwoMap ↔
    PortHasSphereCharacteristic twoTwoMap.toPortCombinatorialMap :=
  twoTwoMap.toPortCombinatorialMap_sphere_iff

example : PortHasCombinatorialGenus portTwoMap 0 ↔
    HasCombinatorialGenus
      (portTwoMap.toFlowCombinatorialMap portDeltaAAssignment) 0 :=
  portTwoMap.toFlowCombinatorialMap_genus_iff portDeltaAAssignment 0

example : PortHasSphereCharacteristic portTwoMap ↔
    HasSphereCharacteristic
      (portTwoMap.toFlowCombinatorialMap portDeltaAAssignment) :=
  portTwoMap.toFlowCombinatorialMap_sphere_iff portDeltaAAssignment

example :
    (portTwoMap.toFlowCombinatorialMap portDeltaAAssignment).vertexCount =
        (portTwoMap.toFlowCombinatorialMap portDeltaBAssignment).vertexCount ∧
      (portTwoMap.toFlowCombinatorialMap portDeltaAAssignment).edgeCount =
        (portTwoMap.toFlowCombinatorialMap portDeltaBAssignment).edgeCount ∧
      (portTwoMap.toFlowCombinatorialMap portDeltaAAssignment).faceCount =
        (portTwoMap.toFlowCombinatorialMap portDeltaBAssignment).faceCount ∧
      (portTwoMap.toFlowCombinatorialMap portDeltaAAssignment).portCount =
        (portTwoMap.toFlowCombinatorialMap portDeltaBAssignment).portCount ∧
      (portTwoMap.toFlowCombinatorialMap portDeltaAAssignment).eulerCharacteristic =
        (portTwoMap.toFlowCombinatorialMap portDeltaBAssignment).eulerCharacteristic :=
  portTwoMap.toFlowCombinatorialMap_assignment_independent
    portDeltaAAssignment portDeltaBAssignment

example (g : Nat) :
    HasCombinatorialGenus
        (portTwoMap.toFlowCombinatorialMap portDeltaAAssignment) g ↔
      HasCombinatorialGenus
        (portTwoMap.toFlowCombinatorialMap portDeltaBAssignment) g :=
  portTwoMap.toFlowCombinatorialMap_genus_assignment_independent
    portDeltaAAssignment portDeltaBAssignment g

example :
    HasSphereCharacteristic
        (portTwoMap.toFlowCombinatorialMap portDeltaAAssignment) ↔
      HasSphereCharacteristic
        (portTwoMap.toFlowCombinatorialMap portDeltaBAssignment) :=
  portTwoMap.toFlowCombinatorialMap_sphere_assignment_independent
    portDeltaAAssignment portDeltaBAssignment

example (p : PortNetworkPort twoRegionFlowNetwork.toPortNetwork) :
    twoTwoMap.toPortCombinatorialMap.crossing.cross p =
      twoTwoMap.crossing.cross p :=
  twoTwoMap.toPortCombinatorialMap_round_trip_cross p

example (p : PortNetworkPort twoRegionFlowNetwork.toPortNetwork) :
    twoTwoMap.toPortCombinatorialMap.rotation.rotate p =
      twoTwoMap.rotation.rotate p :=
  twoTwoMap.toPortCombinatorialMap_round_trip_rotate p

example (p : PortNetworkPort portTwoNetwork) :
    ((portTwoMap.toFlowCombinatorialMap portDeltaAAssignment).crossing.toPortCrossing).cross p = portTwoMap.crossing.cross p :=
  portTwoMap.toFlowCombinatorialMap_round_trip_cross portDeltaAAssignment p

example (p : PortNetworkPort portTwoNetwork) :
    ((portTwoMap.toFlowCombinatorialMap portDeltaAAssignment).rotation.toPortRotationSystem).rotate p = portTwoMap.rotation.rotate p :=
  portTwoMap.toFlowCombinatorialMap_round_trip_rotate portDeltaAAssignment p

#print axioms DkMath.Tromino.PortCombinatorialMap
#print axioms DkMath.Tromino.PortGenusZeroCombinatorialMap
#print axioms DkMath.Tromino.FlowCombinatorialMap.toPortCombinatorialMap
#print axioms DkMath.Tromino.PortCombinatorialMap.toFlowCombinatorialMap
#print axioms DkMath.Tromino.PortCombinatorialMap.toFlowCombinatorialMap_assignment_independent
#print axioms DkMath.Tromino.PortCombinatorialMap.toFlowCombinatorialMap_genus_assignment_independent
#print axioms DkMath.Tromino.PortCombinatorialMap.toFlowCombinatorialMap_sphere_assignment_independent

end DkMathTest.Tromino.PortCombinatorialMapAxiomAudit
