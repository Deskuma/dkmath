/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortEulerCount
import DkMath.Tromino.PortRegionWalk
import DkMath.Tromino.CombinatorialMap

#print "file: DkMath.Tromino.PortCombinatorialMap"

namespace DkMath.Tromino

structure PortCombinatorialMap (P : PortNetwork) where
  crossing : PortCrossing P
  rotation : PortRotationSystem P
  nonemptyRegions : 0 < P.regionCount
  connected : PortRegionConnected crossing

def PortCombinatorialMap.localRotation {P : PortNetwork}
    (M : PortCombinatorialMap P) : PortLocalRotation P :=
  M.rotation.toPortLocalRotation

def PortCombinatorialMap.vertexCount {P : PortNetwork}
    (_M : PortCombinatorialMap P) : Nat :=
  portRegionVertexCount P

def PortCombinatorialMap.edgeCount {P : PortNetwork}
    (M : PortCombinatorialMap P) : Nat :=
  portCrossingEdgeCount M.crossing

def PortCombinatorialMap.faceCount {P : PortNetwork}
    (M : PortCombinatorialMap P) : Nat :=
  portFaceCount M.localRotation M.crossing

def PortCombinatorialMap.portCount {P : PortNetwork}
    (_M : PortCombinatorialMap P) : Nat :=
  P.portCount

def PortCombinatorialMap.eulerCharacteristic {P : PortNetwork}
    (M : PortCombinatorialMap P) : Int :=
  portCombinatorialEulerCharacteristic M.localRotation M.crossing

def SamePortVertexRotationOrbit {P : PortNetwork}
    (M : PortCombinatorialMap P) (p q : PortNetworkPort P) : Prop :=
  p.1 = q.1 ∧
    ∃ n : Nat, (M.localRotation.rotate^[n]) p = q

theorem PortCombinatorialMap.rotation_reaches_same_region
    {P : PortNetwork} (M : PortCombinatorialMap P)
    (p q : PortNetworkPort P) (hregion : p.1 = q.1) :
    ∃ n : Nat, (M.localRotation.rotate^[n]) p = q := by
  cases p with
  | mk r i =>
    cases q with
    | mk s j =>
      dsimp at hregion
      subst s
      simpa [PortCombinatorialMap.localRotation] using
        M.rotation.cyclic r i j

theorem PortCombinatorialMap.sameVertexRotationOrbit_of_same_region
    {P : PortNetwork} (M : PortCombinatorialMap P)
    (p q : PortNetworkPort P) (hregion : p.1 = q.1) :
    SamePortVertexRotationOrbit M p q :=
  ⟨hregion, M.rotation_reaches_same_region p q hregion⟩

theorem PortCombinatorialMap.connected_regions {P : PortNetwork}
    (M : PortCombinatorialMap P) (r s : Fin P.regionCount) :
    PortRegionReachable M.crossing r s :=
  M.connected r s

def PortHasCombinatorialGenus {P : PortNetwork}
    (M : PortCombinatorialMap P) (g : Nat) : Prop :=
  M.eulerCharacteristic = (2 : Int) - 2 * (g : Int)

theorem portCombinatorialGenus_unique {P : PortNetwork}
    (M : PortCombinatorialMap P) {g h : Nat}
    (hg : PortHasCombinatorialGenus M g)
    (hh : PortHasCombinatorialGenus M h) :
    g = h := by
  simp only [PortHasCombinatorialGenus] at hg hh
  omega

theorem portCombinatorialGenus_zero_iff {P : PortNetwork}
    (M : PortCombinatorialMap P) :
    PortHasCombinatorialGenus M 0 ↔ M.eulerCharacteristic = 2 := by
  simp [PortHasCombinatorialGenus]

theorem portCombinatorialGenus_one_iff {P : PortNetwork}
    (M : PortCombinatorialMap P) :
    PortHasCombinatorialGenus M 1 ↔ M.eulerCharacteristic = 0 := by
  simp [PortHasCombinatorialGenus]

theorem portCombinatorialGenus_characteristic_le_two
    {P : PortNetwork} (M : PortCombinatorialMap P) {g : Nat}
    (hg : PortHasCombinatorialGenus M g) :
    M.eulerCharacteristic ≤ 2 := by
  simp only [PortHasCombinatorialGenus] at hg
  omega

theorem portCombinatorialGenus_characteristic_even
    {P : PortNetwork} (M : PortCombinatorialMap P) {g : Nat}
    (hg : PortHasCombinatorialGenus M g) :
    Even M.eulerCharacteristic := by
  refine ⟨(1 : Int) - (g : Int), ?_⟩
  rw [hg]
  ring

def PortHasSphereCharacteristic {P : PortNetwork}
    (M : PortCombinatorialMap P) : Prop :=
  M.eulerCharacteristic = 2

theorem portHasSphereCharacteristic_iff_genus_zero {P : PortNetwork}
    (M : PortCombinatorialMap P) :
    PortHasSphereCharacteristic M ↔ PortHasCombinatorialGenus M 0 := by
  rw [PortHasSphereCharacteristic, (portCombinatorialGenus_zero_iff M).symm]

structure PortGenusZeroCombinatorialMap (P : PortNetwork) where
  map : PortCombinatorialMap P
  genusZero : PortHasCombinatorialGenus map 0

theorem PortGenusZeroCombinatorialMap.hasSphereCharacteristic
    {P : PortNetwork} (M : PortGenusZeroCombinatorialMap P) :
    PortHasSphereCharacteristic M.map :=
  (portHasSphereCharacteristic_iff_genus_zero M.map).mpr M.genusZero

def PortGenusZeroCombinatorialMap.crossing {P : PortNetwork}
    (M : PortGenusZeroCombinatorialMap P) : PortCrossing P :=
  M.map.crossing

def PortGenusZeroCombinatorialMap.rotation {P : PortNetwork}
    (M : PortGenusZeroCombinatorialMap P) : PortRotationSystem P :=
  M.map.rotation

def PortGenusZeroCombinatorialMap.vertexCount {P : PortNetwork}
    (M : PortGenusZeroCombinatorialMap P) : Nat :=
  M.map.vertexCount

def PortGenusZeroCombinatorialMap.edgeCount {P : PortNetwork}
    (M : PortGenusZeroCombinatorialMap P) : Nat :=
  M.map.edgeCount

def PortGenusZeroCombinatorialMap.faceCount {P : PortNetwork}
    (M : PortGenusZeroCombinatorialMap P) : Nat :=
  M.map.faceCount

def PortGenusZeroCombinatorialMap.portCount {P : PortNetwork}
    (M : PortGenusZeroCombinatorialMap P) : Nat :=
  M.map.portCount

def PortGenusZeroCombinatorialMap.eulerCharacteristic {P : PortNetwork}
    (M : PortGenusZeroCombinatorialMap P) : Int :=
  M.map.eulerCharacteristic

def FlowCombinatorialMap.toPortCombinatorialMap {N : FlowNetwork}
    (M : FlowCombinatorialMap N) :
    PortCombinatorialMap N.toPortNetwork where
  crossing := M.crossing.toPortCrossing
  rotation := M.rotation.toPortRotationSystem
  nonemptyRegions := M.nonemptyRegions
  connected := by
    intro r s
    exact flowRegionReachable_imp_port M.crossing (M.connected r s)

theorem FlowCombinatorialMap.toPortCombinatorialMap_vertexCount
    {N : FlowNetwork} (M : FlowCombinatorialMap N) :
    M.toPortCombinatorialMap.vertexCount = M.vertexCount := by
  rfl

theorem FlowCombinatorialMap.toPortCombinatorialMap_edgeCount
    {N : FlowNetwork} (M : FlowCombinatorialMap N) :
    M.toPortCombinatorialMap.edgeCount = M.edgeCount := by
  rfl

theorem FlowCombinatorialMap.toPortCombinatorialMap_faceCount
    {N : FlowNetwork} (M : FlowCombinatorialMap N) :
    M.toPortCombinatorialMap.faceCount = M.faceCount := by
  exact portFaceCount_of_flow_erasure M.rotation.toFlowLocalRotation M.crossing

theorem FlowCombinatorialMap.toPortCombinatorialMap_portCount
    {N : FlowNetwork} (M : FlowCombinatorialMap N) :
    M.toPortCombinatorialMap.portCount = M.portCount := by
  rfl

theorem FlowCombinatorialMap.toPortCombinatorialMap_eulerCharacteristic
    {N : FlowNetwork} (M : FlowCombinatorialMap N) :
    M.toPortCombinatorialMap.eulerCharacteristic = M.eulerCharacteristic := by
  exact portCombinatorialEulerCharacteristic_of_flow_erasure
    M.rotation.toFlowLocalRotation M.crossing

def PortCombinatorialMap.toFlowCombinatorialMap {P : PortNetwork}
    (M : PortCombinatorialMap P) (A : V4FlowAssignment M.crossing) :
    FlowCombinatorialMap A.toFlowNetwork where
  crossing := A.toFlowCrossing
  rotation := M.rotation.toFlowRotationSystem A
  nonemptyRegions := M.nonemptyRegions
  connected := by
    intro r s
    exact (portRegionReachable_iff_flow_lift A).mp (M.connected r s)

theorem PortCombinatorialMap.toFlowCombinatorialMap_vertexCount
    {P : PortNetwork} (M : PortCombinatorialMap P)
    (A : V4FlowAssignment M.crossing) :
    (M.toFlowCombinatorialMap A).vertexCount = M.vertexCount := by
  rfl

theorem PortCombinatorialMap.toFlowCombinatorialMap_edgeCount
    {P : PortNetwork} (M : PortCombinatorialMap P)
    (A : V4FlowAssignment M.crossing) :
    (M.toFlowCombinatorialMap A).edgeCount = M.edgeCount := by
  rfl

theorem PortCombinatorialMap.toFlowCombinatorialMap_faceCount
    {P : PortNetwork} (M : PortCombinatorialMap P)
    (A : V4FlowAssignment M.crossing) :
    (M.toFlowCombinatorialMap A).faceCount = M.faceCount := by
  exact (portFaceCount_of_flow_erasure
    (M.rotation.toFlowLocalRotation A) A.toFlowCrossing).symm

theorem PortCombinatorialMap.toFlowCombinatorialMap_portCount
    {P : PortNetwork} (M : PortCombinatorialMap P)
    (A : V4FlowAssignment M.crossing) :
    (M.toFlowCombinatorialMap A).portCount = M.portCount := by
  rfl

theorem PortCombinatorialMap.toFlowCombinatorialMap_eulerCharacteristic
    {P : PortNetwork} (M : PortCombinatorialMap P)
    (A : V4FlowAssignment M.crossing) :
    (M.toFlowCombinatorialMap A).eulerCharacteristic = M.eulerCharacteristic := by
  exact (portCombinatorialEulerCharacteristic_of_flow_erasure
    (M.rotation.toFlowLocalRotation A) A.toFlowCrossing).symm

theorem FlowCombinatorialMap.toPortCombinatorialMap_genus_iff
    {N : FlowNetwork} (M : FlowCombinatorialMap N) (g : Nat) :
    HasCombinatorialGenus M g ↔
      PortHasCombinatorialGenus M.toPortCombinatorialMap g := by
  unfold HasCombinatorialGenus PortHasCombinatorialGenus
  rw [M.toPortCombinatorialMap_eulerCharacteristic]

theorem FlowCombinatorialMap.toPortCombinatorialMap_sphere_iff
    {N : FlowNetwork} (M : FlowCombinatorialMap N) :
    HasSphereCharacteristic M ↔
      PortHasSphereCharacteristic M.toPortCombinatorialMap := by
  unfold HasSphereCharacteristic PortHasSphereCharacteristic
  rw [M.toPortCombinatorialMap_eulerCharacteristic]

theorem PortCombinatorialMap.toFlowCombinatorialMap_genus_iff
    {P : PortNetwork} (M : PortCombinatorialMap P)
    (A : V4FlowAssignment M.crossing) (g : Nat) :
    PortHasCombinatorialGenus M g ↔
      HasCombinatorialGenus (M.toFlowCombinatorialMap A) g := by
  unfold PortHasCombinatorialGenus HasCombinatorialGenus
  rw [M.toFlowCombinatorialMap_eulerCharacteristic]

theorem PortCombinatorialMap.toFlowCombinatorialMap_sphere_iff
    {P : PortNetwork} (M : PortCombinatorialMap P)
    (A : V4FlowAssignment M.crossing) :
    PortHasSphereCharacteristic M ↔
      HasSphereCharacteristic (M.toFlowCombinatorialMap A) := by
  unfold PortHasSphereCharacteristic HasSphereCharacteristic
  rw [M.toFlowCombinatorialMap_eulerCharacteristic]

theorem PortCombinatorialMap.toFlowCombinatorialMap_assignment_independent
    {P : PortNetwork} (M : PortCombinatorialMap P)
    (A B : V4FlowAssignment M.crossing) :
    (M.toFlowCombinatorialMap A).vertexCount =
        (M.toFlowCombinatorialMap B).vertexCount ∧
      (M.toFlowCombinatorialMap A).edgeCount =
        (M.toFlowCombinatorialMap B).edgeCount ∧
      (M.toFlowCombinatorialMap A).faceCount =
        (M.toFlowCombinatorialMap B).faceCount ∧
      (M.toFlowCombinatorialMap A).portCount =
        (M.toFlowCombinatorialMap B).portCount ∧
      (M.toFlowCombinatorialMap A).eulerCharacteristic =
        (M.toFlowCombinatorialMap B).eulerCharacteristic := by
  constructor
  · rw [M.toFlowCombinatorialMap_vertexCount,
      M.toFlowCombinatorialMap_vertexCount]
  constructor
  · rw [M.toFlowCombinatorialMap_edgeCount,
      M.toFlowCombinatorialMap_edgeCount]
  constructor
  · rw [M.toFlowCombinatorialMap_faceCount,
      M.toFlowCombinatorialMap_faceCount]
  constructor
  · rw [M.toFlowCombinatorialMap_portCount,
      M.toFlowCombinatorialMap_portCount]
  · rw [M.toFlowCombinatorialMap_eulerCharacteristic,
      M.toFlowCombinatorialMap_eulerCharacteristic]

theorem PortCombinatorialMap.toFlowCombinatorialMap_genus_assignment_independent
    {P : PortNetwork} (M : PortCombinatorialMap P)
    (A B : V4FlowAssignment M.crossing) (g : Nat) :
    HasCombinatorialGenus (M.toFlowCombinatorialMap A) g ↔
      HasCombinatorialGenus (M.toFlowCombinatorialMap B) g := by
  constructor
  · intro h
    exact (M.toFlowCombinatorialMap_genus_iff B g).mp
      ((M.toFlowCombinatorialMap_genus_iff A g).mpr h)
  · intro h
    exact (M.toFlowCombinatorialMap_genus_iff A g).mp
      ((M.toFlowCombinatorialMap_genus_iff B g).mpr h)

theorem PortCombinatorialMap.toFlowCombinatorialMap_sphere_assignment_independent
    {P : PortNetwork} (M : PortCombinatorialMap P)
    (A B : V4FlowAssignment M.crossing) :
    HasSphereCharacteristic (M.toFlowCombinatorialMap A) ↔
      HasSphereCharacteristic (M.toFlowCombinatorialMap B) := by
  constructor
  · intro h
    exact (M.toFlowCombinatorialMap_sphere_iff B).mp
      ((M.toFlowCombinatorialMap_sphere_iff A).mpr h)
  · intro h
    exact (M.toFlowCombinatorialMap_sphere_iff A).mp
      ((M.toFlowCombinatorialMap_sphere_iff B).mpr h)

theorem FlowCombinatorialMap.toPortCombinatorialMap_round_trip_cross
    {N : FlowNetwork} (M : FlowCombinatorialMap N)
    (p : PortNetworkPort N.toPortNetwork) :
    M.toPortCombinatorialMap.crossing.cross p =
      M.crossing.cross p := rfl

theorem FlowCombinatorialMap.toPortCombinatorialMap_round_trip_rotate
    {N : FlowNetwork} (M : FlowCombinatorialMap N)
    (p : PortNetworkPort N.toPortNetwork) :
    M.toPortCombinatorialMap.rotation.rotate p = M.rotation.rotate p := rfl

theorem PortCombinatorialMap.toFlowCombinatorialMap_round_trip_cross
    {P : PortNetwork} (M : PortCombinatorialMap P)
    (A : V4FlowAssignment M.crossing) (p : PortNetworkPort P) :
    (M.toFlowCombinatorialMap A).crossing.toPortCrossing.cross p =
      M.crossing.cross p := rfl

theorem PortCombinatorialMap.toFlowCombinatorialMap_round_trip_rotate
    {P : PortNetwork} (M : PortCombinatorialMap P)
    (A : V4FlowAssignment M.crossing) (p : PortNetworkPort P) :
    (M.toFlowCombinatorialMap A).rotation.toPortRotationSystem.rotate p =
      M.rotation.rotate p := rfl

end DkMath.Tromino
