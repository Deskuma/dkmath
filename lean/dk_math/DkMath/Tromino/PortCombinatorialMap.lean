/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortEulerCount
import DkMath.Tromino.PortRegionWalk
import DkMath.Tromino.CombinatorialMap

#print "file: DkMath.Tromino.PortCombinatorialMap"

/-!
# Port combinatorial maps

A `PortCombinatorialMap` packages a crossing involution, a cyclic local
rotation at every region, positivity of the vertex set, and region
connectedness.  It is the finite rotation-system substitute for a connected
embedded graph: regions act as vertices, crossing orbits as edges, and
face-step orbits as faces.  Its Euler characteristic and genus-zero
predicates are therefore combinatorial certificates with no implicit
topological realization claim.
-/

namespace DkMath.Tromino

/-- A connected finite rotation system on a port network.

The crossing and rotation give the two permutations of the dart model.
`nonemptyRegions` rules out the empty vertex carrier, while `connected`
states that every pair of region cells is joined by a finite crossing walk.
-/
structure PortCombinatorialMap (P : PortNetwork) where
  crossing : PortCrossing P
  rotation : PortRotationSystem P
  nonemptyRegions : 0 < P.regionCount
  connected : PortRegionConnected crossing

/-- The local rotation component of a port map.

This is the permutation used at a vertex when constructing the global face
step.  It forgets only the cyclicity proof carried by the larger structure.
-/
def PortCombinatorialMap.localRotation {P : PortNetwork}
    (M : PortCombinatorialMap P) : PortLocalRotation P :=
  M.rotation.toPortLocalRotation

/-- Number of vertices, namely the regions of the port network.

The port map's vertex cells are indexed directly by its regions. -/
def PortCombinatorialMap.vertexCount {P : PortNetwork}
    (_M : PortCombinatorialMap P) : Nat :=
  portRegionVertexCount P

/-- Number of edges, namely crossing orbits.

An edge is an orbit of the fixed-point-free crossing involution, so each
edge is represented by its two incident ports. -/
def PortCombinatorialMap.edgeCount {P : PortNetwork}
    (M : PortCombinatorialMap P) : Nat :=
  portCrossingEdgeCount M.crossing

/-- Number of faces, namely face-step orbits.

Faces are the finite cyclic orbits of crossing followed by local rotation.
-/
def PortCombinatorialMap.faceCount {P : PortNetwork}
    (M : PortCombinatorialMap P) : Nat :=
  portFaceCount M.localRotation M.crossing

/-- Number of darts in the finite port carrier. -/
def PortCombinatorialMap.portCount {P : PortNetwork}
    (_M : PortCombinatorialMap P) : Nat :=
  P.portCount

/-- The combinatorial Euler characteristic `V - E + F`.

This delegates to the partition counts of `PortEulerCount`; it is an
integer because later genus identities use subtraction. -/
def PortCombinatorialMap.eulerCharacteristic {P : PortNetwork}
    (M : PortCombinatorialMap P) : Int :=
  portCombinatorialEulerCharacteristic M.localRotation M.crossing

/-- Same-region reachability under the local vertex rotation. -/
def SamePortVertexRotationOrbit {P : PortNetwork}
    (M : PortCombinatorialMap P) (p q : PortNetworkPort P) : Prop :=
  p.1 = q.1 ∧
    ∃ n : Nat, (M.localRotation.rotate^[n]) p = q

/-- Cyclicity reaches every slot in a fixed region. -/
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

/-- Equal region indices give the same vertex rotation orbit. -/
theorem PortCombinatorialMap.sameVertexRotationOrbit_of_same_region
    {P : PortNetwork} (M : PortCombinatorialMap P)
    (p q : PortNetworkPort P) (hregion : p.1 = q.1) :
    SamePortVertexRotationOrbit M p q :=
  ⟨hregion, M.rotation_reaches_same_region p q hregion⟩

/-- The map's connectedness gives region reachability. -/
theorem PortCombinatorialMap.connected_regions {P : PortNetwork}
    (M : PortCombinatorialMap P) (r s : Fin P.regionCount) :
    PortRegionReachable M.crossing r s :=
  M.connected r s

/-- Genus `g` is encoded by the Euler identity `χ = 2 - 2g`.

This is a certificate predicate on finite counts.  It does not assert that
the combinatorial map has already been realized as a surface. -/
def PortHasCombinatorialGenus {P : PortNetwork}
    (M : PortCombinatorialMap P) (g : Nat) : Prop :=
  M.eulerCharacteristic = (2 : Int) - 2 * (g : Int)

/-- The genus parameter satisfying the Euler identity is unique. -/
theorem portCombinatorialGenus_unique {P : PortNetwork}
    (M : PortCombinatorialMap P) {g h : Nat}
    (hg : PortHasCombinatorialGenus M g)
    (hh : PortHasCombinatorialGenus M h) :
    g = h := by
  simp only [PortHasCombinatorialGenus] at hg hh
  omega

/-- Genus zero is equivalent to Euler characteristic two. -/
theorem portCombinatorialGenus_zero_iff {P : PortNetwork}
    (M : PortCombinatorialMap P) :
    PortHasCombinatorialGenus M 0 ↔ M.eulerCharacteristic = 2 := by
  simp [PortHasCombinatorialGenus]

/-- Genus one is equivalent to Euler characteristic zero. -/
theorem portCombinatorialGenus_one_iff {P : PortNetwork}
    (M : PortCombinatorialMap P) :
    PortHasCombinatorialGenus M 1 ↔ M.eulerCharacteristic = 0 := by
  simp [PortHasCombinatorialGenus]

/-- Any certified combinatorial genus has characteristic at most two. -/
theorem portCombinatorialGenus_characteristic_le_two
    {P : PortNetwork} (M : PortCombinatorialMap P) {g : Nat}
    (hg : PortHasCombinatorialGenus M g) :
    M.eulerCharacteristic ≤ 2 := by
  simp only [PortHasCombinatorialGenus] at hg
  omega

/-- A certified orientable genus gives an even Euler characteristic. -/
theorem portCombinatorialGenus_characteristic_even
    {P : PortNetwork} (M : PortCombinatorialMap P) {g : Nat}
    (hg : PortHasCombinatorialGenus M g) :
    Even M.eulerCharacteristic := by
  refine ⟨(1 : Int) - (g : Int), ?_⟩
  rw [hg]
  ring

/-- The sphere characteristic predicate. -/
def PortHasSphereCharacteristic {P : PortNetwork}
    (M : PortCombinatorialMap P) : Prop :=
  M.eulerCharacteristic = 2

/-- Sphere characteristic and genus zero are equivalent predicates. -/
theorem portHasSphereCharacteristic_iff_genus_zero {P : PortNetwork}
    (M : PortCombinatorialMap P) :
    PortHasSphereCharacteristic M ↔ PortHasCombinatorialGenus M 0 := by
  rw [PortHasSphereCharacteristic, (portCombinatorialGenus_zero_iff M).symm]

/-- A packaged connected map carrying its genus-zero certificate.

The structure keeps the map data and the equation `χ = 2` together, making
the sphere-characteristic assumption explicit at every later use. -/
structure PortGenusZeroCombinatorialMap (P : PortNetwork) where
  map : PortCombinatorialMap P
  genusZero : PortHasCombinatorialGenus map 0

/-- A genus-zero certificate implies sphere characteristic. -/
theorem PortGenusZeroCombinatorialMap.hasSphereCharacteristic
    {P : PortNetwork} (M : PortGenusZeroCombinatorialMap P) :
    PortHasSphereCharacteristic M.map :=
  (portHasSphereCharacteristic_iff_genus_zero M.map).mpr M.genusZero

/-- The crossing of a genus-zero map. -/
def PortGenusZeroCombinatorialMap.crossing {P : PortNetwork}
    (M : PortGenusZeroCombinatorialMap P) : PortCrossing P :=
  M.map.crossing

/-- The rotation system of a genus-zero map. -/
def PortGenusZeroCombinatorialMap.rotation {P : PortNetwork}
    (M : PortGenusZeroCombinatorialMap P) : PortRotationSystem P :=
  M.map.rotation

/-- Vertex count inherited by a genus-zero map. -/
def PortGenusZeroCombinatorialMap.vertexCount {P : PortNetwork}
    (M : PortGenusZeroCombinatorialMap P) : Nat :=
  M.map.vertexCount

/-- Edge count inherited by a genus-zero map. -/
def PortGenusZeroCombinatorialMap.edgeCount {P : PortNetwork}
    (M : PortGenusZeroCombinatorialMap P) : Nat :=
  M.map.edgeCount

/-- Face count inherited by a genus-zero map. -/
def PortGenusZeroCombinatorialMap.faceCount {P : PortNetwork}
    (M : PortGenusZeroCombinatorialMap P) : Nat :=
  M.map.faceCount

/-- Port count inherited by a genus-zero map. -/
def PortGenusZeroCombinatorialMap.portCount {P : PortNetwork}
    (M : PortGenusZeroCombinatorialMap P) : Nat :=
  M.map.portCount

/-- Euler characteristic inherited by a genus-zero map. -/
def PortGenusZeroCombinatorialMap.eulerCharacteristic {P : PortNetwork}
    (M : PortGenusZeroCombinatorialMap P) : Int :=
  M.map.eulerCharacteristic

/-- Convert a flow combinatorial map into the port presentation.

Labels are erased, but the crossing involution, local rotation, region
nonemptiness, and connectivity are retained.  Thus the port map exposes
the finite incidence structure underlying the flow map. -/
def FlowCombinatorialMap.toPortCombinatorialMap {N : FlowNetwork}
    (M : FlowCombinatorialMap N) :
    PortCombinatorialMap N.toPortNetwork where
  crossing := M.crossing.toPortCrossing
  rotation := M.rotation.toPortRotationSystem
  nonemptyRegions := M.nonemptyRegions
  connected := by
    intro r s
    exact flowRegionReachable_imp_port M.crossing (M.connected r s)

/-- The conversion preserves vertex count. -/
theorem FlowCombinatorialMap.toPortCombinatorialMap_vertexCount
    {N : FlowNetwork} (M : FlowCombinatorialMap N) :
    M.toPortCombinatorialMap.vertexCount = M.vertexCount := by
  rfl

/-- The conversion preserves edge count. -/
theorem FlowCombinatorialMap.toPortCombinatorialMap_edgeCount
    {N : FlowNetwork} (M : FlowCombinatorialMap N) :
    M.toPortCombinatorialMap.edgeCount = M.edgeCount := by
  rfl

/-- The conversion preserves face count. -/
theorem FlowCombinatorialMap.toPortCombinatorialMap_faceCount
    {N : FlowNetwork} (M : FlowCombinatorialMap N) :
    M.toPortCombinatorialMap.faceCount = M.faceCount := by
  exact portFaceCount_of_flow_erasure M.rotation.toFlowLocalRotation M.crossing

/-- The conversion preserves port count. -/
theorem FlowCombinatorialMap.toPortCombinatorialMap_portCount
    {N : FlowNetwork} (M : FlowCombinatorialMap N) :
    M.toPortCombinatorialMap.portCount = M.portCount := by
  rfl

/-- The conversion preserves Euler characteristic. -/
theorem FlowCombinatorialMap.toPortCombinatorialMap_eulerCharacteristic
    {N : FlowNetwork} (M : FlowCombinatorialMap N) :
    M.toPortCombinatorialMap.eulerCharacteristic = M.eulerCharacteristic := by
  exact portCombinatorialEulerCharacteristic_of_flow_erasure
    M.rotation.toFlowLocalRotation M.crossing

/-- Restore a port map as a flow combinatorial map using an assignment.

An edge-constant nonzero V4 assignment supplies exactly the label data
needed to rebuild the flow signature; all map permutations and connectivity
proofs are lifted from the port map. -/
def PortCombinatorialMap.toFlowCombinatorialMap {P : PortNetwork}
    (M : PortCombinatorialMap P) (A : V4FlowAssignment M.crossing) :
    FlowCombinatorialMap A.toFlowNetwork where
  crossing := A.toFlowCrossing
  rotation := M.rotation.toFlowRotationSystem A
  nonemptyRegions := M.nonemptyRegions
  connected := by
    intro r s
    exact (portRegionReachable_iff_flow_lift A).mp (M.connected r s)

/-- The lifted flow map has the same vertex count as the port map. -/
theorem PortCombinatorialMap.toFlowCombinatorialMap_vertexCount
    {P : PortNetwork} (M : PortCombinatorialMap P)
    (A : V4FlowAssignment M.crossing) :
    (M.toFlowCombinatorialMap A).vertexCount = M.vertexCount := by
  rfl

/-- The lifted flow map has the same edge count as the port map. -/
theorem PortCombinatorialMap.toFlowCombinatorialMap_edgeCount
    {P : PortNetwork} (M : PortCombinatorialMap P)
    (A : V4FlowAssignment M.crossing) :
    (M.toFlowCombinatorialMap A).edgeCount = M.edgeCount := by
  rfl

/-- The lifted flow map has the same face count as the port map. -/
theorem PortCombinatorialMap.toFlowCombinatorialMap_faceCount
    {P : PortNetwork} (M : PortCombinatorialMap P)
    (A : V4FlowAssignment M.crossing) :
    (M.toFlowCombinatorialMap A).faceCount = M.faceCount := by
  exact (portFaceCount_of_flow_erasure
    (M.rotation.toFlowLocalRotation A) A.toFlowCrossing).symm

/-- The lifted flow map has the same port count as the port map. -/
theorem PortCombinatorialMap.toFlowCombinatorialMap_portCount
    {P : PortNetwork} (M : PortCombinatorialMap P)
    (A : V4FlowAssignment M.crossing) :
    (M.toFlowCombinatorialMap A).portCount = M.portCount := by
  rfl

/-- The lifted flow map has the same Euler characteristic as the port map. -/
theorem PortCombinatorialMap.toFlowCombinatorialMap_eulerCharacteristic
    {P : PortNetwork} (M : PortCombinatorialMap P)
    (A : V4FlowAssignment M.crossing) :
    (M.toFlowCombinatorialMap A).eulerCharacteristic = M.eulerCharacteristic := by
  exact (portCombinatorialEulerCharacteristic_of_flow_erasure
    (M.rotation.toFlowLocalRotation A) A.toFlowCrossing).symm

/-- Genus certification is preserved by conversion to the port presentation. -/
theorem FlowCombinatorialMap.toPortCombinatorialMap_genus_iff
    {N : FlowNetwork} (M : FlowCombinatorialMap N) (g : Nat) :
    HasCombinatorialGenus M g ↔
      PortHasCombinatorialGenus M.toPortCombinatorialMap g := by
  unfold HasCombinatorialGenus PortHasCombinatorialGenus
  rw [M.toPortCombinatorialMap_eulerCharacteristic]

/-- Sphere characteristic is preserved by conversion to the port presentation. -/
theorem FlowCombinatorialMap.toPortCombinatorialMap_sphere_iff
    {N : FlowNetwork} (M : FlowCombinatorialMap N) :
    HasSphereCharacteristic M ↔
      PortHasSphereCharacteristic M.toPortCombinatorialMap := by
  unfold HasSphereCharacteristic PortHasSphereCharacteristic
  rw [M.toPortCombinatorialMap_eulerCharacteristic]

/-- Genus certification is preserved by a flow lift of a port map. -/
theorem PortCombinatorialMap.toFlowCombinatorialMap_genus_iff
    {P : PortNetwork} (M : PortCombinatorialMap P)
    (A : V4FlowAssignment M.crossing) (g : Nat) :
    PortHasCombinatorialGenus M g ↔
      HasCombinatorialGenus (M.toFlowCombinatorialMap A) g := by
  unfold PortHasCombinatorialGenus HasCombinatorialGenus
  rw [M.toFlowCombinatorialMap_eulerCharacteristic]

/-- Sphere characteristic is preserved by a flow lift of a port map. -/
theorem PortCombinatorialMap.toFlowCombinatorialMap_sphere_iff
    {P : PortNetwork} (M : PortCombinatorialMap P)
    (A : V4FlowAssignment M.crossing) :
    PortHasSphereCharacteristic M ↔
      HasSphereCharacteristic (M.toFlowCombinatorialMap A) := by
  unfold PortHasSphereCharacteristic HasSphereCharacteristic
  rw [M.toFlowCombinatorialMap_eulerCharacteristic]

/-- All numerical map invariants are independent of the chosen flow assignment.

The assignment changes only the decoration of the same finite port map, so
vertex, edge, face, dart, and Euler counts are identical for any two valid
choices. -/
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

/-- The genus predicate is independent of the chosen flow assignment. -/
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

/-- The sphere predicate is independent of the chosen flow assignment. -/
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

/-- The crossing involution is unchanged by a flow-to-port round trip. -/
theorem FlowCombinatorialMap.toPortCombinatorialMap_round_trip_cross
    {N : FlowNetwork} (M : FlowCombinatorialMap N)
    (p : PortNetworkPort N.toPortNetwork) :
    M.toPortCombinatorialMap.crossing.cross p =
      M.crossing.cross p := rfl

/-- The rotation is unchanged by a flow-to-port round trip. -/
theorem FlowCombinatorialMap.toPortCombinatorialMap_round_trip_rotate
    {N : FlowNetwork} (M : FlowCombinatorialMap N)
    (p : PortNetworkPort N.toPortNetwork) :
    M.toPortCombinatorialMap.rotation.rotate p = M.rotation.rotate p := rfl

/-- The crossing involution is unchanged by a port-to-flow round trip. -/
theorem PortCombinatorialMap.toFlowCombinatorialMap_round_trip_cross
    {P : PortNetwork} (M : PortCombinatorialMap P)
    (A : V4FlowAssignment M.crossing) (p : PortNetworkPort P) :
    (M.toFlowCombinatorialMap A).crossing.toPortCrossing.cross p =
      M.crossing.cross p := rfl

/-- The rotation is unchanged by a port-to-flow round trip. -/
theorem PortCombinatorialMap.toFlowCombinatorialMap_round_trip_rotate
    {P : PortNetwork} (M : PortCombinatorialMap P)
    (A : V4FlowAssignment M.crossing) (p : PortNetworkPort P) :
    (M.toFlowCombinatorialMap A).rotation.toPortRotationSystem.rotate p =
      M.rotation.rotate p := rfl

end DkMath.Tromino
