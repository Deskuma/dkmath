/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortFaceOrbit
import DkMath.Tromino.EulerCount

#print "file: DkMath.Tromino.PortEulerCount"

/-!
# Finite Euler counts

Crossing orbits are the edges, local-rotation orbits are the faces, and
regions are the vertices of a port combinatorial map.  The finite-set
lemmas here establish the corresponding partitions and define the Euler
characteristic `V - E + F`; later modules use this integer as the genus-zero
certificate rather than as a topological assertion.
-/

namespace DkMath.Tromino

/-- The vertex count of a port map is its number of regions. -/
def portRegionVertexCount (P : PortNetwork) : Nat := P.regionCount

/-- The two-dart carrier of one crossing edge. -/
def portCrossingEdgePair {P : PortNetwork} (C : PortCrossing P)
    (p : PortNetworkPort P) : Finset (PortNetworkPort P) := {p, C.cross p}

/-- A crossing port belongs to its edge pair. -/
theorem portCrossingEdgePair_mem {P : PortNetwork} (C : PortCrossing P)
    (p : PortNetworkPort P) : p ∈ portCrossingEdgePair C p := by
  simp [portCrossingEdgePair]

/-- The crossed port belongs to the same edge pair. -/
theorem portCrossingEdgePair_cross_mem {P : PortNetwork} (C : PortCrossing P)
    (p : PortNetworkPort P) : C.cross p ∈ portCrossingEdgePair C p := by
  simp [portCrossingEdgePair]

/-- Every crossing edge pair has exactly two darts. -/
theorem portCrossingEdgePair_card {P : PortNetwork} (C : PortCrossing P)
    (p : PortNetworkPort P) : (portCrossingEdgePair C p).card = 2 := by
  have hne : p ≠ C.cross p := (C.cross_ne p).symm
  simp [portCrossingEdgePair, hne]

/-- Crossing either endpoint gives the same edge pair. -/
theorem portCrossingEdgePair_cross_eq {P : PortNetwork}
    (C : PortCrossing P) (p : PortNetworkPort P) :
    portCrossingEdgePair C (C.cross p) = portCrossingEdgePair C p := by
  ext q
  simp [portCrossingEdgePair, C.involutive p, or_comm]

/-- Any dart in an edge pair identifies that same pair. -/
theorem portCrossingEdgePair_eq_of_mem {P : PortNetwork}
    (C : PortCrossing P) (p q : PortNetworkPort P)
    (hq : q ∈ portCrossingEdgePair C p) :
    portCrossingEdgePair C q = portCrossingEdgePair C p := by
  simp only [portCrossingEdgePair, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · rfl
  · exact portCrossingEdgePair_cross_eq C p

/-- Crossing edge pairs partition the port carrier. -/
theorem portCrossingEdgePair_eq_or_disjoint {P : PortNetwork}
    (C : PortCrossing P) (p q : PortNetworkPort P) :
    portCrossingEdgePair C p = portCrossingEdgePair C q ∨
      Disjoint (portCrossingEdgePair C p) (portCrossingEdgePair C q) := by
  by_cases h : portCrossingEdgePair C p = portCrossingEdgePair C q
  · exact Or.inl h
  · right
    refine Finset.disjoint_left.mpr ?_
    intro x hxp hxq
    apply h
    exact (portCrossingEdgePair_eq_of_mem C p x hxp).symm.trans
      (portCrossingEdgePair_eq_of_mem C q x hxq)

/-- The finite set of crossing edge orbits. -/
def portCrossingEdgeOrbits {P : PortNetwork} (C : PortCrossing P) :
    Finset (Finset (PortNetworkPort P)) :=
  Finset.univ.image (portCrossingEdgePair C)

/-- Number of crossing edges. -/
def portCrossingEdgeCount {P : PortNetwork} (C : PortCrossing P) : Nat :=
  (portCrossingEdgeOrbits C).card

/-- Every crossing pair is one of the edge orbits. -/
theorem portCrossingEdgePair_mem_orbits {P : PortNetwork}
    (C : PortCrossing P) (p : PortNetworkPort P) :
    portCrossingEdgePair C p ∈ portCrossingEdgeOrbits C := by
  apply Finset.mem_image.mpr
  exact ⟨p, Finset.mem_univ p, rfl⟩

/-- Orbit membership is equivalent to being a crossing edge pair. -/
theorem portCrossingEdgeOrbits_mem_iff {P : PortNetwork}
    (C : PortCrossing P) (E : Finset (PortNetworkPort P)) :
    E ∈ portCrossingEdgeOrbits C ↔
      ∃ p : PortNetworkPort P, E = portCrossingEdgePair C p := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨p, _, rfl⟩
    exact ⟨p, rfl⟩
  · rintro ⟨p, rfl⟩
    exact portCrossingEdgePair_mem_orbits C p

/-- Edge orbits cover every port. -/
theorem portCrossingEdgeOrbits_coverage {P : PortNetwork}
    (C : PortCrossing P) (p : PortNetworkPort P) :
    ∃ E ∈ portCrossingEdgeOrbits C, p ∈ E :=
  ⟨portCrossingEdgePair C p, portCrossingEdgePair_mem_orbits C p,
    portCrossingEdgePair_mem C p⟩

/-- Distinct edge orbits are pairwise disjoint. -/
theorem portCrossingEdgeOrbits_pairwise_disjoint {P : PortNetwork}
    (C : PortCrossing P) :
    ((portCrossingEdgeOrbits C : Finset (Finset (PortNetworkPort P))) : Set
      (Finset (PortNetworkPort P))).Pairwise Disjoint := by
  intro E hE F hF hne
  rcases (portCrossingEdgeOrbits_mem_iff C E).mp hE with ⟨p, rfl⟩
  rcases (portCrossingEdgeOrbits_mem_iff C F).mp hF with ⟨q, rfl⟩
  exact (portCrossingEdgePair_eq_or_disjoint C p q).resolve_left hne

/-- The union of edge orbits is the complete port carrier. -/
theorem portCrossingEdgeOrbits_biUnion {P : PortNetwork}
    (C : PortCrossing P) :
    (portCrossingEdgeOrbits C).biUnion id = Finset.univ := by
  ext p
  constructor
  · intro _
    exact Finset.mem_univ p
  · intro _
    rcases portCrossingEdgeOrbits_coverage C p with ⟨E, hE, hp⟩
    exact Finset.mem_biUnion.mpr ⟨E, hE, hp⟩

/-- The sum of edge-orbit cardinalities equals twice the edge count. -/
theorem portCrossingEdgeSum_card {P : PortNetwork} (C : PortCrossing P) :
    (∑ E ∈ portCrossingEdgeOrbits C, E.card) = P.portCount := by
  rw [sum_card_eq_card_univ_of_pairwise_disjoint_cover
    (portCrossingEdgeOrbits C) (portCrossingEdgeOrbits_pairwise_disjoint C)
    (portCrossingEdgeOrbits_biUnion C)]
  rfl

/-- Port count is twice the crossing-edge count. -/
theorem portCrossingEdgeCount_mul_two {P : PortNetwork}
    (C : PortCrossing P) :
    portCrossingEdgeCount C * 2 = P.portCount := by
  calc
    portCrossingEdgeCount C * 2 =
        ∑ E ∈ portCrossingEdgeOrbits C, 2 := by
          simp [portCrossingEdgeCount, Nat.mul_comm]
    _ = ∑ E ∈ portCrossingEdgeOrbits C, E.card := by
      apply Finset.sum_congr rfl
      intro E hE
      rcases (portCrossingEdgeOrbits_mem_iff C E).mp hE with ⟨p, rfl⟩
      exact (portCrossingEdgePair_card C p).symm
    _ = P.portCount := portCrossingEdgeSum_card C

/-- Symmetric form of the two-darts-per-edge identity. -/
theorem two_mul_portCrossingEdgeCount {P : PortNetwork}
    (C : PortCrossing P) :
    2 * portCrossingEdgeCount C = P.portCount := by
  simpa [Nat.mul_comm] using portCrossingEdgeCount_mul_two C

/-- The finite set of face-step orbits. -/
def portFaceOrbits {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) :
    Finset (Finset (PortNetworkPort P)) :=
  Finset.univ.image (portFaceOrbit R C)

/-- Number of face orbits. -/
def portFaceCount {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) : Nat :=
  (portFaceOrbits R C).card

/-- Every individual face orbit belongs to the orbit collection. -/
theorem portFaceOrbit_mem_orbits {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) :
    portFaceOrbit R C p ∈ portFaceOrbits R C := by
  apply Finset.mem_image.mpr
  exact ⟨p, Finset.mem_univ p, rfl⟩

/-- Face-orbit membership is characterized by orbit equality. -/
theorem portFaceOrbits_mem_iff {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (F : Finset (PortNetworkPort P)) :
    F ∈ portFaceOrbits R C ↔
      ∃ p : PortNetworkPort P, F = portFaceOrbit R C p := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨p, _, rfl⟩
    exact ⟨p, rfl⟩
  · rintro ⟨p, rfl⟩
    exact portFaceOrbit_mem_orbits R C p

/-- Face orbits cover every port. -/
theorem portFaceOrbits_coverage {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) :
    ∃ F ∈ portFaceOrbits R C, p ∈ F :=
  ⟨portFaceOrbit R C p, portFaceOrbit_mem_orbits R C p,
    portFaceOrbit_contains R C p⟩

/-- Distinct face orbits are pairwise disjoint. -/
theorem portFaceOrbits_pairwise_disjoint {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P) :
    ((portFaceOrbits R C : Finset (Finset (PortNetworkPort P))) : Set
      (Finset (PortNetworkPort P))).Pairwise Disjoint := by
  intro F hF G hG hne
  rcases (portFaceOrbits_mem_iff R C F).mp hF with ⟨p, rfl⟩
  rcases (portFaceOrbits_mem_iff R C G).mp hG with ⟨q, rfl⟩
  exact (portFaceOrbit_eq_or_disjoint R C p q).resolve_left hne

/-- The union of face orbits is the complete port carrier. -/
theorem portFaceOrbits_biUnion {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P) :
    (portFaceOrbits R C).biUnion id = Finset.univ := by
  ext p
  constructor
  · intro _
    exact Finset.mem_univ p
  · intro _
    rcases portFaceOrbits_coverage R C p with ⟨F, hF, hp⟩
    exact Finset.mem_biUnion.mpr ⟨F, hF, hp⟩

/-- The sum of face-orbit cardinalities equals the port count. -/
theorem portFaceSum_card {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) :
    (∑ F ∈ portFaceOrbits R C, F.card) = P.portCount := by
  rw [sum_card_eq_card_univ_of_pairwise_disjoint_cover
    (portFaceOrbits R C) (portFaceOrbits_pairwise_disjoint R C)
    (portFaceOrbits_biUnion R C)]
  rfl

/-- The finite Euler characteristic `V - E + F`. -/
def portCombinatorialEulerCharacteristic {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P) : Int :=
  (portRegionVertexCount P : Int)
    - (portCrossingEdgeCount C : Int)
    + (portFaceCount R C : Int)

/-- Expanded formula for the port Euler characteristic. -/
theorem portCombinatorialEulerCharacteristic_eq {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P) :
    portCombinatorialEulerCharacteristic R C =
      (portRegionVertexCount P : Int) - (portCrossingEdgeCount C : Int)
        + (portFaceCount R C : Int) := rfl

/-- Flow erasure preserves the total port count. -/
theorem portCount_of_flow_erasure {N : FlowNetwork} :
    N.toPortNetwork.portCount = totalPortCount N := rfl

/-- Flow erasure identifies a crossing pair with its port-level pair. -/
theorem portCrossingEdgePair_of_flow_erasure {N : FlowNetwork}
    (C : FlowCrossing N) (p : PortNetworkPort N.toPortNetwork) :
    portCrossingEdgePair C.toPortCrossing p = crossingEdgePair C p := rfl

/-- Flow erasure identifies port crossing orbits with flow crossing orbits. -/
theorem portCrossingEdgeOrbits_of_flow_erasure {N : FlowNetwork}
    (C : FlowCrossing N) :
    portCrossingEdgeOrbits C.toPortCrossing = crossingEdgeOrbits C := rfl

/-- Flow erasure preserves the number of crossing edge orbits. -/
theorem portCrossingEdgeCount_of_flow_erasure {N : FlowNetwork}
    (C : FlowCrossing N) :
    portCrossingEdgeCount C.toPortCrossing = crossingEdgeCount C := rfl

/-- Flow erasure identifies port face orbits with flow face orbits. -/
theorem portFaceOrbits_of_flow_erasure {N : FlowNetwork}
    (R : FlowLocalRotation N) (C : FlowCrossing N) :
    portFaceOrbits R.toPortLocalRotation C.toPortCrossing = faceOrbits R C := by
  ext F
  constructor
  · intro hF
    rcases (portFaceOrbits_mem_iff R.toPortLocalRotation C.toPortCrossing F).mp hF
      with ⟨p, rfl⟩
    rw [portFaceOrbit_of_flow_erasure R C p]
    exact faceOrbit_mem_orbits R C p
  · intro hF
    rcases (faceOrbits_mem_iff R C F).mp hF with ⟨p, rfl⟩
    rw [← portFaceOrbit_of_flow_erasure R C p]
    exact portFaceOrbit_mem_orbits R.toPortLocalRotation C.toPortCrossing p

/-- Flow erasure preserves the number of face orbits. -/
theorem portFaceCount_of_flow_erasure {N : FlowNetwork}
    (R : FlowLocalRotation N) (C : FlowCrossing N) :
    portFaceCount R.toPortLocalRotation C.toPortCrossing = faceCount R C := by
  unfold portFaceCount faceCount
  rw [portFaceOrbits_of_flow_erasure]
  rfl

/-- The port Euler characteristic agrees with its flow-erased form. -/
theorem portCombinatorialEulerCharacteristic_of_flow_erasure
    {N : FlowNetwork} (R : FlowLocalRotation N) (C : FlowCrossing N) :
    portCombinatorialEulerCharacteristic R.toPortLocalRotation C.toPortCrossing =
      combinatorialEulerCharacteristic R C := by
  unfold portCombinatorialEulerCharacteristic combinatorialEulerCharacteristic
    portRegionVertexCount regionVertexCount
  rw [portCrossingEdgeCount_of_flow_erasure,
    portFaceCount_of_flow_erasure]
  rfl

/-- A V4 flow lift has the port Euler characteristic of its source map. -/
theorem combinatorialEulerCharacteristic_of_flow_lift
    {P : PortNetwork} {C : PortCrossing P} (R : PortLocalRotation P)
    (A : V4FlowAssignment C) :
    combinatorialEulerCharacteristic (R.toFlowLocalRotation A)
      A.toFlowCrossing = portCombinatorialEulerCharacteristic R C := by
  rw [← portCombinatorialEulerCharacteristic_of_flow_erasure
    (R := R.toFlowLocalRotation A) (C := A.toFlowCrossing)]
  rfl

/-- The combinatorial Euler characteristic is independent of the flow assignment. -/
theorem combinatorialEulerCharacteristic_assignment_independent
    {P : PortNetwork} {C : PortCrossing P} (R : PortLocalRotation P)
    (A B : V4FlowAssignment C) :
    combinatorialEulerCharacteristic (R.toFlowLocalRotation A)
      A.toFlowCrossing =
      combinatorialEulerCharacteristic (R.toFlowLocalRotation B)
        B.toFlowCrossing := by
  rw [combinatorialEulerCharacteristic_of_flow_lift,
    combinatorialEulerCharacteristic_of_flow_lift]

end DkMath.Tromino
