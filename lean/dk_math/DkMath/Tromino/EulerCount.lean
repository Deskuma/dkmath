/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.FaceOrbit

#print "file: DkMath.Tromino.EulerCount"

/-!
# Finite Euler counts for flow maps

Crossing involution orbits are edges, local face-step orbits are faces, and
regions are vertices.  The finite-set partition lemmas establish the counts
and the identity `2E = D`, leading to the combinatorial Euler characteristic
`V - E + F`.
-/

namespace DkMath.Tromino

/-- Number of vertices, namely the number of regions. -/
def regionVertexCount (N : FlowNetwork) : Nat := N.regionCount

/-- The two-port orbit of one crossing edge. -/
def crossingEdgePair {N : FlowNetwork} (C : FlowCrossing N)
    (p : FlowNetworkPort N) : Finset (FlowNetworkPort N) := {p, C.cross p}

/-- A crossing port belongs to its edge pair. -/
theorem crossingEdgePair_mem {N : FlowNetwork} (C : FlowCrossing N)
    (p : FlowNetworkPort N) : p ∈ crossingEdgePair C p := by
  simp [crossingEdgePair]

/-- The crossed port belongs to the same edge pair. -/
theorem crossingEdgePair_cross_mem {N : FlowNetwork} (C : FlowCrossing N)
    (p : FlowNetworkPort N) : C.cross p ∈ crossingEdgePair C p := by
  simp [crossingEdgePair]

/-- Every crossing edge pair has two ports. -/
theorem crossingEdgePair_card {N : FlowNetwork} (C : FlowCrossing N)
    (p : FlowNetworkPort N) : (crossingEdgePair C p).card = 2 := by
  have hne : p ≠ C.cross p := by
    intro h
    apply C.changesRegion p
    exact (congrArg Sigma.fst h).symm
  simp [crossingEdgePair, hne]

/-- Both endpoints determine the same crossing edge pair. -/
theorem crossingEdgePair_cross_eq {N : FlowNetwork} (C : FlowCrossing N)
    (p : FlowNetworkPort N) :
    crossingEdgePair C (C.cross p) = crossingEdgePair C p := by
  ext q
  simp [crossingEdgePair, C.involutive p, or_comm]

/-- Any port in an edge pair identifies that pair. -/
theorem crossingEdgePair_eq_of_mem {N : FlowNetwork} (C : FlowCrossing N)
    (p q : FlowNetworkPort N) (hq : q ∈ crossingEdgePair C p) :
    crossingEdgePair C q = crossingEdgePair C p := by
  simp only [crossingEdgePair, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · rfl
  · exact crossingEdgePair_cross_eq C p

/-- Crossing edge pairs partition the port carrier. -/
theorem crossingEdgePair_eq_or_disjoint {N : FlowNetwork}
    (C : FlowCrossing N) (p q : FlowNetworkPort N) :
    crossingEdgePair C p = crossingEdgePair C q ∨
      Disjoint (crossingEdgePair C p) (crossingEdgePair C q) := by
  by_cases h : crossingEdgePair C p = crossingEdgePair C q
  · exact Or.inl h
  · right
    refine Finset.disjoint_left.mpr ?_
    intro x hxp hxq
    apply h
    exact (crossingEdgePair_eq_of_mem C p x hxp).symm.trans
      (crossingEdgePair_eq_of_mem C q x hxq)

/-- The finite collection of crossing edge orbits. -/
def crossingEdgeOrbits {N : FlowNetwork} (C : FlowCrossing N) :
    Finset (Finset (FlowNetworkPort N)) :=
  Finset.univ.image (crossingEdgePair C)

/-- Number of crossing edges. -/
def crossingEdgeCount {N : FlowNetwork} (C : FlowCrossing N) : Nat :=
  (crossingEdgeOrbits C).card

/-- Every edge pair occurs in the edge-orbit collection. -/
theorem crossingEdgePair_mem_orbits {N : FlowNetwork} (C : FlowCrossing N)
    (p : FlowNetworkPort N) :
    crossingEdgePair C p ∈ crossingEdgeOrbits C := by
  apply Finset.mem_image.mpr
  exact ⟨p, Finset.mem_univ p, rfl⟩

/-- Edge-orbit membership is characterized by pair equality. -/
theorem crossingEdgeOrbits_mem_iff {N : FlowNetwork} (C : FlowCrossing N)
    (E : Finset (FlowNetworkPort N)) :
    E ∈ crossingEdgeOrbits C ↔
      ∃ p : FlowNetworkPort N, E = crossingEdgePair C p := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨p, _, rfl⟩
    exact ⟨p, rfl⟩
  · rintro ⟨p, rfl⟩
    exact crossingEdgePair_mem_orbits C p

/-- Edge orbits cover all flow-network ports. -/
theorem crossingEdgeOrbits_coverage {N : FlowNetwork} (C : FlowCrossing N)
    (p : FlowNetworkPort N) :
    ∃ E ∈ crossingEdgeOrbits C, p ∈ E :=
  ⟨crossingEdgePair C p, crossingEdgePair_mem_orbits C p,
    crossingEdgePair_mem C p⟩

/-- Distinct crossing edge orbits are pairwise disjoint. -/
theorem crossingEdgeOrbits_pairwise_disjoint {N : FlowNetwork}
    (C : FlowCrossing N) :
    ((crossingEdgeOrbits C : Finset (Finset (FlowNetworkPort N))) : Set
      (Finset (FlowNetworkPort N))).Pairwise Disjoint := by
  intro E hE F hF hne
  rcases (crossingEdgeOrbits_mem_iff C E).mp hE with ⟨p, rfl⟩
  rcases (crossingEdgeOrbits_mem_iff C F).mp hF with ⟨q, rfl⟩
  exact (crossingEdgePair_eq_or_disjoint C p q).resolve_left hne

/-- The union of crossing edge orbits is the whole port carrier. -/
theorem crossingEdgeOrbits_biUnion {N : FlowNetwork} (C : FlowCrossing N) :
    (crossingEdgeOrbits C).biUnion id = Finset.univ := by
  ext p
  constructor
  · intro _
    exact Finset.mem_univ p
  · intro _
    rcases crossingEdgeOrbits_coverage C p with ⟨E, hE, hp⟩
    exact Finset.mem_biUnion.mpr ⟨E, hE, hp⟩

/-- A finite disjoint cover has total cardinality equal to its carrier. -/
theorem sum_card_eq_card_univ_of_pairwise_disjoint_cover
    {α : Type*} [Fintype α] [DecidableEq α]
    (family : Finset (Finset α))
    (hdis : (family : Set (Finset α)).Pairwise Disjoint)
    (hcover : family.biUnion id = (Finset.univ : Finset α)) :
    (∑ E ∈ family, E.card) = Fintype.card α := by
  calc
    (∑ E ∈ family, E.card) = (family.biUnion id).card := by
      symm
      exact Finset.card_biUnion hdis
    _ = (Finset.univ : Finset α).card := by rw [hcover]
    _ = Fintype.card α := Finset.card_univ

/-- Summed edge-orbit cardinalities equal the total port count. -/
theorem crossingEdgeSum_card {N : FlowNetwork} (C : FlowCrossing N) :
    (∑ E ∈ crossingEdgeOrbits C, E.card) = totalPortCount N := by
  rw [sum_card_eq_card_univ_of_pairwise_disjoint_cover
    (crossingEdgeOrbits C) (crossingEdgeOrbits_pairwise_disjoint C)
    (crossingEdgeOrbits_biUnion C)]
  rfl

/-- The port count is twice the crossing-edge count. -/
theorem crossingEdgeCount_mul_two {N : FlowNetwork} (C : FlowCrossing N) :
    crossingEdgeCount C * 2 = totalPortCount N := by
  calc
    crossingEdgeCount C * 2 =
        ∑ E ∈ crossingEdgeOrbits C, 2 := by
          simp [crossingEdgeCount, Nat.mul_comm]
    _ = ∑ E ∈ crossingEdgeOrbits C, E.card := by
      apply Finset.sum_congr rfl
      intro E hE
      rcases (crossingEdgeOrbits_mem_iff C E).mp hE with ⟨p, rfl⟩
      exact (crossingEdgePair_card C p).symm
    _ = totalPortCount N := crossingEdgeSum_card C

/-- Symmetric form of the two-ports-per-edge identity. -/
theorem two_mul_crossingEdgeCount {N : FlowNetwork} (C : FlowCrossing N) :
    2 * crossingEdgeCount C = totalPortCount N := by
  simpa [Nat.mul_comm] using crossingEdgeCount_mul_two C

/-- The finite collection of face-step orbits. -/
def faceOrbits {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) :
    Finset (Finset (FlowNetworkPort N)) :=
  Finset.univ.image (faceOrbit R C)

/-- Number of faces in the flow rotation system. -/
def faceCount {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) : Nat :=
  (faceOrbits R C).card

/-- Every face orbit occurs in the face-orbit collection. -/
theorem faceOrbit_mem_orbits {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p : FlowNetworkPort N) :
    faceOrbit R C p ∈ faceOrbits R C := by
  apply Finset.mem_image.mpr
  exact ⟨p, Finset.mem_univ p, rfl⟩

/-- Face-orbit membership is characterized by orbit equality. -/
theorem faceOrbits_mem_iff {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (F : Finset (FlowNetworkPort N)) :
    F ∈ faceOrbits R C ↔
      ∃ p : FlowNetworkPort N, F = faceOrbit R C p := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨p, _, rfl⟩
    exact ⟨p, rfl⟩
  · rintro ⟨p, rfl⟩
    exact faceOrbit_mem_orbits R C p

/-- Face orbits cover every flow-network port. -/
theorem faceOrbits_coverage {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p : FlowNetworkPort N) :
    ∃ F ∈ faceOrbits R C, p ∈ F :=
  ⟨faceOrbit R C p, faceOrbit_mem_orbits R C p,
    faceOrbit_contains R C p⟩

/-- Distinct face orbits are pairwise disjoint. -/
theorem faceOrbits_pairwise_disjoint {N : FlowNetwork}
    (R : FlowLocalRotation N) (C : FlowCrossing N) :
    ((faceOrbits R C : Finset (Finset (FlowNetworkPort N))) : Set
      (Finset (FlowNetworkPort N))).Pairwise Disjoint := by
  intro F hF G hG hne
  rcases (faceOrbits_mem_iff R C F).mp hF with ⟨p, rfl⟩
  rcases (faceOrbits_mem_iff R C G).mp hG with ⟨q, rfl⟩
  exact (faceOrbit_eq_or_disjoint R C p q).resolve_left hne

/-- The union of face orbits is the full port carrier. -/
theorem faceOrbits_biUnion {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) :
    (faceOrbits R C).biUnion id = Finset.univ := by
  ext p
  constructor
  · intro _
    exact Finset.mem_univ p
  · intro _
    rcases faceOrbits_coverage R C p with ⟨F, hF, hp⟩
    exact Finset.mem_biUnion.mpr ⟨F, hF, hp⟩

/-- Summed face-orbit cardinalities equal the total port count. -/
theorem faceSum_card {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) :
    (∑ F ∈ faceOrbits R C, F.card) = totalPortCount N := by
  rw [sum_card_eq_card_univ_of_pairwise_disjoint_cover
    (faceOrbits R C) (faceOrbits_pairwise_disjoint R C)
    (faceOrbits_biUnion R C)]
  rfl

/-- The finite Euler characteristic `V - E + F`. -/
def combinatorialEulerCharacteristic {N : FlowNetwork}
    (R : FlowLocalRotation N) (C : FlowCrossing N) : Int :=
  (regionVertexCount N : Int)
    - (crossingEdgeCount C : Int)
    + (faceCount R C : Int)

/-- Expanded formula for the combinatorial Euler characteristic. -/
theorem combinatorialEulerCharacteristic_eq {N : FlowNetwork}
    (R : FlowLocalRotation N) (C : FlowCrossing N) :
    combinatorialEulerCharacteristic R C =
      (regionVertexCount N : Int) - (crossingEdgeCount C : Int)
        + (faceCount R C : Int) := rfl

end DkMath.Tromino
