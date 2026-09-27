/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.EulerCount

#print "file: DkMath.Tromino.CombinatorialMap"

/-!
# Flow combinatorial maps

A flow combinatorial map packages a crossing involution, a cyclic local
rotation, nonempty regions, and region connectedness.  Its vertex, edge, and
face counts are finite orbit counts, so its genus predicates are purely
combinatorial Euler-characteristic certificates.
-/

namespace DkMath.Tromino

/-- A connected finite rotation system on a flow network. -/
structure FlowCombinatorialMap (N : FlowNetwork) where
  crossing : FlowCrossing N
  rotation : FlowRotationSystem N
  nonemptyRegions : 0 < N.regionCount
  connected : ∀ r s : Fin N.regionCount,
    RegionReachable crossing r s

/-- The local rotation component of a flow map. -/
def FlowCombinatorialMap.localRotation {N : FlowNetwork}
    (M : FlowCombinatorialMap N) : FlowLocalRotation N :=
  M.rotation.toFlowLocalRotation

/-- Number of vertices, namely regions. -/
def FlowCombinatorialMap.vertexCount {N : FlowNetwork}
    (_M : FlowCombinatorialMap N) : Nat :=
  regionVertexCount N

/-- Number of edges, namely crossing orbits. -/
def FlowCombinatorialMap.edgeCount {N : FlowNetwork}
    (M : FlowCombinatorialMap N) : Nat :=
  crossingEdgeCount M.crossing

/-- Number of faces, namely face-step orbits. -/
def FlowCombinatorialMap.faceCount {N : FlowNetwork}
    (M : FlowCombinatorialMap N) : Nat :=
  DkMath.Tromino.faceCount M.localRotation M.crossing

/-- Number of ports in the finite carrier. -/
def FlowCombinatorialMap.portCount {N : FlowNetwork}
    (_M : FlowCombinatorialMap N) : Nat :=
  totalPortCount N

/-- The map's combinatorial Euler characteristic. -/
def FlowCombinatorialMap.eulerCharacteristic {N : FlowNetwork}
    (M : FlowCombinatorialMap N) : Int :=
  combinatorialEulerCharacteristic M.localRotation M.crossing

/-- The packaged connectedness hypothesis gives region reachability. -/
theorem FlowCombinatorialMap.connected_regions {N : FlowNetwork}
    (M : FlowCombinatorialMap N) (r s : Fin N.regionCount) :
    RegionReachable M.crossing r s :=
  M.connected r s

/-- Same-region reachability under local rotation. -/
def SameVertexRotationOrbit {N : FlowNetwork}
    (M : FlowCombinatorialMap N) (p q : FlowNetworkPort N) : Prop :=
  p.1 = q.1 ∧
    ∃ n : Nat, (M.localRotation.rotate^[n]) p = q

/-- Cyclic local rotation reaches any slot in one region. -/
theorem FlowCombinatorialMap.rotation_reaches_same_region
    {N : FlowNetwork} (M : FlowCombinatorialMap N)
    (p q : FlowNetworkPort N) (hregion : p.1 = q.1) :
    ∃ n : Nat, (M.localRotation.rotate^[n]) p = q := by
  cases p with
  | mk r i =>
    cases q with
    | mk s j =>
      dsimp at hregion
      subst s
      simpa [FlowCombinatorialMap.localRotation] using
        M.rotation.cyclic r i j

/-- Equal region indices give the same vertex rotation orbit. -/
theorem FlowCombinatorialMap.sameVertexRotationOrbit_of_same_region
    {N : FlowNetwork} (M : FlowCombinatorialMap N)
    (p q : FlowNetworkPort N) (hregion : p.1 = q.1) :
    SameVertexRotationOrbit M p q :=
  ⟨hregion, M.rotation_reaches_same_region p q hregion⟩

/-- Encode genus `g` by the Euler identity `χ = 2 - 2g`. -/
def HasCombinatorialGenus {N : FlowNetwork}
    (M : FlowCombinatorialMap N) (g : Nat) : Prop :=
  M.eulerCharacteristic = (2 : Int) - 2 * (g : Int)

/-- The genus parameter satisfying the Euler identity is unique. -/
theorem combinatorialGenus_unique {N : FlowNetwork}
    (M : FlowCombinatorialMap N) {g h : Nat}
    (hg : HasCombinatorialGenus M g)
    (hh : HasCombinatorialGenus M h) :
    g = h := by
  simp only [HasCombinatorialGenus] at hg hh
  omega

/-- Genus zero is equivalent to Euler characteristic two. -/
theorem combinatorialGenus_zero_iff {N : FlowNetwork}
    (M : FlowCombinatorialMap N) :
    HasCombinatorialGenus M 0 ↔ M.eulerCharacteristic = 2 := by
  simp [HasCombinatorialGenus]

/-- Genus one is equivalent to Euler characteristic zero. -/
theorem combinatorialGenus_one_iff {N : FlowNetwork}
    (M : FlowCombinatorialMap N) :
    HasCombinatorialGenus M 1 ↔ M.eulerCharacteristic = 0 := by
  simp [HasCombinatorialGenus]

/-- A certified genus has Euler characteristic at most two. -/
theorem combinatorialGenus_characteristic_le_two {N : FlowNetwork}
    (M : FlowCombinatorialMap N) {g : Nat}
    (hg : HasCombinatorialGenus M g) :
    M.eulerCharacteristic ≤ 2 := by
  simp only [HasCombinatorialGenus] at hg
  omega

/-- A certified genus gives an even Euler characteristic. -/
theorem combinatorialGenus_characteristic_even {N : FlowNetwork}
    (M : FlowCombinatorialMap N) {g : Nat}
    (hg : HasCombinatorialGenus M g) :
    Even M.eulerCharacteristic := by
  refine ⟨(1 : Int) - (g : Int), ?_⟩
  rw [hg]
  ring

/-- The sphere characteristic predicate `χ = 2`. -/
def HasSphereCharacteristic {N : FlowNetwork}
    (M : FlowCombinatorialMap N) : Prop :=
  M.eulerCharacteristic = 2

/-- Sphere characteristic and genus zero are equivalent. -/
theorem hasSphereCharacteristic_iff_genus_zero {N : FlowNetwork}
    (M : FlowCombinatorialMap N) :
    HasSphereCharacteristic M ↔ HasCombinatorialGenus M 0 := by
  rw [HasSphereCharacteristic, (combinatorialGenus_zero_iff M).symm]

end DkMath.Tromino
