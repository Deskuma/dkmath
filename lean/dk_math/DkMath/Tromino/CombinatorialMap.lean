/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.EulerCount

#print "file: DkMath.Tromino.CombinatorialMap"

namespace DkMath.Tromino

structure FlowCombinatorialMap (N : FlowNetwork) where
  crossing : FlowCrossing N
  rotation : FlowRotationSystem N
  nonemptyRegions : 0 < N.regionCount
  connected : ∀ r s : Fin N.regionCount,
    RegionReachable crossing r s

def FlowCombinatorialMap.localRotation {N : FlowNetwork}
    (M : FlowCombinatorialMap N) : FlowLocalRotation N :=
  M.rotation.toFlowLocalRotation

def FlowCombinatorialMap.vertexCount {N : FlowNetwork}
    (_M : FlowCombinatorialMap N) : Nat :=
  regionVertexCount N

def FlowCombinatorialMap.edgeCount {N : FlowNetwork}
    (M : FlowCombinatorialMap N) : Nat :=
  crossingEdgeCount M.crossing

def FlowCombinatorialMap.faceCount {N : FlowNetwork}
    (M : FlowCombinatorialMap N) : Nat :=
  DkMath.Tromino.faceCount M.localRotation M.crossing

def FlowCombinatorialMap.portCount {N : FlowNetwork}
    (_M : FlowCombinatorialMap N) : Nat :=
  totalPortCount N

def FlowCombinatorialMap.eulerCharacteristic {N : FlowNetwork}
    (M : FlowCombinatorialMap N) : Int :=
  combinatorialEulerCharacteristic M.localRotation M.crossing

theorem FlowCombinatorialMap.connected_regions {N : FlowNetwork}
    (M : FlowCombinatorialMap N) (r s : Fin N.regionCount) :
    RegionReachable M.crossing r s :=
  M.connected r s

def SameVertexRotationOrbit {N : FlowNetwork}
    (M : FlowCombinatorialMap N) (p q : FlowNetworkPort N) : Prop :=
  p.1 = q.1 ∧
    ∃ n : Nat, (M.localRotation.rotate^[n]) p = q

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

theorem FlowCombinatorialMap.sameVertexRotationOrbit_of_same_region
    {N : FlowNetwork} (M : FlowCombinatorialMap N)
    (p q : FlowNetworkPort N) (hregion : p.1 = q.1) :
    SameVertexRotationOrbit M p q :=
  ⟨hregion, M.rotation_reaches_same_region p q hregion⟩

def HasCombinatorialGenus {N : FlowNetwork}
    (M : FlowCombinatorialMap N) (g : Nat) : Prop :=
  M.eulerCharacteristic = (2 : Int) - 2 * (g : Int)

theorem combinatorialGenus_unique {N : FlowNetwork}
    (M : FlowCombinatorialMap N) {g h : Nat}
    (hg : HasCombinatorialGenus M g)
    (hh : HasCombinatorialGenus M h) :
    g = h := by
  simp only [HasCombinatorialGenus] at hg hh
  omega

theorem combinatorialGenus_zero_iff {N : FlowNetwork}
    (M : FlowCombinatorialMap N) :
    HasCombinatorialGenus M 0 ↔ M.eulerCharacteristic = 2 := by
  simp [HasCombinatorialGenus]

theorem combinatorialGenus_one_iff {N : FlowNetwork}
    (M : FlowCombinatorialMap N) :
    HasCombinatorialGenus M 1 ↔ M.eulerCharacteristic = 0 := by
  simp [HasCombinatorialGenus]

theorem combinatorialGenus_characteristic_le_two {N : FlowNetwork}
    (M : FlowCombinatorialMap N) {g : Nat}
    (hg : HasCombinatorialGenus M g) :
    M.eulerCharacteristic ≤ 2 := by
  simp only [HasCombinatorialGenus] at hg
  omega

theorem combinatorialGenus_characteristic_even {N : FlowNetwork}
    (M : FlowCombinatorialMap N) {g : Nat}
    (hg : HasCombinatorialGenus M g) :
    Even M.eulerCharacteristic := by
  refine ⟨(1 : Int) - (g : Int), ?_⟩
  rw [hg]
  ring

def HasSphereCharacteristic {N : FlowNetwork}
    (M : FlowCombinatorialMap N) : Prop :=
  M.eulerCharacteristic = 2

theorem hasSphereCharacteristic_iff_genus_zero {N : FlowNetwork}
    (M : FlowCombinatorialMap N) :
    HasSphereCharacteristic M ↔ HasCombinatorialGenus M 0 := by
  rw [HasSphereCharacteristic, (combinatorialGenus_zero_iff M).symm]

end DkMath.Tromino
