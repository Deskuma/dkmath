/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortEulerCount
import DkMathTest.Tromino.PortFaceOrbitAxiomAudit

#print "file: DkMathTest.Tromino.PortEulerCountAxiomAudit"

namespace DkMathTest.Tromino.PortEulerCountAxiomAudit

open DkMath.Tromino
open DkMathTest.Tromino.PortRotationSystemAxiomAudit

example : portRegionVertexCount portTwoNetwork = 2 := by rfl
example : portCrossingEdgeCount portTwoCrossing = 2 := by decide

theorem portFaceCount_22 : portFaceCount portTwoRotation portTwoCrossing = 2 := by
  have h10 : portFaceOrbit portTwoRotation portTwoCrossing p22_10 =
      portFaceOrbit portTwoRotation portTwoCrossing p22_01 := by
    apply portFaceOrbit_eq_of_mem
    rw [portFaceOrbit_mem_iff_iterate]
    exact ⟨1, portFaceStep_22_01⟩
  have h11 : portFaceOrbit portTwoRotation portTwoCrossing p22_11 =
      portFaceOrbit portTwoRotation portTwoCrossing p22_00 := by
    apply portFaceOrbit_eq_of_mem
    rw [portFaceOrbit_mem_iff_iterate]
    exact ⟨1, portFaceStep_22_00⟩
  have hfamily : portFaceOrbits portTwoRotation portTwoCrossing =
      {portFaceOrbit portTwoRotation portTwoCrossing p22_00,
       portFaceOrbit portTwoRotation portTwoCrossing p22_01} := by
    ext F
    constructor
    · intro h
      rcases (portFaceOrbits_mem_iff portTwoRotation portTwoCrossing F).mp h
        with ⟨p, rfl⟩
      rcases p with ⟨r, i⟩
      fin_cases r <;> fin_cases i
      · change portFaceOrbit portTwoRotation portTwoCrossing p22_00 ∈ _
        exact Finset.mem_insert.mpr (Or.inl rfl)
      · change portFaceOrbit portTwoRotation portTwoCrossing p22_01 ∈ _
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
      · change portFaceOrbit portTwoRotation portTwoCrossing p22_10 ∈ _
        rw [h10]
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
      · change portFaceOrbit portTwoRotation portTwoCrossing p22_11 ∈ _
        rw [h11]
        exact Finset.mem_insert.mpr (Or.inl rfl)
    · intro h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl
      · exact portFaceOrbit_mem_orbits portTwoRotation portTwoCrossing p22_00
      · exact portFaceOrbit_mem_orbits portTwoRotation portTwoCrossing p22_01
  have hne : portFaceOrbit portTwoRotation portTwoCrossing p22_00 ≠
      portFaceOrbit portTwoRotation portTwoCrossing p22_01 := by
    intro h
    have h00 : portFaceOrbit portTwoRotation portTwoCrossing p22_00 =
        {p22_00, p22_11} := by
      rw [portFaceOrbit, firstPortFaceReturn_22_00]
      decide
    have h01 : portFaceOrbit portTwoRotation portTwoCrossing p22_01 =
        {p22_01, p22_10} := by
      rw [portFaceOrbit, firstPortFaceReturn_22_01]
      decide
    rw [h00, h01] at h
    exact (by decide : ({p22_00, p22_11} : Finset _ ) ≠ {p22_01, p22_10}) h
  unfold portFaceCount
  rw [hfamily]
  simp [hne]

example : portCombinatorialEulerCharacteristic portTwoRotation
    portTwoCrossing = 2 := by
  have he : portCrossingEdgeCount portTwoCrossing = 2 := by decide
  have hf : portFaceCount portTwoRotation portTwoCrossing = 2 := portFaceCount_22
  unfold portCombinatorialEulerCharacteristic
  rw [he, hf]
  norm_num [portRegionVertexCount, portTwoNetwork]

example : portRegionVertexCount portThreeNetwork = 2 := by rfl
example : portCrossingEdgeCount portThreeCrossing = 3 := by decide

theorem portFaceCount_23 : portFaceCount portThreeRotation portThreeCrossing = 1 := by
  have hs : ∀ q : PortNetworkPort portThreeNetwork,
      portFaceOrbit portThreeRotation portThreeCrossing q =
        portFaceOrbit portThreeRotation portThreeCrossing p30 := by
    intro q
    rcases q with ⟨r, i⟩
    fin_cases r <;> fin_cases i
    · rfl
    · apply portFaceOrbit_eq_of_mem
      rw [portFaceOrbit_mem_iff_iterate]
      exact ⟨4, by simpa [p34] using portFaceStep_iterate_30_4⟩
    · apply portFaceOrbit_eq_of_mem
      rw [portFaceOrbit_mem_iff_iterate]
      exact ⟨2, by simpa [p32] using portFaceStep_iterate_30_2⟩
    · apply portFaceOrbit_eq_of_mem
      rw [portFaceOrbit_mem_iff_iterate]
      exact ⟨3, by simpa [p33] using portFaceStep_iterate_30_3⟩
    · apply portFaceOrbit_eq_of_mem
      rw [portFaceOrbit_mem_iff_iterate]
      exact ⟨1, by simpa [p31] using portFaceStep_iterate_30_1⟩
    · apply portFaceOrbit_eq_of_mem
      rw [portFaceOrbit_mem_iff_iterate]
      exact ⟨5, by simpa [p35] using portFaceStep_iterate_30_5⟩
  have hfamily : portFaceOrbits portThreeRotation portThreeCrossing =
      {portFaceOrbit portThreeRotation portThreeCrossing p30} := by
    ext F
    constructor
    · intro h
      rcases (portFaceOrbits_mem_iff portThreeRotation portThreeCrossing F).mp h
        with ⟨p, rfl⟩
      rw [hs p]
      simp
    · intro h
      simp only [Finset.mem_singleton] at h
      rw [h]
      exact portFaceOrbit_mem_orbits portThreeRotation portThreeCrossing p30
  unfold portFaceCount
  rw [hfamily]
  simp

example : portCombinatorialEulerCharacteristic portThreeRotation
    portThreeCrossing = 0 := by
  have he : portCrossingEdgeCount portThreeCrossing = 3 := by decide
  have hf : portFaceCount portThreeRotation portThreeCrossing = 1 := portFaceCount_23
  unfold portCombinatorialEulerCharacteristic
  rw [he, hf]
  norm_num [portRegionVertexCount, portThreeNetwork]

example : portCrossingEdgeCount portTwoCrossing * 2 =
    portTwoNetwork.portCount := portCrossingEdgeCount_mul_two _
example : (∑ E ∈ portCrossingEdgeOrbits portTwoCrossing, E.card) =
    portTwoNetwork.portCount := portCrossingEdgeSum_card _
example : (∑ F ∈ portFaceOrbits portTwoRotation portTwoCrossing, F.card) =
    portTwoNetwork.portCount := portFaceSum_card _ _

example {N : FlowNetwork} (_R : FlowLocalRotation N) (C : FlowCrossing N) :
    N.toPortNetwork.portCount = totalPortCount N :=
  portCount_of_flow_erasure

example {N : FlowNetwork} (_R : FlowLocalRotation N) (C : FlowCrossing N) :
    portCrossingEdgeCount C.toPortCrossing = crossingEdgeCount C :=
  portCrossingEdgeCount_of_flow_erasure C

example {N : FlowNetwork} (R : FlowLocalRotation N) (C : FlowCrossing N) :
    portFaceCount R.toPortLocalRotation C.toPortCrossing = faceCount R C :=
  portFaceCount_of_flow_erasure R C

example {N : FlowNetwork} (R : FlowLocalRotation N) (C : FlowCrossing N) :
    portCombinatorialEulerCharacteristic R.toPortLocalRotation C.toPortCrossing =
      combinatorialEulerCharacteristic R C :=
  portCombinatorialEulerCharacteristic_of_flow_erasure R C

example {P : PortNetwork} {C : PortCrossing P} (R : PortLocalRotation P)
    (A B : V4FlowAssignment C) :
    combinatorialEulerCharacteristic (R.toFlowLocalRotation A)
      A.toFlowCrossing =
      combinatorialEulerCharacteristic (R.toFlowLocalRotation B)
        B.toFlowCrossing :=
  combinatorialEulerCharacteristic_assignment_independent R A B

#print axioms DkMath.Tromino.portCrossingEdgePair_card
#print axioms DkMath.Tromino.portCrossingEdgeOrbits_pairwise_disjoint
#print axioms DkMath.Tromino.portCrossingEdgeCount_mul_two
#print axioms DkMath.Tromino.portFaceOrbits_pairwise_disjoint
#print axioms DkMath.Tromino.portFaceSum_card
#print axioms DkMath.Tromino.portCombinatorialEulerCharacteristic
#print axioms DkMath.Tromino.portCombinatorialEulerCharacteristic_of_flow_erasure
#print axioms DkMath.Tromino.combinatorialEulerCharacteristic_assignment_independent

end DkMathTest.Tromino.PortEulerCountAxiomAudit
