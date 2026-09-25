/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortFaceOrbit
import DkMathTest.Tromino.PortRotationSystemAxiomAudit

#print "file: DkMathTest.Tromino.PortFaceOrbitAxiomAudit"

namespace DkMathTest.Tromino.PortFaceOrbitAxiomAudit

open DkMath.Tromino
open DkMathTest.Tromino.PortRotationSystemAxiomAudit

example : portFaceOrbit portTwoRotation portTwoCrossing p22_00 =
    {p22_00, p22_11} := by
  rw [portFaceOrbit, firstPortFaceReturn_22_00]
  decide

example : portFaceOrbit portTwoRotation portTwoCrossing p22_01 =
    {p22_01, p22_10} := by
  rw [portFaceOrbit, firstPortFaceReturn_22_01]
  decide

example : (portFaceOrbit portTwoRotation portTwoCrossing p22_00).card = 2 := by
  rw [portFaceOrbit_card, firstPortFaceReturn_22_00]

example : (portFaceOrbit portTwoRotation portTwoCrossing p22_01).card = 2 := by
  rw [portFaceOrbit_card, firstPortFaceReturn_22_01]

example : portFaceOrbit portTwoRotation portTwoCrossing p22_11 =
    portFaceOrbit portTwoRotation portTwoCrossing p22_00 := by
  apply portFaceOrbit_eq_of_mem
  rw [portFaceOrbit_mem_iff_iterate]
  exact ⟨1, portFaceStep_22_00⟩

example : Disjoint
    (portFaceOrbit portTwoRotation portTwoCrossing p22_00)
    (portFaceOrbit portTwoRotation portTwoCrossing p22_01) := by
  have h0 : portFaceOrbit portTwoRotation portTwoCrossing p22_00 =
      {p22_00, p22_11} := by
    rw [portFaceOrbit, firstPortFaceReturn_22_00]
    decide
  have h1 : portFaceOrbit portTwoRotation portTwoCrossing p22_01 =
      {p22_01, p22_10} := by
    rw [portFaceOrbit, firstPortFaceReturn_22_01]
    decide
  rw [h0, h1]
  decide

example : portFaceOrbit portThreeRotation portThreeCrossing p30 =
    {p30, p31, p32, p33, p34, p35} := by
  rw [portFaceOrbit, firstPortFaceReturn_30]
  decide

example : (portFaceOrbit portThreeRotation portThreeCrossing p30).card = 6 := by
  rw [portFaceOrbit_card, firstPortFaceReturn_30]

example : portFaceOrbit portThreeRotation portThreeCrossing p35 =
    portFaceOrbit portThreeRotation portThreeCrossing p30 := by
  apply portFaceOrbit_eq_of_mem
  rw [portFaceOrbit_mem_iff_iterate]
  exact ⟨5, portFaceStep_iterate_30_5⟩

example {N : FlowNetwork} (R : FlowLocalRotation N) (C : FlowCrossing N)
    (p : PortNetworkPort N.toPortNetwork) :
    portFaceOrbit R.toPortLocalRotation C.toPortCrossing p = faceOrbit R C p :=
  portFaceOrbit_of_flow_erasure R C p

example {P : PortNetwork} {C : PortCrossing P} (R : PortLocalRotation P)
    (A B : V4FlowAssignment C) (p : PortNetworkPort P) :
    faceOrbit (R.toFlowLocalRotation A) A.toFlowCrossing p =
      faceOrbit (R.toFlowLocalRotation B) B.toFlowCrossing p :=
  faceOrbit_assignment_independent R A B p

#print axioms DkMath.Tromino.portFaceOrbit
#print axioms DkMath.Tromino.portFaceOrbit_mem_iff_iterate
#print axioms DkMath.Tromino.portFaceOrbit_card
#print axioms DkMath.Tromino.portFaceOrbit_eq_or_disjoint
#print axioms DkMath.Tromino.portFaceOrbitSetoid
#print axioms DkMath.Tromino.firstPortFaceReturn_of_flow_erasure
#print axioms DkMath.Tromino.faceOrbit_assignment_independent

end DkMathTest.Tromino.PortFaceOrbitAxiomAudit
