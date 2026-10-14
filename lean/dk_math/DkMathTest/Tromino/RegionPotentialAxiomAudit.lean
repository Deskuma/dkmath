/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.RegionPotential
import DkMathTest.Tromino.FlowTransitionXorAxiomAudit
import DkMathTest.Tromino.RegionWalkAxiomAudit

#print "file: DkMathTest.Tromino.RegionPotentialAxiomAudit"

namespace DkMathTest.Tromino.RegionPotentialAxiomAudit

open DkMath.Tromino
open DkMathTest.Tromino.FlowTransitionXorAxiomAudit
open DkMathTest.Tromino.RegionWalkAxiomAudit

def twoRegionPotential : RegionPotential twoRegionFlowClosed.crossing where
  state := fun r => if r.val = 0 then 0 else deltaA
  edgeLaw := by
    intro p
    cases p with
    | mk r i =>
      fin_cases r <;> fin_cases i <;>
        simp [twoRegionFlowClosed, twoRegionFlowCrossing,
          twoRegionFlowNetwork, swapRegion, flowEdgeSource,
          flowEdgeTarget, flowEdgeLabel, aaFlow, state_add_self]

theorem twoRegionRooted :
    RootedRegionConnected twoRegionFlowClosed.crossing p2.1 := by
  intro s
  fin_cases s
  · exact ⟨FlowRegionWalk.nil twoRegionFlowClosed.crossing p2.1⟩
  · exact ⟨twoEdgeWalk⟩

theorem twoRegionZeroHolonomy :
    RegionZeroHolonomy twoRegionFlowClosed.crossing :=
  regionPotential_regionZeroHolonomy twoRegionPotential

example :
    twoRegionPotential.state p2.1 = 0 := by
  rfl

example :
    twoRegionPotential.state (twoRegionFlowClosed.crossing.cross p2).1 = deltaA := by
  rfl

example :
    twoRegionPotential.state (twoRegionFlowClosed.crossing.cross p2).1 =
      twoRegionPotential.state p2.1 + flowEdgeLabel twoRegionFlowClosed.crossing p2 :=
  twoRegionPotential.edgeLaw p2

example :
    twoRegionPotential.state p2.1 =
      twoRegionPotential.state p2.1 + regionWalkXor twoClosedWalk := by
  exact regionPotential_integrates twoRegionPotential twoClosedWalk

example :
    RegionZeroHolonomy twoRegionFlowClosed.crossing :=
  twoRegionZeroHolonomy

example : ∃ P : RegionPotential twoRegionFlowClosed.crossing,
    P.state p2.1 = 0 := by
  exact regionPotential_exists_of_zeroHolonomy p2.1 0 twoRegionRooted
    twoRegionZeroHolonomy

example (P Q : RegionPotential twoRegionFlowClosed.crossing)
    (hbase : P.state p2.1 = Q.state p2.1) :
    ∀ s, P.state s = Q.state s :=
  regionPotential_eq_of_same_base p2.1 twoRegionRooted P Q hbase

example (gamma : TrominoState) (P : RegionPotential twoRegionFlowClosed.crossing)
    (p : FlowNetworkPort twoRegionFlowClosed.toFlowNetwork) :
    (translateRegionPotential gamma P).state
        (flowEdgeTarget twoRegionFlowClosed.crossing p) =
      (translateRegionPotential gamma P).state
        (flowEdgeSource twoRegionFlowClosed.crossing p) +
        flowEdgeLabel twoRegionFlowClosed.crossing p :=
  (translateRegionPotential gamma P).edgeLaw p

example (P Q : RegionPotential twoRegionFlowClosed.crossing) :
    ∀ s, Q.state s =
      P.state s + (P.state p2.1 + Q.state p2.1) :=
  regionPotential_gauge p2.1 twoRegionRooted P Q

example (p : FlowNetworkPort twoRegionFlowClosed.toFlowNetwork) :
    twoRegionPotential.state (flowEdgeSource twoRegionFlowClosed.crossing p) +
      twoRegionPotential.state (flowEdgeTarget twoRegionFlowClosed.crossing p) =
      flowEdgeLabel twoRegionFlowClosed.crossing p :=
  regionPotential_edgeLabel twoRegionPotential p

example (p : FlowNetworkPort twoRegionFlowClosed.toFlowNetwork) :
    twoRegionPotential.state (flowEdgeSource twoRegionFlowClosed.crossing p) ≠
      twoRegionPotential.state (flowEdgeTarget twoRegionFlowClosed.crossing p) :=
  regionPotential_adjacent_ne twoRegionPotential p

example : ¬ ∃ P : RegionPotential threeRegionFlowClosed.crossing,
    P.state p3.1 = 0 := by
  rintro ⟨P, _⟩
  have hzero := regionPotential_regionZeroHolonomy P
  have hz := flowTransitionXor_eq_zero_of_regionZeroHolonomy
    threeRegionFlowClosed p3 3 hzero flowPrimitive_three.1
  have hx : flowTransitionXor threeRegionFlowClosed p3 3 = deltaA := by
    rw [flowTransitionXor_eq_nsmul]
    change 3 • deltaA = deltaA
    rw [nsmul_state_eq_mod_two]
    decide
  rw [hx] at hz
  exact deltaA_ne_zero hz

#print axioms DkMath.Tromino.regionPotential_exists_of_zeroHolonomy
#print axioms DkMath.Tromino.regionPotential_regionZeroHolonomy
#print axioms DkMath.Tromino.regionPotential_eq_of_same_base
#print axioms DkMath.Tromino.translateRegionPotential
#print axioms DkMath.Tromino.regionPotential_gauge
#print axioms DkMath.Tromino.regionPotential_edgeLabel
#print axioms DkMath.Tromino.regionPotential_adjacent_ne

end DkMathTest.Tromino.RegionPotentialAxiomAudit
