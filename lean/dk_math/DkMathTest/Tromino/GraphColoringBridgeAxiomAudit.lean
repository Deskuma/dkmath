/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.GraphColoringBridge
import DkMathTest.Tromino.FlowTransitionXorAxiomAudit
import DkMathTest.Tromino.RegionPotentialAxiomAudit
import DkMathTest.Tromino.RegionWalkAxiomAudit

#print "file: DkMathTest.Tromino.GraphColoringBridgeAxiomAudit"

namespace DkMathTest.Tromino.GraphColoringBridgeAxiomAudit

open DkMath.Tromino
open DkMathTest.Tromino.FlowTransitionXorAxiomAudit
open DkMathTest.Tromino.RegionPotentialAxiomAudit
open DkMathTest.Tromino.RegionWalkAxiomAudit

def p2Alt : FlowNetworkPort twoRegionFlowClosed.toFlowNetwork :=
  ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩

example :
    (regionSimpleGraph twoRegionFlowClosed.crossing).Adj
      p2.1 (twoRegionFlowClosed.crossing.cross p2).1 :=
  regionSimpleGraph_adj_of_port twoRegionFlowClosed.crossing p2

example :
    (regionSimpleGraph twoRegionFlowClosed.crossing).Adj p2.1
      (twoRegionFlowClosed.crossing.cross p2).1 ↔
      ∃ p : FlowNetworkPort twoRegionFlowClosed.toFlowNetwork,
        p.1 = p2.1 ∧ (twoRegionFlowClosed.crossing.cross p).1 =
          (twoRegionFlowClosed.crossing.cross p2).1 :=
  regionSimpleGraph_adj_iff twoRegionFlowClosed.crossing p2.1
    (twoRegionFlowClosed.crossing.cross p2).1

example :
    (flowPortToDart twoRegionFlowClosed.crossing p2).fst = p2.1 := by
  rfl

example :
    (flowPortToDart twoRegionFlowClosed.crossing p2).snd =
      (twoRegionFlowClosed.crossing.cross p2).1 := by
  rfl

example :
    flowPortToDart twoRegionFlowClosed.crossing
        (reverseEdge twoRegionFlowClosed.crossing p2) =
      (flowPortToDart twoRegionFlowClosed.crossing p2).symm :=
  flowPortToDart_reverse twoRegionFlowClosed.crossing p2

example :
    (flowPortToDart twoRegionFlowClosed.crossing
        (reverseEdge twoRegionFlowClosed.crossing p2)).edge =
      (flowPortToDart twoRegionFlowClosed.crossing p2).edge :=
  flowPortToDart_edge_reverse twoRegionFlowClosed.crossing p2

example (d : (regionSimpleGraph twoRegionFlowClosed.crossing).Dart) :
    ∃ p : FlowNetworkPort twoRegionFlowClosed.toFlowNetwork,
      p.1 = d.fst ∧ (twoRegionFlowClosed.crossing.cross p).1 = d.snd :=
  dart_has_flowPort twoRegionFlowClosed.crossing d

set_option linter.unnecessarySimpa false in
example : p2 ≠ p2Alt := by
  intro h
  have hval := congrArg
    (fun q : FlowNetworkPort twoRegionFlowClosed.toFlowNetwork => q.2.val) h
  have hval' : (0 : Nat) = 1 := by
    simpa [p2, p2Alt] using hval
  omega

example :
    flowPortToDart twoRegionFlowClosed.crossing p2 =
      flowPortToDart twoRegionFlowClosed.crossing p2Alt := by
  apply SimpleGraph.Dart.ext
  apply Prod.ext <;> rfl

example :
    twoRegionPotential.toColoring p2.1 = 0 := by
  rfl

example :
    twoRegionPotential.toColoring
        (twoRegionFlowClosed.crossing.cross p2).1 = deltaA := by
  rfl

example {r s : Fin twoRegionFlowClosed.regionCount}
    (h : (regionSimpleGraph twoRegionFlowClosed.crossing).Adj r s) :
    twoRegionPotential.toColoring r ≠ twoRegionPotential.toColoring s :=
  twoRegionPotential.toColoring.valid h

example :
    (regionSimpleGraph twoRegionFlowClosed.crossing).Colorable 4 :=
  twoRegionPotential.toColoring_colorable

example :
    (regionSimpleGraph twoRegionFlowClosed.crossing).Colorable 4 :=
  regionSimpleGraph_colorable_four_of_zeroHolonomy p2.1 twoRegionRooted
    twoRegionZeroHolonomy

example (p : FlowNetworkPort twoRegionFlowClosed.toFlowNetwork) :
    twoRegionPotential.toColoring (flowEdgeSource twoRegionFlowClosed.crossing p) +
        twoRegionPotential.toColoring (flowEdgeTarget twoRegionFlowClosed.crossing p) =
      flowEdgeLabel twoRegionFlowClosed.crossing p :=
  twoRegionPotential.toColoring_edgeLabel p

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

#print axioms DkMath.Tromino.regionSimpleGraph_adj_iff
#print axioms DkMath.Tromino.flowPortToDart_reverse
#print axioms DkMath.Tromino.dart_has_flowPort
#print axioms DkMath.Tromino.RegionPotential.toColoring
#print axioms DkMath.Tromino.RegionPotential.toColoring_colorable
#print axioms DkMath.Tromino.regionSimpleGraph_colorable_four_of_zeroHolonomy

end DkMathTest.Tromino.GraphColoringBridgeAxiomAudit
