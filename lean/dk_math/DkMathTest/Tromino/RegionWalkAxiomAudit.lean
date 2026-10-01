/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.RegionWalk
import DkMathTest.Tromino.FlowTransitionXorAxiomAudit

#print "file: DkMathTest.Tromino.RegionWalkAxiomAudit"

namespace DkMathTest.Tromino.RegionWalkAxiomAudit

open DkMath.Tromino
open DkMathTest.Tromino.FlowTransitionXorAxiomAudit

example {N : FlowNetwork} (C : FlowCrossing N)
    (p : FlowNetworkPort N) :
    flowEdgeSource C (reverseEdge C p) = flowEdgeTarget C p :=
  flowEdgeSource_reverseEdge C p

example {N : FlowNetwork} (C : FlowCrossing N)
    (p : FlowNetworkPort N) :
    flowEdgeTarget C (reverseEdge C p) = flowEdgeSource C p :=
  flowEdgeTarget_reverseEdge C p

example {N : FlowNetwork} (C : FlowCrossing N)
    (p : FlowNetworkPort N) :
    reverseEdge C (reverseEdge C p) = p :=
  reverseEdge_reverseEdge C p

def twoEdgeWalk : FlowRegionWalk twoRegionFlowClosed.crossing p2.1
    (twoRegionFlowClosed.crossing.cross p2).1 :=
  FlowRegionWalk.singleton twoRegionFlowClosed.crossing p2

def twoClosedWalk : ClosedRegionWalk twoRegionFlowClosed.crossing p2.1 :=
  FlowRegionWalk.append twoEdgeWalk (FlowRegionWalk.reverse twoEdgeWalk)

example : FlowRegionWalk.length twoClosedWalk = 2 := by
  simp [twoClosedWalk, twoEdgeWalk, FlowRegionWalk.length,
    FlowRegionWalk.append, FlowRegionWalk.reverse,
    FlowRegionWalk.reverseEdges, FlowRegionWalk.singleton]

example : regionWalkXor twoClosedWalk = 0 := by
  change regionWalkXor
    (FlowRegionWalk.append twoEdgeWalk (FlowRegionWalk.reverse twoEdgeWalk)) = 0
  have hlabel : regionWalkXor twoEdgeWalk = deltaA := by
    change regionWalkXor
      (FlowRegionWalk.singleton twoRegionFlowClosed.crossing p2) = deltaA
    rw [regionWalkXor_singleton]
    rfl
  rw [regionWalkXor_append, regionWalkXor_reverse, hlabel]
  exact state_add_self deltaA

example (W₁ W₂ : FlowRegionWalk twoRegionFlowClosed.crossing p2.1 p2.1)
    (hzero : RegionZeroHolonomy twoRegionFlowClosed.crossing) :
    regionWalkXor W₁ = regionWalkXor W₂ :=
  regionWalkXor_eq_of_zeroHolonomy twoRegionFlowClosed.crossing hzero W₁ W₂

example : RegionReachable twoRegionFlowClosed.crossing p2.1 p2.1 :=
  regionReachable_refl twoRegionFlowClosed.crossing p2.1

example : RegionReachable twoRegionFlowClosed.crossing p2.1
    (twoRegionFlowClosed.crossing.cross p2).1 :=
  ⟨twoEdgeWalk⟩

example : RegionReachable twoRegionFlowClosed.crossing
    (twoRegionFlowClosed.crossing.cross p2).1 p2.1 := by
  exact regionReachable_symm twoRegionFlowClosed.crossing ⟨twoEdgeWalk⟩

example : regionWalkXor (transitionRegionWalk threeRegionFlowClosed p3 3) =
    flowTransitionXor threeRegionFlowClosed p3 3 :=
  transitionRegionWalk_xor threeRegionFlowClosed p3 3

example : FlowRegionWalk.length (transitionRegionWalk threeRegionFlowClosed p3 3) = 3 :=
  transitionRegionWalk_endpoint threeRegionFlowClosed p3 3

example : regionWalkXor (transitionRegionWalk threeRegionFlowClosed p3 3) = deltaA := by
  rw [transitionRegionWalk_xor]
  rw [flowTransitionXor_eq_nsmul]
  change 3 • deltaA = deltaA
  rw [nsmul_state_eq_mod_two]
  decide

example (hzero : RegionZeroHolonomy twoRegionFlowClosed.crossing) :
    flowTransitionXor twoRegionFlowClosed p2 2 = 0 := by
  exact flowTransitionXor_eq_zero_of_regionZeroHolonomy
    twoRegionFlowClosed p2 2 hzero flowPrimitive_two.1

example (hzero : RegionZeroHolonomy twoRegionFlowClosed.crossing) :
    2 % 2 = 0 :=
  primitiveFlowTransitionReturn_even_of_regionZeroHolonomy
    twoRegionFlowClosed p2 2 hzero flowPrimitive_two

example : ¬ RegionZeroHolonomy threeRegionFlowClosed.crossing := by
  intro hzero
  have hz := flowTransitionXor_eq_zero_of_regionZeroHolonomy
    threeRegionFlowClosed p3 3 hzero flowPrimitive_three.1
  have hx : flowTransitionXor threeRegionFlowClosed p3 3 = deltaA := by
    rw [flowTransitionXor_eq_nsmul]
    change 3 • deltaA = deltaA
    rw [nsmul_state_eq_mod_two]
    decide
  rw [hx] at hz
  exact deltaA_ne_zero hz

example : flowTransitionXor threeRegionFlowClosed p3 3 ≠ 0 := by
  rw [flowTransitionXor_eq_nsmul]
  change 3 • deltaA ≠ 0
  rw [nsmul_state_eq_mod_two]
  exact deltaA_ne_zero

#print axioms DkMath.Tromino.regionWalkXor_eq_of_zeroHolonomy
#print axioms DkMath.Tromino.RegionZeroHolonomy_of_same_endpoint_xor
#print axioms DkMath.Tromino.transitionRegionWalk_xor
#print axioms DkMath.Tromino.flowTransitionXor_eq_zero_of_regionZeroHolonomy
#print axioms DkMath.Tromino.primitiveFlowTransitionReturn_even_of_regionZeroHolonomy

end DkMathTest.Tromino.RegionWalkAxiomAudit
