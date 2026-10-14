/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortTensionColoring
import DkMathTest.Tromino.PortCombinatorialMapAxiomAudit

#print "file: DkMathTest.Tromino.PortTensionColoringAxiomAudit"

namespace DkMathTest.Tromino.PortTensionColoringAxiomAudit

open DkMath.Tromino
open DkMathTest.Tromino.PortCombinatorialMapAxiomAudit
open DkMathTest.Tromino.PortRegionWalkAxiomAudit
open DkMathTest.Tromino.PortRotationSystemAxiomAudit
open DkMathTest.Tromino.FlowTransitionXorAxiomAudit
open DkMathTest.Tromino.RotationSystemAxiomAudit

def portTwoColoring :
    (portRegionSimpleGraph portTwoCrossing).Coloring TrominoState :=
  SimpleGraph.Coloring.mk
    (fun r : Fin 2 => if r.val = 0 then 0 else deltaA) (by
      intro r s h
      fin_cases r <;> fin_cases s <;>
        simp_all [portRegionSimpleGraph_adj_iff, portTwoCrossing, deltaA_ne_zero, Ne.symm deltaA_ne_zero])

def portThreeColoring :
    (portRegionSimpleGraph portThreeCrossing).Coloring TrominoState :=
  SimpleGraph.Coloring.mk
    (fun r : Fin 2 => if r.val = 0 then 0 else deltaA) (by
      intro r s h
      fin_cases r <;> fin_cases s <;>
        simp_all [portRegionSimpleGraph_adj_iff, portThreeCrossing, deltaA_ne_zero, Ne.symm deltaA_ne_zero])

example (p : PortNetworkPort portTwoNetwork) :
    (portRegionSimpleGraph portTwoCrossing).Adj p.1
      (portTwoCrossing.cross p).1 :=
  portRegionSimpleGraph_adj_of_port portTwoCrossing p

example (r s : Fin portTwoNetwork.regionCount) :
    (portRegionSimpleGraph portTwoCrossing).Adj r s ↔
      ∃ p, p.1 = r ∧ (portTwoCrossing.cross p).1 = s :=
  portRegionSimpleGraph_adj_iff portTwoCrossing r s

example : portRegionSimpleGraph portTwoCrossing =
    regionSimpleGraph portDeltaAAssignment.toFlowCrossing :=
  portRegionSimpleGraph_eq_regionSimpleGraph_of_assignment portDeltaAAssignment

example : portRegionSimpleGraph twoThreeCrossing.toPortCrossing =
    regionSimpleGraph twoThreeCrossing :=
  portRegionSimpleGraph_eq_regionSimpleGraph_of_flow_erasure twoThreeCrossing

example : PortFourStateColorable portTwoCrossing :=
  ⟨portTwoColoring⟩

example : PortFourStateColorable portThreeCrossing :=
  ⟨portThreeColoring⟩

example : (portRegionSimpleGraph portTwoCrossing).Colorable 4 :=
  portFourStateColorable_implies_colorable_four ⟨portTwoColoring⟩

example : ∀ p : PortNetworkPort portTwoNetwork,
    (coloringToV4Assignment portTwoColoring).label p = deltaA := by
  intro p
  cases p with
  | mk r i =>
    fin_cases r <;> rfl

example : ∀ p : PortNetworkPort portTwoNetwork,
    (coloringToV4Assignment portTwoColoring).label p ≠ 0 := by
  intro p
  exact (coloringToV4Assignment portTwoColoring).nonzero p

example : ∀ p : PortNetworkPort portTwoNetwork,
    (coloringToV4Assignment portTwoColoring).label
        (portTwoCrossing.cross p) =
      (coloringToV4Assignment portTwoColoring).label p := by
  intro p
  exact (coloringToV4Assignment portTwoColoring).cross_sameLabel p

example : IsZeroHolonomyV4Tension
    (coloringToV4Assignment portTwoColoring) :=
  coloringToV4Assignment_isZeroHolonomy portTwoColoring

theorem v4Assignment_ext {P : PortNetwork} {C : PortCrossing P}
    {A B : V4FlowAssignment C}
    (h : ∀ p, A.label p = B.label p) : A = B := by
  cases A with
  | mk labelA nonzeroA crossA =>
    cases B with
    | mk labelB nonzeroB crossB =>
      simp only at h ⊢
      congr
      funext p
      exact h p

theorem portTwoColoring_assignment_eq_deltaA :
    coloringToV4Assignment portTwoColoring = portDeltaAAssignment := by
  apply v4Assignment_ext
  intro p
  calc
    (coloringToV4Assignment portTwoColoring).label p = deltaA := by
      cases p with
      | mk r i => fin_cases r <;> rfl
    _ = portDeltaAAssignment.label p := by rfl

theorem portDeltaAAssignment_zeroHolonomy :
    IsZeroHolonomyV4Tension portDeltaAAssignment := by
  rw [← portTwoColoring_assignment_eq_deltaA]
  exact coloringToV4Assignment_isZeroHolonomy portTwoColoring

example : HasZeroHolonomyV4Tension portTwoMap := by
  exact ⟨portDeltaAAssignment, portDeltaAAssignment_zeroHolonomy⟩

example : HasZeroHolonomyV4Tension portTwoMap ↔
    PortFourStateColorable portTwoCrossing :=
  portCombinatorialMap_tension_iff_colorable portTwoMap

example : ∃ K : (portRegionSimpleGraph portTwoCrossing).Coloring TrominoState,
    ∀ p, (coloringToV4Assignment K).label p =
      portDeltaAAssignment.label p := by
  obtain ⟨K, hK⟩ := exists_portColoring_of_zeroHolonomyV4Tension
    portTwoMap portDeltaAAssignment portDeltaAAssignment_zeroHolonomy
  refine ⟨K, ?_⟩
  intro p
  exact (hK p).trans (by rfl)

example : PortFourStateColorable portThreeCrossing ↔
    HasZeroHolonomyV4Tension portThreeMap := by
  exact (portCombinatorialMap_tension_iff_colorable portThreeMap).symm

example :
    HasZeroHolonomyV4Tension portTwoGenusZero.map ↔
      PortFourStateColorable portTwoGenusZero.map.crossing :=
  portTwoGenusZero.tension_iff_colorable

example : PortGenusZeroTensionTarget ↔ PortGenusZeroFourColorTarget :=
  portGenusZeroTensionTarget_iff_fourColorTarget

#print axioms DkMath.Tromino.portRegionSimpleGraph_adj_iff
#print axioms DkMath.Tromino.portRegionSimpleGraph_eq_regionSimpleGraph_of_assignment
#print axioms DkMath.Tromino.coloringToV4Assignment
#print axioms DkMath.Tromino.coloringToV4Assignment_isZeroHolonomy
#print axioms DkMath.Tromino.RegionPotential.toPortColoring
#print axioms DkMath.Tromino.exists_portColoring_of_zeroHolonomyV4Tension
#print axioms DkMath.Tromino.portCombinatorialMap_tension_iff_colorable
#print axioms DkMath.Tromino.PortGenusZeroCombinatorialMap.tension_iff_colorable
#print axioms DkMath.Tromino.portGenusZeroTensionTarget_iff_fourColorTarget

end DkMathTest.Tromino.PortTensionColoringAxiomAudit
