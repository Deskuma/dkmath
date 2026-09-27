/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Combinatorics.SimpleGraph.Dart
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import DkMath.Tromino.RegionPotential

#print "file: DkMath.Tromino.GraphColoringBridge"

namespace DkMath.Tromino

def regionCrossingRel {N : FlowNetwork} (C : FlowCrossing N)
    (r s : Fin N.regionCount) : Prop :=
  ∃ p : FlowNetworkPort N, p.1 = r ∧ (C.cross p).1 = s

def regionSimpleGraph {N : FlowNetwork} (C : FlowCrossing N) :
    SimpleGraph (Fin N.regionCount) :=
  SimpleGraph.fromRel (regionCrossingRel C)

theorem regionSimpleGraph_adj_iff {N : FlowNetwork} (C : FlowCrossing N)
    (r s : Fin N.regionCount) :
    (regionSimpleGraph C).Adj r s ↔
      ∃ p : FlowNetworkPort N, p.1 = r ∧ (C.cross p).1 = s := by
  constructor
  · intro h
    rw [regionSimpleGraph, SimpleGraph.fromRel_adj] at h
    rcases h with ⟨_, h | h⟩
    · exact h
    · rcases h with ⟨q, hqsource, hqtarget⟩
      refine ⟨C.cross q, hqtarget, ?_⟩
      exact (congrArg Sigma.fst (C.involutive q)).trans hqsource
  · rintro ⟨p, hsource, htarget⟩
    rw [regionSimpleGraph, SimpleGraph.fromRel_adj]
    have hne : r ≠ s := by
      intro hrs
      apply C.changesRegion p
      calc
        (C.cross p).1 = s := htarget
        _ = r := hrs.symm
        _ = p.1 := hsource.symm
    exact ⟨hne, Or.inl ⟨p, hsource, htarget⟩⟩

theorem regionSimpleGraph_adj_of_port {N : FlowNetwork}
    (C : FlowCrossing N) (p : FlowNetworkPort N) :
    (regionSimpleGraph C).Adj p.1 (C.cross p).1 := by
  exact (regionSimpleGraph_adj_iff C p.1 (C.cross p).1).2 ⟨p, rfl, rfl⟩

def flowPortToDart {N : FlowNetwork} (C : FlowCrossing N)
    (p : FlowNetworkPort N) : (regionSimpleGraph C).Dart :=
  ⟨(flowEdgeSource C p, flowEdgeTarget C p), regionSimpleGraph_adj_of_port C p⟩

@[simp] theorem flowPortToDart_fst {N : FlowNetwork} (C : FlowCrossing N)
    (p : FlowNetworkPort N) : (flowPortToDart C p).fst = flowEdgeSource C p := rfl

@[simp] theorem flowPortToDart_snd {N : FlowNetwork} (C : FlowCrossing N)
    (p : FlowNetworkPort N) : (flowPortToDart C p).snd = flowEdgeTarget C p := rfl

theorem flowPortToDart_reverse {N : FlowNetwork} (C : FlowCrossing N)
    (p : FlowNetworkPort N) :
    flowPortToDart C (reverseEdge C p) = (flowPortToDart C p).symm := by
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · exact flowEdgeSource_reverseEdge C p
  · exact flowEdgeTarget_reverseEdge C p

theorem flowPortToDart_edge_reverse {N : FlowNetwork} (C : FlowCrossing N)
    (p : FlowNetworkPort N) :
    (flowPortToDart C (reverseEdge C p)).edge = (flowPortToDart C p).edge := by
  rw [flowPortToDart_reverse]
  exact SimpleGraph.Dart.edge_symm _

theorem dart_has_flowPort {N : FlowNetwork} (C : FlowCrossing N)
    (d : (regionSimpleGraph C).Dart) :
    ∃ p : FlowNetworkPort N, p.1 = d.fst ∧ (C.cross p).1 = d.snd := by
  exact (regionSimpleGraph_adj_iff C d.fst d.snd).mp d.adj

def RegionPotential.toColoring {N : FlowNetwork} {C : FlowCrossing N}
    (P : RegionPotential C) : (regionSimpleGraph C).Coloring TrominoState :=
  SimpleGraph.Coloring.mk P.state (by
    intro r s h
    obtain ⟨p, hsource, htarget⟩ :=
      (regionSimpleGraph_adj_iff C r s).mp h
    have hne := regionPotential_adjacent_ne P p
    simpa [flowEdgeSource, flowEdgeTarget, hsource, htarget] using hne)

@[simp] theorem RegionPotential.toColoring_apply
    {N : FlowNetwork} {C : FlowCrossing N} (P : RegionPotential C)
    (r : Fin N.regionCount) : P.toColoring r = P.state r := rfl

theorem RegionPotential.toColoring_colorable
    {N : FlowNetwork} {C : FlowCrossing N} (P : RegionPotential C) :
    (regionSimpleGraph C).Colorable 4 := by
  have hcard : Fintype.card TrominoState = 4 := by
    rw [Fintype.card_eq_nat_card]
    exact card_state
  have hc := P.toColoring.colorable
  rw [hcard] at hc
  exact hc

theorem RegionPotential.toColoring_edgeLabel
    {N : FlowNetwork} {C : FlowCrossing N} (P : RegionPotential C)
    (p : FlowNetworkPort N) :
    P.toColoring (flowEdgeSource C p) +
        P.toColoring (flowEdgeTarget C p) = flowEdgeLabel C p := by
  exact regionPotential_edgeLabel P p

theorem exists_regionColoring_of_zeroHolonomy
    {N : FlowNetwork} {C : FlowCrossing N}
    (base : Fin N.regionCount)
    (hreach : RootedRegionConnected C base)
    (hzero : RegionZeroHolonomy C) :
    ∃ _K : (regionSimpleGraph C).Coloring TrominoState, True := by
  obtain ⟨P, _⟩ := regionPotential_exists_of_zeroHolonomy base 0 hreach hzero
  exact ⟨P.toColoring, trivial⟩

theorem regionSimpleGraph_colorable_four_of_zeroHolonomy
    {N : FlowNetwork} {C : FlowCrossing N}
    (base : Fin N.regionCount)
    (hreach : RootedRegionConnected C base)
    (hzero : RegionZeroHolonomy C) :
    (regionSimpleGraph C).Colorable 4 := by
  obtain ⟨P, _⟩ := regionPotential_exists_of_zeroHolonomy base 0 hreach hzero
  exact P.toColoring_colorable

end DkMath.Tromino
