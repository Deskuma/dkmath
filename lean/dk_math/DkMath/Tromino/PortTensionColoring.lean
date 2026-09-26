/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortCombinatorialMap
import DkMath.Tromino.GraphColoringBridge

#print "file: DkMath.Tromino.PortTensionColoring"

namespace DkMath.Tromino

/-!
The historical name `V4FlowAssignment` is retained for compatibility.  In
this file an assignment together with `RegionZeroHolonomy` is treated as a
nowhere-zero V4 tension (a coboundary/exact 1-cochain), not as a Kirchhoff
conservation law for a graph flow.
-/

def portRegionCrossingRel {P : PortNetwork} (C : PortCrossing P)
    (r s : Fin P.regionCount) : Prop :=
  ∃ p : PortNetworkPort P, p.1 = r ∧ (C.cross p).1 = s

def portRegionSimpleGraph {P : PortNetwork} (C : PortCrossing P) :
    SimpleGraph (Fin P.regionCount) :=
  SimpleGraph.fromRel (portRegionCrossingRel C)

theorem portRegionSimpleGraph_adj_iff {P : PortNetwork} (C : PortCrossing P)
    (r s : Fin P.regionCount) :
    (portRegionSimpleGraph C).Adj r s ↔
      ∃ p : PortNetworkPort P, p.1 = r ∧ (C.cross p).1 = s := by
  constructor
  · intro h
    rw [portRegionSimpleGraph, SimpleGraph.fromRel_adj] at h
    rcases h with ⟨_, h | h⟩
    · exact h
    · rcases h with ⟨q, hqsource, hqtarget⟩
      refine ⟨C.cross q, hqtarget, ?_⟩
      exact (congrArg Sigma.fst (C.involutive q)).trans hqsource
  · rintro ⟨p, hsource, htarget⟩
    rw [portRegionSimpleGraph, SimpleGraph.fromRel_adj]
    have hne : r ≠ s := by
      intro hrs
      apply C.changesRegion p
      calc
        (C.cross p).1 = s := htarget
        _ = r := hrs.symm
        _ = p.1 := hsource.symm
    exact ⟨hne, Or.inl ⟨p, hsource, htarget⟩⟩

theorem portRegionSimpleGraph_adj_of_port {P : PortNetwork}
    (C : PortCrossing P) (p : PortNetworkPort P) :
    (portRegionSimpleGraph C).Adj p.1 (C.cross p).1 := by
  exact (portRegionSimpleGraph_adj_iff C p.1 (C.cross p).1).2
    ⟨p, rfl, rfl⟩

theorem portRegionSimpleGraph_eq_regionSimpleGraph_of_assignment
    {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) :
    portRegionSimpleGraph C = regionSimpleGraph A.toFlowCrossing := by
  rfl

theorem portRegionSimpleGraph_eq_regionSimpleGraph_of_flow_erasure
    {N : FlowNetwork} (C : FlowCrossing N) :
    portRegionSimpleGraph C.toPortCrossing = regionSimpleGraph C := by
  rfl

def PortFourStateColorable {P : PortNetwork} (C : PortCrossing P) : Prop :=
  Nonempty ((portRegionSimpleGraph C).Coloring TrominoState)

theorem portFourStateColorable_implies_colorable_four
    {P : PortNetwork} {C : PortCrossing P}
    (h : PortFourStateColorable C) :
    (portRegionSimpleGraph C).Colorable 4 := by
  rcases h with ⟨K⟩
  have hcard : Fintype.card TrominoState = 4 := by
    rw [Fintype.card_eq_nat_card]
    exact card_state
  have hcolorable := K.colorable
  rw [hcard] at hcolorable
  exact hcolorable

def coloringToV4Assignment {P : PortNetwork} {C : PortCrossing P}
    (K : (portRegionSimpleGraph C).Coloring TrominoState) :
    V4FlowAssignment C where
  label := fun p => K p.1 + K (C.cross p).1
  nonzero := by
    intro p hzero
    have hne := K.valid (portRegionSimpleGraph_adj_of_port C p)
    apply hne
    have h := congrArg (fun x : TrominoState => x + K (C.cross p).1) hzero
    simpa [add_assoc, state_add_self] using h
  cross_sameLabel := by
    intro p
    rw [C.involutive p]
    ac_rfl

@[simp] theorem coloringToV4Assignment_label
    {P : PortNetwork} {C : PortCrossing P}
    (K : (portRegionSimpleGraph C).Coloring TrominoState)
    (p : PortNetworkPort P) :
    (coloringToV4Assignment K).label p = K p.1 + K (C.cross p).1 := rfl

def IsZeroHolonomyV4Tension {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) : Prop :=
  RegionZeroHolonomy A.toFlowCrossing

def HasZeroHolonomyV4Tension {P : PortNetwork}
    (M : PortCombinatorialMap P) : Prop :=
  ∃ A : V4FlowAssignment M.crossing, IsZeroHolonomyV4Tension A

def coloringToRegionPotential {P : PortNetwork} {C : PortCrossing P}
    (K : (portRegionSimpleGraph C).Coloring TrominoState) :
    RegionPotential (coloringToV4Assignment K).toFlowCrossing where
  state := fun r => K r
  edgeLaw := by
    intro p
    change K (C.cross p).1 =
      K p.1 + (K p.1 + K (C.cross p).1)
    calc
      K (C.cross p).1 = 0 + K (C.cross p).1 := by rw [zero_add]
      _ = (K p.1 + K p.1) + K (C.cross p).1 := by
        rw [state_add_self]
      _ = K p.1 + (K p.1 + K (C.cross p).1) := by ac_rfl

theorem coloringToV4Assignment_isZeroHolonomy
    {P : PortNetwork} {C : PortCrossing P}
    (K : (portRegionSimpleGraph C).Coloring TrominoState) :
    IsZeroHolonomyV4Tension (coloringToV4Assignment K) :=
  regionPotential_regionZeroHolonomy (coloringToRegionPotential K)

def RegionPotential.toPortColoring
    {P : PortNetwork} {C : PortCrossing P}
    {A : V4FlowAssignment C} (Q : RegionPotential A.toFlowCrossing) :
    (portRegionSimpleGraph C).Coloring TrominoState := by
  refine SimpleGraph.Coloring.mk Q.state ?_
  intro r s h
  obtain ⟨p, hsource, htarget⟩ :=
    (portRegionSimpleGraph_adj_iff C r s).mp h
  have hne := regionPotential_adjacent_ne Q (p : FlowNetworkPort A.toFlowNetwork)
  have htarget2 : (A.toFlowCrossing.cross (p : FlowNetworkPort A.toFlowNetwork)).1 = s := by
    change (C.cross p).1 = s
    exact htarget
  change Q.state p.1 ≠ Q.state (A.toFlowCrossing.cross p).1 at hne
  rw [hsource, htarget2] at hne
  exact hne

@[simp] theorem RegionPotential.toPortColoring_apply
    {P : PortNetwork} {C : PortCrossing P}
    {A : V4FlowAssignment C} (Q : RegionPotential A.toFlowCrossing)
    (r : Fin P.regionCount) : Q.toPortColoring r = Q.state r := rfl

theorem RegionPotential.toPortColoring_label
    {P : PortNetwork} {C : PortCrossing P}
    {A : V4FlowAssignment C} (Q : RegionPotential A.toFlowCrossing)
    (p : PortNetworkPort P) :
    (coloringToV4Assignment Q.toPortColoring).label p = A.label p := by
  change Q.toPortColoring p.1 + Q.toPortColoring (C.cross p).1 = A.label p
  rw [Q.toPortColoring_apply, Q.toPortColoring_apply]
  change Q.state p.1 + Q.state (A.toFlowCrossing.cross p).1 =
    (A.toFlowNetwork.signature p.1).label p.2
  simpa [flowEdgeSource, flowEdgeTarget, flowEdgeLabel] using
    (regionPotential_edgeLabel Q (p : FlowNetworkPort A.toFlowNetwork))

theorem exists_portColoring_of_zeroHolonomyV4Tension
    {P : PortNetwork} (M : PortCombinatorialMap P)
    (A : V4FlowAssignment M.crossing)
    (hzero : IsZeroHolonomyV4Tension A) :
    ∃ K : (portRegionSimpleGraph M.crossing).Coloring TrominoState,
      ∀ p, (coloringToV4Assignment K).label p = A.label p := by
  let base : Fin P.regionCount := ⟨0, M.nonemptyRegions⟩
  have hrootPort := portRegionConnected_rooted M.crossing M.connected base
  have hrootFlow : RootedRegionConnected A.toFlowCrossing base := by
    intro s
    exact (portRootedRegionConnected_iff_flow_lift A base).mp hrootPort s
  obtain ⟨Q, _⟩ := regionPotential_exists_of_zeroHolonomy
    base 0 hrootFlow hzero
  refine ⟨Q.toPortColoring, ?_⟩
  intro p
  exact Q.toPortColoring_label p

theorem exists_portColoring_of_zeroHolonomyV4Tension_only
    {P : PortNetwork} (M : PortCombinatorialMap P)
    (A : V4FlowAssignment M.crossing)
    (hzero : IsZeroHolonomyV4Tension A) :
    ∃ _K : (portRegionSimpleGraph M.crossing).Coloring TrominoState, True := by
  obtain ⟨K, _⟩ := exists_portColoring_of_zeroHolonomyV4Tension M A hzero
  exact ⟨K, trivial⟩

theorem portCombinatorialMap_tension_iff_colorable
    {P : PortNetwork} (M : PortCombinatorialMap P) :
    HasZeroHolonomyV4Tension M ↔ PortFourStateColorable M.crossing := by
  constructor
  · rintro ⟨A, hzero⟩
    exact ⟨(exists_portColoring_of_zeroHolonomyV4Tension M A hzero).choose⟩
  · rintro ⟨K⟩
    exact ⟨coloringToV4Assignment K, coloringToV4Assignment_isZeroHolonomy K⟩

theorem PortGenusZeroCombinatorialMap.tension_iff_colorable
    {P : PortNetwork} (G : PortGenusZeroCombinatorialMap P) :
    HasZeroHolonomyV4Tension G.map ↔ PortFourStateColorable G.map.crossing := by
  exact portCombinatorialMap_tension_iff_colorable G.map

def PortGenusZeroTensionTarget : Prop :=
  ∀ (P : PortNetwork) (G : PortGenusZeroCombinatorialMap P),
    HasZeroHolonomyV4Tension G.map

def PortGenusZeroFourColorTarget : Prop :=
  ∀ (P : PortNetwork) (G : PortGenusZeroCombinatorialMap P),
    PortFourStateColorable G.map.crossing

theorem portGenusZeroTensionTarget_iff_fourColorTarget :
    PortGenusZeroTensionTarget ↔ PortGenusZeroFourColorTarget := by
  constructor
  · intro h P G
    exact (G.tension_iff_colorable).mp (h P G)
  · intro h P G
    exact (G.tension_iff_colorable).mpr (h P G)

end DkMath.Tromino
