/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.RegionWalk

#print "file: DkMath.Tromino.RegionPotential"

namespace DkMath.Tromino

structure RegionPotential {N : FlowNetwork} (C : FlowCrossing N) where
  state : Fin N.regionCount → TrominoState
  edgeLaw : ∀ p : FlowNetworkPort N,
    state (flowEdgeTarget C p) =
      state (flowEdgeSource C p) + flowEdgeLabel C p

theorem regionPotential_integrates_valid
    {N : FlowNetwork} {C : FlowCrossing N}
    (P : RegionPotential C) {r s : Fin N.regionCount}
    (xs : List (FlowNetworkPort N))
    (hvalid : FlowRegionWalk.Valid C r s xs) :
    P.state s = P.state r + (xs.map (flowEdgeLabel C)).sum := by
  induction xs generalizing r s with
  | nil =>
    simp only [FlowRegionWalk.Valid] at hvalid
    subst s
    simp
  | cons p xs ih =>
    simp only [FlowRegionWalk.Valid] at hvalid
    have htail := ih hvalid.2
    calc
      P.state s = P.state (C.cross p).1 +
          (xs.map (flowEdgeLabel C)).sum := htail
      _ = (P.state p.1 + flowEdgeLabel C p) +
          (xs.map (flowEdgeLabel C)).sum := by
        have hedge : P.state (C.cross p).1 =
            P.state p.1 + flowEdgeLabel C p := by
          exact P.edgeLaw p
        rw [hedge]
      _ = P.state p.1 +
          (flowEdgeLabel C p + (xs.map (flowEdgeLabel C)).sum) := by
        ac_rfl
      _ = P.state r + (List.map (flowEdgeLabel C) (p :: xs)).sum := by
        rw [hvalid.1]
        rfl

theorem regionPotential_integrates
    {N : FlowNetwork} {C : FlowCrossing N}
    (P : RegionPotential C) {r s : Fin N.regionCount}
    (W : FlowRegionWalk C r s) :
    P.state s = P.state r + regionWalkXor W := by
  exact regionPotential_integrates_valid P W.edges W.valid

theorem regionPotential_integrates_nil
    {N : FlowNetwork} {C : FlowCrossing N}
    (P : RegionPotential C) (r : Fin N.regionCount) :
    P.state r = P.state r + regionWalkXor (FlowRegionWalk.nil C r) := by
  simp [regionWalkXor_nil]

theorem regionPotential_integrates_singleton
    {N : FlowNetwork} {C : FlowCrossing N}
    (P : RegionPotential C) (p : FlowNetworkPort N) :
    P.state (flowEdgeTarget C p) =
      P.state (flowEdgeSource C p) +
        regionWalkXor (FlowRegionWalk.singleton C p) := by
  simpa [regionWalkXor_singleton] using P.edgeLaw p

theorem regionPotential_regionZeroHolonomy
    {N : FlowNetwork} {C : FlowCrossing N}
    (P : RegionPotential C) :
    RegionZeroHolonomy C := by
  intro r W
  have h := regionPotential_integrates P W
  calc
    regionWalkXor W = 0 + regionWalkXor W := by rw [zero_add]
    _ = (P.state r + P.state r) + regionWalkXor W := by
      rw [state_add_self, zero_add]
    _ = P.state r + (P.state r + regionWalkXor W) := by ac_rfl
    _ = P.state r + P.state r := by rw [← h]
    _ = 0 := state_add_self _

def RootedRegionConnected {N : FlowNetwork}
    (C : FlowCrossing N) (base : Fin N.regionCount) : Prop :=
  ∀ s, RegionReachable C base s

theorem regionPotential_exists_of_zeroHolonomy
    {N : FlowNetwork} {C : FlowCrossing N}
    (base : Fin N.regionCount) (baseState : TrominoState)
    (hreach : RootedRegionConnected C base)
    (hzero : RegionZeroHolonomy C) :
    ∃ P : RegionPotential C, P.state base = baseState := by
  classical
  let walk : ∀ s, FlowRegionWalk C base s :=
    fun s => Classical.choice (hreach s)
  let baseWalk : FlowRegionWalk C base base := walk base
  let potentialState : Fin N.regionCount → TrominoState := fun s =>
    baseState + regionWalkXor (walk s) + regionWalkXor baseWalk
  have hedge : ∀ p : FlowNetworkPort N,
      potentialState (flowEdgeTarget C p) =
        potentialState (flowEdgeSource C p) + flowEdgeLabel C p := by
    intro p
    have hpaths := regionWalkXor_eq_of_zeroHolonomy C hzero
      (FlowRegionWalk.append (walk p.1)
        (FlowRegionWalk.singleton C p)) (walk (C.cross p).1)
    have happ := regionWalkXor_append
      (walk p.1) (FlowRegionWalk.singleton C p)
    have hsingle := regionWalkXor_singleton C p
    rw [happ, hsingle] at hpaths
    calc
      potentialState (flowEdgeTarget C p) =
          baseState + regionWalkXor (walk (C.cross p).1) +
            regionWalkXor baseWalk := rfl
      _ = baseState +
          (regionWalkXor (walk p.1) +
            flowEdgeLabel C p) + regionWalkXor baseWalk := by
        rw [← hpaths]
      _ = potentialState p.1 + flowEdgeLabel C p := by
        simp only [potentialState]
        ac_rfl
      _ = potentialState (flowEdgeSource C p) + flowEdgeLabel C p := by
        rfl
  refine ⟨⟨potentialState, hedge⟩, ?_⟩
  change baseState + regionWalkXor (walk base) +
    regionWalkXor baseWalk = baseState
  change baseState + regionWalkXor baseWalk +
    regionWalkXor baseWalk = baseState
  rw [add_assoc, state_add_self, add_zero]

theorem regionPotential_eq_of_same_base
    {N : FlowNetwork} {C : FlowCrossing N}
    (base : Fin N.regionCount) (hreach : RootedRegionConnected C base)
    (P Q : RegionPotential C)
    (hbase : P.state base = Q.state base) :
    ∀ s, P.state s = Q.state s := by
  intro s
  obtain ⟨W⟩ := hreach s
  calc
    P.state s = P.state base + regionWalkXor W :=
      regionPotential_integrates P W
    _ = Q.state base + regionWalkXor W := by rw [hbase]
    _ = Q.state s := (regionPotential_integrates Q W).symm

theorem regionPotential_ext
    {N : FlowNetwork} {C : FlowCrossing N}
    {P Q : RegionPotential C}
    (h : ∀ r, P.state r = Q.state r) : P = Q := by
  cases P with
  | mk pstate plaw =>
    cases Q with
    | mk qstate qlaw =>
      simp only at h
      congr
      funext r
      exact h r

def translateRegionPotential
    {N : FlowNetwork} {C : FlowCrossing N}
    (gamma : TrominoState) (P : RegionPotential C) : RegionPotential C where
  state := fun r => P.state r + gamma
  edgeLaw := by
    intro p
    rw [P.edgeLaw p]
    ac_rfl

theorem translateRegionPotential_state
    {N : FlowNetwork} {C : FlowCrossing N}
    (gamma : TrominoState) (P : RegionPotential C)
    (r : Fin N.regionCount) :
    (translateRegionPotential gamma P).state r = P.state r + gamma := rfl

theorem regionPotential_gauge
    {N : FlowNetwork} {C : FlowCrossing N}
    (base : Fin N.regionCount) (hreach : RootedRegionConnected C base)
    (P Q : RegionPotential C) :
    ∀ s, Q.state s =
      P.state s + (P.state base + Q.state base) := by
  intro s
  obtain ⟨W⟩ := hreach s
  have hp := regionPotential_integrates P W
  have hq := regionPotential_integrates Q W
  calc
    Q.state s = Q.state base + regionWalkXor W := hq
    _ = Q.state base + regionWalkXor W + 0 := by rw [add_zero]
    _ = Q.state base + regionWalkXor W +
        (P.state base + P.state base) := by
      rw [state_add_self, add_zero]
    _ = (P.state base + regionWalkXor W) +
        (P.state base + Q.state base) := by ac_rfl
    _ = P.state s + (P.state base + Q.state base) := by rw [← hp]

theorem regionPotential_edgeLabel
    {N : FlowNetwork} {C : FlowCrossing N}
    (P : RegionPotential C) (p : FlowNetworkPort N) :
    P.state (flowEdgeSource C p) + P.state (flowEdgeTarget C p) =
      flowEdgeLabel C p := by
  rw [P.edgeLaw p]
  rw [← add_assoc, state_add_self, zero_add]

theorem regionPotential_adjacent_ne
    {N : FlowNetwork} {C : FlowCrossing N}
    (P : RegionPotential C) (p : FlowNetworkPort N) :
    P.state (flowEdgeSource C p) ≠ P.state (flowEdgeTarget C p) := by
  intro heq
  have hlabel := regionPotential_edgeLabel P p
  rw [heq, state_add_self] at hlabel
  exact (N.signature p.1).nonzero p.2 hlabel.symm

theorem regionPotential_proper_on_crossing
    {N : FlowNetwork} {C : FlowCrossing N}
    (P : RegionPotential C) (p : FlowNetworkPort N) :
    P.state (flowEdgeSource C p) ≠ P.state (flowEdgeTarget C p) :=
  regionPotential_adjacent_ne P p

theorem regionZeroHolonomy_iff_regionPotential
    {N : FlowNetwork} {C : FlowCrossing N}
    (base : Fin N.regionCount) (baseState : TrominoState)
    (hreach : RootedRegionConnected C base) :
    RegionZeroHolonomy C ↔
      ∃ P : RegionPotential C, P.state base = baseState := by
  constructor
  · exact regionPotential_exists_of_zeroHolonomy base baseState hreach
  · rintro ⟨P, _⟩
    exact regionPotential_regionZeroHolonomy P

end DkMath.Tromino
