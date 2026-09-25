/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.FlowTransitionXor

#print "file: DkMath.Tromino.RegionWalk"

namespace DkMath.Tromino

open scoped BigOperators

def flowEdgeSource {N : FlowNetwork} (_C : FlowCrossing N)
    (p : FlowNetworkPort N) : Fin N.regionCount := p.1

def flowEdgeTarget {N : FlowNetwork} (C : FlowCrossing N)
    (p : FlowNetworkPort N) : Fin N.regionCount := (C.cross p).1

def flowEdgeLabel {N : FlowNetwork} (_C : FlowCrossing N)
    (p : FlowNetworkPort N) : TrominoState :=
  (N.signature p.1).label p.2

def reverseEdge {N : FlowNetwork} (C : FlowCrossing N)
    (p : FlowNetworkPort N) : FlowNetworkPort N := C.cross p

theorem flowEdgeSource_reverseEdge {N : FlowNetwork} (C : FlowCrossing N)
    (p : FlowNetworkPort N) :
    flowEdgeSource C (reverseEdge C p) = flowEdgeTarget C p := rfl

theorem flowEdgeTarget_reverseEdge {N : FlowNetwork} (C : FlowCrossing N)
    (p : FlowNetworkPort N) :
    flowEdgeTarget C (reverseEdge C p) = flowEdgeSource C p :=
  congrArg Sigma.fst (C.involutive p)

theorem reverseEdge_reverseEdge {N : FlowNetwork} (C : FlowCrossing N)
    (p : FlowNetworkPort N) : reverseEdge C (reverseEdge C p) = p :=
  C.involutive p

theorem flowEdgeLabel_reverseEdge {N : FlowNetwork} (C : FlowCrossing N)
    (p : FlowNetworkPort N) :
    flowEdgeLabel C (reverseEdge C p) = flowEdgeLabel C p :=
  C.sameLabel p

theorem flowEdge_source_ne_target {N : FlowNetwork} (C : FlowCrossing N)
    (p : FlowNetworkPort N) :
    flowEdgeSource C p ≠ flowEdgeTarget C p :=
  (C.changesRegion p).symm

def FlowRegionWalk.Valid {N : FlowNetwork} (C : FlowCrossing N)
    (r s : Fin N.regionCount) :
    List (FlowNetworkPort N) → Prop
  | [] => r = s
  | p :: ps => p.1 = r ∧ FlowRegionWalk.Valid C (C.cross p).1 s ps

structure FlowRegionWalk {N : FlowNetwork} (C : FlowCrossing N)
    (r s : Fin N.regionCount) where
  edges : List (FlowNetworkPort N)
  valid : FlowRegionWalk.Valid C r s edges

namespace FlowRegionWalk

theorem ext {N : FlowNetwork} {C : FlowCrossing N}
    {r s : Fin N.regionCount} {w₁ w₂ : FlowRegionWalk C r s}
    (h : w₁.edges = w₂.edges) : w₁ = w₂ := by
  cases w₁
  cases w₂
  cases h
  rfl

def nil {N : FlowNetwork} (C : FlowCrossing N)
    (r : Fin N.regionCount) : FlowRegionWalk C r r :=
  ⟨[], rfl⟩

def length {N : FlowNetwork} {C : FlowCrossing N}
    {r s : Fin N.regionCount} (w : FlowRegionWalk C r s) : Nat :=
  w.edges.length

theorem valid_append {N : FlowNetwork} {C : FlowCrossing N}
    {r s t : Fin N.regionCount} {xs : List (FlowNetworkPort N)}
    (hxs : FlowRegionWalk.Valid C r s xs) {ys : List (FlowNetworkPort N)}
    (hys : FlowRegionWalk.Valid C s t ys) :
    FlowRegionWalk.Valid C r t (xs ++ ys) := by
  induction xs generalizing r s with
  | nil =>
    simp only [FlowRegionWalk.Valid] at hxs
    subst r
    exact hys
  | cons p xs ih =>
    simp only [FlowRegionWalk.Valid] at hxs ⊢
    exact ⟨hxs.1, ih hxs.2 hys⟩

def append {N : FlowNetwork} {C : FlowCrossing N}
    {r s t : Fin N.regionCount}
    (w₁ : FlowRegionWalk C r s) (w₂ : FlowRegionWalk C s t) :
    FlowRegionWalk C r t :=
  ⟨w₁.edges ++ w₂.edges, valid_append w₁.valid w₂.valid⟩

@[simp] theorem append_nil_left {N : FlowNetwork} {C : FlowCrossing N}
    {r s : Fin N.regionCount} (w : FlowRegionWalk C r s) :
    append (nil C r) w = w := by
  apply FlowRegionWalk.ext
  rfl

@[simp] theorem append_nil_right {N : FlowNetwork} {C : FlowCrossing N}
    {r s : Fin N.regionCount} (w : FlowRegionWalk C r s) :
    append w (nil C s) = w := by
  apply FlowRegionWalk.ext
  simp [append, nil]

theorem append_assoc {N : FlowNetwork} {C : FlowCrossing N}
    {r s t u : Fin N.regionCount}
    (w₁ : FlowRegionWalk C r s) (w₂ : FlowRegionWalk C s t)
    (w₃ : FlowRegionWalk C t u) :
    append (append w₁ w₂) w₃ = append w₁ (append w₂ w₃) := by
  apply FlowRegionWalk.ext
  simp [append, List.append_assoc]

def singleton {N : FlowNetwork} (C : FlowCrossing N)
    (p : FlowNetworkPort N) : FlowRegionWalk C p.1 (C.cross p).1 :=
  ⟨[p], by simp [FlowRegionWalk.Valid]⟩

def reverseEdges {N : FlowNetwork} (C : FlowCrossing N) :
    List (FlowNetworkPort N) → List (FlowNetworkPort N) :=
  fun xs => xs.reverse.map C.cross

theorem valid_reverseEdges {N : FlowNetwork} {C : FlowCrossing N}
    {r s : Fin N.regionCount} {xs : List (FlowNetworkPort N)}
    (hxs : FlowRegionWalk.Valid C r s xs) :
    FlowRegionWalk.Valid C s r (reverseEdges C xs) := by
  induction xs generalizing r s with
  | nil =>
    simp only [FlowRegionWalk.Valid, reverseEdges] at *
    exact hxs.symm
  | cons p xs ih =>
    simp only [FlowRegionWalk.Valid] at hxs
    have htail := ih hxs.2
    have hcross : FlowRegionWalk.Valid C (C.cross p).1 p.1 [C.cross p] := by
      change (C.cross p).1 = (C.cross p).1 ∧
        (C.cross (C.cross p)).1 = p.1
      exact ⟨rfl, congrArg Sigma.fst (C.involutive p)⟩
    have happ := valid_append htail hcross
    simpa only [reverseEdges, List.reverse_cons, List.map_append,
      List.map_singleton, hxs.1] using happ

def reverse {N : FlowNetwork} {C : FlowCrossing N}
    {r s : Fin N.regionCount} (w : FlowRegionWalk C r s) :
    FlowRegionWalk C s r :=
  ⟨reverseEdges C w.edges, valid_reverseEdges w.valid⟩

@[simp] theorem reverse_nil {N : FlowNetwork} {C : FlowCrossing N}
    (r : Fin N.regionCount) :
    reverse (nil C r) = nil C r := by
  apply FlowRegionWalk.ext
  rfl

theorem reverse_append {N : FlowNetwork} {C : FlowCrossing N}
    {r s t : Fin N.regionCount}
    (w₁ : FlowRegionWalk C r s) (w₂ : FlowRegionWalk C s t) :
    reverse (append w₁ w₂) = append (reverse w₂) (reverse w₁) := by
  apply FlowRegionWalk.ext
  simp [reverse, append, reverseEdges, List.map_append]

theorem reverse_reverse {N : FlowNetwork} {C : FlowCrossing N}
    {r s : Fin N.regionCount} (w : FlowRegionWalk C r s) :
    reverse (reverse w) = w := by
  apply FlowRegionWalk.ext
  simp [reverse, reverseEdges, List.map_map, C.involutive]

end FlowRegionWalk

def regionWalkXor {N : FlowNetwork} {C : FlowCrossing N}
    {r s : Fin N.regionCount} (W : FlowRegionWalk C r s) : TrominoState :=
  (W.edges.map (flowEdgeLabel C)).sum

@[simp] theorem regionWalkXor_nil {N : FlowNetwork} (C : FlowCrossing N)
    (r : Fin N.regionCount) :
    regionWalkXor (FlowRegionWalk.nil C r) = 0 := by
  simp [regionWalkXor, FlowRegionWalk.nil]

theorem regionWalkXor_singleton {N : FlowNetwork} (C : FlowCrossing N)
    (p : FlowNetworkPort N) :
    regionWalkXor (FlowRegionWalk.singleton C p) = flowEdgeLabel C p := by
  simp [regionWalkXor, FlowRegionWalk.singleton]

theorem regionWalkXor_append {N : FlowNetwork} {C : FlowCrossing N}
    {r s t : Fin N.regionCount}
    (W₁ : FlowRegionWalk C r s) (W₂ : FlowRegionWalk C s t) :
    regionWalkXor (FlowRegionWalk.append W₁ W₂) =
      regionWalkXor W₁ + regionWalkXor W₂ := by
  simp [regionWalkXor, FlowRegionWalk.append, List.map_append, List.sum_append]

theorem flowEdgeLabel_sum_cross {N : FlowNetwork} (C : FlowCrossing N)
    (xs : List (FlowNetworkPort N)) :
    (xs.map C.cross |>.map (flowEdgeLabel C)).sum =
      (xs.map (flowEdgeLabel C)).sum := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    simp only [List.map, List.sum_cons]
    have hp : flowEdgeLabel C (C.cross p) = flowEdgeLabel C p :=
      C.sameLabel p
    rw [hp, ih]

theorem regionWalkXor_reverse {N : FlowNetwork} {C : FlowCrossing N}
    {r s : Fin N.regionCount} (W : FlowRegionWalk C r s) :
    regionWalkXor (FlowRegionWalk.reverse W) = regionWalkXor W := by
  simp only [regionWalkXor, FlowRegionWalk.reverse, FlowRegionWalk.reverseEdges,
    List.map_reverse, List.sum_reverse]
  exact flowEdgeLabel_sum_cross C W.edges

abbrev ClosedRegionWalk {N : FlowNetwork} (C : FlowCrossing N)
    (r : Fin N.regionCount) := FlowRegionWalk C r r

def RegionZeroHolonomy {N : FlowNetwork} (C : FlowCrossing N) : Prop :=
  ∀ r (W : ClosedRegionWalk C r), regionWalkXor W = 0

theorem regionWalkXor_eq_of_zeroHolonomy {N : FlowNetwork} (C : FlowCrossing N)
    (hzero : RegionZeroHolonomy C)
    {r s : Fin N.regionCount} (W₁ W₂ : FlowRegionWalk C r s) :
    regionWalkXor W₁ = regionWalkXor W₂ := by
  have hclosed := hzero r (FlowRegionWalk.append W₁ (FlowRegionWalk.reverse W₂))
  rw [regionWalkXor_append, regionWalkXor_reverse] at hclosed
  calc
    regionWalkXor W₁ = regionWalkXor W₁ + 0 := by rw [add_zero]
    _ = regionWalkXor W₁ +
        (regionWalkXor W₂ + regionWalkXor W₂) := by
      rw [state_add_self, add_zero]
    _ = (regionWalkXor W₁ + regionWalkXor W₂) +
        regionWalkXor W₂ := by ac_rfl
    _ = 0 + regionWalkXor W₂ := by rw [hclosed]
    _ = regionWalkXor W₂ := by rw [zero_add]

theorem RegionZeroHolonomy_of_same_endpoint_xor
    {N : FlowNetwork} (C : FlowCrossing N)
    (heq : ∀ r s (W₁ W₂ : FlowRegionWalk C r s),
      regionWalkXor W₁ = regionWalkXor W₂) :
    RegionZeroHolonomy C := by
  intro r W
  have h := heq r r (FlowRegionWalk.nil C r) W
  rw [regionWalkXor_nil] at h
  exact h.symm

def RegionReachable {N : FlowNetwork} (C : FlowCrossing N)
    (r s : Fin N.regionCount) : Prop :=
  Nonempty (FlowRegionWalk C r s)

theorem regionReachable_refl {N : FlowNetwork} (C : FlowCrossing N)
    (r : Fin N.regionCount) : RegionReachable C r r :=
  ⟨FlowRegionWalk.nil C r⟩

theorem regionReachable_symm {N : FlowNetwork} (C : FlowCrossing N)
    {r s : Fin N.regionCount} : RegionReachable C r s → RegionReachable C s r := by
  rintro ⟨W⟩
  exact ⟨FlowRegionWalk.reverse W⟩

theorem regionReachable_trans {N : FlowNetwork} (C : FlowCrossing N)
    {r s t : Fin N.regionCount} :
    RegionReachable C r s → RegionReachable C s t → RegionReachable C r t := by
  rintro ⟨W₁⟩ ⟨W₂⟩
  exact ⟨FlowRegionWalk.append W₁ W₂⟩

def transitionRegionWalk (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    (n : Nat) →
      FlowRegionWalk N.crossing p.1
        ((flowTransitionStep N)^[n] p).1
  | 0 => FlowRegionWalk.nil N.crossing p.1
  | n + 1 =>
      let q := (flowTransitionStep N)^[n] p
      let W := FlowRegionWalk.append
        (transitionRegionWalk N p n) (FlowRegionWalk.singleton N.crossing q)
      have htarget :
          (N.crossing.cross q).1 = ((flowTransitionStep N)^[n + 1] p).1 := by
        rw [Function.iterate_succ_apply']
        rfl
      ⟨W.edges, by simpa [htarget] using W.valid⟩

theorem flowTransitionXor_succ (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) (n : Nat) :
    flowTransitionXor N p (n + 1) =
      flowTransitionXor N p n +
        flowEdgeLabel N.crossing ((flowTransitionStep N)^[n] p) := by
  rw [flowTransitionXor, Finset.sum_range_succ]
  rfl

theorem transitionRegionWalk_xor (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) (n : Nat) :
    regionWalkXor (transitionRegionWalk N p n) =
      flowTransitionXor N p n := by
  induction n with
  | zero =>
    change regionWalkXor (FlowRegionWalk.nil N.crossing p.1) =
      flowTransitionXor N p 0
    simp [flowTransitionXor]
  | succ n ih =>
    let q := (flowTransitionStep N)^[n] p
    change regionWalkXor
      (FlowRegionWalk.append (transitionRegionWalk N p n)
        (FlowRegionWalk.singleton N.crossing q)) =
      flowTransitionXor N p (n + 1)
    rw [regionWalkXor_append, regionWalkXor_singleton, ih,
      flowTransitionXor_succ]

theorem transitionRegionWalk_endpoint (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) (n : Nat) :
    (transitionRegionWalk N p n).edges.length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [transitionRegionWalk, FlowRegionWalk.append, FlowRegionWalk.singleton, ih]

def transitionRegionWalk_closed_of_return (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) (n : Nat)
    (hreturn : FlowTransitionReturn N p n) :
    ClosedRegionWalk N.crossing p.1 := by
  have W := transitionRegionWalk N p n
  refine ⟨W.edges, ?_⟩
  simpa [hreturn.2] using W.valid

theorem flowTransitionXor_eq_zero_of_regionZeroHolonomy
    (N : ClosedFlowNetwork) (p : FlowNetworkPort N.toFlowNetwork) (n : Nat)
    (hzero : RegionZeroHolonomy N.crossing)
    (hreturn : FlowTransitionReturn N p n) :
    flowTransitionXor N p n = 0 := by
  rw [← transitionRegionWalk_xor N p n]
  exact hzero p.1 (transitionRegionWalk_closed_of_return N p n hreturn)

theorem primitiveFlowTransitionReturn_even_of_regionZeroHolonomy
    (N : ClosedFlowNetwork) (p : FlowNetworkPort N.toFlowNetwork) (n : Nat)
    (hzero : RegionZeroHolonomy N.crossing)
    (hprimitive : FlowPrimitiveTransitionReturn N p n) :
    n % 2 = 0 := by
  apply (flowPrimitiveCycleXor_iff_even N p n hprimitive).mp
  exact flowTransitionXor_eq_zero_of_regionZeroHolonomy N p n hzero hprimitive.1

end DkMath.Tromino
