/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortNetwork
import DkMath.Tromino.RegionWalk

#print "file: DkMath.Tromino.PortRegionWalk"

/-!
# Walks in the region adjacency graph

A `PortRegionWalk` is a list of crossing ports whose successive region
indices match.  The validity predicate is deliberately inductive: each dart
must start in the current region, and the crossed dart determines the next
one.  The constructors and lemmas below give concatenation, reversal, and
the induced equivalence relation of region reachability.  Consequently
connectedness is expressed entirely by finite port data and can be
transported to and from the earlier flow-network presentation without
changing the underlying list of darts.
-/

namespace DkMath.Tromino

/-- Inductive validity condition for a list of crossing darts.

The empty list witnesses equality of its endpoints.  A nonempty list is
valid when its first dart starts in the current region and its tail is valid
from the region reached after crossing that dart.  This is the path
invariant used by every walk operation below. -/
def PortRegionWalk.Valid {P : PortNetwork} (C : PortCrossing P)
    (r s : Fin P.regionCount) :
    List (PortNetworkPort P) → Prop
  | [] => r = s
  | p :: ps => p.1 = r ∧ PortRegionWalk.Valid C (C.cross p).1 s ps

/-- A valid finite walk between two region indices.

The list records the local incidences traversed by the walk; `valid` ties
the list's endpoints to the crossing involution rather than treating it as
an arbitrary sequence of ports. -/
structure PortRegionWalk {P : PortNetwork} (C : PortCrossing P)
    (r s : Fin P.regionCount) where
  edges : List (PortNetworkPort P)
  valid : PortRegionWalk.Valid C r s edges

/-- Flow-walk validity descends to the port presentation. -/
theorem flowValid_toPort {N : FlowNetwork} {C : FlowCrossing N}
    {r s : Fin N.regionCount} {xs : List (FlowNetworkPort N)}
    (h : FlowRegionWalk.Valid C r s xs) :
    PortRegionWalk.Valid C.toPortCrossing r s xs := by
  induction xs generalizing r s with
  | nil =>
    simp only [FlowRegionWalk.Valid] at h
    exact h
  | cons p xs ih =>
    simp only [FlowRegionWalk.Valid] at h
    simp only [PortRegionWalk.Valid]
    exact ⟨h.1, ih h.2⟩

/-- Port-walk validity lifts to the flow presentation under an assignment. -/
theorem portValid_toFlow {P : PortNetwork} {C : PortCrossing P}
    {r s : Fin P.regionCount} {xs : List (PortNetworkPort P)}
    (h : PortRegionWalk.Valid C r s xs) (A : V4FlowAssignment C) :
    FlowRegionWalk.Valid A.toFlowCrossing r s xs := by
  induction xs generalizing r s with
  | nil =>
    simp only [PortRegionWalk.Valid] at h
    exact h
  | cons p xs ih =>
    simp only [PortRegionWalk.Valid] at h
    simp only [FlowRegionWalk.Valid]
    exact ⟨h.1, ih h.2⟩

namespace PortRegionWalk

/-- A port walk is determined by its dart list. -/
theorem ext {P : PortNetwork} {C : PortCrossing P}
    {r s : Fin P.regionCount} {w₁ w₂ : PortRegionWalk C r s}
    (h : w₁.edges = w₂.edges) : w₁ = w₂ := by
  cases w₁
  cases w₂
  cases h
  rfl

/-- The empty walk between equal regions. -/
def nil {P : PortNetwork} (C : PortCrossing P)
    (r : Fin P.regionCount) : PortRegionWalk C r r :=
  ⟨[], rfl⟩

/-- Number of crossing darts in a walk. -/
def length {P : PortNetwork} {C : PortCrossing P}
    {r s : Fin P.regionCount} (w : PortRegionWalk C r s) : Nat :=
  w.edges.length

/-- Appending composable valid walks yields a valid walk.

Induction on the first list transports its endpoint invariant to the start
of the second list.  This is the finite path-composition law behind
reachability transitivity. -/
theorem valid_append {P : PortNetwork} {C : PortCrossing P}
    {r s t : Fin P.regionCount} {xs : List (PortNetworkPort P)}
    (hxs : PortRegionWalk.Valid C r s xs) {ys : List (PortNetworkPort P)}
    (hys : PortRegionWalk.Valid C s t ys) :
    PortRegionWalk.Valid C r t (xs ++ ys) := by
  induction xs generalizing r s with
  | nil =>
    simp only [PortRegionWalk.Valid] at hxs
    subst r
    exact hys
  | cons p xs ih =>
    simp only [PortRegionWalk.Valid] at hxs ⊢
    exact ⟨hxs.1, ih hxs.2 hys⟩

/-- Concatenate two walks whose endpoint and start agree.

The endpoint indices are part of the type, so only composable walks can be
passed to `append`; validity of the concatenated list is supplied by
`valid_append`. -/
def append {P : PortNetwork} {C : PortCrossing P}
    {r s t : Fin P.regionCount}
    (w₁ : PortRegionWalk C r s) (w₂ : PortRegionWalk C s t) :
    PortRegionWalk C r t :=
  ⟨w₁.edges ++ w₂.edges, valid_append w₁.valid w₂.valid⟩

@[simp] theorem append_nil_left {P : PortNetwork} {C : PortCrossing P}
    {r s : Fin P.regionCount} (w : PortRegionWalk C r s) :
    append (nil C r) w = w := by
  apply PortRegionWalk.ext
  rfl

@[simp] theorem append_nil_right {P : PortNetwork} {C : PortCrossing P}
    {r s : Fin P.regionCount} (w : PortRegionWalk C r s) :
    append w (nil C s) = w := by
  apply PortRegionWalk.ext
  simp [append, nil]

/-- Walk concatenation is associative. -/
theorem append_assoc {P : PortNetwork} {C : PortCrossing P}
    {r s t u : Fin P.regionCount}
    (w₁ : PortRegionWalk C r s) (w₂ : PortRegionWalk C s t)
    (w₃ : PortRegionWalk C t u) :
    append (append w₁ w₂) w₃ = append w₁ (append w₂ w₃) := by
  apply PortRegionWalk.ext
  simp [append, List.append_assoc]

/-- The one-dart walk starting at a port's source region. -/
def singleton {P : PortNetwork} (C : PortCrossing P)
    (p : PortNetworkPort P) : PortRegionWalk C p.1 (C.cross p).1 :=
  ⟨[p], by simp [PortRegionWalk.Valid]⟩

/-- Reverse the order and crossing direction of a dart list.

Reversal is not just list reversal: every dart is replaced by its crossed
end.  The involution then makes the reversed sequence traverse the original
path backwards. -/
def reverseEdges {P : PortNetwork} (C : PortCrossing P) :
    List (PortNetworkPort P) → List (PortNetworkPort P) :=
  fun xs => xs.reverse.map C.cross

/-- Reversing edges turns a valid walk around. -/
theorem valid_reverseEdges {P : PortNetwork} {C : PortCrossing P}
    {r s : Fin P.regionCount} {xs : List (PortNetworkPort P)}
    (hxs : PortRegionWalk.Valid C r s xs) :
    PortRegionWalk.Valid C s r (reverseEdges C xs) := by
  induction xs generalizing r s with
  | nil =>
    simp only [PortRegionWalk.Valid, reverseEdges] at *
    exact hxs.symm
  | cons p xs ih =>
    simp only [PortRegionWalk.Valid] at hxs
    have htail := ih hxs.2
    have hcross : PortRegionWalk.Valid C (C.cross p).1 p.1 [C.cross p] := by
      change (C.cross p).1 = (C.cross p).1 ∧
        (C.cross (C.cross p)).1 = p.1
      exact ⟨rfl, congrArg Sigma.fst (C.involutive p)⟩
    have happ := valid_append htail hcross
    simpa only [reverseEdges, List.reverse_cons, List.map_append,
      List.map_singleton, hxs.1] using happ

/-- Reverse a valid walk and exchange its endpoints.

The local crossing involution is exactly what closes the endpoint proof,
so reachability will be symmetric even though a walk is represented by an
oriented list. -/
def reverse {P : PortNetwork} {C : PortCrossing P}
    {r s : Fin P.regionCount} (w : PortRegionWalk C r s) :
    PortRegionWalk C s r :=
  ⟨reverseEdges C w.edges, valid_reverseEdges w.valid⟩

@[simp] theorem reverse_nil {P : PortNetwork} {C : PortCrossing P}
    (r : Fin P.regionCount) :
    reverse (nil C r) = nil C r := by
  apply PortRegionWalk.ext
  rfl

/-- Reversal changes an appended walk into reversed append order. -/
theorem reverse_append {P : PortNetwork} {C : PortCrossing P}
    {r s t : Fin P.regionCount}
    (w₁ : PortRegionWalk C r s) (w₂ : PortRegionWalk C s t) :
    reverse (append w₁ w₂) = append (reverse w₂) (reverse w₁) := by
  apply PortRegionWalk.ext
  simp [reverse, append, reverseEdges, List.map_append]

/-- Reversing twice recovers the original walk. -/
theorem reverse_reverse {P : PortNetwork} {C : PortCrossing P}
    {r s : Fin P.regionCount} (w : PortRegionWalk C r s) :
    reverse (reverse w) = w := by
  apply PortRegionWalk.ext
  simp [reverse, reverseEdges, List.map_map, C.involutive]

end PortRegionWalk

/-- Region reachability generated by finite valid walks.

This is the reflexive-transitive connectivity relation generated by the
crossing darts, with symmetry supplied by `reverse`.  It remains a finite
combinatorial statement and makes no appeal to an embedding. -/
def PortRegionReachable {P : PortNetwork} (C : PortCrossing P)
    (r s : Fin P.regionCount) : Prop :=
  Nonempty (PortRegionWalk C r s)

/-- Region reachability is reflexive. -/
theorem portRegionReachable_refl {P : PortNetwork} (C : PortCrossing P)
    (r : Fin P.regionCount) : PortRegionReachable C r r :=
  ⟨PortRegionWalk.nil C r⟩

/-- Region reachability is symmetric. -/
theorem portRegionReachable_symm {P : PortNetwork} (C : PortCrossing P)
    {r s : Fin P.regionCount} :
    PortRegionReachable C r s → PortRegionReachable C s r := by
  rintro ⟨W⟩
  exact ⟨PortRegionWalk.reverse W⟩

/-- Region reachability is transitive. -/
theorem portRegionReachable_trans {P : PortNetwork} (C : PortCrossing P)
    {r s t : Fin P.regionCount} :
    PortRegionReachable C r s → PortRegionReachable C s t →
      PortRegionReachable C r t := by
  rintro ⟨W₁⟩ ⟨W₂⟩
  exact ⟨PortRegionWalk.append W₁ W₂⟩

/-- Every region is reachable from a designated root region.

Rooted connectedness is the pointed form convenient for induction or for a
chosen base region; the next definitions and lemmas relate it to pairwise
connectedness. -/
def PortRootedRegionConnected {P : PortNetwork} (C : PortCrossing P)
    (base : Fin P.regionCount) : Prop :=
  ∀ s, PortRegionReachable C base s

/-- Every pair of regions is connected by a valid port walk.

This is the unpointed connectivity condition for the finite region graph.
It is equivalent to rooted connectedness because reachability is an
equivalence relation. -/
def PortRegionConnected {P : PortNetwork} (C : PortCrossing P) : Prop :=
  ∀ r s, PortRegionReachable C r s

/-- Pairwise connectedness implies rooted connectedness. -/
theorem portRegionConnected_rooted {P : PortNetwork} (C : PortCrossing P)
    (h : PortRegionConnected C) (base : Fin P.regionCount) :
    PortRootedRegionConnected C base :=
  fun s => h base s

/-- Rooted connectedness implies pairwise connectedness. -/
theorem portRegionConnected_of_rooted {P : PortNetwork}
    (C : PortCrossing P) (base : Fin P.regionCount)
    (h : PortRootedRegionConnected C base) :
    PortRegionConnected C := by
  intro r s
  exact portRegionReachable_trans C
    (portRegionReachable_symm C (h r)) (h s)

/-- Forget flow labels from a valid flow region walk.

The flow and port walks have the same dart list and the same endpoint
equations; this conversion only changes the type-level wrapper around each
port. -/
def FlowRegionWalk.toPortRegionWalk {N : FlowNetwork}
    {C : FlowCrossing N} {r s : Fin N.regionCount}
  (W : FlowRegionWalk C r s) :
    PortRegionWalk C.toPortCrossing r s :=
  ⟨W.edges, flowValid_toPort W.valid⟩

@[simp] theorem FlowRegionWalk.toPortRegionWalk_edges {N : FlowNetwork}
    {C : FlowCrossing N} {r s : Fin N.regionCount}
    (W : FlowRegionWalk C r s) :
    W.toPortRegionWalk.edges = W.edges := rfl

/-- Restore flow labels on a port region walk. -/
def PortRegionWalk.toFlowRegionWalk {P : PortNetwork}
    {C : PortCrossing P} {r s : Fin P.regionCount}
  (A : V4FlowAssignment C) (W : PortRegionWalk C r s) :
    FlowRegionWalk A.toFlowCrossing r s :=
  ⟨W.edges, portValid_toFlow W.valid A⟩

@[simp] theorem PortRegionWalk.toFlowRegionWalk_edges {P : PortNetwork}
    {C : PortCrossing P} {r s : Fin P.regionCount}
    (A : V4FlowAssignment C) (W : PortRegionWalk C r s) :
    (W.toFlowRegionWalk A).edges = W.edges := rfl

@[simp] theorem FlowRegionWalk.toPortRegionWalk_nil {N : FlowNetwork}
    (C : FlowCrossing N) (r : Fin N.regionCount) :
    (FlowRegionWalk.nil C r).toPortRegionWalk =
      PortRegionWalk.nil C.toPortCrossing r := by
  apply PortRegionWalk.ext
  rfl

@[simp] theorem FlowRegionWalk.toPortRegionWalk_singleton {N : FlowNetwork}
    (C : FlowCrossing N) (p : FlowNetworkPort N) :
    (FlowRegionWalk.singleton C p).toPortRegionWalk =
      PortRegionWalk.singleton C.toPortCrossing p := by
  apply PortRegionWalk.ext
  rfl

@[simp] theorem PortRegionWalk.toFlowRegionWalk_nil {P : PortNetwork}
    {C : PortCrossing P} (A : V4FlowAssignment C)
    (r : Fin P.regionCount) :
    (PortRegionWalk.nil C r).toFlowRegionWalk A =
      FlowRegionWalk.nil A.toFlowCrossing r := by
  apply FlowRegionWalk.ext
  rfl

@[simp] theorem PortRegionWalk.toFlowRegionWalk_singleton {P : PortNetwork}
    {C : PortCrossing P} (A : V4FlowAssignment C)
    (p : PortNetworkPort P) :
    (PortRegionWalk.singleton C p).toFlowRegionWalk A =
      FlowRegionWalk.singleton A.toFlowCrossing p := by
  apply FlowRegionWalk.ext
  rfl

/-- Flow-to-port conversion commutes with walk append. -/
theorem FlowRegionWalk.toPortRegionWalk_append {N : FlowNetwork}
    {C : FlowCrossing N} {r s t : Fin N.regionCount}
    (W₁ : FlowRegionWalk C r s) (W₂ : FlowRegionWalk C s t) :
    (FlowRegionWalk.append W₁ W₂).toPortRegionWalk =
      PortRegionWalk.append W₁.toPortRegionWalk W₂.toPortRegionWalk := by
  apply PortRegionWalk.ext
  rfl

/-- Port-to-flow conversion commutes with walk append. -/
theorem PortRegionWalk.toFlowRegionWalk_append {P : PortNetwork}
    {C : PortCrossing P} {r s t : Fin P.regionCount}
    (A : V4FlowAssignment C) (W₁ : PortRegionWalk C r s)
    (W₂ : PortRegionWalk C s t) :
    (PortRegionWalk.append W₁ W₂).toFlowRegionWalk A =
      FlowRegionWalk.append (W₁.toFlowRegionWalk A) (W₂.toFlowRegionWalk A) := by
  apply FlowRegionWalk.ext
  rfl

/-- Flow-to-port conversion commutes with reversal. -/
theorem FlowRegionWalk.toPortRegionWalk_reverse {N : FlowNetwork}
    {C : FlowCrossing N} {r s : Fin N.regionCount}
    (W : FlowRegionWalk C r s) :
    (W.reverse).toPortRegionWalk =
      PortRegionWalk.reverse W.toPortRegionWalk := by
  apply PortRegionWalk.ext
  rfl

/-- Port-to-flow conversion commutes with reversal. -/
theorem PortRegionWalk.toFlowRegionWalk_reverse {P : PortNetwork}
    {C : PortCrossing P} {r s : Fin P.regionCount}
    (A : V4FlowAssignment C) (W : PortRegionWalk C r s) :
    (W.reverse).toFlowRegionWalk A =
      FlowRegionWalk.reverse (W.toFlowRegionWalk A) := by
  apply FlowRegionWalk.ext
  rfl

/-- Flow region reachability implies port region reachability. -/
theorem flowRegionReachable_imp_port {N : FlowNetwork}
    (C : FlowCrossing N) {r s : Fin N.regionCount}
    (h : RegionReachable C r s) :
    PortRegionReachable C.toPortCrossing r s := by
  rcases h with ⟨W⟩
  exact ⟨W.toPortRegionWalk⟩

/-- Port and flow region reachability agree after lifting labels. -/
theorem portRegionReachable_iff_flow_lift {P : PortNetwork}
    {C : PortCrossing P} (A : V4FlowAssignment C)
    {r s : Fin P.regionCount} :
    PortRegionReachable C r s ↔
      RegionReachable A.toFlowCrossing r s := by
  constructor
  · rintro ⟨W⟩
    exact ⟨W.toFlowRegionWalk A⟩
  · rintro ⟨W⟩
    exact ⟨W.toPortRegionWalk⟩

/-- Reachability does not depend on the chosen V4 assignment. -/
theorem regionReachable_assignment_independent {P : PortNetwork}
    {C : PortCrossing P} (A B : V4FlowAssignment C)
    {r s : Fin P.regionCount} :
    RegionReachable A.toFlowCrossing r s ↔
      RegionReachable B.toFlowCrossing r s := by
  constructor
  · intro h
    exact (portRegionReachable_iff_flow_lift B).mp
      ((portRegionReachable_iff_flow_lift A).mpr h)
  · intro h
    exact (portRegionReachable_iff_flow_lift A).mp
      ((portRegionReachable_iff_flow_lift B).mpr h)

/-- Rooted connectedness is invariant under port/flow lifting. -/
theorem portRootedRegionConnected_iff_flow_lift {P : PortNetwork}
    {C : PortCrossing P} (A : V4FlowAssignment C)
    (base : Fin P.regionCount) :
    PortRootedRegionConnected C base ↔
      (∀ s, RegionReachable A.toFlowCrossing base s) := by
  constructor
  · intro h s
    exact (portRegionReachable_iff_flow_lift A).mp (h s)
  · intro h s
    exact (portRegionReachable_iff_flow_lift A).mpr (h s)

/-- Pairwise connectedness is invariant under port/flow lifting. -/
theorem portRegionConnected_iff_flow_lift {P : PortNetwork}
    {C : PortCrossing P} (A : V4FlowAssignment C) :
    PortRegionConnected C ↔
      (∀ r s, RegionReachable A.toFlowCrossing r s) := by
  constructor
  · intro h r s
    exact (portRegionReachable_iff_flow_lift A).mp (h r s)
  · intro h r s
    exact (portRegionReachable_iff_flow_lift A).mpr (h r s)

/-- Connectedness is independent of the V4 assignment. -/
theorem regionConnected_assignment_independent {P : PortNetwork}
    {C : PortCrossing P} (A B : V4FlowAssignment C) :
    (∀ r s, RegionReachable A.toFlowCrossing r s) ↔
      (∀ r s, RegionReachable B.toFlowCrossing r s) := by
  constructor
  · intro h r s
    exact (regionReachable_assignment_independent A B).mp (h r s)
  · intro h r s
    exact (regionReachable_assignment_independent A B).mpr (h r s)

/-- Flow-to-port-to-flow recovers the original dart list and validity. -/
theorem FlowRegionWalk.toPortRegionWalk_toFlowRegionWalk
    {N : FlowNetwork} {C : FlowCrossing N}
    {r s : Fin N.regionCount} (W : FlowRegionWalk C r s) :
    (W.toPortRegionWalk.toFlowRegionWalk C.toV4FlowAssignment) = W := by
  apply FlowRegionWalk.ext
  rfl

/-- Port-to-flow-to-port recovers the original dart list and validity. -/
theorem PortRegionWalk.toFlowRegionWalk_toPortRegionWalk
    {P : PortNetwork} {C : PortCrossing P}
    {r s : Fin P.regionCount} (A : V4FlowAssignment C)
    (W : PortRegionWalk C r s) :
    (W.toFlowRegionWalk A).toPortRegionWalk = W := by
  apply PortRegionWalk.ext
  rfl

end DkMath.Tromino
