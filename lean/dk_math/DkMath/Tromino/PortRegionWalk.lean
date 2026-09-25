/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortNetwork
import DkMath.Tromino.RegionWalk

#print "file: DkMath.Tromino.PortRegionWalk"

namespace DkMath.Tromino

def PortRegionWalk.Valid {P : PortNetwork} (C : PortCrossing P)
    (r s : Fin P.regionCount) :
    List (PortNetworkPort P) → Prop
  | [] => r = s
  | p :: ps => p.1 = r ∧ PortRegionWalk.Valid C (C.cross p).1 s ps

structure PortRegionWalk {P : PortNetwork} (C : PortCrossing P)
    (r s : Fin P.regionCount) where
  edges : List (PortNetworkPort P)
  valid : PortRegionWalk.Valid C r s edges

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

theorem ext {P : PortNetwork} {C : PortCrossing P}
    {r s : Fin P.regionCount} {w₁ w₂ : PortRegionWalk C r s}
    (h : w₁.edges = w₂.edges) : w₁ = w₂ := by
  cases w₁
  cases w₂
  cases h
  rfl

def nil {P : PortNetwork} (C : PortCrossing P)
    (r : Fin P.regionCount) : PortRegionWalk C r r :=
  ⟨[], rfl⟩

def length {P : PortNetwork} {C : PortCrossing P}
    {r s : Fin P.regionCount} (w : PortRegionWalk C r s) : Nat :=
  w.edges.length

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

theorem append_assoc {P : PortNetwork} {C : PortCrossing P}
    {r s t u : Fin P.regionCount}
    (w₁ : PortRegionWalk C r s) (w₂ : PortRegionWalk C s t)
    (w₃ : PortRegionWalk C t u) :
    append (append w₁ w₂) w₃ = append w₁ (append w₂ w₃) := by
  apply PortRegionWalk.ext
  simp [append, List.append_assoc]

def singleton {P : PortNetwork} (C : PortCrossing P)
    (p : PortNetworkPort P) : PortRegionWalk C p.1 (C.cross p).1 :=
  ⟨[p], by simp [PortRegionWalk.Valid]⟩

def reverseEdges {P : PortNetwork} (C : PortCrossing P) :
    List (PortNetworkPort P) → List (PortNetworkPort P) :=
  fun xs => xs.reverse.map C.cross

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

def reverse {P : PortNetwork} {C : PortCrossing P}
    {r s : Fin P.regionCount} (w : PortRegionWalk C r s) :
    PortRegionWalk C s r :=
  ⟨reverseEdges C w.edges, valid_reverseEdges w.valid⟩

@[simp] theorem reverse_nil {P : PortNetwork} {C : PortCrossing P}
    (r : Fin P.regionCount) :
    reverse (nil C r) = nil C r := by
  apply PortRegionWalk.ext
  rfl

theorem reverse_append {P : PortNetwork} {C : PortCrossing P}
    {r s t : Fin P.regionCount}
    (w₁ : PortRegionWalk C r s) (w₂ : PortRegionWalk C s t) :
    reverse (append w₁ w₂) = append (reverse w₂) (reverse w₁) := by
  apply PortRegionWalk.ext
  simp [reverse, append, reverseEdges, List.map_append]

theorem reverse_reverse {P : PortNetwork} {C : PortCrossing P}
    {r s : Fin P.regionCount} (w : PortRegionWalk C r s) :
    reverse (reverse w) = w := by
  apply PortRegionWalk.ext
  simp [reverse, reverseEdges, List.map_map, C.involutive]

end PortRegionWalk

def PortRegionReachable {P : PortNetwork} (C : PortCrossing P)
    (r s : Fin P.regionCount) : Prop :=
  Nonempty (PortRegionWalk C r s)

theorem portRegionReachable_refl {P : PortNetwork} (C : PortCrossing P)
    (r : Fin P.regionCount) : PortRegionReachable C r r :=
  ⟨PortRegionWalk.nil C r⟩

theorem portRegionReachable_symm {P : PortNetwork} (C : PortCrossing P)
    {r s : Fin P.regionCount} :
    PortRegionReachable C r s → PortRegionReachable C s r := by
  rintro ⟨W⟩
  exact ⟨PortRegionWalk.reverse W⟩

theorem portRegionReachable_trans {P : PortNetwork} (C : PortCrossing P)
    {r s t : Fin P.regionCount} :
    PortRegionReachable C r s → PortRegionReachable C s t →
      PortRegionReachable C r t := by
  rintro ⟨W₁⟩ ⟨W₂⟩
  exact ⟨PortRegionWalk.append W₁ W₂⟩

def PortRootedRegionConnected {P : PortNetwork} (C : PortCrossing P)
    (base : Fin P.regionCount) : Prop :=
  ∀ s, PortRegionReachable C base s

def PortRegionConnected {P : PortNetwork} (C : PortCrossing P) : Prop :=
  ∀ r s, PortRegionReachable C r s

theorem portRegionConnected_rooted {P : PortNetwork} (C : PortCrossing P)
    (h : PortRegionConnected C) (base : Fin P.regionCount) :
    PortRootedRegionConnected C base :=
  fun s => h base s

theorem portRegionConnected_of_rooted {P : PortNetwork}
    (C : PortCrossing P) (base : Fin P.regionCount)
    (h : PortRootedRegionConnected C base) :
    PortRegionConnected C := by
  intro r s
  exact portRegionReachable_trans C
    (portRegionReachable_symm C (h r)) (h s)

def FlowRegionWalk.toPortRegionWalk {N : FlowNetwork}
    {C : FlowCrossing N} {r s : Fin N.regionCount}
  (W : FlowRegionWalk C r s) :
    PortRegionWalk C.toPortCrossing r s :=
  ⟨W.edges, flowValid_toPort W.valid⟩

@[simp] theorem FlowRegionWalk.toPortRegionWalk_edges {N : FlowNetwork}
    {C : FlowCrossing N} {r s : Fin N.regionCount}
    (W : FlowRegionWalk C r s) :
    W.toPortRegionWalk.edges = W.edges := rfl

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

theorem FlowRegionWalk.toPortRegionWalk_append {N : FlowNetwork}
    {C : FlowCrossing N} {r s t : Fin N.regionCount}
    (W₁ : FlowRegionWalk C r s) (W₂ : FlowRegionWalk C s t) :
    (FlowRegionWalk.append W₁ W₂).toPortRegionWalk =
      PortRegionWalk.append W₁.toPortRegionWalk W₂.toPortRegionWalk := by
  apply PortRegionWalk.ext
  rfl

theorem PortRegionWalk.toFlowRegionWalk_append {P : PortNetwork}
    {C : PortCrossing P} {r s t : Fin P.regionCount}
    (A : V4FlowAssignment C) (W₁ : PortRegionWalk C r s)
    (W₂ : PortRegionWalk C s t) :
    (PortRegionWalk.append W₁ W₂).toFlowRegionWalk A =
      FlowRegionWalk.append (W₁.toFlowRegionWalk A) (W₂.toFlowRegionWalk A) := by
  apply FlowRegionWalk.ext
  rfl

theorem FlowRegionWalk.toPortRegionWalk_reverse {N : FlowNetwork}
    {C : FlowCrossing N} {r s : Fin N.regionCount}
    (W : FlowRegionWalk C r s) :
    (W.reverse).toPortRegionWalk =
      PortRegionWalk.reverse W.toPortRegionWalk := by
  apply PortRegionWalk.ext
  rfl

theorem PortRegionWalk.toFlowRegionWalk_reverse {P : PortNetwork}
    {C : PortCrossing P} {r s : Fin P.regionCount}
    (A : V4FlowAssignment C) (W : PortRegionWalk C r s) :
    (W.reverse).toFlowRegionWalk A =
      FlowRegionWalk.reverse (W.toFlowRegionWalk A) := by
  apply FlowRegionWalk.ext
  rfl

theorem flowRegionReachable_imp_port {N : FlowNetwork}
    (C : FlowCrossing N) {r s : Fin N.regionCount}
    (h : RegionReachable C r s) :
    PortRegionReachable C.toPortCrossing r s := by
  rcases h with ⟨W⟩
  exact ⟨W.toPortRegionWalk⟩

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

theorem portRegionConnected_iff_flow_lift {P : PortNetwork}
    {C : PortCrossing P} (A : V4FlowAssignment C) :
    PortRegionConnected C ↔
      (∀ r s, RegionReachable A.toFlowCrossing r s) := by
  constructor
  · intro h r s
    exact (portRegionReachable_iff_flow_lift A).mp (h r s)
  · intro h r s
    exact (portRegionReachable_iff_flow_lift A).mpr (h r s)

theorem regionConnected_assignment_independent {P : PortNetwork}
    {C : PortCrossing P} (A B : V4FlowAssignment C) :
    (∀ r s, RegionReachable A.toFlowCrossing r s) ↔
      (∀ r s, RegionReachable B.toFlowCrossing r s) := by
  constructor
  · intro h r s
    exact (regionReachable_assignment_independent A B).mp (h r s)
  · intro h r s
    exact (regionReachable_assignment_independent A B).mpr (h r s)

theorem FlowRegionWalk.toPortRegionWalk_toFlowRegionWalk
    {N : FlowNetwork} {C : FlowCrossing N}
    {r s : Fin N.regionCount} (W : FlowRegionWalk C r s) :
    (W.toPortRegionWalk.toFlowRegionWalk C.toV4FlowAssignment) = W := by
  apply FlowRegionWalk.ext
  rfl

theorem PortRegionWalk.toFlowRegionWalk_toPortRegionWalk
    {P : PortNetwork} {C : PortCrossing P}
    {r s : Fin P.regionCount} (A : V4FlowAssignment C)
    (W : PortRegionWalk C r s) :
    (W.toFlowRegionWalk A).toPortRegionWalk = W := by
  apply PortRegionWalk.ext
  rfl

end DkMath.Tromino
