/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Dynamics.PeriodicPts.Defs
import DkMath.Tromino.PortRotationSystem
import DkMath.Tromino.FaceOrbit

#print "file: DkMath.Tromino.PortFaceOrbit"

namespace DkMath.Tromino

def portFaceOrbit {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) : Finset (PortNetworkPort P) :=
  (Finset.range (firstPortFaceReturn R C p)).image
    (fun n => (portFaceStep R C)^[n] p)

theorem portFaceOrbit_contains {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) :
    p ∈ portFaceOrbit R C p := by
  apply Finset.mem_image.mpr
  exact ⟨0, Finset.mem_range.mpr (firstPortFaceReturn_spec R C p).1,
    by simp⟩

theorem portFaceOrbit_mem_iterate {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) (n : Nat) :
    (portFaceStep R C)^[n] p ∈ portFaceOrbit R C p := by
  have hk : 0 < firstPortFaceReturn R C p :=
    (firstPortFaceReturn_spec R C p).1
  have hperiod : Function.IsPeriodicPt (portFaceStep R C)
      (firstPortFaceReturn R C p) p :=
    (firstPortFaceReturn_spec R C p).2
  apply Finset.mem_image.mpr
  refine ⟨n % firstPortFaceReturn R C p,
    Finset.mem_range.mpr (Nat.mod_lt n hk), ?_⟩
  exact hperiod.iterate_mod_apply n

theorem portFaceOrbit_mem_iff_iterate {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (p q : PortNetworkPort P) :
    q ∈ portFaceOrbit R C p ↔
      ∃ n : Nat, (portFaceStep R C)^[n] p = q := by
  constructor
  · intro hq
    rcases Finset.mem_image.mp hq with ⟨n, _, rfl⟩
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact portFaceOrbit_mem_iterate R C p n

theorem portFaceOrbit_iterate_distinct
    {P : PortNetwork} (R : PortLocalRotation P) (C : PortCrossing P)
    (p : PortNetworkPort P) {i j : Nat}
    (hi : i < firstPortFaceReturn R C p)
    (hj : j < firstPortFaceReturn R C p)
    (hij : (portFaceStep R C)^[i] p = (portFaceStep R C)^[j] p) :
    i = j := by
  have hinj : Function.Injective (portFaceStep R C) := by
    intro a b hab
    exact (portFaceEquiv R C).injective hab
  by_cases hijle : i ≤ j
  · have hcancel : (portFaceStep R C)^[j - i] p = p := by
      exact Function.iterate_cancel hinj hij.symm
    by_cases hzero : j - i = 0
    · omega
    · have hpos : 0 < j - i := Nat.pos_of_ne_zero hzero
      have hlt : j - i < firstPortFaceReturn R C p := by omega
      exact False.elim
        ((firstPortFaceReturn_primitive R C p).2.2 (j - i) hpos hlt hcancel)
  · have hjle : j ≤ i := by omega
    have hcancel : (portFaceStep R C)^[i - j] p = p := by
      exact Function.iterate_cancel hinj hij
    by_cases hzero : i - j = 0
    · omega
    · have hpos : 0 < i - j := Nat.pos_of_ne_zero hzero
      have hlt : i - j < firstPortFaceReturn R C p := by omega
      exact False.elim
        ((firstPortFaceReturn_primitive R C p).2.2 (i - j) hpos hlt hcancel)

theorem portFaceOrbit_card {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) :
    (portFaceOrbit R C p).card = firstPortFaceReturn R C p := by
  unfold portFaceOrbit
  calc
    (Finset.image (fun n => (portFaceStep R C)^[n] p)
        (Finset.range (firstPortFaceReturn R C p))).card =
        (Finset.range (firstPortFaceReturn R C p)).card := by
          apply Finset.card_image_iff.mpr
          intro i hi j hj hij
          exact portFaceOrbit_iterate_distinct R C p
            (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
    _ = firstPortFaceReturn R C p := Finset.card_range _

theorem portFaceOrbit_reverse_mem {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (p q : PortNetworkPort P) (hq : q ∈ portFaceOrbit R C p) :
    p ∈ portFaceOrbit R C q := by
  rcases Finset.mem_image.mp hq with ⟨n, hn, hqeq⟩
  have hperiod := (firstPortFaceReturn_spec R C p).2
  have hnlt : n < firstPortFaceReturn R C p := Finset.mem_range.mp hn
  apply (portFaceOrbit_mem_iff_iterate R C q p).2
  refine ⟨firstPortFaceReturn R C p - n, ?_⟩
  calc
    (portFaceStep R C)^[firstPortFaceReturn R C p - n] q =
        (portFaceStep R C)^[firstPortFaceReturn R C p - n]
          ((portFaceStep R C)^[n] p) := by rw [hqeq]
    _ = (portFaceStep R C)^[firstPortFaceReturn R C p - n + n] p := by
      rw [Function.iterate_add_apply]
    _ = (portFaceStep R C)^[firstPortFaceReturn R C p] p := by
      rw [Nat.sub_add_cancel (Nat.le_of_lt hnlt)]
    _ = p := hperiod

theorem portFaceOrbit_subset_of_mem {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (p q : PortNetworkPort P) (hq : q ∈ portFaceOrbit R C p) :
    portFaceOrbit R C q ⊆ portFaceOrbit R C p := by
  intro x hx
  rcases (portFaceOrbit_mem_iff_iterate R C q x).mp hx with ⟨m, hmx⟩
  rcases (portFaceOrbit_mem_iff_iterate R C p q).mp hq with ⟨n, hn⟩
  apply (portFaceOrbit_mem_iff_iterate R C p x).2
  refine ⟨m + n, ?_⟩
  rw [Function.iterate_add_apply, hn]
  exact hmx

theorem portFaceOrbit_eq_of_mem {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (p q : PortNetworkPort P) (hq : q ∈ portFaceOrbit R C p) :
    portFaceOrbit R C q = portFaceOrbit R C p := by
  apply Finset.Subset.antisymm
  · exact portFaceOrbit_subset_of_mem R C p q hq
  · exact portFaceOrbit_subset_of_mem R C q p
      (portFaceOrbit_reverse_mem R C p q hq)

def SamePortFaceOrbit {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p q : PortNetworkPort P) : Prop :=
  q ∈ portFaceOrbit R C p

theorem samePortFaceOrbit_refl {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) :
    SamePortFaceOrbit R C p p :=
  portFaceOrbit_contains R C p

theorem samePortFaceOrbit_symm {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) {p q : PortNetworkPort P}
    (hpq : SamePortFaceOrbit R C p q) :
    SamePortFaceOrbit R C q p :=
  portFaceOrbit_reverse_mem R C p q hpq

theorem samePortFaceOrbit_trans {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) {p q r : PortNetworkPort P}
    (hpq : SamePortFaceOrbit R C p q) (hqr : SamePortFaceOrbit R C q r) :
    SamePortFaceOrbit R C p r := by
  exact portFaceOrbit_subset_of_mem R C p q hpq hqr

def portFaceOrbitSetoid {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) : Setoid (PortNetworkPort P) where
  r := SamePortFaceOrbit R C
  iseqv := ⟨samePortFaceOrbit_refl R C, @samePortFaceOrbit_symm P R C,
    @samePortFaceOrbit_trans P R C⟩

theorem portFaceOrbit_eq_or_disjoint {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (p q : PortNetworkPort P) :
    portFaceOrbit R C p = portFaceOrbit R C q ∨
      Disjoint (portFaceOrbit R C p) (portFaceOrbit R C q) := by
  by_cases h : portFaceOrbit R C p = portFaceOrbit R C q
  · exact Or.inl h
  · right
    refine Finset.disjoint_left.mpr ?_
    intro x hxp hxq
    apply h
    exact (portFaceOrbit_eq_of_mem R C p x hxp).symm.trans
      (portFaceOrbit_eq_of_mem R C q x hxq)

theorem portFaceOrbit_coverage {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) :
    ∀ p : PortNetworkPort P, p ∈ portFaceOrbit R C p :=
  fun p => portFaceOrbit_contains R C p

theorem firstPortFaceReturn_eq_of_mem {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (p q : PortNetworkPort P) (hq : q ∈ portFaceOrbit R C p) :
    firstPortFaceReturn R C q = firstPortFaceReturn R C p := by
  calc
    firstPortFaceReturn R C q = (portFaceOrbit R C q).card :=
      (portFaceOrbit_card R C q).symm
    _ = (portFaceOrbit R C p).card := by
      rw [portFaceOrbit_eq_of_mem R C p q hq]
    _ = firstPortFaceReturn R C p := portFaceOrbit_card R C p

theorem firstPortFaceReturn_of_flow_erasure {N : FlowNetwork}
    (R : FlowLocalRotation N) (C : FlowCrossing N)
    (p : PortNetworkPort N.toPortNetwork) :
    firstPortFaceReturn R.toPortLocalRotation C.toPortCrossing p =
      firstFaceReturn R C p := by
  apply Nat.le_antisymm
  · apply firstPortFaceReturn_min R.toPortLocalRotation C.toPortCrossing p
    exact ⟨(firstFaceReturn_spec R C p).1,
      (firstFaceReturn_spec R C p).2⟩
  · apply firstFaceReturn_min R C p
    exact ⟨(firstPortFaceReturn_spec R.toPortLocalRotation C.toPortCrossing p).1,
      (firstPortFaceReturn_spec R.toPortLocalRotation C.toPortCrossing p).2⟩

theorem portFaceOrbit_of_flow_erasure {N : FlowNetwork}
    (R : FlowLocalRotation N) (C : FlowCrossing N)
    (p : PortNetworkPort N.toPortNetwork) :
    portFaceOrbit R.toPortLocalRotation C.toPortCrossing p =
      faceOrbit R C p := by
  unfold portFaceOrbit faceOrbit
  rw [firstPortFaceReturn_of_flow_erasure]
  rfl

theorem firstFaceReturn_of_flow_lift {P : PortNetwork}
    {C : PortCrossing P} (R : PortLocalRotation P)
    (A : V4FlowAssignment C) (p : PortNetworkPort P) :
    firstFaceReturn (R.toFlowLocalRotation A) A.toFlowCrossing p =
      firstPortFaceReturn R C p := by
  apply Nat.le_antisymm
  · apply firstFaceReturn_min (R.toFlowLocalRotation A) A.toFlowCrossing p
    exact ⟨(firstPortFaceReturn_spec R C p).1,
      (firstPortFaceReturn_spec R C p).2⟩
  · apply firstPortFaceReturn_min R C p
    exact ⟨(firstFaceReturn_spec (R.toFlowLocalRotation A)
        A.toFlowCrossing p).1,
      (firstFaceReturn_spec (R.toFlowLocalRotation A)
        A.toFlowCrossing p).2⟩

theorem faceOrbit_of_flow_lift {P : PortNetwork} {C : PortCrossing P}
    (R : PortLocalRotation P) (A : V4FlowAssignment C)
    (p : PortNetworkPort P) :
    faceOrbit (R.toFlowLocalRotation A) A.toFlowCrossing p =
      portFaceOrbit R C p := by
  unfold faceOrbit portFaceOrbit
  rw [firstFaceReturn_of_flow_lift]
  rfl

theorem faceOrbit_assignment_independent {P : PortNetwork}
    {C : PortCrossing P} (R : PortLocalRotation P)
    (A B : V4FlowAssignment C) (p : PortNetworkPort P) :
    faceOrbit (R.toFlowLocalRotation A) A.toFlowCrossing p =
      faceOrbit (R.toFlowLocalRotation B) B.toFlowCrossing p := by
  rw [faceOrbit_of_flow_lift, faceOrbit_of_flow_lift]

end DkMath.Tromino
