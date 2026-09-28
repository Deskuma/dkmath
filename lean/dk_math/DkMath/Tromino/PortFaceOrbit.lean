/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Dynamics.PeriodicPts.Defs
import DkMath.Tromino.PortRotationSystem
import DkMath.Tromino.FaceOrbit

#print "file: DkMath.Tromino.PortFaceOrbit"

/-!
# Face orbits of the dart permutation

The face step is the crossing followed by the local rotation.  Since it is
a permutation of a finite port type, the orbit of a dart is a finite face
cell.  We represent that cell by the iterates before the least positive
return, prove that these iterates are distinct and exhaustive, and then
derive equality-or-disjointness and coverage.  The final theorems transport
this orbit calculus across the flow/port encodings, showing that labels do
not affect the underlying face partition.
-/

namespace DkMath.Tromino

/-- The finite set of darts in the primitive face orbit of a port.

The range stops just before the first positive return.  Thus the image is a
canonical finite representative of one cyclic face orbit, with no repeated
dart in its defining list. -/
def portFaceOrbit {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) : Finset (PortNetworkPort P) :=
  (Finset.range (firstPortFaceReturn R C p)).image
    (fun n => (portFaceStep R C)^[n] p)

/-- An orbit contains its chosen starting dart. -/
theorem portFaceOrbit_contains {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) :
    p ∈ portFaceOrbit R C p := by
  apply Finset.mem_image.mpr
  exact ⟨0, Finset.mem_range.mpr (firstPortFaceReturn_spec R C p).1,
    by simp⟩

/-- Every face-step iterate lies in the primitive orbit.

Reduce the iterate index modulo the first return time.  Periodicity then
identifies the original iterate with one of the canonical representatives
used by `portFaceOrbit`. -/
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

/-- Orbit membership is equivalent to reachability by face steps.

This is the bridge between the finite-set presentation and the dynamical
presentation: a dart is in the face exactly when it is reached by some
nonnegative iterate of the face permutation. -/
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

/-- Distinct indices before the return time give distinct darts.

Injectivity lets equal iterates be cancelled.  Any remaining positive
difference would be a smaller return time, contradicting the primitive
minimality of the first return. -/
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

/-- The orbit cardinality equals the first return time.

The defining range has exactly that many indices, and the preceding
distinctness theorem makes the iterate map injective on the range.  The
return time therefore counts the darts on the face boundary. -/
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

/-- Reversing a face boundary remains in the same orbit. -/
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

/-- An orbit based at an orbit member is contained in the original orbit.

Starting at an already reached dart merely adds iterates to an existing
iterate; the iterate-addition law composes the two finite paths. -/
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

/-- Orbits based at members of one orbit are equal.

The reverse-iterate lemma gives the opposite inclusion, so changing the
chosen starting dart changes only the representative, not the face set. -/
theorem portFaceOrbit_eq_of_mem {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (p q : PortNetworkPort P) (hq : q ∈ portFaceOrbit R C p) :
    portFaceOrbit R C q = portFaceOrbit R C p := by
  apply Finset.Subset.antisymm
  · exact portFaceOrbit_subset_of_mem R C p q hq
  · exact portFaceOrbit_subset_of_mem R C q p
      (portFaceOrbit_reverse_mem R C p q hq)

/-- Equivalence relation of lying in the same face orbit.

Membership in the finite orbit is used as the relation; reflexivity,
symmetry, and transitivity follow from orbit containment and reversibility. -/
def SamePortFaceOrbit {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p q : PortNetworkPort P) : Prop :=
  q ∈ portFaceOrbit R C p

/-- Same-face orbit is reflexive. -/
theorem samePortFaceOrbit_refl {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) :
    SamePortFaceOrbit R C p p :=
  portFaceOrbit_contains R C p

/-- Same-face orbit is symmetric. -/
theorem samePortFaceOrbit_symm {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) {p q : PortNetworkPort P}
    (hpq : SamePortFaceOrbit R C p q) :
    SamePortFaceOrbit R C q p :=
  portFaceOrbit_reverse_mem R C p q hpq

/-- Same-face orbit is transitive. -/
theorem samePortFaceOrbit_trans {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) {p q r : PortNetworkPort P}
    (hpq : SamePortFaceOrbit R C p q) (hqr : SamePortFaceOrbit R C q r) :
    SamePortFaceOrbit R C p r := by
  exact portFaceOrbit_subset_of_mem R C p q hpq hqr

/-- Setoid whose classes are the face orbits. -/
def portFaceOrbitSetoid {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) : Setoid (PortNetworkPort P) where
  r := SamePortFaceOrbit R C
  iseqv := ⟨samePortFaceOrbit_refl R C, @samePortFaceOrbit_symm P R C,
    @samePortFaceOrbit_trans P R C⟩

/-- Two finite face orbits are equal or disjoint.

If the finite representatives are not equal, a common dart would identify
both with the orbit based at that dart, forcing equality.  Hence face
orbits form disjoint equivalence classes. -/
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

/-- Every dart belongs to its own face orbit.

Together with equality-or-disjointness, this gives the finite coverage
statement needed to view the face orbits as a partition of all ports. -/
theorem portFaceOrbit_coverage {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) :
    ∀ p : PortNetworkPort P, p ∈ portFaceOrbit R C p :=
  fun p => portFaceOrbit_contains R C p

/-- The first return time is constant on a face orbit.

The return time is recovered as the cardinality of the orbit, so changing
the base dart cannot change the numerical length of the same face. -/
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

/-- Flow and port encodings have the same first face return. -/
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

/-- Flow face orbits become the corresponding port face orbits. -/
theorem portFaceOrbit_of_flow_erasure {N : FlowNetwork}
    (R : FlowLocalRotation N) (C : FlowCrossing N)
    (p : PortNetworkPort N.toPortNetwork) :
    portFaceOrbit R.toPortLocalRotation C.toPortCrossing p =
      faceOrbit R C p := by
  unfold portFaceOrbit faceOrbit
  rw [firstPortFaceReturn_of_flow_erasure]
  rfl

/-- Restoring a port map in the flow language preserves first return. -/
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

/-- Restoring a port map in the flow language preserves face orbits. -/
theorem faceOrbit_of_flow_lift {P : PortNetwork} {C : PortCrossing P}
    (R : PortLocalRotation P) (A : V4FlowAssignment C)
    (p : PortNetworkPort P) :
    faceOrbit (R.toFlowLocalRotation A) A.toFlowCrossing p =
      portFaceOrbit R C p := by
  unfold faceOrbit portFaceOrbit
  rw [firstFaceReturn_of_flow_lift]
  rfl

/-- Face orbits do not depend on the chosen V4 assignment.

The assignment only decorates the same port carrier.  Since both lifted
flow systems induce the same face permutation and first-return time, their
finite face sets coincide exactly. -/
theorem faceOrbit_assignment_independent {P : PortNetwork}
    {C : PortCrossing P} (R : PortLocalRotation P)
    (A B : V4FlowAssignment C) (p : PortNetworkPort P) :
    faceOrbit (R.toFlowLocalRotation A) A.toFlowCrossing p =
      faceOrbit (R.toFlowLocalRotation B) B.toFlowCrossing p := by
  rw [faceOrbit_of_flow_lift, faceOrbit_of_flow_lift]

end DkMath.Tromino
