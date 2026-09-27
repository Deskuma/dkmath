/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Dynamics.PeriodicPts.Defs
import DkMath.Tromino.RotationSystem

#print "file: DkMath.Tromino.FaceOrbit"

namespace DkMath.Tromino

def totalPortCount (N : FlowNetwork) : Nat :=
  Fintype.card (FlowNetworkPort N)

def faceOrbit {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p : FlowNetworkPort N) : Finset (FlowNetworkPort N) :=
  (Finset.range (firstFaceReturn R C p)).image
    (fun n => (faceStep R C)^[n] p)

theorem faceOrbit_contains {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p : FlowNetworkPort N) :
    p ∈ faceOrbit R C p := by
  apply Finset.mem_image.mpr
  exact ⟨0, Finset.mem_range.mpr (firstFaceReturn_spec R C p).1,
    by simp⟩

theorem faceOrbit_mem_iterate {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p : FlowNetworkPort N) (n : Nat) :
    (faceStep R C)^[n] p ∈ faceOrbit R C p := by
  have hk : 0 < firstFaceReturn R C p :=
    (firstFaceReturn_spec R C p).1
  have hperiod : Function.IsPeriodicPt (faceStep R C)
      (firstFaceReturn R C p) p :=
    (firstFaceReturn_spec R C p).2
  apply Finset.mem_image.mpr
  refine ⟨n % firstFaceReturn R C p,
    Finset.mem_range.mpr (Nat.mod_lt n hk), ?_⟩
  exact hperiod.iterate_mod_apply n

theorem faceOrbit_mem_iff_iterate {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p q : FlowNetworkPort N) :
    q ∈ faceOrbit R C p ↔
      ∃ n : Nat, (faceStep R C)^[n] p = q := by
  constructor
  · intro hq
    rcases Finset.mem_image.mp hq with ⟨n, _, rfl⟩
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact faceOrbit_mem_iterate R C p n

theorem faceOrbit_iterate_distinct
    {N : FlowNetwork} (R : FlowLocalRotation N) (C : FlowCrossing N)
    (p : FlowNetworkPort N) {i j : Nat}
    (hi : i < firstFaceReturn R C p)
    (hj : j < firstFaceReturn R C p)
    (hij : (faceStep R C)^[i] p = (faceStep R C)^[j] p) :
    i = j := by
  have hinj : Function.Injective (faceStep R C) := by
    intro a b hab
    exact (faceEquiv R C).injective hab
  by_cases hijle : i ≤ j
  · have hcancel : (faceStep R C)^[j - i] p = p := by
      exact Function.iterate_cancel hinj hij.symm
    by_cases hzero : j - i = 0
    · omega
    · have hpos : 0 < j - i := Nat.pos_of_ne_zero hzero
      have hlt : j - i < firstFaceReturn R C p := by omega
      exact False.elim
        ((firstFaceReturn_primitive R C p).2.2 (j - i) hpos hlt hcancel)
  · have hjle : j ≤ i := by omega
    have hcancel : (faceStep R C)^[i - j] p = p := by
      exact Function.iterate_cancel hinj hij
    by_cases hzero : i - j = 0
    · omega
    · have hpos : 0 < i - j := Nat.pos_of_ne_zero hzero
      have hlt : i - j < firstFaceReturn R C p := by omega
      exact False.elim
        ((firstFaceReturn_primitive R C p).2.2 (i - j) hpos hlt hcancel)

theorem faceOrbit_card {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p : FlowNetworkPort N) :
    (faceOrbit R C p).card = firstFaceReturn R C p := by
  unfold faceOrbit
  calc
    (Finset.image (fun n => (faceStep R C)^[n] p)
        (Finset.range (firstFaceReturn R C p))).card =
        (Finset.range (firstFaceReturn R C p)).card := by
          apply Finset.card_image_iff.mpr
          intro i hi j hj hij
          exact faceOrbit_iterate_distinct R C p
            (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
    _ = firstFaceReturn R C p := Finset.card_range _

theorem faceOrbit_reverse_mem {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p q : FlowNetworkPort N)
    (hq : q ∈ faceOrbit R C p) :
    p ∈ faceOrbit R C q := by
  rcases Finset.mem_image.mp hq with ⟨n, hn, hqeq⟩
  have hperiod := (firstFaceReturn_spec R C p).2
  have hnlt : n < firstFaceReturn R C p := Finset.mem_range.mp hn
  apply (faceOrbit_mem_iff_iterate R C q p).2
  refine ⟨firstFaceReturn R C p - n, ?_⟩
  calc
    (faceStep R C)^[firstFaceReturn R C p - n] q =
        (faceStep R C)^[firstFaceReturn R C p - n]
          ((faceStep R C)^[n] p) := by rw [hqeq]
    _ = (faceStep R C)^[firstFaceReturn R C p - n + n] p := by
      rw [Function.iterate_add_apply]
    _ = (faceStep R C)^[firstFaceReturn R C p] p := by
      rw [Nat.sub_add_cancel (Nat.le_of_lt hnlt)]
    _ = p := hperiod

theorem faceOrbit_subset_of_mem {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p q : FlowNetworkPort N)
    (hq : q ∈ faceOrbit R C p) :
    faceOrbit R C q ⊆ faceOrbit R C p := by
  intro x hx
  rcases (faceOrbit_mem_iff_iterate R C q x).mp hx with ⟨m, hmx⟩
  rcases (faceOrbit_mem_iff_iterate R C p q).mp hq with ⟨n, hn⟩
  apply (faceOrbit_mem_iff_iterate R C p x).2
  refine ⟨m + n, ?_⟩
  rw [Function.iterate_add_apply, hn]
  exact hmx

theorem faceOrbit_eq_of_mem {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p q : FlowNetworkPort N)
    (hq : q ∈ faceOrbit R C p) :
    faceOrbit R C q = faceOrbit R C p := by
  apply Finset.Subset.antisymm
  · exact faceOrbit_subset_of_mem R C p q hq
  · exact faceOrbit_subset_of_mem R C q p
      (faceOrbit_reverse_mem R C p q hq)

def SameFaceOrbit {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p q : FlowNetworkPort N) : Prop :=
  q ∈ faceOrbit R C p

theorem sameFaceOrbit_refl {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p : FlowNetworkPort N) :
    SameFaceOrbit R C p p :=
  faceOrbit_contains R C p

theorem sameFaceOrbit_symm {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) {p q : FlowNetworkPort N}
    (hpq : SameFaceOrbit R C p q) :
    SameFaceOrbit R C q p :=
  faceOrbit_reverse_mem R C p q hpq

theorem sameFaceOrbit_trans {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) {p q r : FlowNetworkPort N}
    (hpq : SameFaceOrbit R C p q) (hqr : SameFaceOrbit R C q r) :
    SameFaceOrbit R C p r := by
  exact faceOrbit_subset_of_mem R C p q hpq hqr

def faceOrbitSetoid {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) : Setoid (FlowNetworkPort N) where
  r := SameFaceOrbit R C
  iseqv := ⟨sameFaceOrbit_refl R C, @sameFaceOrbit_symm N R C,
    @sameFaceOrbit_trans N R C⟩

theorem faceOrbit_eq_or_disjoint {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p q : FlowNetworkPort N) :
    faceOrbit R C p = faceOrbit R C q ∨
      Disjoint (faceOrbit R C p) (faceOrbit R C q) := by
  by_cases h : faceOrbit R C p = faceOrbit R C q
  · exact Or.inl h
  · right
    refine Finset.disjoint_left.mpr ?_
    intro x hxp hxq
    apply h
    exact (faceOrbit_eq_of_mem R C p x hxp).symm.trans
      (faceOrbit_eq_of_mem R C q x hxq)

theorem faceOrbit_coverage {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) :
    ∀ p : FlowNetworkPort N, p ∈ faceOrbit R C p :=
  fun p => faceOrbit_contains R C p

theorem firstFaceReturn_eq_of_mem {N : FlowNetwork}
    (R : FlowLocalRotation N) (C : FlowCrossing N)
    (p q : FlowNetworkPort N) (hq : q ∈ faceOrbit R C p) :
    firstFaceReturn R C q = firstFaceReturn R C p := by
  calc
    firstFaceReturn R C q = (faceOrbit R C q).card :=
      (faceOrbit_card R C q).symm
    _ = (faceOrbit R C p).card := by
      rw [faceOrbit_eq_of_mem R C p q hq]
    _ = firstFaceReturn R C p := faceOrbit_card R C p

end DkMath.Tromino
