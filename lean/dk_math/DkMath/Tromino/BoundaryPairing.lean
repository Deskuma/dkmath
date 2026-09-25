/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.BoundarySignature
import Mathlib.Data.Finset.Sort

#print "file: DkMath.Tromino.BoundaryPairing"

namespace DkMath.Tromino

open scoped BigOperators

/-! ### Ordered finite pairing -/

/-- Pair consecutive elements of `Fin n`; the last element is fixed when `n` is odd. -/
def adjacentMate (n : Nat) (i : Fin n) : Fin n :=
  if hi : i.val % 2 = 0 then
    if hnext : i.val + 1 < n then ⟨i.val + 1, by omega⟩ else i
  else ⟨i.val - 1, by omega⟩

theorem adjacentMate_even_val (n : Nat) (i : Fin n)
    (hi : i.val % 2 = 0) (hnext : i.val + 1 < n) :
    (adjacentMate n i).val = i.val + 1 := by
  simp [adjacentMate, hi, hnext]

theorem adjacentMate_even_last (n : Nat) (i : Fin n)
    (hi : i.val % 2 = 0) (hnext : ¬ i.val + 1 < n) :
    adjacentMate n i = i := by
  simp [adjacentMate, hi, hnext]

theorem adjacentMate_odd_val (n : Nat) (i : Fin n)
    (hi : i.val % 2 ≠ 0) : (adjacentMate n i).val = i.val - 1 := by
  simp [adjacentMate, hi]

theorem adjacentMate_involutive (n : Nat) :
    Function.Involutive (adjacentMate n) := by
  intro i
  by_cases hi : i.val % 2 = 0
  · by_cases hnext : i.val + 1 < n
    · have hmate := adjacentMate_even_val n i hi hnext
      have hodd : (adjacentMate n i).val % 2 ≠ 0 := by rw [hmate]; omega
      have hback := adjacentMate_odd_val n (adjacentMate n i) hodd
      apply Fin.ext
      omega
    · simp [adjacentMate_even_last n i hi hnext]
  · have hi1 : i.val % 2 = 1 := by omega
    have hmate_even : (adjacentMate n i).val % 2 = 0 := by
      rw [adjacentMate_odd_val n i hi]
      omega
    have hnext : (adjacentMate n i).val + 1 < n := by
      rw [adjacentMate_odd_val n i hi]
      omega
    have hback := adjacentMate_even_val n (adjacentMate n i) hmate_even hnext
    rw [adjacentMate_odd_val n i hi] at hmate_even hnext hback
    apply Fin.ext
    omega

theorem adjacentMate_eq_self_iff (n : Nat) (i : Fin n) :
    adjacentMate n i = i ↔ i.val % 2 = 0 ∧ i.val + 1 = n := by
  constructor
  · intro h
    by_cases hi : i.val % 2 = 0
    · refine ⟨hi, ?_⟩
      by_cases hnext : i.val + 1 < n
      · have hval := adjacentMate_even_val n i hi hnext
        rw [h] at hval
        omega
      · omega
    · have hval := adjacentMate_odd_val n i hi
      rw [h] at hval
      omega
  · rintro ⟨hi, hlast⟩
    exact adjacentMate_even_last n i hi (by omega)

theorem adjacentMate_card_residual (n : Nat) :
    (Finset.univ.filter (fun i : Fin n => adjacentMate n i = i)).card = n % 2 := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    by_cases hodd : n % 2 = 1
    · have hlast : (n - 1 : Nat) % 2 = 0 := by omega
      have hlt : n - 1 < n := by omega
      have hset : Finset.univ.filter (fun i : Fin n => adjacentMate n i = i) =
          {⟨n - 1, hlt⟩} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        rw [adjacentMate_eq_self_iff]
        constructor
        · rintro ⟨_, hlast_i⟩
          apply Fin.ext
          change i.val = n - 1
          omega
        · intro hi_singleton
          have hi_val : i.val = n - 1 := congrArg Fin.val hi_singleton
          exact ⟨by omega, by omega⟩
      rw [hset, Finset.card_singleton, hodd]
    · have heven : n % 2 = 0 := by omega
      have hset : Finset.univ.filter (fun i : Fin n => adjacentMate n i = i) = ∅ := by
        ext i
        simp [adjacentMate_eq_self_iff]
        omega
      rw [hset, Finset.card_empty, heven]

structure BoundaryPairing (S : BoundarySignature) where
  mate : Fin S.arity → Fin S.arity
  involutive : Function.Involutive mate
  sameLabel : ∀ i, boundaryDelta S (mate i) = boundaryDelta S i

def residualPorts {S : BoundarySignature} (P : BoundaryPairing S) :
    Finset (Fin S.arity) := Finset.univ.filter (fun i => P.mate i = i)

theorem mem_residualPorts_iff {S : BoundarySignature} (P : BoundaryPairing S)
    (i : Fin S.arity) : i ∈ residualPorts P ↔ P.mate i = i := by
  simp [residualPorts]

def pairedPorts {S : BoundarySignature} (P : BoundaryPairing S) :
    Finset (Fin S.arity) := (residualPorts P)ᶜ

theorem not_mem_residualPorts_iff {S : BoundarySignature} (P : BoundaryPairing S)
    (i : Fin S.arity) : i ∉ residualPorts P ↔ P.mate i ≠ i := by
  rw [mem_residualPorts_iff]

theorem mate_ne_of_not_mem_residualPorts {S : BoundarySignature}
    (P : BoundaryPairing S) {i : Fin S.arity} (hi : i ∉ residualPorts P) :
    P.mate i ≠ i := (not_mem_residualPorts_iff P i).mp hi

theorem mate_not_mem_residualPorts {S : BoundarySignature} (P : BoundaryPairing S)
    {i : Fin S.arity} (hi : i ∉ residualPorts P) : P.mate i ∉ residualPorts P := by
  intro hmate
  apply hi
  rw [mem_residualPorts_iff] at hmate ⊢
  have hfixed : P.mate (P.mate i) = P.mate i := hmate
  rw [P.involutive i] at hfixed
  exact False.elim ((mate_ne_of_not_mem_residualPorts P hi) hfixed.symm)

theorem mate_sameLabel {S : BoundarySignature} (P : BoundaryPairing S)
    (i : Fin S.arity) : boundaryDelta S (P.mate i) = boundaryDelta S i := P.sameLabel i

def portsWithLabel (S : BoundarySignature) (delta : TrominoState) :
    Finset (Fin S.arity) := Finset.univ.filter (fun i => boundaryDelta S i = delta)

theorem mem_portsWithLabel_iff (S : BoundarySignature) (delta : TrominoState)
    (i : Fin S.arity) : i ∈ portsWithLabel S delta ↔ boundaryDelta S i = delta := by
  simp [portsWithLabel]

theorem portsWithLabel_card (S : BoundarySignature) (delta : TrominoState) :
    (portsWithLabel S delta).card = boundaryLabelCount S delta := rfl

def fiberPairing {α : Type*} [LinearOrder α] (s : Finset α) (x : s) : s :=
  Finset.orderIsoOfFin s rfl (adjacentMate s.card ((Finset.orderIsoOfFin s rfl).symm x))

theorem fiberPairing_involutive {α : Type*} [LinearOrder α]
    (s : Finset α) (x : s) : fiberPairing s (fiberPairing s x) = x := by
  unfold fiberPairing
  let e := Finset.orderIsoOfFin s rfl
  change e (adjacentMate s.card (e.symm (e (adjacentMate s.card (e.symm x))))) = x
  rw [e.symm_apply_apply, adjacentMate_involutive]
  exact e.apply_symm_apply x

def fiberMate (S : BoundarySignature) (delta : TrominoState)
    (i : Fin S.arity) : Fin S.arity :=
  if hi : i ∈ portsWithLabel S delta then
    (fiberPairing (portsWithLabel S delta) ⟨i, hi⟩).val
  else i

theorem fiberMate_mem (S : BoundarySignature) (delta : TrominoState)
    {i : Fin S.arity} (hi : i ∈ portsWithLabel S delta) :
    fiberMate S delta i ∈ portsWithLabel S delta := by
  simp [fiberMate, hi]

theorem fiberMate_sameLabel (S : BoundarySignature) (delta : TrominoState)
    {i : Fin S.arity} (hi : i ∈ portsWithLabel S delta) :
    boundaryDelta S (fiberMate S delta i) = delta :=
  (mem_portsWithLabel_iff S delta _).mp (fiberMate_mem S delta hi)

theorem fiberMate_involutive (S : BoundarySignature) (delta : TrominoState)
    {i : Fin S.arity} (hi : i ∈ portsWithLabel S delta) :
    fiberMate S delta (fiberMate S delta i) = i := by
  simp only [fiberMate, dite_eq_left hi, dite_eq_left (fiberPairing _ ⟨i, hi⟩).property]
  have hsub :
      (⟨(fiberPairing (portsWithLabel S delta) ⟨i, hi⟩).val,
        (fiberPairing (portsWithLabel S delta) ⟨i, hi⟩).property⟩ :
        portsWithLabel S delta) = fiberPairing (portsWithLabel S delta) ⟨i, hi⟩ := by
    rfl
  rw [hsub, fiberPairing_involutive]

def canonicalMate (S : BoundarySignature) (i : Fin S.arity) : Fin S.arity :=
  fiberMate S (boundaryDelta S i) i

theorem canonicalMate_mem (S : BoundarySignature) (i : Fin S.arity) :
    canonicalMate S i ∈ portsWithLabel S (boundaryDelta S i) := by
  apply fiberMate_mem
  exact (mem_portsWithLabel_iff S _ _).mpr rfl

theorem canonicalMate_sameLabel (S : BoundarySignature) (i : Fin S.arity) :
    boundaryDelta S (canonicalMate S i) = boundaryDelta S i :=
  fiberMate_sameLabel S _ ((mem_portsWithLabel_iff S _ _).mpr rfl)

theorem canonicalMate_involutive (S : BoundarySignature) :
    Function.Involutive (canonicalMate S) := by
  intro i
  rw [canonicalMate]
  rw [show boundaryDelta S (canonicalMate S i) = boundaryDelta S i by
    exact canonicalMate_sameLabel S i]
  exact fiberMate_involutive S _ ((mem_portsWithLabel_iff S _ _).mpr rfl)

def canonicalBoundaryPairing (S : BoundarySignature) : BoundaryPairing S where
  mate := canonicalMate S
  involutive := canonicalMate_involutive S
  sameLabel := canonicalMate_sameLabel S

theorem canonicalBoundaryPairing_mate (S : BoundarySignature) (i : Fin S.arity) :
    (canonicalBoundaryPairing S).mate i = canonicalMate S i := rfl

def fiberResidualIndices (S : BoundarySignature) (delta : TrominoState) :
    Finset (Fin (portsWithLabel S delta).card) :=
  Finset.univ.filter (fun r => adjacentMate _ r = r)

def fiberResidualPorts (S : BoundarySignature) (delta : TrominoState) :
    Finset (Fin S.arity) :=
  (fiberResidualIndices S delta).image
    (fun r => (Finset.orderIsoOfFin (portsWithLabel S delta) rfl r).val)

theorem fiberResidualPorts_card (S : BoundarySignature) (delta : TrominoState) :
    (fiberResidualPorts S delta).card = boundaryLabelCount S delta % 2 := by
  unfold fiberResidualPorts fiberResidualIndices
  rw [Finset.card_image_of_injective _]
  · rw [adjacentMate_card_residual, portsWithLabel_card]
  · intro a b hab
    apply (Finset.orderIsoOfFin (portsWithLabel S delta) rfl).injective
    apply Subtype.ext
    exact hab

theorem residual_filter_eq_fiberResidual (S : BoundarySignature)
    (delta : TrominoState) :
    (residualPorts (canonicalBoundaryPairing S)).filter
        (fun i => boundaryDelta S i = delta) = fiberResidualPorts S delta := by
  ext i
  simp only [Finset.mem_filter, mem_residualPorts_iff]
  unfold fiberResidualPorts fiberResidualIndices
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hfix, hlabel⟩
    let s := portsWithLabel S delta
    let e := Finset.orderIsoOfFin s rfl
    have hiS : i ∈ s := (mem_portsWithLabel_iff S delta i).mpr hlabel
    let a := e.symm ⟨i, hiS⟩
    have hfix' : canonicalMate S i = i := by
      simpa [canonicalBoundaryPairing_mate] using hfix
    have hmate : fiberMate S delta i = i := by
      simpa [canonicalMate, hlabel] using hfix'
    have hpair : fiberPairing s ⟨i, hiS⟩ = ⟨i, hiS⟩ := by
      unfold fiberMate at hmate
      rw [dite_eq_left hiS] at hmate
      apply Subtype.ext
      exact hmate
    have hxe : e a = ⟨i, hiS⟩ := e.apply_symm_apply _
    have hpaired : e (adjacentMate s.card a) = e a := hpair.trans hxe.symm
    have hadj : adjacentMate s.card a = a := e.injective hpaired
    have hval := congrArg Subtype.val (e.apply_symm_apply (⟨i, hiS⟩ : s))
    exact ⟨a, hadj, by
      calc
        (Finset.orderIsoOfFin s rfl a).val = (e a).val := rfl
        _ = i := hval⟩
  · rintro ⟨a, ha, hai⟩
    let s := portsWithLabel S delta
    let e := Finset.orderIsoOfFin s rfl
    have hiS : i ∈ s := by rw [← hai]; exact (e a).property
    have hlabel : boundaryDelta S i = delta := (mem_portsWithLabel_iff S delta i).mp hiS
    have hxe : e a = ⟨i, hiS⟩ := by apply Subtype.ext; exact hai
    have harg : e.symm ⟨i, hiS⟩ = a := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact hxe.symm
    have hpair : fiberPairing s ⟨i, hiS⟩ = ⟨i, hiS⟩ := by
      unfold fiberPairing
      rw [harg, ha]
      exact hxe
    have hmate : fiberMate S delta i = i := by
      unfold fiberMate
      rw [dite_eq_left hiS]
      exact congrArg Subtype.val hpair
    exact ⟨by simpa [canonicalBoundaryPairing_mate, canonicalMate, hlabel] using hmate,
      hlabel⟩

theorem residualPorts_canonical_card_by_label (S : BoundarySignature)
    (delta : TrominoState) :
    ((residualPorts (canonicalBoundaryPairing S)).filter
        (fun i => boundaryDelta S i = delta)).card =
      boundaryLabelCount S delta % 2 := by
  rw [residual_filter_eq_fiberResidual]
  exact fiberResidualPorts_card S delta

theorem canonicalBoundaryPairing_residual_card (S : BoundarySignature) :
    (residualPorts (canonicalBoundaryPairing S)).card =
      boundaryLabelCount S deltaA % 2 +
        (boundaryLabelCount S deltaB % 2 + boundaryLabelCount S deltaC % 2) := by
  let R := residualPorts (canonicalBoundaryPairing S)
  let RA := R.filter (fun i => boundaryDelta S i = deltaA)
  let RB := R.filter (fun i => boundaryDelta S i = deltaB)
  let RC := R.filter (fun i => boundaryDelta S i = deltaC)
  have hunion : R = (RA ∪ RB) ∪ RC := by
    ext i
    constructor
    · intro hi
      rcases boundaryDelta_eq_deltaA_or_deltaB_or_deltaC S i with hA | hB | hC
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
          (Or.inl (Finset.mem_filter.mpr ⟨hi, hA⟩))))
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
          (Or.inr (Finset.mem_filter.mpr ⟨hi, hB⟩))))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hi, hC⟩))
    · intro hi
      rcases Finset.mem_union.mp hi with hi | hi
      · rcases Finset.mem_union.mp hi with hi | hi
        · exact (Finset.mem_filter.mp hi).1
        · exact (Finset.mem_filter.mp hi).1
      · exact (Finset.mem_filter.mp hi).1
  have hab : Disjoint RA RB := by
    rw [Finset.disjoint_left]
    intro i hiA hiB
    exact deltaA_ne_deltaB ((Finset.mem_filter.mp hiA).2.symm.trans
      (Finset.mem_filter.mp hiB).2)
  have hac : Disjoint (RA ∪ RB) RC := by
    rw [Finset.disjoint_left]
    intro i hiAB hiC
    rcases Finset.mem_union.mp hiAB with hiA | hiB
    · exact deltaA_ne_deltaC ((Finset.mem_filter.mp hiA).2.symm.trans
        (Finset.mem_filter.mp hiC).2)
    · exact deltaB_ne_deltaC ((Finset.mem_filter.mp hiB).2.symm.trans
        (Finset.mem_filter.mp hiC).2)
  have hAcard : RA.card = boundaryLabelCount S deltaA % 2 := by
    simpa [RA, R] using residualPorts_canonical_card_by_label S deltaA
  have hBcard : RB.card = boundaryLabelCount S deltaB % 2 := by
    simpa [RB, R] using residualPorts_canonical_card_by_label S deltaB
  have hCcard : RC.card = boundaryLabelCount S deltaC % 2 := by
    simpa [RC, R] using residualPorts_canonical_card_by_label S deltaC
  change R.card = _
  rw [hunion, Finset.card_union_of_disjoint hac,
    Finset.card_union_of_disjoint hab, hAcard, hBcard, hCcard]
  omega

theorem canonicalBoundaryPairing_even_perfect (S : BoundarySignature)
    (hA : boundaryLabelCount S deltaA % 2 = 0)
    (hB : boundaryLabelCount S deltaB % 2 = 0)
    (hC : boundaryLabelCount S deltaC % 2 = 0) :
    residualPorts (canonicalBoundaryPairing S) = ∅ := by
  ext i
  constructor
  · intro hi
    rcases boundaryDelta_eq_deltaA_or_deltaB_or_deltaC S i with hlabel | hlabel | hlabel
    · have hcard := residualPorts_canonical_card_by_label S deltaA
      have hmem : i ∈ (residualPorts (canonicalBoundaryPairing S)).filter
          (fun j => boundaryDelta S j = deltaA) := Finset.mem_filter.mpr ⟨hi, hlabel⟩
      have hpos := Finset.card_pos.mpr ⟨i, hmem⟩
      rw [hcard, hA] at hpos
      omega
    · have hcard := residualPorts_canonical_card_by_label S deltaB
      have hmem : i ∈ (residualPorts (canonicalBoundaryPairing S)).filter
          (fun j => boundaryDelta S j = deltaB) := Finset.mem_filter.mpr ⟨hi, hlabel⟩
      have hpos := Finset.card_pos.mpr ⟨i, hmem⟩
      rw [hcard, hB] at hpos
      omega
    · have hcard := residualPorts_canonical_card_by_label S deltaC
      have hmem : i ∈ (residualPorts (canonicalBoundaryPairing S)).filter
          (fun j => boundaryDelta S j = deltaC) := Finset.mem_filter.mpr ⟨hi, hlabel⟩
      have hpos := Finset.card_pos.mpr ⟨i, hmem⟩
      rw [hcard, hC] at hpos
      omega
  · intro hi
    simp at hi

theorem canonicalBoundaryPairing_odd_residual_card (S : BoundarySignature)
    (hA : boundaryLabelCount S deltaA % 2 = 1)
    (hB : boundaryLabelCount S deltaB % 2 = 1)
    (hC : boundaryLabelCount S deltaC % 2 = 1) :
    (residualPorts (canonicalBoundaryPairing S)).card = 3 := by
  rw [canonicalBoundaryPairing_residual_card]
  omega

theorem canonicalBoundaryPairing_conserved_decomposition (S : BoundarySignature)
    (hconserved : BoundaryConserved S) :
    residualPorts (canonicalBoundaryPairing S) = ∅ ∨
      (residualPorts (canonicalBoundaryPairing S)).card = 3 := by
  rcases boundaryConserved_even_or_odd S hconserved with hEven | hOdd
  · exact Or.inl (canonicalBoundaryPairing_even_perfect S hEven.1 hEven.2.1 hEven.2.2)
  · exact Or.inr (canonicalBoundaryPairing_odd_residual_card S hOdd.1 hOdd.2.1 hOdd.2.2)

theorem canonicalBoundaryPairing_transition_ready (S : BoundarySignature)
    (i : Fin S.arity)
    (hi : i ∉ residualPorts (canonicalBoundaryPairing S)) :
    canonicalMate S i ≠ i ∧
      boundaryDelta S (canonicalMate S i) = boundaryDelta S i ∧
        canonicalMate S (canonicalMate S i) = i := by
  exact ⟨mate_ne_of_not_mem_residualPorts (canonicalBoundaryPairing S) hi,
    canonicalMate_sameLabel S i, canonicalMate_involutive S i⟩

end DkMath.Tromino
