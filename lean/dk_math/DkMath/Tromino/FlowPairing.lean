/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.FlowSignature
import DkMath.Tromino.BoundaryPairing

#print "file: DkMath.Tromino.FlowPairing"

namespace DkMath.Tromino

open scoped BigOperators

structure FlowPairing (F : FlowSignature) where
  mate : Fin F.arity → Fin F.arity
  involutive : Function.Involutive mate
  sameLabel : ∀ i, F.label (mate i) = F.label i

def flowResidualPorts {F : FlowSignature} (P : FlowPairing F) :
    Finset (Fin F.arity) := Finset.univ.filter (fun i => P.mate i = i)

def flowPairedPorts {F : FlowSignature} (P : FlowPairing F) :
    Finset (Fin F.arity) := (flowResidualPorts P)ᶜ

theorem mem_flowResidualPorts_iff {F : FlowSignature} (P : FlowPairing F)
    (i : Fin F.arity) : i ∈ flowResidualPorts P ↔ P.mate i = i := by
  simp [flowResidualPorts]

theorem mem_flowPairedPorts_iff {F : FlowSignature} (P : FlowPairing F)
    (i : Fin F.arity) : i ∈ flowPairedPorts P ↔ P.mate i ≠ i := by
  simp [flowPairedPorts, mem_flowResidualPorts_iff]

theorem not_mem_flowResidualPorts_iff {F : FlowSignature} (P : FlowPairing F)
    (i : Fin F.arity) : i ∉ flowResidualPorts P ↔ P.mate i ≠ i := by
  rw [mem_flowResidualPorts_iff]

theorem flowMate_ne_of_not_mem_residualPorts {F : FlowSignature}
    (P : FlowPairing F) {i : Fin F.arity} (hi : i ∉ flowResidualPorts P) :
    P.mate i ≠ i := (not_mem_flowResidualPorts_iff P i).mp hi

theorem flowMate_not_mem_residualPorts {F : FlowSignature} (P : FlowPairing F)
    {i : Fin F.arity} (hi : i ∉ flowResidualPorts P) :
    P.mate i ∉ flowResidualPorts P := by
  intro hmate
  apply hi
  rw [mem_flowResidualPorts_iff] at hmate ⊢
  have hfixed : P.mate (P.mate i) = P.mate i := hmate
  rw [P.involutive i] at hfixed
  exact False.elim ((flowMate_ne_of_not_mem_residualPorts P hi) hfixed.symm)

theorem flowMate_sameLabel {F : FlowSignature} (P : FlowPairing F)
    (i : Fin F.arity) : F.label (P.mate i) = F.label i := P.sameLabel i

def flowPortsWithLabel (F : FlowSignature) (delta : TrominoState) :
    Finset (Fin F.arity) := Finset.univ.filter (fun i => F.label i = delta)

theorem mem_flowPortsWithLabel_iff (F : FlowSignature) (delta : TrominoState)
    (i : Fin F.arity) : i ∈ flowPortsWithLabel F delta ↔ F.label i = delta := by
  simp [flowPortsWithLabel]

theorem flowPortsWithLabel_card (F : FlowSignature) (delta : TrominoState) :
    (flowPortsWithLabel F delta).card = flowLabelCount F delta := rfl

def flowFiberMate (F : FlowSignature) (delta : TrominoState)
    (i : Fin F.arity) : Fin F.arity :=
  if hi : i ∈ flowPortsWithLabel F delta then
    (fiberPairing (flowPortsWithLabel F delta) ⟨i, hi⟩).val
  else i

theorem flowFiberMate_mem (F : FlowSignature) (delta : TrominoState)
    {i : Fin F.arity} (hi : i ∈ flowPortsWithLabel F delta) :
    flowFiberMate F delta i ∈ flowPortsWithLabel F delta := by
  simp [flowFiberMate, hi]

theorem flowFiberMate_sameLabel (F : FlowSignature) (delta : TrominoState)
    {i : Fin F.arity} (hi : i ∈ flowPortsWithLabel F delta) :
    F.label (flowFiberMate F delta i) = delta :=
  (mem_flowPortsWithLabel_iff F delta _).mp (flowFiberMate_mem F delta hi)

theorem flowFiberMate_involutive (F : FlowSignature) (delta : TrominoState)
    {i : Fin F.arity} (hi : i ∈ flowPortsWithLabel F delta) :
    flowFiberMate F delta (flowFiberMate F delta i) = i := by
  simp only [flowFiberMate, dite_eq_left hi,
    dite_eq_left (fiberPairing _ ⟨i, hi⟩).property]
  have hsub :
      (⟨(fiberPairing (flowPortsWithLabel F delta) ⟨i, hi⟩).val,
        (fiberPairing (flowPortsWithLabel F delta) ⟨i, hi⟩).property⟩ :
        flowPortsWithLabel F delta) = fiberPairing (flowPortsWithLabel F delta) ⟨i, hi⟩ := by
    rfl
  rw [hsub, fiberPairing_involutive]

def canonicalFlowMate (F : FlowSignature) (i : Fin F.arity) : Fin F.arity :=
  flowFiberMate F (F.label i) i

theorem canonicalFlowMate_mem (F : FlowSignature) (i : Fin F.arity) :
    canonicalFlowMate F i ∈ flowPortsWithLabel F (F.label i) := by
  apply flowFiberMate_mem
  exact (mem_flowPortsWithLabel_iff F _ _).mpr rfl

theorem canonicalFlowMate_sameLabel (F : FlowSignature) (i : Fin F.arity) :
    F.label (canonicalFlowMate F i) = F.label i :=
  flowFiberMate_sameLabel F _ ((mem_flowPortsWithLabel_iff F _ _).mpr rfl)

theorem canonicalFlowMate_involutive (F : FlowSignature) :
    Function.Involutive (canonicalFlowMate F) := by
  intro i
  rw [canonicalFlowMate]
  rw [show F.label (canonicalFlowMate F i) = F.label i by
    exact canonicalFlowMate_sameLabel F i]
  exact flowFiberMate_involutive F _ ((mem_flowPortsWithLabel_iff F _ _).mpr rfl)

def canonicalFlowPairing (F : FlowSignature) : FlowPairing F where
  mate := canonicalFlowMate F
  involutive := canonicalFlowMate_involutive F
  sameLabel := canonicalFlowMate_sameLabel F

theorem canonicalFlowPairing_mate (F : FlowSignature) (i : Fin F.arity) :
    (canonicalFlowPairing F).mate i = canonicalFlowMate F i := rfl

def flowResidualPortsWithLabel {F : FlowSignature} (P : FlowPairing F)
    (delta : TrominoState) : Finset (Fin F.arity) :=
  (flowResidualPorts P).filter (fun i => F.label i = delta)

theorem mem_flowResidualPortsWithLabel_iff {F : FlowSignature}
    (P : FlowPairing F) (delta : TrominoState) (i : Fin F.arity) :
    i ∈ flowResidualPortsWithLabel P delta ↔
      P.mate i = i ∧ F.label i = delta := by
  simp [flowResidualPortsWithLabel, mem_flowResidualPorts_iff]

def flowFiberResidualIndices (F : FlowSignature) (delta : TrominoState) :
    Finset (Fin (flowPortsWithLabel F delta).card) :=
  Finset.univ.filter (fun r => adjacentMate _ r = r)

def flowFiberResidualPorts (F : FlowSignature) (delta : TrominoState) :
    Finset (Fin F.arity) :=
  (flowFiberResidualIndices F delta).image
    (fun r => (Finset.orderIsoOfFin (flowPortsWithLabel F delta) rfl r).val)

theorem flowFiberResidualPorts_card (F : FlowSignature) (delta : TrominoState) :
    (flowFiberResidualPorts F delta).card = flowLabelCount F delta % 2 := by
  unfold flowFiberResidualPorts flowFiberResidualIndices
  rw [Finset.card_image_of_injective _]
  · rw [adjacentMate_card_residual, flowPortsWithLabel_card]
  · intro a b hab
    apply (Finset.orderIsoOfFin (flowPortsWithLabel F delta) rfl).injective
    apply Subtype.ext
    exact hab

theorem flowResidual_filter_eq_fiberResidual (F : FlowSignature)
    (delta : TrominoState) :
    flowResidualPortsWithLabel (canonicalFlowPairing F) delta =
      flowFiberResidualPorts F delta := by
  ext i
  simp only [mem_flowResidualPortsWithLabel_iff]
  unfold flowFiberResidualPorts flowFiberResidualIndices
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hfix, hlabel⟩
    let s := flowPortsWithLabel F delta
    let e := Finset.orderIsoOfFin s rfl
    have hiS : i ∈ s := (mem_flowPortsWithLabel_iff F delta i).mpr hlabel
    let a := e.symm ⟨i, hiS⟩
    have hfix' : canonicalFlowMate F i = i := by
      simpa [canonicalFlowPairing_mate] using hfix
    have hmate : flowFiberMate F delta i = i := by
      simpa [canonicalFlowMate, hlabel] using hfix'
    have hpair : fiberPairing s ⟨i, hiS⟩ = ⟨i, hiS⟩ := by
      unfold flowFiberMate at hmate
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
    let s := flowPortsWithLabel F delta
    let e := Finset.orderIsoOfFin s rfl
    have hiS : i ∈ s := by rw [← hai]; exact (e a).property
    have hlabel : F.label i = delta := (mem_flowPortsWithLabel_iff F delta i).mp hiS
    have hxe : e a = ⟨i, hiS⟩ := by apply Subtype.ext; exact hai
    have harg : e.symm ⟨i, hiS⟩ = a := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact hxe.symm
    have hpair : fiberPairing s ⟨i, hiS⟩ = ⟨i, hiS⟩ := by
      unfold fiberPairing
      rw [harg, ha]
      exact hxe
    have hmate : flowFiberMate F delta i = i := by
      unfold flowFiberMate
      rw [dite_eq_left hiS]
      exact congrArg Subtype.val hpair
    exact ⟨by simpa [canonicalFlowPairing_mate, canonicalFlowMate, hlabel] using hmate,
      hlabel⟩

theorem flowResidualPorts_canonical_card_by_label (F : FlowSignature)
    (delta : TrominoState) :
    (flowResidualPortsWithLabel (canonicalFlowPairing F) delta).card =
      flowLabelCount F delta % 2 := by
  rw [flowResidual_filter_eq_fiberResidual]
  exact flowFiberResidualPorts_card F delta

theorem canonicalFlowPairing_residual_card (F : FlowSignature) :
    (flowResidualPorts (canonicalFlowPairing F)).card =
      flowLabelCount F deltaA % 2 +
        (flowLabelCount F deltaB % 2 + flowLabelCount F deltaC % 2) := by
  let R := flowResidualPorts (canonicalFlowPairing F)
  let RA := R.filter (fun i => F.label i = deltaA)
  let RB := R.filter (fun i => F.label i = deltaB)
  let RC := R.filter (fun i => F.label i = deltaC)
  have hunion : R = (RA ∪ RB) ∪ RC := by
    ext i
    constructor
    · intro hi
      rcases flowLabel_eq_deltaA_or_deltaB_or_deltaC F i with hA | hB | hC
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
  have hAcard : RA.card = flowLabelCount F deltaA % 2 := by
    simpa [RA, R, flowResidualPortsWithLabel] using
      flowResidualPorts_canonical_card_by_label F deltaA
  have hBcard : RB.card = flowLabelCount F deltaB % 2 := by
    simpa [RB, R, flowResidualPortsWithLabel] using
      flowResidualPorts_canonical_card_by_label F deltaB
  have hCcard : RC.card = flowLabelCount F deltaC % 2 := by
    simpa [RC, R, flowResidualPortsWithLabel] using
      flowResidualPorts_canonical_card_by_label F deltaC
  change R.card = _
  rw [hunion, Finset.card_union_of_disjoint hac,
    Finset.card_union_of_disjoint hab, hAcard, hBcard, hCcard]
  omega

theorem canonicalFlowPairing_even_perfect (F : FlowSignature)
    (hA : flowLabelCount F deltaA % 2 = 0)
    (hB : flowLabelCount F deltaB % 2 = 0)
    (hC : flowLabelCount F deltaC % 2 = 0) :
    flowResidualPorts (canonicalFlowPairing F) = ∅ := by
  ext i
  constructor
  · intro hi
    rcases flowLabel_eq_deltaA_or_deltaB_or_deltaC F i with hlabel | hlabel | hlabel
    · have hcard := flowResidualPorts_canonical_card_by_label F deltaA
      have hmem : i ∈ flowResidualPortsWithLabel (canonicalFlowPairing F) deltaA :=
        (mem_flowResidualPortsWithLabel_iff (canonicalFlowPairing F) deltaA i).mpr
          ⟨(mem_flowResidualPorts_iff (canonicalFlowPairing F) i).mp hi, hlabel⟩
      have hpos := Finset.card_pos.mpr ⟨i, hmem⟩
      rw [hcard, hA] at hpos
      omega
    · have hcard := flowResidualPorts_canonical_card_by_label F deltaB
      have hmem : i ∈ flowResidualPortsWithLabel (canonicalFlowPairing F) deltaB :=
        (mem_flowResidualPortsWithLabel_iff (canonicalFlowPairing F) deltaB i).mpr
          ⟨(mem_flowResidualPorts_iff (canonicalFlowPairing F) i).mp hi, hlabel⟩
      have hpos := Finset.card_pos.mpr ⟨i, hmem⟩
      rw [hcard, hB] at hpos
      omega
    · have hcard := flowResidualPorts_canonical_card_by_label F deltaC
      have hmem : i ∈ flowResidualPortsWithLabel (canonicalFlowPairing F) deltaC :=
        (mem_flowResidualPortsWithLabel_iff (canonicalFlowPairing F) deltaC i).mpr
          ⟨(mem_flowResidualPorts_iff (canonicalFlowPairing F) i).mp hi, hlabel⟩
      have hpos := Finset.card_pos.mpr ⟨i, hmem⟩
      rw [hcard, hC] at hpos
      omega
  · intro hi
    simp at hi

theorem canonicalFlowPairing_odd_residual_card (F : FlowSignature)
    (hA : flowLabelCount F deltaA % 2 = 1)
    (hB : flowLabelCount F deltaB % 2 = 1)
    (hC : flowLabelCount F deltaC % 2 = 1) :
    (flowResidualPorts (canonicalFlowPairing F)).card = 3 := by
  rw [canonicalFlowPairing_residual_card]
  omega

theorem canonicalFlowPairing_odd_one_each (F : FlowSignature)
    (hA : flowLabelCount F deltaA % 2 = 1)
    (hB : flowLabelCount F deltaB % 2 = 1)
    (hC : flowLabelCount F deltaC % 2 = 1) :
    (flowResidualPortsWithLabel (canonicalFlowPairing F) deltaA).card = 1 ∧
      (flowResidualPortsWithLabel (canonicalFlowPairing F) deltaB).card = 1 ∧
        (flowResidualPortsWithLabel (canonicalFlowPairing F) deltaC).card = 1 := by
  exact ⟨(flowResidualPorts_canonical_card_by_label F deltaA).trans hA,
    (flowResidualPorts_canonical_card_by_label F deltaB).trans hB,
    (flowResidualPorts_canonical_card_by_label F deltaC).trans hC⟩

theorem canonicalFlowPairing_conserved_decomposition (F : FlowSignature)
    (hconserved : FlowConserved F) :
    flowResidualPorts (canonicalFlowPairing F) = ∅ ∨
      (flowResidualPorts (canonicalFlowPairing F)).card = 3 := by
  rcases flowConserved_even_or_odd F hconserved with hEven | hOdd
  · exact Or.inl (canonicalFlowPairing_even_perfect F hEven.1 hEven.2.1 hEven.2.2)
  · exact Or.inr (canonicalFlowPairing_odd_residual_card F hOdd.1 hOdd.2.1 hOdd.2.2)

theorem canonicalFlowPairing_transition_ready (F : FlowSignature)
    (i : Fin F.arity)
    (hi : i ∉ flowResidualPorts (canonicalFlowPairing F)) :
    canonicalFlowMate F i ≠ i ∧
      F.label (canonicalFlowMate F i) = F.label i ∧
        canonicalFlowMate F (canonicalFlowMate F i) = i := by
  exact ⟨flowMate_ne_of_not_mem_residualPorts (canonicalFlowPairing F) hi,
    canonicalFlowMate_sameLabel F i, canonicalFlowMate_involutive F i⟩

def BoundaryPairing.toFlowPairing {S : BoundarySignature} (P : BoundaryPairing S) :
    FlowPairing S.toFlowSignature where
  mate := P.mate
  involutive := P.involutive
  sameLabel := P.sameLabel

@[simp] theorem BoundaryPairing.toFlowPairing_mate {S : BoundarySignature}
    (P : BoundaryPairing S) (i : Fin S.arity) :
    P.toFlowPairing.mate i = P.mate i := rfl

theorem flowResidualPorts_toFlowPairing {S : BoundarySignature}
    (P : BoundaryPairing S) :
    flowResidualPorts P.toFlowPairing = residualPorts P := rfl

theorem flowPairedPorts_toFlowPairing {S : BoundarySignature}
    (P : BoundaryPairing S) :
    flowPairedPorts P.toFlowPairing = pairedPorts P := rfl

theorem canonicalFlowMate_toFlowSignature (S : BoundarySignature)
    (i : Fin S.arity) :
    canonicalFlowMate S.toFlowSignature i = canonicalMate S i := by
  rfl

theorem canonicalBoundaryPairing_mate_eq_canonicalFlowPairing_mate
    (S : BoundarySignature) (i : Fin S.arity) :
    (canonicalBoundaryPairing S).mate i =
      (canonicalFlowPairing S.toFlowSignature).mate i := by
  rfl

theorem canonicalFlowResidual_toFlowSignature (S : BoundarySignature) :
    flowResidualPorts (canonicalFlowPairing S.toFlowSignature) =
      residualPorts (canonicalBoundaryPairing S) := by
  rfl

theorem canonicalFlowPaired_toFlowSignature (S : BoundarySignature) :
    flowPairedPorts (canonicalFlowPairing S.toFlowSignature) =
      pairedPorts (canonicalBoundaryPairing S) := by
  rfl

theorem canonicalFlowResidual_card_by_label_toFlowSignature
    (S : BoundarySignature) (delta : TrominoState) :
    (flowResidualPortsWithLabel (canonicalFlowPairing S.toFlowSignature) delta).card =
      ((residualPorts (canonicalBoundaryPairing S)).filter
        (fun i => boundaryDelta S i = delta)).card := by
  rfl

end DkMath.Tromino
