/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.BoundarySignature

#print "file: DkMath.Tromino.FlowSignature"

namespace DkMath.Tromino

open scoped BigOperators

/-!
# Flow signatures

A flow signature is the label-only form of a boundary signature: it stores a
finite family of nonzero V4 labels and forgets the geometric contact data that
produced them.  Its total V4 sum is the conservation quantity.  Counting the
three nonzero labels and reducing those counts modulo two gives the two scalar
coordinate tests used by closed flow networks.
-/

/-- A finite indexed family of nonzero V4 labels.

The `nonzero` field records the properness condition inherited from boundary
contacts. -/
structure FlowSignature where
  arity : Nat
  label : Fin arity → TrominoState
  nonzero : ∀ i, label i ≠ 0

/-- Project a boundary signature to its label-only flow signature.

This forgets which inside/outside states produced a delta while preserving
arity, labels, and nonzeroness. -/
def BoundarySignature.toFlowSignature (S : BoundarySignature) : FlowSignature where
  arity := S.arity
  label := boundaryDelta S
  nonzero := boundaryDelta_ne_zero S

@[simp] theorem BoundarySignature.toFlowSignature_arity (S : BoundarySignature) :
    S.toFlowSignature.arity = S.arity := rfl

@[simp] theorem BoundarySignature.toFlowSignature_label (S : BoundarySignature)
    (i : Fin S.toFlowSignature.arity) : S.toFlowSignature.label i = boundaryDelta S i := rfl

/-- The total V4 sum of all labels in a flow signature.

`flowSum F = 0` is the finite conservation equation. -/
def flowSum (F : FlowSignature) : TrominoState := Finset.sum Finset.univ F.label
/-- Predicate expressing conservation of the total V4 label. -/
def FlowConserved (F : FlowSignature) : Prop := flowSum F = 0
/-- The multiplicity of one chosen V4 label in the finite signature. -/
def flowLabelCount (F : FlowSignature) (delta : TrominoState) : Nat :=
  (Finset.univ.filter (fun i => F.label i = delta)).card

/-- Label multiplicity is the sum of its pointwise indicator function. -/
theorem flowLabelCount_eq_sum_indicator (F : FlowSignature) (delta : TrominoState) :
    flowLabelCount F delta =
      Finset.sum Finset.univ (fun i : Fin F.arity => if F.label i = delta then 1 else 0) := by
  simp [flowLabelCount]

/-- The parity of a label multiplicity is its indicator sum in `ZMod 2`. -/
theorem flowLabelCount_cast (F : FlowSignature) (delta : TrominoState) :
    (flowLabelCount F delta : ZMod 2) =
      Finset.sum Finset.univ
        (fun i : Fin F.arity => if F.label i = delta then (1 : ZMod 2) else 0) := by
  rw [flowLabelCount_eq_sum_indicator]
  norm_cast

/-- Proper flow signatures contain no zero labels. -/
theorem flowLabelCount_zero (F : FlowSignature) : flowLabelCount F 0 = 0 := by
  unfold flowLabelCount
  apply Finset.card_eq_zero.mpr
  ext i
  simp [F.nonzero i]

/-- Every flow label is one of the three named nonzero V4 directions. -/
theorem flowLabel_eq_deltaA_or_deltaB_or_deltaC (F : FlowSignature)
    (i : Fin F.arity) :
    F.label i = deltaA ∨ F.label i = deltaB ∨ F.label i = deltaC := by
  exact nonzeroState_eq_deltaA_or_deltaB_or_deltaC _ (F.nonzero i)

/-- The three nonzero fibers partition the signature, so their multiplicities
sum to the arity. -/
theorem flowLabelCount_sum (F : FlowSignature) :
    flowLabelCount F deltaA + flowLabelCount F deltaB + flowLabelCount F deltaC = F.arity := by
  have hpoint (i : Fin F.arity) :
      (if F.label i = deltaA then 1 else 0) +
          (if F.label i = deltaB then 1 else 0) +
            (if F.label i = deltaC then 1 else 0) = 1 := by
    rcases flowLabel_eq_deltaA_or_deltaB_or_deltaC F i with hA | hB | hC
    · simp [hA, deltaA_ne_deltaB, deltaA_ne_deltaC]
    · simp [hB, deltaB_ne_deltaA, deltaB_ne_deltaC]
    · simp [hC, deltaC_ne_deltaA, deltaC_ne_deltaB]
  calc
    flowLabelCount F deltaA + flowLabelCount F deltaB + flowLabelCount F deltaC =
        (Finset.sum Finset.univ
          (fun i : Fin F.arity => if F.label i = deltaA then 1 else 0)) +
          (Finset.sum Finset.univ
            (fun i : Fin F.arity => if F.label i = deltaB then 1 else 0)) +
            Finset.sum Finset.univ
              (fun i : Fin F.arity => if F.label i = deltaC then 1 else 0) := by
      simp [flowLabelCount_eq_sum_indicator]
    _ = Finset.sum Finset.univ (fun i : Fin F.arity =>
          (if F.label i = deltaA then 1 else 0) +
            (if F.label i = deltaB then 1 else 0) +
              (if F.label i = deltaC then 1 else 0)) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    _ = Finset.sum Finset.univ (fun i : Fin F.arity => 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hpoint i
    _ = F.arity := by simp

/-- The first V4 coordinate of the total sum is the parity of the `A` and `C`
fibers. -/
theorem flowSum_fst (F : FlowSignature) :
    (flowSum F).1 =
      (flowLabelCount F deltaA + flowLabelCount F deltaC : ZMod 2) := by
  change (Finset.sum Finset.univ (fun i : Fin F.arity => F.label i)).1 = _
  rw [Prod.fst_sum]
  calc
    Finset.sum Finset.univ (fun i : Fin F.arity => (F.label i).1) =
        Finset.sum Finset.univ (fun i : Fin F.arity =>
          (if F.label i = deltaA then (1 : ZMod 2) else 0) +
            (if F.label i = deltaC then (1 : ZMod 2) else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rcases flowLabel_eq_deltaA_or_deltaB_or_deltaC F i with hA | hB | hC
      · simp [hA, deltaA,         deltaC]
      · simp [hB, deltaA, deltaB, deltaC]
      · simp [hC, deltaA,         deltaC]
    _ = (Finset.sum Finset.univ
          (fun i : Fin F.arity => if F.label i = deltaA then (1 : ZMod 2) else 0)) +
          Finset.sum Finset.univ
            (fun i : Fin F.arity => if F.label i = deltaC then (1 : ZMod 2) else 0) := by
      rw [Finset.sum_add_distrib]
    _ = (flowLabelCount F deltaA + flowLabelCount F deltaC : ZMod 2) := by
      rw [← flowLabelCount_cast, ← flowLabelCount_cast]

/-- The second V4 coordinate of the total sum is the parity of the `B` and `C`
fibers. -/
theorem flowSum_snd (F : FlowSignature) :
    (flowSum F).2 =
      (flowLabelCount F deltaB + flowLabelCount F deltaC : ZMod 2) := by
  change (Finset.sum Finset.univ (fun i : Fin F.arity => F.label i)).2 = _
  rw [Prod.snd_sum]
  calc
    Finset.sum Finset.univ (fun i : Fin F.arity => (F.label i).2) =
        Finset.sum Finset.univ (fun i : Fin F.arity =>
          (if F.label i = deltaB then (1 : ZMod 2) else 0) +
            (if F.label i = deltaC then (1 : ZMod 2) else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rcases flowLabel_eq_deltaA_or_deltaB_or_deltaC F i with hA | hB | hC
      · simp [hA, deltaA, deltaB, deltaC]
      · simp [hB,         deltaB, deltaC]
      · simp [hC,         deltaB, deltaC]
    _ = (Finset.sum Finset.univ
          (fun i : Fin F.arity => if F.label i = deltaB then (1 : ZMod 2) else 0)) +
          Finset.sum Finset.univ
            (fun i : Fin F.arity => if F.label i = deltaC then (1 : ZMod 2) else 0) := by
      rw [Finset.sum_add_distrib]
    _ = (flowLabelCount F deltaB + flowLabelCount F deltaC : ZMod 2) := by
      rw [← flowLabelCount_cast, ← flowLabelCount_cast]

/-- V4 conservation is equivalent to equality of the three nonzero fiber
parities, expressed by two independent equations. -/
theorem flowConserved_iff_parity (F : FlowSignature) :
    FlowConserved F ↔
      flowLabelCount F deltaA % 2 = flowLabelCount F deltaC % 2 ∧
        flowLabelCount F deltaB % 2 = flowLabelCount F deltaC % 2 := by
  constructor
  · intro h
    have hfst : (flowSum F).1 = 0 := congrArg Prod.fst h
    have hsnd : (flowSum F).2 = 0 := congrArg Prod.snd h
    rw [flowSum_fst, ← Nat.cast_add] at hfst
    rw [flowSum_snd, ← Nat.cast_add] at hsnd
    exact ⟨(zmodTwo_natCast_add_eq_zero_iff_mod_eq _ _).mp hfst,
      (zmodTwo_natCast_add_eq_zero_iff_mod_eq _ _).mp hsnd⟩
  · rintro ⟨hAC, hBC⟩
    apply Prod.ext
    · rw [flowSum_fst, ← Nat.cast_add]
      exact (zmodTwo_natCast_add_eq_zero_iff_mod_eq _ _).mpr hAC
    · rw [flowSum_snd, ← Nat.cast_add]
      exact (zmodTwo_natCast_add_eq_zero_iff_mod_eq _ _).mpr hBC

/-- Conservation leaves exactly two parity patterns: all three nonzero fibers
are even, or all three are odd. -/
theorem flowConserved_even_or_odd (F : FlowSignature)
    (hconserved : FlowConserved F) :
    (flowLabelCount F deltaA % 2 = 0 ∧
        flowLabelCount F deltaB % 2 = 0 ∧ flowLabelCount F deltaC % 2 = 0) ∨
      (flowLabelCount F deltaA % 2 = 1 ∧
        flowLabelCount F deltaB % 2 = 1 ∧ flowLabelCount F deltaC % 2 = 1) := by
  have hpar := (flowConserved_iff_parity F).mp hconserved
  rcases Nat.mod_two_eq_zero_or_one (flowLabelCount F deltaA) with hA | hA
  · left
    exact ⟨hA, by omega, by omega⟩
  · right
    exact ⟨hA, by omega, by omega⟩

/-- The boundary-to-flow projection preserves the total V4 sum. -/
theorem flowSum_toFlowSignature (S : BoundarySignature) :
    flowSum S.toFlowSignature = boundarySum S := rfl

/-- Boundary conservation is equivalent to conservation of its projected flow
signature. -/
theorem flowConserved_toFlowSignature_iff (S : BoundarySignature) :
    FlowConserved S.toFlowSignature ↔ BoundaryConserved S := Iff.rfl

/-- The projection preserves every label multiplicity. -/
theorem flowLabelCount_toFlowSignature (S : BoundarySignature) (delta : TrominoState) :
    flowLabelCount S.toFlowSignature delta = boundaryLabelCount S delta := rfl

/-- The boundary parity criterion is unchanged when expressed through the
projected flow signature. -/
theorem boundaryConserved_iff_flowConserved_parity (S : BoundarySignature) :
    BoundaryConserved S ↔
      flowLabelCount S.toFlowSignature deltaA % 2 =
          flowLabelCount S.toFlowSignature deltaC % 2 ∧
        flowLabelCount S.toFlowSignature deltaB % 2 =
          flowLabelCount S.toFlowSignature deltaC % 2 := by
  rw [← flowConserved_toFlowSignature_iff S]
  exact flowConserved_iff_parity S.toFlowSignature

/-- Apply one common V4 translation to both endpoints of a boundary contact.

This changes the representatives but not their relative delta. -/
def exchangeBoundaryContact (gamma : TrominoState) (c : BoundaryContact) : BoundaryContact :=
  { inside := exchange gamma c.inside, outside := exchange gamma c.outside }

/-- Common translation cancels from the endpoint difference, so the contact
delta is invariant. -/
theorem contactDelta_exchangeBoundaryContact (gamma : TrominoState) (c : BoundaryContact) :
    contactDelta (exchangeBoundaryContact gamma c) = contactDelta c := by
  simp only [contactDelta, exchangeBoundaryContact, forbiddenDelta, exchange]
  calc
    c.inside + gamma + (c.outside + gamma) =
        (c.inside + c.outside) + (gamma + gamma) := by ac_rfl
    _ = c.inside + c.outside := by rw [state_add_self, add_zero]

/-- A contact written in translated normal form has the prescribed delta. -/
theorem contactDelta_same_of_translation (x delta : TrominoState) :
    contactDelta { inside := x, outside := x + delta } = delta := by
  simp only [contactDelta, forbiddenDelta]
  rw [← add_assoc, state_add_self, zero_add]

end DkMath.Tromino
