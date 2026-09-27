/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.BoundarySignature

#print "file: DkMath.Tromino.FlowSignature"

namespace DkMath.Tromino

open scoped BigOperators

structure FlowSignature where
  arity : Nat
  label : Fin arity → TrominoState
  nonzero : ∀ i, label i ≠ 0

def BoundarySignature.toFlowSignature (S : BoundarySignature) : FlowSignature where
  arity := S.arity
  label := boundaryDelta S
  nonzero := boundaryDelta_ne_zero S

@[simp] theorem BoundarySignature.toFlowSignature_arity (S : BoundarySignature) :
    S.toFlowSignature.arity = S.arity := rfl

@[simp] theorem BoundarySignature.toFlowSignature_label (S : BoundarySignature)
    (i : Fin S.toFlowSignature.arity) : S.toFlowSignature.label i = boundaryDelta S i := rfl

def flowSum (F : FlowSignature) : TrominoState := Finset.sum Finset.univ F.label
def FlowConserved (F : FlowSignature) : Prop := flowSum F = 0
def flowLabelCount (F : FlowSignature) (delta : TrominoState) : Nat :=
  (Finset.univ.filter (fun i => F.label i = delta)).card

theorem flowLabelCount_eq_sum_indicator (F : FlowSignature) (delta : TrominoState) :
    flowLabelCount F delta =
      Finset.sum Finset.univ (fun i : Fin F.arity => if F.label i = delta then 1 else 0) := by
  simp [flowLabelCount]

theorem flowLabelCount_cast (F : FlowSignature) (delta : TrominoState) :
    (flowLabelCount F delta : ZMod 2) =
      Finset.sum Finset.univ
        (fun i : Fin F.arity => if F.label i = delta then (1 : ZMod 2) else 0) := by
  rw [flowLabelCount_eq_sum_indicator]
  norm_cast

theorem flowLabelCount_zero (F : FlowSignature) : flowLabelCount F 0 = 0 := by
  unfold flowLabelCount
  apply Finset.card_eq_zero.mpr
  ext i
  simp [F.nonzero i]

theorem flowLabel_eq_deltaA_or_deltaB_or_deltaC (F : FlowSignature)
    (i : Fin F.arity) :
    F.label i = deltaA ∨ F.label i = deltaB ∨ F.label i = deltaC := by
  exact nonzeroState_eq_deltaA_or_deltaB_or_deltaC _ (F.nonzero i)

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

set_option linter.unusedSimpArgs false in
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
      · simp [hA, deltaA, deltaB, deltaC]
      · simp [hB, deltaA, deltaB, deltaC]
      · simp [hC, deltaA, deltaB, deltaC]
    _ = (Finset.sum Finset.univ
          (fun i : Fin F.arity => if F.label i = deltaA then (1 : ZMod 2) else 0)) +
          Finset.sum Finset.univ
            (fun i : Fin F.arity => if F.label i = deltaC then (1 : ZMod 2) else 0) := by
      rw [Finset.sum_add_distrib]
    _ = (flowLabelCount F deltaA + flowLabelCount F deltaC : ZMod 2) := by
      rw [← flowLabelCount_cast, ← flowLabelCount_cast]

set_option linter.unusedSimpArgs false in
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
      · simp [hB, deltaA, deltaB, deltaC]
      · simp [hC, deltaA, deltaB, deltaC]
    _ = (Finset.sum Finset.univ
          (fun i : Fin F.arity => if F.label i = deltaB then (1 : ZMod 2) else 0)) +
          Finset.sum Finset.univ
            (fun i : Fin F.arity => if F.label i = deltaC then (1 : ZMod 2) else 0) := by
      rw [Finset.sum_add_distrib]
    _ = (flowLabelCount F deltaB + flowLabelCount F deltaC : ZMod 2) := by
      rw [← flowLabelCount_cast, ← flowLabelCount_cast]

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

theorem flowSum_toFlowSignature (S : BoundarySignature) :
    flowSum S.toFlowSignature = boundarySum S := rfl

theorem flowConserved_toFlowSignature_iff (S : BoundarySignature) :
    FlowConserved S.toFlowSignature ↔ BoundaryConserved S := Iff.rfl

theorem flowLabelCount_toFlowSignature (S : BoundarySignature) (delta : TrominoState) :
    flowLabelCount S.toFlowSignature delta = boundaryLabelCount S delta := rfl

theorem boundaryConserved_iff_flowConserved_parity (S : BoundarySignature) :
    BoundaryConserved S ↔
      flowLabelCount S.toFlowSignature deltaA % 2 =
          flowLabelCount S.toFlowSignature deltaC % 2 ∧
        flowLabelCount S.toFlowSignature deltaB % 2 =
          flowLabelCount S.toFlowSignature deltaC % 2 := by
  rw [← flowConserved_toFlowSignature_iff S]
  exact flowConserved_iff_parity S.toFlowSignature

def exchangeBoundaryContact (gamma : TrominoState) (c : BoundaryContact) : BoundaryContact :=
  { inside := exchange gamma c.inside, outside := exchange gamma c.outside }

theorem contactDelta_exchangeBoundaryContact (gamma : TrominoState) (c : BoundaryContact) :
    contactDelta (exchangeBoundaryContact gamma c) = contactDelta c := by
  simp only [contactDelta, exchangeBoundaryContact, forbiddenDelta, exchange]
  calc
    c.inside + gamma + (c.outside + gamma) =
        (c.inside + c.outside) + (gamma + gamma) := by ac_rfl
    _ = c.inside + c.outside := by rw [state_add_self, add_zero]

theorem contactDelta_same_of_translation (x delta : TrominoState) :
    contactDelta { inside := x, outside := x + delta } = delta := by
  simp only [contactDelta, forbiddenDelta]
  rw [← add_assoc, state_add_self, zero_add]

end DkMath.Tromino
