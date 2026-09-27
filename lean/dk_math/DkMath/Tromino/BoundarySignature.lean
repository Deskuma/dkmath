/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PieceExchange

#print "file: DkMath.Tromino.BoundarySignature"

namespace DkMath.Tromino

open scoped BigOperators

def contactDelta (contact : BoundaryContact) : TrominoState := forbiddenDelta contact

theorem contactDelta_eq_zero_iff (contact : BoundaryContact) :
    contactDelta contact = 0 ↔ contact.inside = contact.outside :=
  forbiddenDelta_eq_zero_iff contact

theorem contactDelta_ne_zero_of_ne (contact : BoundaryContact)
    (h : contact.inside ≠ contact.outside) : contactDelta contact ≠ 0 := by
  intro hzero
  exact h ((contactDelta_eq_zero_iff contact).mp hzero)

def deltaA : TrominoState := (1, 0)
def deltaB : TrominoState := (0, 1)
def deltaC : TrominoState := (1, 1)

theorem deltaA_ne_zero : deltaA ≠ 0 := by decide
theorem deltaB_ne_zero : deltaB ≠ 0 := by decide
theorem deltaC_ne_zero : deltaC ≠ 0 := by decide
theorem deltaA_ne_deltaB : deltaA ≠ deltaB := by decide
theorem deltaA_ne_deltaC : deltaA ≠ deltaC := by decide
theorem deltaB_ne_deltaC : deltaB ≠ deltaC := by decide
theorem deltaB_ne_deltaA : deltaB ≠ deltaA := by decide
theorem deltaC_ne_deltaA : deltaC ≠ deltaA := by decide
theorem deltaC_ne_deltaB : deltaC ≠ deltaB := by decide

theorem deltaA_add_deltaB : deltaA + deltaB = deltaC := by decide
theorem deltaB_add_deltaC : deltaB + deltaC = deltaA := by decide
theorem deltaC_add_deltaA : deltaC + deltaA = deltaB := by decide

theorem deltaA_add_deltaB_add_deltaC : deltaA + deltaB + deltaC = 0 := by
  rw [deltaA_add_deltaB]
  exact state_add_self deltaC

theorem nonzeroState_eq_deltaA_or_deltaB_or_deltaC
    (delta : TrominoState) (hdelta : delta ≠ 0) :
    delta = deltaA ∨ delta = deltaB ∨ delta = deltaC := by
  fin_cases delta
  · exact (hdelta rfl).elim
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl
  · exact Or.inr (Or.inr rfl)

structure BoundarySignature where
  arity : Nat
  contact : Fin arity → BoundaryContact
  proper : ∀ i, (contact i).inside ≠ (contact i).outside

def boundaryDelta (S : BoundarySignature) (i : Fin S.arity) : TrominoState :=
  contactDelta (S.contact i)

theorem boundaryDelta_ne_zero (S : BoundarySignature)
    (i : Fin S.arity) : boundaryDelta S i ≠ 0 := by
  exact contactDelta_ne_zero_of_ne (S.contact i) (S.proper i)

theorem boundaryDelta_eq_deltaA_or_deltaB_or_deltaC (S : BoundarySignature)
    (i : Fin S.arity) :
    boundaryDelta S i = deltaA ∨ boundaryDelta S i = deltaB ∨
      boundaryDelta S i = deltaC := by
  exact nonzeroState_eq_deltaA_or_deltaB_or_deltaC _
    (boundaryDelta_ne_zero S i)

def boundarySum (S : BoundarySignature) : TrominoState :=
  Finset.sum Finset.univ (fun i : Fin S.arity => boundaryDelta S i)

def BoundaryConserved (S : BoundarySignature) : Prop := boundarySum S = 0

def boundaryLabelCount (S : BoundarySignature) (delta : TrominoState) : Nat :=
  (Finset.univ.filter (fun i : Fin S.arity => boundaryDelta S i = delta)).card

theorem boundaryLabelCount_eq_sum_indicator
    (S : BoundarySignature) (delta : TrominoState) :
    boundaryLabelCount S delta =
      Finset.sum Finset.univ
        (fun i : Fin S.arity => if boundaryDelta S i = delta then 1 else 0) := by
  simp [boundaryLabelCount]

theorem boundaryLabelCount_cast
    (S : BoundarySignature) (delta : TrominoState) :
    (boundaryLabelCount S delta : ZMod 2) =
      Finset.sum Finset.univ
        (fun i : Fin S.arity =>
          if boundaryDelta S i = delta then (1 : ZMod 2) else 0) := by
  rw [boundaryLabelCount_eq_sum_indicator]
  norm_cast

theorem boundaryLabelCount_zero (S : BoundarySignature) :
    boundaryLabelCount S 0 = 0 := by
  simp [boundaryLabelCount, boundaryDelta_ne_zero S]

theorem boundaryLabelCount_sum (S : BoundarySignature) :
    boundaryLabelCount S deltaA + boundaryLabelCount S deltaB +
        boundaryLabelCount S deltaC = S.arity := by
  have hpoint (i : Fin S.arity) :
      (if boundaryDelta S i = deltaA then 1 else 0) +
          (if boundaryDelta S i = deltaB then 1 else 0) +
            (if boundaryDelta S i = deltaC then 1 else 0) = 1 := by
    rcases boundaryDelta_eq_deltaA_or_deltaB_or_deltaC S i with hA | hB | hC
    · simp [hA, deltaA_ne_deltaB, deltaA_ne_deltaC]
    · simp [hB, deltaB_ne_deltaA, deltaB_ne_deltaC]
    · simp [hC, deltaC_ne_deltaA, deltaC_ne_deltaB]
  calc
    boundaryLabelCount S deltaA + boundaryLabelCount S deltaB +
        boundaryLabelCount S deltaC =
        (Finset.sum Finset.univ
          (fun i : Fin S.arity => if boundaryDelta S i = deltaA then 1 else 0)) +
          (Finset.sum Finset.univ
            (fun i : Fin S.arity => if boundaryDelta S i = deltaB then 1 else 0)) +
            Finset.sum Finset.univ
              (fun i : Fin S.arity => if boundaryDelta S i = deltaC then 1 else 0) := by
          simp [boundaryLabelCount_eq_sum_indicator]
    _ = Finset.sum Finset.univ (fun i : Fin S.arity =>
          (if boundaryDelta S i = deltaA then 1 else 0) +
            (if boundaryDelta S i = deltaB then 1 else 0) +
              (if boundaryDelta S i = deltaC then 1 else 0)) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    _ = Finset.sum Finset.univ (fun i : Fin S.arity => 1) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hpoint i
    _ = S.arity := by simp

set_option linter.unusedSimpArgs false in
theorem boundarySum_fst (S : BoundarySignature) :
    (boundarySum S).1 =
      (boundaryLabelCount S deltaA + boundaryLabelCount S deltaC : ZMod 2) := by
  change (Finset.sum Finset.univ
      (fun i : Fin S.arity => boundaryDelta S i)).1 = _
  rw [Prod.fst_sum]
  calc
    Finset.sum Finset.univ (fun i : Fin S.arity => (boundaryDelta S i).1) =
        Finset.sum Finset.univ (fun i : Fin S.arity =>
          (if boundaryDelta S i = deltaA then (1 : ZMod 2) else 0) +
            (if boundaryDelta S i = deltaC then (1 : ZMod 2) else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rcases boundaryDelta_eq_deltaA_or_deltaB_or_deltaC S i with hA | hB | hC
      · simp [hA, deltaA, deltaB, deltaC]
      · simp [hB, deltaA, deltaB, deltaC]
      · simp [hC, deltaA, deltaB, deltaC]
    _ = (Finset.sum Finset.univ
          (fun i : Fin S.arity =>
            if boundaryDelta S i = deltaA then (1 : ZMod 2) else 0)) +
          Finset.sum Finset.univ
            (fun i : Fin S.arity =>
              if boundaryDelta S i = deltaC then (1 : ZMod 2) else 0) := by
      rw [Finset.sum_add_distrib]
    _ = (boundaryLabelCount S deltaA + boundaryLabelCount S deltaC : ZMod 2) := by
      rw [← boundaryLabelCount_cast, ← boundaryLabelCount_cast]

set_option linter.unusedSimpArgs false in
theorem boundarySum_snd (S : BoundarySignature) :
    (boundarySum S).2 =
      (boundaryLabelCount S deltaB + boundaryLabelCount S deltaC : ZMod 2) := by
  change (Finset.sum Finset.univ
      (fun i : Fin S.arity => boundaryDelta S i)).2 = _
  rw [Prod.snd_sum]
  calc
    Finset.sum Finset.univ (fun i : Fin S.arity => (boundaryDelta S i).2) =
        Finset.sum Finset.univ (fun i : Fin S.arity =>
          (if boundaryDelta S i = deltaB then (1 : ZMod 2) else 0) +
            (if boundaryDelta S i = deltaC then (1 : ZMod 2) else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rcases boundaryDelta_eq_deltaA_or_deltaB_or_deltaC S i with hA | hB | hC
      · simp [hA, deltaA, deltaB, deltaC]
      · simp [hB, deltaA, deltaB, deltaC]
      · simp [hC, deltaA, deltaB, deltaC]
    _ = (Finset.sum Finset.univ
          (fun i : Fin S.arity =>
            if boundaryDelta S i = deltaB then (1 : ZMod 2) else 0)) +
          Finset.sum Finset.univ
            (fun i : Fin S.arity =>
              if boundaryDelta S i = deltaC then (1 : ZMod 2) else 0) := by
      rw [Finset.sum_add_distrib]
    _ = (boundaryLabelCount S deltaB + boundaryLabelCount S deltaC : ZMod 2) := by
      rw [← boundaryLabelCount_cast, ← boundaryLabelCount_cast]

theorem zmodTwo_natCast_add_eq_zero_iff_mod_eq (m n : Nat) :
    ((m + n : Nat) : ZMod 2) = 0 ↔ m % 2 = n % 2 := by
  rw [ZMod.natCast_eq_zero_iff_even, Nat.even_iff]
  omega

theorem boundaryConserved_iff_parity (S : BoundarySignature) :
    BoundaryConserved S ↔
      boundaryLabelCount S deltaA % 2 = boundaryLabelCount S deltaC % 2 ∧
        boundaryLabelCount S deltaB % 2 = boundaryLabelCount S deltaC % 2 := by
  constructor
  · intro h
    have hfst : (boundarySum S).1 = 0 := congrArg Prod.fst h
    have hsnd : (boundarySum S).2 = 0 := congrArg Prod.snd h
    rw [boundarySum_fst, ← Nat.cast_add] at hfst
    rw [boundarySum_snd, ← Nat.cast_add] at hsnd
    exact ⟨(zmodTwo_natCast_add_eq_zero_iff_mod_eq _ _).mp hfst,
      (zmodTwo_natCast_add_eq_zero_iff_mod_eq _ _).mp hsnd⟩
  · rintro ⟨hAC, hBC⟩
    apply Prod.ext
    · rw [boundarySum_fst, ← Nat.cast_add]
      exact (zmodTwo_natCast_add_eq_zero_iff_mod_eq _ _).mpr hAC
    · rw [boundarySum_snd, ← Nat.cast_add]
      exact (zmodTwo_natCast_add_eq_zero_iff_mod_eq _ _).mpr hBC

theorem boundaryConserved_even_or_odd (S : BoundarySignature)
    (hconserved : BoundaryConserved S) :
    (boundaryLabelCount S deltaA % 2 = 0 ∧
        boundaryLabelCount S deltaB % 2 = 0 ∧
          boundaryLabelCount S deltaC % 2 = 0) ∨
      (boundaryLabelCount S deltaA % 2 = 1 ∧
        boundaryLabelCount S deltaB % 2 = 1 ∧
          boundaryLabelCount S deltaC % 2 = 1) := by
  have hpar := (boundaryConserved_iff_parity S).mp hconserved
  rcases Nat.mod_two_eq_zero_or_one (boundaryLabelCount S deltaA) with hA | hA
  · left
    exact ⟨hA, by omega, by omega⟩
  · right
    exact ⟨hA, by omega, by omega⟩

def emptyBoundarySignature : BoundarySignature where
  arity := 0
  contact := fun i => Fin.elim0 i
  proper := by
    intro i
    exact Fin.elim0 i

theorem emptyBoundarySignature_conserved :
    BoundaryConserved emptyBoundarySignature := by
  unfold BoundaryConserved boundarySum
  change Finset.sum (Finset.univ : Finset (Fin 0))
      (fun i => contactDelta (Fin.elim0 i)) = 0
  rw [Finset.univ_eq_empty]
  rfl

end DkMath.Tromino
