/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTail
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

#print "file: DkMath.Lib.Cosmic.CyclicDeterminant"

/-!
# Full cyclic determinant carrier

The pencil acts on `n + 1` coordinates, so every natural parameter represents
a positive cycle length. Its shift is the standard `finRotate` row permutation.
The full determinant is a power difference, and its cosmic specialization is
the gap times GN. No field norm or division is introduced.
-/

namespace DkMath.CosmicFormula

open Matrix

/-- The cyclic successor shift on `n + 1` coordinates, including length one. -/
def cyclicShift {R : Type*} [CommRing R] (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun i j => if j.val = i.val + 1 ∨ (i.val = n ∧ j.val = 0) then 1 else 0

/-- The full cyclic pencil `z I - u S`, of positive length `n + 1`. -/
def cyclicPencil {R : Type*} [CommRing R] (n : ℕ) (z u : R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun i j => (if i = j then z else 0) - u * cyclicShift n i j

/-- The entry description agrees with the existing standard cyclic rotation. -/
theorem cyclicShift_apply {R : Type*} [CommRing R] (n : ℕ)
    (i j : Fin (n + 1)) :
    cyclicShift (R := R) n i j = if finRotate (n + 1) i = j then 1 else 0 := by
  have h : (j.val = i.val + 1 ∨ (i.val = n ∧ j.val = 0)) ↔
      finRotate (n + 1) i = j := by
    by_cases hi : i.val < n
    · have he : i = ⟨i.val, i.isLt⟩ := rfl
      rw [he, finRotate_of_lt hi]
      simp only [Fin.ext_iff]
      omega
    · have he : i = Fin.last n := by
        apply Fin.ext
        change i.val = n
        omega
      rw [he, finRotate_last]
      simp only [Fin.ext_iff, Fin.val_zero]
      change (j.val = n + 1 ∨ (n = n ∧ j.val = 0)) ↔ 0 = j.val
      omega
  simp only [cyclicShift, h]

/-- The shift reuses Mathlib's permutation-matrix carrier for `finRotate`. -/
theorem cyclicShift_eq_permMatrix {R : Type*} [CommRing R] (n : ℕ) :
    cyclicShift (R := R) n = (finRotate (n + 1)).permMatrix R := by
  ext i j
  rw [cyclicShift_apply]
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, eq_comm]

/-- The entrywise pencil is literally the scalar identity minus the scalar shift. -/
theorem cyclicPencil_eq_scalar_sub_shift {R : Type*} [CommRing R]
    (n : ℕ) (z u : R) :
    cyclicPencil n z u = z • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) -
      u • cyclicShift n := by
  ext i j
  simp only [cyclicPencil, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply]
  split_ifs <;> simp

private theorem first_minor_det {R : Type*} [CommRing R] (n : ℕ) (z u : R) :
    ((cyclicPencil (n + 1) z u).submatrix Fin.succ Fin.succ).det = z ^ (n + 1) := by
  have ht : ((cyclicPencil (n + 1) z u).submatrix Fin.succ Fin.succ).IsUpperTriangular := by
    intro i j hij
    have hv : j.val < i.val := hij
    simp only [submatrix_apply, cyclicPencil, cyclicShift, Fin.val_succ]
    have hne : i.succ ≠ j.succ := by
      intro h
      have hh := congrArg Fin.val h
      simp only [Fin.val_succ] at hh
      omega
    rw [ite_eq_right hne]
    have hs : ¬ (j.val + 1 = i.val + 1 + 1 ∨ (i.val + 1 = n + 1 ∧ j.val + 1 = 0)) := by omega
    rw [ite_eq_right hs]
    simp
  rw [det_of_isUpperTriangular ht]
  have hd : ∀ i : Fin (n + 1),
      (cyclicPencil (n + 1) z u).submatrix Fin.succ Fin.succ i i = z := by
    intro i
    simp [submatrix_apply, cyclicPencil, cyclicShift]
  simp only [hd, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem last_minor_det {R : Type*} [CommRing R] (n : ℕ) (z u : R) :
    ((cyclicPencil (n + 1) z u).submatrix Fin.castSucc Fin.succ).det = (-u) ^ (n + 1) := by
  have ht : ((cyclicPencil (n + 1) z u).submatrix Fin.castSucc Fin.succ).IsLowerTriangular := by
    intro i j hij
    have hv : i.val < j.val := hij
    simp only [submatrix_apply, cyclicPencil, cyclicShift, Fin.val_succ, Fin.val_castSucc]
    have hne : i.castSucc ≠ j.succ := by
      intro h
      have hh := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_castSucc] at hh
      omega
    rw [ite_eq_right hne]
    have hs : ¬ (j.val + 1 = i.val + 1 ∨ (i.val = n + 1 ∧ j.val + 1 = 0)) := by omega
    rw [ite_eq_right hs]
    simp
  rw [det_of_isLowerTriangular _ ht]
  have hd : ∀ i : Fin (n + 1),
      (cyclicPencil (n + 1) z u).submatrix Fin.castSucc Fin.succ i i = -u := by
    intro i
    have hne : i.castSucc ≠ i.succ := by
      intro h
      have hh := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_castSucc] at hh
      omega
    simp [submatrix_apply, cyclicPencil, cyclicShift, hne]
  simp only [hd, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The full power-difference determinant of an arbitrary positive cyclic pencil. -/
theorem det_cyclicPencil {R : Type*} [CommRing R] (n : ℕ) (z u : R) :
    (cyclicPencil n z u).det = z ^ (n + 1) - u ^ (n + 1) := by
  cases n with
  | zero => simp [cyclicPencil, cyclicShift]
  | succ n =>
    rw [det_succ_column_zero]
    have hsum :
        (∑ i : Fin (n + 2), (-1 : R) ^ i.val * cyclicPencil (n + 1) z u i 0 *
          ((cyclicPencil (n + 1) z u).submatrix i.succAbove Fin.succ).det) =
        z * z ^ (n + 1) + (-1 : R) ^ (n + 1) * (-u) * (-u) ^ (n + 1) := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
      have hzero : cyclicPencil (n + 1) z u 0 0 = z := by
        simp [cyclicPencil, cyclicShift]
      rw [hzero, first_minor_det]
      congr 1
      rw [Finset.sum_eq_single (Fin.last n)]
      · simp [cyclicPencil, cyclicShift, Fin.succ_last, last_minor_det]
      · intro i _ hi
        have hv : i.val < n := Fin.val_lt_last hi
        have hentry : cyclicPencil (n + 1) z u i.succ 0 = 0 := by
          simp only [cyclicPencil, cyclicShift, Fin.val_succ, Fin.val_zero]
          have hne : i.succ ≠ 0 := Fin.succ_ne_zero i
          rw [ite_eq_right hne]
          have hs : ¬ (0 = i.val + 1 + 1 ∨ (i.val + 1 = n + 1 ∧ True)) := by omega
          rw [ite_eq_right hs]
          simp
        rw [hentry, mul_zero, zero_mul]
      · simp
    rw [hsum]
    rw [neg_pow u]
    have hs : (-1 : R) ^ (n + 1) * (-1) ^ (n + 1) = 1 := by
      rw [← mul_pow]
      simp
    calc
      z * z ^ (n + 1) + (-1) ^ (n + 1) * (-u) *
          ((-1) ^ (n + 1) * u ^ (n + 1)) =
          z * z ^ (n + 1) -
            ((-1 : R) ^ (n + 1) * (-1) ^ (n + 1)) * (u * u ^ (n + 1)) := by ring
      _ = _ := by rw [hs, one_mul]; simp only [pow_succ']

/-- Standard scalar-matrix formulation of the cyclic determinant identity. -/
theorem det_scalar_sub_cyclicShift {R : Type*} [CommRing R]
    (n : ℕ) (z u : R) :
    (z • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - u • cyclicShift n).det =
      z ^ (n + 1) - u ^ (n + 1) := by
  rw [← cyclicPencil_eq_scalar_sub_shift, det_cyclicPencil]

/-- The cyclic determinant recovers the entire Cosmic Formula body, not just GN. -/
theorem det_cyclicPencil_eq_mul_GN {R : Type*} [CommRing R]
    (n : ℕ) (g u : R) :
    (cyclicPencil n (g + u) u).det = g * GTail (n + 1) 1 g u := by
  rw [det_cyclicPencil, add_pow_eq_mul_GTail_one_add_gap]
  exact add_sub_cancel_right _ _

end DkMath.CosmicFormula
