/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Basic

#print "file: DkMath.NumberTheory.TraceOneQuadratic"

namespace DkMath.NumberTheory.TraceOneQuadratic

/-- Integral coordinates `a + b * tau`, reduced by `tau^2 = tau + s`. -/
structure TraceOneInt (s : ℤ) where
  fst : ℤ
  snd : ℤ
deriving DecidableEq, Repr

@[ext] theorem traceOne_ext {x y : TraceOneInt s}
    (hfst : x.fst = y.fst) (hsnd : x.snd = y.snd) : x = y := by
  cases x
  cases y
  simp_all

def ofInt (s a : ℤ) : TraceOneInt s := ⟨a, 0⟩
def tau (s : ℤ) : TraceOneInt s := ⟨0, 1⟩

def mul (x y : TraceOneInt s) : TraceOneInt s :=
  ⟨x.fst * y.fst + s * x.snd * y.snd,
    x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩

def conj (x : TraceOneInt s) : TraceOneInt s :=
  ⟨x.fst + x.snd, -x.snd⟩

def trace (x : TraceOneInt s) : ℤ := 2 * x.fst + x.snd
def norm (x : TraceOneInt s) : ℤ := x.fst ^ 2 + x.fst * x.snd - s * x.snd ^ 2
def discr (s : ℤ) : ℤ := 1 + 4 * s

instance : Zero (TraceOneInt s) := ⟨⟨0, 0⟩⟩
instance : One (TraceOneInt s) := ⟨⟨1, 0⟩⟩
instance : Add (TraceOneInt s) := ⟨fun x y => ⟨x.fst + y.fst, x.snd + y.snd⟩⟩
instance : Neg (TraceOneInt s) := ⟨fun x => ⟨-x.fst, -x.snd⟩⟩
instance : Sub (TraceOneInt s) := ⟨fun x y => ⟨x.fst - y.fst, x.snd - y.snd⟩⟩
instance : Mul (TraceOneInt s) := ⟨mul⟩

@[simp] theorem fst_zero : (0 : TraceOneInt s).fst = 0 := rfl
@[simp] theorem snd_zero : (0 : TraceOneInt s).snd = 0 := rfl
@[simp] theorem fst_one : (1 : TraceOneInt s).fst = 1 := rfl
@[simp] theorem snd_one : (1 : TraceOneInt s).snd = 0 := rfl
@[simp] theorem fst_add (x y : TraceOneInt s) : (x + y).fst = x.fst + y.fst := rfl
@[simp] theorem snd_add (x y : TraceOneInt s) : (x + y).snd = x.snd + y.snd := rfl
@[simp] theorem fst_neg (x : TraceOneInt s) : (-x).fst = -x.fst := rfl
@[simp] theorem snd_neg (x : TraceOneInt s) : (-x).snd = -x.snd := rfl
@[simp] theorem fst_sub (x y : TraceOneInt s) : (x - y).fst = x.fst - y.fst := rfl
@[simp] theorem snd_sub (x y : TraceOneInt s) : (x - y).snd = x.snd - y.snd := rfl
@[simp] theorem fst_mul (x y : TraceOneInt s) :
    (x * y).fst = x.fst * y.fst + s * x.snd * y.snd := rfl
@[simp] theorem snd_mul (x y : TraceOneInt s) :
    (x * y).snd = x.fst * y.snd + x.snd * y.fst + x.snd * y.snd := rfl

instance traceOneAddCommGroup : AddCommGroup (TraceOneInt s) := by
  refine
    { sub := fun x y => ⟨x.fst - y.fst, x.snd - y.snd⟩
      nsmul := @nsmulRec (TraceOneInt s) inferInstance inferInstance
      zsmul := @zsmulRec (TraceOneInt s) inferInstance inferInstance inferInstance
        (@nsmulRec (TraceOneInt s) inferInstance inferInstance)
      add_assoc := ?_
      zero_add := ?_
      add_zero := ?_
      neg_add_cancel := ?_
      add_comm := ?_ } <;>
    intros <;> ext <;> simp [add_comm, add_left_comm]

instance traceOneAddGroupWithOne : AddGroupWithOne (TraceOneInt s) :=
  { traceOneAddCommGroup with
    natCast := fun n => ⟨n, 0⟩
    intCast := fun z => ⟨z, 0⟩ }

instance traceOneCommRing : CommRing (TraceOneInt s) := by
  refine
    { traceOneAddGroupWithOne with
      add_comm := ?_
      mul_assoc := ?_
      one_mul := ?_
      mul_one := ?_
      left_distrib := ?_
      right_distrib := ?_
      zero_mul := ?_
      mul_zero := ?_
      mul_comm := ?_ } <;>
    intros <;> ext <;> simp <;> ring

@[simp] theorem traceOne_tau_sq : tau s * tau s = tau s + ofInt s s := by
  ext <;> simp [tau, ofInt]

@[simp] theorem traceOne_conj_invol (x : TraceOneInt s) : conj (conj x) = x := by
  ext <;> simp [conj]

theorem traceOne_conj_mul (x y : TraceOneInt s) : conj (x * y) = conj x * conj y := by
  ext <;> simp [conj] <;> ring

theorem traceOne_mul_conj (x : TraceOneInt s) : x * conj x = ofInt s (norm x) := by
  ext <;> simp [conj, ofInt, norm] <;> ring

theorem traceOne_norm_mul (x y : TraceOneInt s) : norm (x * y) = norm x * norm y := by
  simp [norm]
  ring

theorem four_mul_traceOneNorm_eq_discriminant (x : TraceOneInt s) :
    4 * norm x = trace x ^ 2 - discr s * x.snd ^ 2 := by
  simp [norm, trace, discr]
  ring

theorem traceOneNorm_neg_one (a b : ℤ) :
    norm (⟨a, b⟩ : TraceOneInt (-1)) = a ^ 2 + a * b + b ^ 2 := by
  simp [norm]

theorem traceOneNorm_one (a b : ℤ) :
    norm (⟨a, b⟩ : TraceOneInt 1) = a ^ 2 + a * b - b ^ 2 := by
  simp [norm]

/-! ## The positive-definite `s = -2` specialization -/

/-- The central quadratic scale axis at discriminant `-7`.  Its norm is `7`,
so this is deliberately not described as a ring unit. -/
def sevenAxis : TraceOneInt (-2) :=
  2 * tau (-2) - 1

theorem sevenAxis_eq : sevenAxis = ⟨-1, 2⟩ := by
  rfl

@[simp] theorem sevenAxis_fst : sevenAxis.fst = -1 := by
  rw [sevenAxis_eq]

@[simp] theorem sevenAxis_snd : sevenAxis.snd = 2 := by
  rw [sevenAxis_eq]

/-- The scale axis squares to the embedded integer `-7`. -/
theorem sevenAxis_sq : sevenAxis ^ 2 = (-7 : TraceOneInt (-2)) := by
  rw [sevenAxis_eq]
  change (⟨-1, 2⟩ : TraceOneInt (-2)) ^ 2 = ⟨-7, 0⟩
  ext <;> norm_num [pow_two]

/-- Conjugation reverses the scale axis. -/
theorem conj_sevenAxis : conj sevenAxis = -sevenAxis := by
  rw [sevenAxis_eq]
  ext <;> norm_num [conj]

/-- The scale axis has norm `7`, rather than unit norm. -/
theorem sevenAxis_norm : norm sevenAxis = 7 := by
  rw [sevenAxis_eq]
  norm_num [norm]

/-- Coordinate formula for the `s = -2` trace-one norm. -/
theorem traceOneNorm_neg_two (a b : ℤ) :
    norm (⟨a, b⟩ : TraceOneInt (-2)) = a ^ 2 + a * b + 2 * b ^ 2 := by
  simp [norm]

/-- Completed-square form of the discriminant `-7` norm. -/
theorem four_mul_traceOneNorm_negTwo_eq_sum_sq (a b : ℤ) :
    4 * norm (⟨a, b⟩ : TraceOneInt (-2)) =
      (2 * a + b) ^ 2 + 7 * b ^ 2 := by
  rw [traceOneNorm_neg_two]
  ring

/-- The positive-definite `s = -2` norm vanishes only at zero coordinates. -/
theorem traceOneNorm_negTwo_eq_zero_iff (a b : ℤ) :
    norm (⟨a, b⟩ : TraceOneInt (-2)) = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hs := four_mul_traceOneNorm_negTwo_eq_sum_sq a b
    have hb_sq : b ^ 2 = 0 := by
      nlinarith [sq_nonneg (2 * a + b), sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg b]
    subst b
    have ha : a = 0 := by
      rw [traceOneNorm_neg_two] at h
      nlinarith [sq_nonneg a]
    exact ⟨ha, rfl⟩
  · rintro ⟨rfl, rfl⟩
    norm_num [norm]

/-- Structured zero-fiber form for the `s = -2` norm. -/
theorem norm_eq_zero_iff_of_negTwo (x : TraceOneInt (-2)) :
    norm x = 0 ↔ x = 0 := by
  rcases x with ⟨a, b⟩
  rw [traceOneNorm_negTwo_eq_zero_iff]
  constructor
  · rintro ⟨rfl, rfl⟩
    rfl
  · intro h
    have hf := congrArg TraceOneInt.fst h
    have hs := congrArg TraceOneInt.snd h
    simpa using And.intro hf hs

/-- Every nonzero integral `s = -2` core has norm at least one. -/
theorem one_le_traceOneNorm_negTwo_of_ne_zero
    (x : TraceOneInt (-2)) (hx : x ≠ 0) :
    1 ≤ norm x := by
  rcases x with ⟨a, b⟩
  have hs := four_mul_traceOneNorm_negTwo_eq_sum_sq a b
  have hnonneg : 0 ≤ norm (⟨a, b⟩ : TraceOneInt (-2)) := by
    nlinarith [sq_nonneg (2 * a + b), sq_nonneg b]
  have hne : norm (⟨a, b⟩ : TraceOneInt (-2)) ≠ 0 := by
    intro h
    apply hx
    exact (norm_eq_zero_iff_of_negTwo ⟨a, b⟩).mp h
  omega

/-- The norm-one shell consists exactly of the two embedded signs. -/
theorem traceOneNorm_negTwo_eq_one_iff (a b : ℤ) :
    norm (⟨a, b⟩ : TraceOneInt (-2)) = 1 ↔
      (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) := by
  constructor
  · intro h
    have hs := four_mul_traceOneNorm_negTwo_eq_sum_sq a b
    have hb_lt : b ^ 2 < 1 := by
      nlinarith [sq_nonneg (2 * a + b)]
    have hb_sq : b ^ 2 = 0 := by
      have := sq_nonneg b
      omega
    have hb : b = 0 := by nlinarith [sq_nonneg b]
    subst b
    rw [traceOneNorm_neg_two] at h
    have hfactor : (a - 1) * (a + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfactor with ha | ha
    · left
      constructor <;> omega
    · right
      constructor <;> omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num [norm]

/-- Structured norm-one classification. -/
theorem norm_eq_one_iff_of_negTwo (x : TraceOneInt (-2)) :
    norm x = 1 ↔ x = 1 ∨ x = -1 := by
  rcases x with ⟨a, b⟩
  rw [traceOneNorm_negTwo_eq_one_iff]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (h | h)
    · left
      exact ⟨congrArg TraceOneInt.fst h, congrArg TraceOneInt.snd h⟩
    · right
      exact ⟨congrArg TraceOneInt.fst h, congrArg TraceOneInt.snd h⟩

end DkMath.NumberTheory.TraceOneQuadratic
