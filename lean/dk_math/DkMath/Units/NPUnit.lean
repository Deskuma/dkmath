/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

namespace DkMath

/-!
# NP unit (front/back phase) numbers

- Front (N): integer lattice points
- Back  (P): half-lattice points

We model a number as (n : ℤ) plus a phase bit (p : Bool):
  p = false  ↔  front (N)
  p = true   ↔  back  (P)

`succ` toggles the phase; if it wraps from P→N then it increments n.
Two `succ` steps equal "+1" while preserving the phase.
-/

/-- NP number: integer coordinate + phase bit (front/back). -/
structure NP where
  n : ℤ
  p : Bool
deriving DecidableEq, Repr

/-- Front point N_n. -/
def N (n : ℤ) : NP := ⟨n, false⟩

/-- Back point P_n (represents n + 1/2). -/
def P (n : ℤ) : NP := ⟨n, true⟩

/-- Origin is the front point N_0. -/
def zero : NP := N 0

/-- Half-step is the back point P_0. -/
def half : NP := P 0

/-- Successor: N_n → P_n,  P_n → N_{n+1}. -/
def succ : NP → NP
  | ⟨n, false⟩ => ⟨n, true⟩
  | ⟨n, true⟩  => ⟨n + 1, false⟩

/-- Concrete value embedding into ℚ: val(n,p) = n + p/2. -/
def val (x : NP) : ℚ :=
  (x.n : ℚ) + (if x.p then (1/2 : ℚ) else 0)

@[simp] lemma N_n (n : ℤ) : (N n).n = n := rfl
@[simp] lemma N_p (n : ℤ) : (N n).p = false := rfl
@[simp] lemma P_n (n : ℤ) : (P n).n = n := rfl
@[simp] lemma P_p (n : ℤ) : (P n).p = true := rfl

@[simp] lemma succ_N (n : ℤ) : succ (N n) = P n := rfl
@[simp] lemma succ_P (n : ℤ) : succ (P n) = N (n+1) := rfl

@[simp] lemma val_N (n : ℤ) : val (N n) = (n : ℚ) := by
  simp [val, N]

@[simp] lemma val_P (n : ℤ) : val (P n) = (n : ℚ) + (1/2 : ℚ) := by
  simp [val, P]

@[simp] lemma val_zero : val zero = 0 := by
  simp [zero]

@[simp] lemma val_half : val half = (1/2 : ℚ) := by
  simp [half]

/-- `succ` always adds a half-step in ℚ. -/
lemma val_succ (x : NP) : val (succ x) = val x + (1/2 : ℚ) := by
  cases x with
  | mk n p =>
    cases p
    · simp [succ, val]
    · simp [succ, val]; ring

/-- Two successors equal "+1" and preserve phase: succ²(n,p) = (n+1,p). -/
lemma succ_succ (x : NP) : succ (succ x) = ⟨x.n + 1, x.p⟩ := by
  cases x with
  | mk n p =>
    cases p <;> rfl

/-- In particular, on the front lattice: succ²(N_n) = N_{n+1}. -/
lemma succ_succ_N (n : ℤ) : succ (succ (N n)) = N (n+1) := by
  simpa [N] using (succ_succ (x := N n))

end DkMath
