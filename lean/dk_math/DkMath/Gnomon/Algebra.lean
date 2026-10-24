/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.SquareCompletion
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

#print "file: DkMath.Gnomon.Algebra"

/-!
# Neutral square-gnomon arithmetic

The general square-completion and finite-band arithmetic is owned by
`DkMath.Lib.Algebra.SquareCompletion` (GN-LIB-003b).
This module keeps the natural-number definitions and compatibility adapters for the
odd gnomon and its finite square-growth bands.  The parameter `u` in
`squareGnomonBand x u` is a side-thickness, not an area increment.  The unit
case `u = 1` is the atomic lattice growth step, whose induced area increment
is `oddGnomon x = 2 * x + 1`.

The module deliberately does not import Collatz, Legendre, Cosmic Formula,
GN, Pascal, Polyomino, FLT, or ABC layers.
-/

namespace DkMath.Gnomon

open scoped BigOperators

/-- The odd gnomon layer at `n`, namely the area added by one square step. -/
def oddGnomon (n : ℕ) : ℕ :=
  2 * n + 1

/-- Area added when a square of side `x` grows by side-thickness `u`. -/
def squareGnomonBand (x u : ℕ) : ℕ :=
  u * (2 * x + u)

/-- Multiplication transported to odd-gnomon addresses. -/
def petalMul (a b : ℕ) : ℕ :=
  2 * a * b + a + b

@[simp] theorem oddGnomon_zero : oddGnomon 0 = 1 := by
  simp [oddGnomon]

theorem oddGnomon_succ (n : ℕ) :
    oddGnomon (n + 1) = oddGnomon n + 2 := by
  simp only [oddGnomon]
  ring

theorem oddGnomon_pos (n : ℕ) :
    0 < oddGnomon n := by
  simp [oddGnomon]

theorem oddGnomon_odd (n : ℕ) :
    Odd (oddGnomon n) := by
  exact ⟨n, by simp [oddGnomon, Nat.mul_comm]⟩

theorem oddGnomon_injective :
    Function.Injective oddGnomon := by
  intro a b h
  dsimp [oddGnomon] at h
  omega

theorem oddGnomon_eq_one_iff (n : ℕ) :
    oddGnomon n = 1 ↔ n = 0 := by
  constructor
  · intro h
    dsimp [oddGnomon] at h
    omega
  · intro h
    subst h
    simp

@[simp] theorem petalMul_zero_left (a : ℕ) :
    petalMul 0 a = a := by
  simp [petalMul]

@[simp] theorem petalMul_zero_right (a : ℕ) :
    petalMul a 0 = a := by
  simp [petalMul]

theorem petalMul_comm (a b : ℕ) :
    petalMul a b = petalMul b a := by
  simp only [petalMul]
  ring

theorem petalMul_assoc (a b c : ℕ) :
    petalMul (petalMul a b) c = petalMul a (petalMul b c) := by
  simp only [petalMul]
  ring

theorem oddGnomon_petalMul (a b : ℕ) :
    oddGnomon (petalMul a b) = oddGnomon a * oddGnomon b := by
  simp only [oddGnomon, petalMul]
  ring

/--
[DkMath.Lib] 昇格済み: `DkMath.Lib.Algebra.square_add_unit_layer`。
この旧APIは従来のNat carrier・全修飾名・型を保持し、Libの一般半環の式を特殊化する。
新しい一般consumerは `DkMath.Lib.Algebra.SquareCompletion` を直接importできる。
-/
theorem square_add_oddGnomon (x : ℕ) :
    x ^ 2 + oddGnomon x = (x + 1) ^ 2 := by
  simpa only [oddGnomon] using DkMath.Lib.Algebra.square_add_unit_layer x

/--
[DkMath.Lib] 昇格済み: `DkMath.Lib.Algebra.square_add_band`。
この旧APIは従来のNat carrier・全修飾名・型を保持し、Libの一般半環の式を特殊化する。
新しい一般consumerは `DkMath.Lib.Algebra.SquareCompletion` を直接importできる。
-/
theorem square_add_squareGnomonBand (x u : ℕ) :
    x ^ 2 + squareGnomonBand x u = (x + u) ^ 2 := by
  simpa only [squareGnomonBand] using DkMath.Lib.Algebra.square_add_band x u

@[simp] theorem squareGnomonBand_zero (x : ℕ) :
    squareGnomonBand x 0 = 0 := by
  simp [squareGnomonBand]

@[simp] theorem squareGnomonBand_unit (x : ℕ) :
    squareGnomonBand x 1 = oddGnomon x := by
  simp [squareGnomonBand, oddGnomon]

@[simp] theorem squareGnomonBand_zero_anchor (u : ℕ) :
    squareGnomonBand 0 u = u ^ 2 := by
  simp [squareGnomonBand, pow_two]

/--
[DkMath.Lib] 昇格済み: `DkMath.Lib.Algebra.band_add_thickness`。
この旧APIは従来のNat carrier・全修飾名・型を保持し、Libの一般半環の式を特殊化する。
新しい一般consumerは `DkMath.Lib.Algebra.SquareCompletion` を直接importできる。
-/
theorem squareGnomonBand_add (x u v : ℕ) :
    squareGnomonBand x (u + v) =
      squareGnomonBand x u + squareGnomonBand (x + u) v := by
  simpa only [squareGnomonBand] using DkMath.Lib.Algebra.band_add_thickness x u v

/--
[DkMath.Lib] 昇格済み: `DkMath.Lib.Algebra.band_eq_sum_unit_layers`。
この旧APIは従来のNat carrier・全修飾名・型を保持し、Libの一般半環の式を特殊化する。
新しい一般consumerは `DkMath.Lib.Algebra.SquareCompletion` を直接importできる。
-/
theorem squareGnomonBand_eq_sum_shifted_oddGnomon
    (x u : ℕ) :
    squareGnomonBand x u =
      (Finset.range u).sum (fun i => oddGnomon (x + i)) := by
  simpa only [squareGnomonBand, oddGnomon, Nat.cast_id] using
    (DkMath.Lib.Algebra.band_eq_sum_unit_layers (R := ℕ) x u)

/--
[DkMath.Lib] 昇格済み: `DkMath.Lib.Algebra.sum_unit_layers_eq_square`。
この旧APIは従来のNat carrier・全修飾名・型を保持し、Libの一般半環の式を特殊化する。
新しい一般consumerは `DkMath.Lib.Algebra.SquareCompletion` を直接importできる。
-/
theorem sum_oddGnomon_eq_square (n : ℕ) :
    (Finset.range n).sum oddGnomon = n ^ 2 := by
  change (Finset.range n).sum (fun i => 2 * i + 1) = n ^ 2
  simpa only [Nat.cast_id] using
    (DkMath.Lib.Algebra.sum_unit_layers_eq_square (R := ℕ) n)

/--
[DkMath.Lib] 昇格済み: `DkMath.Lib.Algebra.sum_unit_layers_eq_square`。
この旧APIは従来のNat carrier・全修飾名・型を保持し、Libの一般半環の式を特殊化する。
新しい一般consumerは `DkMath.Lib.Algebra.SquareCompletion` を直接importできる。
-/
theorem sum_odd_eq_square (n : ℕ) :
    (Finset.range n).sum (fun i => 2 * i + 1) = n ^ 2 := by
  simpa only [Nat.cast_id] using
    (DkMath.Lib.Algebra.sum_unit_layers_eq_square (R := ℕ) n)

example : oddGnomon 0 = 1 := by norm_num [oddGnomon]

example : oddGnomon 1 = 3 := by norm_num [oddGnomon]

example : oddGnomon 2 = 5 := by norm_num [oddGnomon]

example : oddGnomon 30 = 61 := by norm_num [oddGnomon]

example : oddGnomon 31 = 63 := by norm_num [oddGnomon]

example : squareGnomonBand 30 1 = 61 := by
  norm_num [squareGnomonBand]

example : squareGnomonBand 30 2 = 124 := by
  norm_num [squareGnomonBand]

example : squareGnomonBand 30 2 = 61 + 63 := by
  norm_num [squareGnomonBand]

end DkMath.Gnomon
