/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.NumberTheory.Goldbach
import DkMath.Lib.Cosmic.GTailBoundary

/-!
# Quadratic primitive Goldbach fiber — research scratch

This file is an audit of normalization, not a universal escape provider.
Production owners retain the finite obstruction and capacity theorems.
All declarations below are scratch observations; the production facade does
not import this target. Reports QP-000 through QP-005 record their interpretation.
-/
namespace DkMathTest.GoldbachQuadraticPrimitiveAstra

open DkMath.NumberTheory DkMath.CosmicFormula
open scoped BigOperators

/-- QP-001: this is precisely Mathlib's bounded subtraction equivalence. -/
theorem coordinate_coprime {n u : ℕ} (hu : u ≤ n) :
    Nat.Coprime n u ↔ Nat.Coprime (n - u) u :=
  (Nat.coprime_sub_self_left hu).symm

/-- Right-coordinate transport does not need a subtraction bound. -/
theorem right_coordinate_coprime (n u : ℕ) :
    Nat.Coprime (n + u) u ↔ Nat.Coprime n u := Nat.coprime_add_self_left

/-- Canonical quadratic tail, with the natural subtraction bound explicit. -/
theorem quadratic_tail {n u : ℕ} (hu : u ≤ n) :
    GTail 2 1 (n - u) u = n + u := by
  rw [GTail_rec 2 1 (n - u) u (by omega)]
  simp only [Nat.choose_one_right, Nat.reduceSub, pow_one, GTail_self_eq_one, mul_one]
  omega

/-- The exact reflected gcd follows from the canonical boundary theorem. -/
theorem quadratic_boundary {n u : ℕ} (hu : u ≤ n) (hc : Nat.Coprime n u) :
    Nat.gcd (n - u) (n + u) = Nat.gcd (n - u) 2 := by
  rw [← quadratic_tail hu]
  exact gcd_GN_eq_gcd_of_one_le (by omega) ((coordinate_coprime hu).mp hc)

/-- Opposite coordinate parity is exactly oddness of either endpoint. -/
theorem parity_iff_odd_left {n u : ℕ} (hu : u ≤ n) :
    n % 2 ≠ u % 2 ↔ Odd (n - u) := by
  rw [Nat.odd_iff]
  omega

/-- Under primitivity, opposite parity is necessary and sufficient. -/
theorem endpoints_coprime_iff {n u : ℕ} (hu : u ≤ n) (hc : Nat.Coprime n u) :
    Nat.Coprime (n - u) (n + u) ↔ n % 2 ≠ u % 2 := by
  change Nat.gcd (n - u) (n + u) = 1 ↔ _
  rw [quadratic_boundary hu hc]
  change Nat.Coprime (n - u) 2 ↔ _
  rw [Nat.coprime_two_right, ← parity_iff_odd_left hu]

/-- Distinct reflected primes force primitive coordinates; positivity suffices
because primality itself supplies the natural subtraction bound. -/
theorem positive_pair_primitive {n u : ℕ} (hu : 0 < u)
    (hl : Nat.Prime (n - u)) (hr : Nat.Prime (n + u)) : Nat.Coprime n u := by
  have hb := hl.two_le
  have he : n - u ≠ n + u := by omega
  have hc := (Nat.coprime_primes hl hr).mpr he
  have hd₁ : Nat.gcd n u ∣ n - u := Nat.dvd_sub (Nat.gcd_dvd_left n u) (Nat.gcd_dvd_right n u)
  have hd₂ : Nat.gcd n u ∣ n + u := dvd_add (Nat.gcd_dvd_left n u) (Nat.gcd_dvd_right n u)
  have hd := Nat.dvd_gcd hd₁ hd₂
  rw [hc.gcd_eq_one] at hd
  exact Nat.dvd_one.mp hd

/-- Positive prime pairs are automatically odd on both ends. -/
theorem positive_pair_parity {n u : ℕ} (hu : 0 < u)
    (hl : Nat.Prime (n - u)) (hr : Nat.Prime (n + u)) : n % 2 ≠ u % 2 := by
  have hb := hl.two_le
  have hc := (Nat.coprime_primes hl hr).mpr (show n - u ≠ n + u by omega)
  exact (endpoints_coprime_iff (by omega) (positive_pair_primitive hu hl hr)).mp hc

/-- Diagonal survival is precisely center primality and is not primitive at n≥2. -/
theorem diagonal_pair (n : ℕ) :
    (Nat.Prime (n - 0) ∧ Nat.Prime (n + 0)) ↔ Nat.Prime n := by simp

/-- Keep the diagonal as a separate branch when normalizing the search. -/
theorem pair_of_center_prime {n : ℕ} (hn : Nat.Prime n) : GoldbachPairAt n :=
  ⟨n, n, hn, hn, by omega⟩

/-- Scratch candidate set, retaining the production admissible interval. -/
def primitiveOffsets (n : ℕ) : Finset ℕ :=
  (goldbachOffsets n).filter (Nat.Coprime n)

/-- Scratch positive primitive candidate set. -/
def primitivePositiveOffsets (n : ℕ) : Finset ℕ :=
  (primitiveOffsets n).filter (fun u => 0 < u)

/-- Scratch positive primitive fiber with opposite coordinate parity. -/
def primitiveParityOffsets (n : ℕ) : Finset ℕ :=
  (primitivePositiveOffsets n).filter (fun u => n % 2 ≠ u % 2)

@[simp] theorem mem_primitiveOffsets {n u : ℕ} :
    u ∈ primitiveOffsets n ↔ u ∈ goldbachOffsets n ∧ Nat.Coprime n u := by
  simp [primitiveOffsets]

@[simp] theorem mem_primitivePositiveOffsets {n u : ℕ} :
    u ∈ primitivePositiveOffsets n ↔
      u ∈ goldbachOffsets n ∧ Nat.Coprime n u ∧ 0 < u := by
  simp [primitivePositiveOffsets, and_assoc]

@[simp] theorem mem_primitiveParityOffsets {n u : ℕ} :
    u ∈ primitiveParityOffsets n ↔
      u ∈ goldbachOffsets n ∧ Nat.Coprime n u ∧ 0 < u ∧ n % 2 ≠ u % 2 := by
  simp [primitiveParityOffsets, and_assoc]

/-- Without parity, primitive coordinates can have gcd two. Smallest positive
admissible example (lexicographic n,u) is (3,1). -/
example : Nat.Coprime 3 1 ∧ Nat.gcd (3 - 1) (3 + 1) = 2 := by decide

/-- The subtraction bound cannot be dropped: (1,2) is primitive/opposite parity. -/
example : Nat.Coprime 1 2 ∧ 1 % 2 ≠ 2 % 2 ∧
    Nat.gcd (1 - 2) (1 + 2) ≠ Nat.gcd (1 - 2) 2 := by decide

/-- Small centers and the lost diagonal. -/
example : primitiveParityOffsets 0 = ∅ ∧ primitiveParityOffsets 1 = ∅ ∧
    primitiveParityOffsets 2 = ∅ ∧ GoldbachPairAt 2 ∧ ¬ Nat.Coprime 2 0 := by
  refine ⟨by decide, by decide, by decide, pair_of_center_prime (by decide), by decide⟩

/-- Bounded zero-offset primitive endpoint edge. -/
example : Nat.Coprime 1 0 ∧ Nat.gcd (1 - 0) (1 + 0) = 1 ∧
    ¬ Nat.Coprime 0 0 := by decide

end DkMathTest.GoldbachQuadraticPrimitiveAstra
