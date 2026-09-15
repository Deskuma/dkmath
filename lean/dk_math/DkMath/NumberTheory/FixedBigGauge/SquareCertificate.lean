/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/
import DkMath.NumberTheory.FixedBigGauge.Basic

/-! # Exact prime certification in the square shell

This is a pointwise criterion. It does not supply an escaping point or pair.
-/

namespace DkMath.NumberTheory.FixedBigGauge

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic

theorem prime_iff_supportDisjointFrom_in_squareShell {P m : ℕ}
    (hm : P < m) (hupper : m ≤ squareBody P) :
    Nat.Prime m ↔ SupportDisjointFrom (primeScalesUpTo P) m := by
  constructor
  · intro hp q hq hqd hmem
    have hqP := (mem_primeScalesUpTo.mp hmem).2
    have hqm := ((Nat.dvd_prime hp).mp hqd).resolve_left hq.ne_one
    omega
  · intro hdisj
    have hP : 0 < P := by
      by_contra h
      have : P = 0 := by omega
      simp [this, squareBody] at hupper
      omega
    exact prime_of_supportDisjointFrom_primeScalesUpTo_le_squareBody
      (by omega) hupper hdisj

theorem prime_iff_coprime_in_squareShell {P m : ℕ}
    (hm : P < m) (hupper : m ≤ squareBody P) :
    Nat.Prime m ↔ Nat.Coprime m (primeWorldModulus (primeScalesUpTo P)) := by
  rw [prime_iff_supportDisjointFrom_in_squareShell hm hupper,
    supportDisjointFrom_iff_coprime_primeWorldModulus (knownPrimeScales_primeScalesUpTo P)]

/-- Positive scaling transports the interval exactly and adds no seats. -/
theorem scaled_le_iff {a b s : ℝ} (hs : 0 < s) : a * s ≤ b * s ↔ a ≤ b :=
  mul_le_mul_iff_left₀ hs

/-- The area observer transports the already certified prime label. -/
theorem prime_iff_coprime_of_physical_squareShell {R : ℝ} (hR : 0 < R)
    {P m : ℕ} (hm : P < m)
    (hupper : (m : ℝ) * fixedBigUnit R (P + 1) ^ 2 ≤
      R ^ 2 - fixedBigUnit R (P + 1) ^ 2) :
    Nat.Prime m ↔ Nat.Coprime m (primeWorldModulus (primeScalesUpTo P)) := by
  have hu : 0 < fixedBigUnit R (P + 1) := fixedBigUnit_pos hR (by omega)
  have hs : 0 < fixedBigUnit R (P + 1) ^ 2 := sq_pos_of_pos hu
  have heq := fixedBig_squareBody_normalization hR.ne' P
  have hmR : (m : ℝ) ≤ (squareBody P : ℝ) := by
    rw [← heq]
    exact (le_div_iff₀ hs).mpr hupper
  exact prime_iff_coprime_in_squareShell hm (by exact_mod_cast hmR)

end DkMath.NumberTheory.FixedBigGauge
