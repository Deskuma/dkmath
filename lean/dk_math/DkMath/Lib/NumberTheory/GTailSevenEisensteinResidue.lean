/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.GTailSevenNormReadout
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

#print "file: DkMath.Lib.NumberTheory.GTailSevenEisensteinResidue"

/-!
# Oriented Eisenstein residue slots

These neutral evaluations distinguish conjugate roots away from characteristic
three. They do not construct prime ideals or reconstruct elements from norms.
-/

namespace DkMath.Lib.NumberTheory

open DkMath.NumberTheory.TraceOneQuadratic

/-- The existing element-level conjugation identity at the chosen coordinate. -/
theorem gtailSevenNormCoord_mul_conj (a b : ℕ) :
    gtailSevenNormCoord a b * conj (gtailSevenNormCoord a b) =
      ofInt (-1) (((a ^ 2 + a * b + b ^ 2 : ℕ) : ℤ)) := by
  rw [traceOne_mul_conj, norm_gtailSevenNormCoord]

/-- Conjugation retains the signed integral coordinates. -/
theorem conj_gtailSevenNormCoord (a b : ℕ) :
    conj (gtailSevenNormCoord a b) =
      (⟨((a + b : ℕ) : ℤ), -(b : ℤ)⟩ : TraceOneInt (-1)) := by
  rw [gtailSevenNormCoord_eq]
  simp [conj]

/-- Scalar ring divisibility requires both lattice coordinates, not just the norm. -/
theorem scalar_dvd_gtailSevenNormCoord_iff (q a b : ℕ) :
    ofInt (-1) (q : ℤ) ∣ gtailSevenNormCoord a b ↔ q ∣ a ∧ q ∣ b := by
  rw [gtailSevenNormCoord_eq]
  constructor
  · rintro ⟨z, hz⟩
    have hf := congrArg TraceOneInt.fst hz
    have hs := congrArg TraceOneInt.snd hz
    have ha : (q : ℤ) ∣ (a : ℤ) := ⟨z.fst, by simpa [ofInt] using hf⟩
    have hb : (q : ℤ) ∣ (b : ℤ) := ⟨z.snd, by simpa [ofInt] using hs⟩
    exact ⟨Int.ofNat_dvd.mp ha, Int.ofNat_dvd.mp hb⟩
  · rintro ⟨ha, hb⟩
    rcases Int.ofNat_dvd.mpr ha with ⟨r, hr⟩
    rcases Int.ofNat_dvd.mpr hb with ⟨s, hs⟩
    refine ⟨⟨r, s⟩, ?_⟩
    apply traceOne_ext <;> simp [ofInt, hr, hs]

/-- Evaluate integral coordinates at a residue parameter, including negative ones. -/
def eisensteinResidueEval {q : ℕ} (t : ZMod q) (z : TraceOneInt (-1)) : ZMod q :=
  (z.fst : ZMod q) + (z.snd : ZMod q) * t

/-- The chosen ratio is defined under the prime-field instance. -/
def gtailSevenResidueRoot (q a b : ℕ) [Fact (Nat.Prime q)] : ZMod q :=
  -(a : ZMod q) / (b : ZMod q)

/-- Coordinate evaluation respects addition for every parameter. -/
theorem eisensteinResidueEval_add {q : ℕ} (t : ZMod q) (x y : TraceOneInt (-1)) :
    eisensteinResidueEval t (x + y) =
      eisensteinResidueEval t x + eisensteinResidueEval t y := by
  simp [eisensteinResidueEval]
  ring

/-- Multiplication is respected precisely under the quadratic root relation. -/
theorem eisensteinResidueEval_mul {q : ℕ} (t : ZMod q)
    (ht : t ^ 2 - t + 1 = 0) (x y : TraceOneInt (-1)) :
    eisensteinResidueEval t (x * y) =
      eisensteinResidueEval t x * eisensteinResidueEval t y := by
  simp only [eisensteinResidueEval, fst_mul, snd_mul, Int.cast_add, Int.cast_mul,
    Int.cast_neg, Int.cast_one]
  linear_combination - (x.snd : ZMod q) * (y.snd : ZMod q) * ht

/-- The norm divisor and a nonzero denominator produce a quadratic root. -/
theorem gtailSevenResidueRoot_polynomial {q a b : ℕ} [Fact (Nat.Prime q)]
    (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬ q ∣ b) :
    gtailSevenResidueRoot q a b ^ 2 - gtailSevenResidueRoot q a b + 1 = 0 := by
  have hb0 : (b : ZMod q) ≠ 0 := fun hz => hb ((ZMod.natCast_eq_zero_iff b q).mp hz)
  have hquad : (a : ZMod q) ^ 2 + (a : ZMod q) * b + (b : ZMod q) ^ 2 = 0 := by
    have hz := (ZMod.natCast_eq_zero_iff (a ^ 2 + a * b + b ^ 2) q).mpr hQ
    push_cast at hz
    exact hz
  dsimp [gtailSevenResidueRoot]
  field_simp [hb0]
  convert hquad using 1 <;> ring

/-- The first residue slot vanishes from the explicit ratio alone. -/
theorem eisensteinResidueEval_gtailSevenNormCoord_zero {q a b : ℕ}
    [Fact (Nat.Prime q)] (hb : ¬ q ∣ b) :
    eisensteinResidueEval (gtailSevenResidueRoot q a b) (gtailSevenNormCoord a b) = 0 := by
  have hb0 : (b : ZMod q) ≠ 0 := fun hz => hb ((ZMod.natCast_eq_zero_iff b q).mp hz)
  rw [gtailSevenNormCoord_eq]
  simp [eisensteinResidueEval, gtailSevenResidueRoot]
  field_simp [hb0]
  ring

/-- The conjugate parameter is a root of the same polynomial. -/
theorem gtailSevenResidueRoot_conjugate_polynomial {q a b : ℕ}
    [Fact (Nat.Prime q)] (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬ q ∣ b) :
    (1 - gtailSevenResidueRoot q a b) ^ 2 -
      (1 - gtailSevenResidueRoot q a b) + 1 = 0 := by
  have ht := gtailSevenResidueRoot_polynomial hQ hb
  linear_combination ht

/-- The other slot reads the explicit trace coordinate. -/
theorem eisensteinResidueEval_gtailSevenNormCoord_conjugate {q a b : ℕ}
    [Fact (Nat.Prime q)] (hb : ¬ q ∣ b) :
    eisensteinResidueEval (1 - gtailSevenResidueRoot q a b) (gtailSevenNormCoord a b) =
      2 * (a : ZMod q) + (b : ZMod q) := by
  have hz := eisensteinResidueEval_gtailSevenNormCoord_zero (a := a) hb
  rw [gtailSevenNormCoord_eq] at hz ⊢
  simp only [eisensteinResidueEval, Int.cast_natCast] at hz ⊢
  linear_combination -hz

/-- Conjugating the element equals conjugating the residue parameter. -/
theorem eisensteinResidueEval_conj {q : ℕ} (t : ZMod q) (z : TraceOneInt (-1)) :
    eisensteinResidueEval t (conj z) = eisensteinResidueEval (1 - t) z := by
  simp [eisensteinResidueEval, conj]
  ring

/-- The trace coordinate cannot vanish at a norm prime away from three. -/
theorem gtailSevenResidue_trace_ne_zero {q a b : ℕ} [Fact (Nat.Prime q)]
    (hq3 : q ≠ 3) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬ q ∣ b) :
    2 * (a : ZMod q) + (b : ZMod q) ≠ 0 := by
  have hb0 : (b : ZMod q) ≠ 0 := fun hz => hb ((ZMod.natCast_eq_zero_iff b q).mp hz)
  have hquad : (a : ZMod q) ^ 2 + (a : ZMod q) * b + (b : ZMod q) ^ 2 = 0 := by
    have hz := (ZMod.natCast_eq_zero_iff (a ^ 2 + a * b + b ^ 2) q).mpr hQ
    push_cast at hz
    exact hz
  intro htrace
  have hidentity : 4 * ((a : ZMod q) ^ 2 + (a : ZMod q) * b + (b : ZMod q) ^ 2) =
      (2 * (a : ZMod q) + b) ^ 2 + 3 * (b : ZMod q) ^ 2 := by ring
  rw [hquad, htrace] at hidentity
  have hmul : (3 : ZMod q) * (b : ZMod q) ^ 2 = 0 := by simpa using hidentity.symm
  have hthree := (mul_eq_zero.mp hmul).resolve_right (pow_ne_zero 2 hb0)
  have hqthree := (ZMod.natCast_eq_zero_iff 3 q).mp hthree
  exact hq3 ((Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime q)
    (by decide : Nat.Prime 3)).mp hqthree)

/-- Away from characteristic three, the conjugate slot is nonzero. -/
theorem eisensteinResidueEval_gtailSevenNormCoord_conjugate_ne_zero {q a b : ℕ}
    [Fact (Nat.Prime q)] (hq3 : q ≠ 3)
    (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬ q ∣ b) :
    eisensteinResidueEval (1 - gtailSevenResidueRoot q a b) (gtailSevenNormCoord a b) ≠ 0 := by
  rw [eisensteinResidueEval_gtailSevenNormCoord_conjugate hb]
  exact gtailSevenResidue_trace_ne_zero hq3 hQ hb

/-- The two roots differ because the evaluations at the same element differ. -/
theorem gtailSevenResidueRoot_ne_conjugate {q a b : ℕ} [Fact (Nat.Prime q)]
    (hq3 : q ≠ 3) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬ q ∣ b) :
    gtailSevenResidueRoot q a b ≠ 1 - gtailSevenResidueRoot q a b := by
  intro heq
  have hz := eisensteinResidueEval_gtailSevenNormCoord_zero (a := a) hb
  rw [heq] at hz
  exact eisensteinResidueEval_gtailSevenNormCoord_conjugate_ne_zero hq3 hQ hb hz

end DkMath.Lib.NumberTheory
