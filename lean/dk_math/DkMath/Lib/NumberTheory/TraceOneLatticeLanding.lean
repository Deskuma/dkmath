/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.TraceOneQuadratic

#print "file: DkMath.Lib.NumberTheory.TraceOneLatticeLanding"

/-!
# General TraceOne lattice landing

This module proves the integral lattice criterion for the existing
`TraceOneInt s` carrier with arbitrary parameter `s`.  The reverse direction
uses only the explicit hypothesis that the divisor has nonzero norm; no
positive-definite norm property is assumed.
-/

namespace DkMath.Lib.NumberTheory

open DkMath.NumberTheory.TraceOneQuadratic

local notation "traceNorm" => DkMath.NumberTheory.TraceOneQuadratic.norm

/-- Conjugation in the structured TraceOne coordinates. -/
theorem traceOne_conj_coordinates (s c d : ℤ) :
    conj (⟨c, d⟩ : TraceOneInt s) = ⟨c + d, -d⟩ := by
  rfl

/-- First coordinate of a conjugate product in arbitrary TraceOne parameter. -/
theorem traceOne_mul_conj_fst (s a b c d : ℤ) :
    ((⟨a, b⟩ : TraceOneInt s) * conj (⟨c, d⟩ : TraceOneInt s)).fst =
      a * c + a * d - s * b * d := by
  simp [DkMath.NumberTheory.TraceOneQuadratic.conj]
  ring

/-- Second coordinate of a conjugate product in arbitrary TraceOne parameter. -/
theorem traceOne_mul_conj_snd (s a b c d : ℤ) :
    ((⟨a, b⟩ : TraceOneInt s) * conj (⟨c, d⟩ : TraceOneInt s)).snd =
      b * c - a * d := by
  simp [DkMath.NumberTheory.TraceOneQuadratic.conj]
  ring

/-- Conjugation preserves the existing TraceOne norm. -/
theorem traceOne_norm_conj (s : ℤ) (z : TraceOneInt s) :
    traceNorm (conj z) = traceNorm z := by
  rcases z with ⟨c, d⟩
  simp [DkMath.NumberTheory.TraceOneQuadratic.conj,
    DkMath.NumberTheory.TraceOneQuadratic.norm]
  ring

private theorem traceOne_mul_eq_zero_of_norm_ne_zero
    {s : ℤ} {x z : TraceOneInt s}
    (hz : traceNorm z ≠ 0) (h : x * z = 0) : x = 0 := by
  rcases x with ⟨p, q⟩
  rcases z with ⟨c, d⟩
  have hfst := congrArg TraceOneInt.fst h
  have hsnd := congrArg TraceOneInt.snd h
  have hfst' : p * c + s * q * d = 0 := by
    simpa [DkMath.NumberTheory.TraceOneQuadratic.mul] using hfst
  have hsnd' : p * d + q * c + q * d = 0 := by
    simpa [DkMath.NumberTheory.TraceOneQuadratic.mul] using hsnd
  have hp : p * traceNorm (⟨c, d⟩ : TraceOneInt s) =
      (p * c + s * q * d) * (c + d) -
        s * d * (p * d + q * c + q * d) := by
    simp [DkMath.NumberTheory.TraceOneQuadratic.norm]
    ring
  have hq : q * traceNorm (⟨c, d⟩ : TraceOneInt s) =
      c * (p * d + q * c + q * d) -
        d * (p * c + s * q * d) := by
    simp [DkMath.NumberTheory.TraceOneQuadratic.norm]
    ring
  have hp0eq : p * traceNorm (⟨c, d⟩ : TraceOneInt s) = 0 := by
    calc
      p * traceNorm (⟨c, d⟩ : TraceOneInt s) =
          (p * c + s * q * d) * (c + d) -
            s * d * (p * d + q * c + q * d) := hp
      _ = 0 := by rw [hfst', hsnd']; simp
  have hq0eq : q * traceNorm (⟨c, d⟩ : TraceOneInt s) = 0 := by
    calc
      q * traceNorm (⟨c, d⟩ : TraceOneInt s) =
          c * (p * d + q * c + q * d) -
            d * (p * c + s * q * d) := hq
      _ = 0 := by rw [hfst', hsnd']; simp
  have hp0 : p = 0 := (mul_eq_zero.mp hp0eq).resolve_right hz
  have hq0 : q = 0 := (mul_eq_zero.mp hq0eq).resolve_right hz
  apply traceOne_ext
  · simp [hp0]
  · simp [hq0]

/-- Right multiplication is cancellable whenever the right norm is nonzero. -/
theorem traceOne_mul_right_cancel_of_norm_ne_zero
    {s : ℤ} {x y z : TraceOneInt s}
    (hz : traceNorm z ≠ 0) (h : x * z = y * z) : x = y := by
  have hzero : (x - y) * z = 0 := by
    rw [sub_mul, h, sub_self]
  have hdiff : x - y = 0 :=
    traceOne_mul_eq_zero_of_norm_ne_zero hz hzero
  exact sub_eq_zero.mp hdiff

/-- Forward coordinate divisibility after multiplication by the conjugate. -/
theorem traceOne_dvd_imp_norm_dvd_mul_conj_coordinates
    {s : ℤ} {alpha beta : TraceOneInt s}
    (h : beta ∣ alpha) :
    traceNorm beta ∣ (alpha * conj beta).fst ∧
      traceNorm beta ∣ (alpha * conj beta).snd := by
  rcases h with ⟨q, hq⟩
  have hprod : alpha * conj beta =
      DkMath.NumberTheory.TraceOneQuadratic.ofInt s (traceNorm beta) * q := by
    calc
      alpha * conj beta = (beta * q) * conj beta := by rw [hq]
      _ = (beta * conj beta) * q := by ring
      _ = DkMath.NumberTheory.TraceOneQuadratic.ofInt s (traceNorm beta) * q := by
        rw [traceOne_mul_conj]
  constructor
  · refine ⟨q.fst, ?_⟩
    simpa [DkMath.NumberTheory.TraceOneQuadratic.ofInt] using
      congrArg TraceOneInt.fst hprod
  · refine ⟨q.snd, ?_⟩
    simpa [DkMath.NumberTheory.TraceOneQuadratic.ofInt] using
      congrArg TraceOneInt.snd hprod

/-- Reconstruct an integral quotient from both conjugate-product coordinates. -/
theorem traceOne_dvd_of_norm_dvd_mul_conj_coordinates
    {s : ℤ} {alpha beta : TraceOneInt s}
    (hNorm : traceNorm beta ≠ 0)
    (hfst : traceNorm beta ∣ (alpha * conj beta).fst)
    (hsnd : traceNorm beta ∣ (alpha * conj beta).snd) :
    beta ∣ alpha := by
  rcases hfst with ⟨r, hr⟩
  rcases hsnd with ⟨t, ht⟩
  let q : TraceOneInt s := ⟨r, t⟩
  have hscalar :
      DkMath.NumberTheory.TraceOneQuadratic.ofInt s (traceNorm beta) * q =
        alpha * conj beta := by
    apply traceOne_ext
    · simpa [q, DkMath.NumberTheory.TraceOneQuadratic.ofInt] using hr.symm
    · simpa [q, DkMath.NumberTheory.TraceOneQuadratic.ofInt] using ht.symm
  have hprod : alpha * conj beta = (beta * q) * conj beta := by
    calc
      alpha * conj beta =
          DkMath.NumberTheory.TraceOneQuadratic.ofInt s (traceNorm beta) * q :=
        hscalar.symm
      _ = (beta * conj beta) * q := by rw [traceOne_mul_conj]
      _ = (beta * q) * conj beta := by ring
  have hNormConj : traceNorm (conj beta) ≠ 0 := by
    simpa only [traceOne_norm_conj] using hNorm
  refine ⟨q, ?_⟩
  exact traceOne_mul_right_cancel_of_norm_ne_zero hNormConj hprod

/-- General exact TraceOne lattice-landing criterion. -/
theorem traceOne_dvd_iff_norm_dvd_mul_conj_coordinates
    {s : ℤ} {alpha beta : TraceOneInt s}
    (hNorm : traceNorm beta ≠ 0) :
    beta ∣ alpha ↔
      traceNorm beta ∣ (alpha * conj beta).fst ∧
        traceNorm beta ∣ (alpha * conj beta).snd := by
  constructor
  · exact traceOne_dvd_imp_norm_dvd_mul_conj_coordinates
  · rintro ⟨hfst, hsnd⟩
    exact traceOne_dvd_of_norm_dvd_mul_conj_coordinates hNorm hfst hsnd

/-- Polynomial-coordinate form of the general TraceOne criterion. -/
theorem traceOne_dvd_iff_polynomial_norm_dvd_mul_conj_coordinates
    {s a b c d : ℤ}
    (hNorm : c ^ 2 + c * d - s * d ^ 2 ≠ 0) :
    (⟨c, d⟩ : TraceOneInt s) ∣ (⟨a, b⟩ : TraceOneInt s) ↔
      (c ^ 2 + c * d - s * d ^ 2) ∣
          (a * c + a * d - s * b * d) ∧
        (c ^ 2 + c * d - s * d ^ 2) ∣ (b * c - a * d) := by
  have hNorm' : traceNorm (⟨c, d⟩ : TraceOneInt s) ≠ 0 := by
    simpa [DkMath.NumberTheory.TraceOneQuadratic.norm] using hNorm
  have hgeneric :=
    traceOne_dvd_iff_norm_dvd_mul_conj_coordinates
      (s := s) (alpha := (⟨a, b⟩ : TraceOneInt s))
      (beta := (⟨c, d⟩ : TraceOneInt s)) hNorm'
  rw [traceOne_mul_conj_fst, traceOne_mul_conj_snd] at hgeneric
  simpa [DkMath.NumberTheory.TraceOneQuadratic.norm] using hgeneric

/-- Norm divisibility is necessary for TraceOne element divisibility. -/
theorem traceOne_dvd_imp_norm_dvd_norm
    {s : ℤ} {alpha beta : TraceOneInt s}
    (h : beta ∣ alpha) : traceNorm beta ∣ traceNorm alpha := by
  rcases h with ⟨q, hq⟩
  refine ⟨traceNorm q, ?_⟩
  rw [hq, traceOne_norm_mul]

/-- At `s = 0`, the nonzero element `tau 0` has zero norm. -/
theorem traceOne_zero_norm_nonzero :
    traceNorm (tau 0) = 0 ∧ tau 0 ≠ (0 : TraceOneInt 0) := by
  constructor
  · norm_num [tau, DkMath.NumberTheory.TraceOneQuadratic.norm]
  · intro h
    have hsnd := congrArg TraceOneInt.snd h
    norm_num [tau] at hsnd

end DkMath.Lib.NumberTheory

#print axioms DkMath.Lib.NumberTheory.traceOne_conj_coordinates
#print axioms DkMath.Lib.NumberTheory.traceOne_mul_conj_fst
#print axioms DkMath.Lib.NumberTheory.traceOne_mul_conj_snd
#print axioms DkMath.Lib.NumberTheory.traceOne_norm_conj
#print axioms DkMath.Lib.NumberTheory.traceOne_mul_right_cancel_of_norm_ne_zero
#print axioms DkMath.Lib.NumberTheory.traceOne_dvd_iff_norm_dvd_mul_conj_coordinates
#print axioms DkMath.Lib.NumberTheory.traceOne_dvd_iff_polynomial_norm_dvd_mul_conj_coordinates
#print axioms DkMath.Lib.NumberTheory.traceOne_dvd_imp_norm_dvd_norm
#print axioms DkMath.Lib.NumberTheory.traceOne_zero_norm_nonzero
