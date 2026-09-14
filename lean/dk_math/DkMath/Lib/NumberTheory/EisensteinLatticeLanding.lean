/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.TraceOneLatticeLanding
import DkMath.Lib.NumberTheory.EisensteinCoordinates

#print "file: DkMath.Lib.NumberTheory.EisensteinLatticeLanding"

/-!
# Eisenstein lattice landing

This module gives the exact integral-coordinate criterion for divisibility in
the standard Eisenstein model inside `TraceOneInt (-1)`.  It deliberately
reuses the existing carrier, multiplication, conjugation, and norm; no field
or Euclidean-domain infrastructure is introduced here.
-/

namespace DkMath.Lib.NumberTheory

open DkMath.NumberTheory.TraceOneQuadratic

local notation "tqNorm" => DkMath.NumberTheory.TraceOneQuadratic.norm

/-- Conjugation in standard Eisenstein coordinates. -/
theorem eisensteinCoord_conj (c d : ℤ) :
    conj (eisensteinCoord c d) = eisensteinCoord (c - d) (-d) := by
  apply traceOne_ext
  · simp [eisensteinCoord, conj]
    ring
  · simp [eisensteinCoord, conj]

/-- Coordinates of the conjugate product in the standard Eisenstein lattice. -/
theorem eisensteinCoord_mul_conj (a b c d : ℤ) :
    eisensteinCoord a b * conj (eisensteinCoord c d) =
      eisensteinCoord (a * c - a * d + b * d) (b * c - a * d) := by
  rw [eisensteinCoord_conj, eisensteinCoord_mul]
  congr 1 <;> ring

/-- The positive-definite standard Eisenstein norm has only the zero fiber. -/
theorem norm_eisensteinCoord_eq_zero_iff (c d : ℤ) :
    tqNorm (eisensteinCoord c d) = 0 ↔ c = 0 ∧ d = 0 := by
  rw [norm_eisensteinCoord]
  constructor
  · intro h
    have hfour :
        4 * (c ^ 2 - c * d + d ^ 2) = (2 * c - d) ^ 2 + 3 * d ^ 2 := by
      ring
    rw [h] at hfour
    have hd_sq : d ^ 2 = 0 := by
      nlinarith [sq_nonneg (2 * c - d), sq_nonneg d]
    have hd : d = 0 := by
      nlinarith [sq_nonneg d]
    subst d
    have hc : c = 0 := by
      nlinarith [sq_nonneg c]
    exact ⟨hc, rfl⟩
  · rintro ⟨rfl, rfl⟩
    norm_num

/-- The same zero-fiber fact for an arbitrary `TraceOneInt (-1)` element. -/
theorem traceOne_neg_one_norm_eq_zero_iff (x : TraceOneInt (-1)) :
    tqNorm x = 0 ↔ x = 0 := by
  rcases x with ⟨c, e⟩
  rw [show tqNorm (⟨c, e⟩ : TraceOneInt (-1)) =
      c ^ 2 + c * e + e ^ 2 by
        simp [DkMath.NumberTheory.TraceOneQuadratic.norm]]
  constructor
  · intro h
    have hfour :
        4 * (c ^ 2 + c * e + e ^ 2) = (2 * c + e) ^ 2 + 3 * e ^ 2 := by
      ring
    rw [h] at hfour
    have he_sq : e ^ 2 = 0 := by
      nlinarith [sq_nonneg (2 * c + e), sq_nonneg e]
    have he : e = 0 := by
      nlinarith [sq_nonneg e]
    subst e
    have hc : c = 0 := by
      nlinarith [sq_nonneg c]
    exact congrArg (fun z : ℤ => (⟨z, 0⟩ : TraceOneInt (-1))) hc
  · intro h
    have hc : c = 0 := by
      simpa using congrArg TraceOneInt.fst h
    have he : e = 0 := by
      simpa using congrArg TraceOneInt.snd h
    subst c
    subst e
    norm_num

/-- A nonzero standard Eisenstein coordinate has nonzero norm. -/
theorem norm_eisensteinCoord_ne_zero_of_ne_zero
    {c d : ℤ} (hcoord : eisensteinCoord c d ≠ 0) :
    tqNorm (eisensteinCoord c d) ≠ 0 := by
  intro hnorm
  apply hcoord
  rcases (norm_eisensteinCoord_eq_zero_iff c d).mp hnorm with ⟨rfl, rfl⟩
  rfl

/-- Nonzero norm gives cancellation on the right in `TraceOneInt (-1)`. -/
theorem traceOne_neg_one_mul_right_cancel
    {x y z : TraceOneInt (-1)}
    (hz : tqNorm z ≠ 0) (h : x * z = y * z) : x = y := by
  have hzero : (x - y) * z = 0 := by
    rw [sub_mul, h, sub_self]
  have hnorm : tqNorm ((x - y) * z) = 0 := by
    rw [hzero]
    simp [DkMath.NumberTheory.TraceOneQuadratic.norm]
  rw [traceOne_norm_mul] at hnorm
  have hxy_norm : tqNorm (x - y) = 0 := by
    exact (mul_eq_zero.mp hnorm).resolve_right hz
  have hxy : x - y = 0 :=
    (traceOne_neg_one_norm_eq_zero_iff (x - y)).mp hxy_norm
  exact sub_eq_zero.mp hxy

private theorem eisensteinCoord_product_scalar_from_dvd
    {a b c d : ℤ} {r s : ℤ}
    (hr : a * c - a * d + b * d =
      tqNorm (eisensteinCoord c d) * r)
    (hs : b * c - a * d =
      tqNorm (eisensteinCoord c d) * s) :
    DkMath.NumberTheory.TraceOneQuadratic.ofInt (-1)
        (tqNorm (eisensteinCoord c d)) *
        eisensteinCoord r s =
      eisensteinCoord (a * c - a * d + b * d) (b * c - a * d) := by
  apply traceOne_ext
  · simp [eisensteinCoord, DkMath.NumberTheory.TraceOneQuadratic.ofInt, hr]
  · simp [eisensteinCoord, DkMath.NumberTheory.TraceOneQuadratic.ofInt, hs]

/-- Necessary coordinate divisibility for an Eisenstein quotient. -/
theorem eisenstein_dvd_imp_norm_dvd_conjugate_coordinates
    {a b c d : ℤ}
    (h : eisensteinCoord c d ∣ eisensteinCoord a b) :
    tqNorm (eisensteinCoord c d) ∣
        (a * c - a * d + b * d) ∧
      tqNorm (eisensteinCoord c d) ∣ (b * c - a * d) := by
  rcases h with ⟨q, hq⟩
  have hprod :
      eisensteinCoord a b * conj (eisensteinCoord c d) =
        DkMath.NumberTheory.TraceOneQuadratic.ofInt (-1)
            (tqNorm (eisensteinCoord c d)) * q := by
    calc
      eisensteinCoord a b * conj (eisensteinCoord c d) =
          (eisensteinCoord c d * q) * conj (eisensteinCoord c d) := by
            rw [hq]
      _ = (eisensteinCoord c d * conj (eisensteinCoord c d)) * q := by
            ring
      _ = DkMath.NumberTheory.TraceOneQuadratic.ofInt (-1)
          (tqNorm (eisensteinCoord c d)) * q := by
            rw [traceOne_mul_conj]
  have hcoord :
      eisensteinCoord (a * c - a * d + b * d) (b * c - a * d) =
        DkMath.NumberTheory.TraceOneQuadratic.ofInt (-1)
            (tqNorm (eisensteinCoord c d)) * q := by
    rw [← eisensteinCoord_mul_conj]
    exact hprod
  constructor
  · refine ⟨q.fst, ?_⟩
    simpa [eisensteinCoord, DkMath.NumberTheory.TraceOneQuadratic.ofInt] using
      congrArg TraceOneInt.fst hcoord
  · refine ⟨-q.snd, ?_⟩
    have hsnd := congrArg TraceOneInt.snd hcoord
    have hsnd' : a * d - b * c =
        tqNorm (eisensteinCoord c d) * q.snd := by
      simpa [eisensteinCoord, DkMath.NumberTheory.TraceOneQuadratic.ofInt,
        DkMath.NumberTheory.TraceOneQuadratic.norm] using hsnd
    calc
      b * c - a * d = -(a * d - b * c) := by ring
      _ = -(tqNorm (eisensteinCoord c d) * q.snd) := by rw [hsnd']
      _ = tqNorm (eisensteinCoord c d) * (-q.snd) := by ring

/-- Exact reconstruction of an integral quotient from both coordinate divisors. -/
theorem eisenstein_dvd_of_norm_dvd_conjugate_coordinates
    {a b c d : ℤ}
    (hbeta : eisensteinCoord c d ≠ 0)
    (hA : tqNorm (eisensteinCoord c d) ∣
      (a * c - a * d + b * d))
    (hB : tqNorm (eisensteinCoord c d) ∣ (b * c - a * d)) :
    eisensteinCoord c d ∣ eisensteinCoord a b := by
  rcases hA with ⟨r, hr⟩
  rcases hB with ⟨s, hs⟩
  let q : TraceOneInt (-1) := eisensteinCoord r s
  have hscalar :
      DkMath.NumberTheory.TraceOneQuadratic.ofInt (-1)
          (tqNorm (eisensteinCoord c d)) * q =
        eisensteinCoord (a * c - a * d + b * d) (b * c - a * d) := by
    exact eisensteinCoord_product_scalar_from_dvd hr hs
  have hprod :
      eisensteinCoord a b * conj (eisensteinCoord c d) =
        (eisensteinCoord c d * q) * conj (eisensteinCoord c d) := by
    calc
      eisensteinCoord a b * conj (eisensteinCoord c d) =
          eisensteinCoord (a * c - a * d + b * d) (b * c - a * d) :=
        eisensteinCoord_mul_conj a b c d
      _ = DkMath.NumberTheory.TraceOneQuadratic.ofInt (-1)
          (tqNorm (eisensteinCoord c d)) * q :=
        hscalar.symm
      _ = (eisensteinCoord c d * conj (eisensteinCoord c d)) * q := by
        rw [traceOne_mul_conj]
      _ = (eisensteinCoord c d * q) * conj (eisensteinCoord c d) := by
        ring
  have hconj : conj (eisensteinCoord c d) ≠ 0 := by
    intro hzero
    apply hbeta
    rw [← traceOne_conj_invol (eisensteinCoord c d), hzero]
    rfl
  refine ⟨q, ?_⟩
  have hnorm_conj : tqNorm (conj (eisensteinCoord c d)) ≠ 0 := by
    simpa only [show tqNorm (conj (eisensteinCoord c d)) =
        tqNorm (eisensteinCoord c d) by
          simp [conj, DkMath.NumberTheory.TraceOneQuadratic.norm]
          ring] using norm_eisensteinCoord_ne_zero_of_ne_zero hbeta
  exact traceOne_neg_one_mul_right_cancel hnorm_conj hprod

/-- Exact lattice landing criterion in standard Eisenstein coordinates. -/
theorem eisenstein_dvd_iff_norm_dvd_conjugate_coordinates
    {a b c d : ℤ}
    (hbeta : eisensteinCoord c d ≠ 0) :
    eisensteinCoord c d ∣ eisensteinCoord a b ↔
      tqNorm (eisensteinCoord c d) ∣
          (a * c - a * d + b * d) ∧
        tqNorm (eisensteinCoord c d) ∣ (b * c - a * d) := by
  constructor
  · exact eisenstein_dvd_imp_norm_dvd_conjugate_coordinates
  · rintro ⟨hA, hB⟩
    exact eisenstein_dvd_of_norm_dvd_conjugate_coordinates hbeta hA hB

/-- The generic TraceOne criterion specializes back to the approved Eisenstein API. -/
theorem eisenstein_dvd_iff_norm_dvd_conjugate_coordinates_via_generic
    {a b c d : ℤ}
    (hNorm : tqNorm (eisensteinCoord c d) ≠ 0) :
    eisensteinCoord c d ∣ eisensteinCoord a b ↔
      tqNorm (eisensteinCoord c d) ∣
          (a * c - a * d + b * d) ∧
        tqNorm (eisensteinCoord c d) ∣ (b * c - a * d) := by
  have hNorm' : tqNorm (⟨c, -d⟩ : TraceOneInt (-1)) ≠ 0 := by
    simpa [eisensteinCoord] using hNorm
  have hgeneric :=
    traceOne_dvd_iff_norm_dvd_mul_conj_coordinates
      (s := (-1 : ℤ))
      (alpha := (⟨a, -b⟩ : TraceOneInt (-1)))
      (beta := (⟨c, -d⟩ : TraceOneInt (-1))) hNorm'
  change (⟨c, -d⟩ : TraceOneInt (-1)) ∣
      (⟨a, -b⟩ : TraceOneInt (-1)) ↔ _
  have hN : tqNorm (eisensteinCoord c d) =
      tqNorm (⟨c, -d⟩ : TraceOneInt (-1)) := by
    rfl
  constructor
  · intro hdiv
    have hg := hgeneric.mp hdiv
    rw [hN]
    constructor
    · have hfst := hg.1
      rw [traceOne_mul_conj_fst (-1) a (-b) c (-d)] at hfst
      convert hfst using 1
      all_goals first | exact hN | exact hN.symm | ring
    · have hsnd := hg.2
      rw [traceOne_mul_conj_snd (-1) a (-b) c (-d)] at hsnd
      have hneg : tqNorm (eisensteinCoord c d) ∣
          -(b * c - a * d) := by
        convert hsnd using 1
        all_goals first | exact hN | exact hN.symm | ring
      exact Int.dvd_neg.mp hneg
  · intro hdiv
    rw [hN] at hdiv
    apply hgeneric.mpr
    constructor
    · have hA := hdiv.1
      rw [traceOne_mul_conj_fst (-1) a (-b) c (-d)]
      convert hA using 1
      all_goals first | exact hN | exact hN.symm | ring
    · have hneg : tqNorm (eisensteinCoord c d) ∣
          -(b * c - a * d) := Int.dvd_neg.mpr hdiv.2
      rw [traceOne_mul_conj_snd (-1) a (-b) c (-d)]
      convert hneg using 1
      all_goals first | exact hN | exact hN.symm | ring

/-- Polynomial form of the exact standard Eisenstein lattice criterion. -/
theorem eisenstein_dvd_iff_polynomial_norm_dvd_conjugate_coordinates
    {a b c d : ℤ}
    (hbeta : eisensteinCoord c d ≠ 0) :
    eisensteinCoord c d ∣ eisensteinCoord a b ↔
      (c ^ 2 - c * d + d ^ 2) ∣
          (a * c - a * d + b * d) ∧
        (c ^ 2 - c * d + d ^ 2) ∣ (b * c - a * d) := by
  simpa [norm_eisensteinCoord] using
    (eisenstein_dvd_iff_norm_dvd_conjugate_coordinates hbeta)

/-- Norm divisibility is necessary for element divisibility. -/
theorem eisenstein_dvd_imp_norm_dvd_norm
    {alpha beta : TraceOneInt (-1)}
    (h : beta ∣ alpha) : tqNorm beta ∣ tqNorm alpha := by
  rcases h with ⟨q, hq⟩
  refine ⟨tqNorm q, ?_⟩
  rw [hq, traceOne_norm_mul]

/-- A concrete norm-only divisibility regression: norm divisibility misses lattice landing. -/
theorem eisenstein_norm_divisibility_not_sufficient :
    tqNorm (eisensteinCoord (-2) 1) ∣ tqNorm (eisensteinCoord (-1) 2) ∧
      ¬ eisensteinCoord (-2) 1 ∣ eisensteinCoord (-1) 2 := by
  have hbeta : eisensteinCoord (-2) 1 ≠ 0 := by
    intro h
    have hsnd := congrArg TraceOneInt.snd h
    norm_num [eisensteinCoord] at hsnd
  constructor
  · norm_num [norm_eisensteinCoord]
  · intro hdiv
    have hcoord :=
      (eisenstein_dvd_iff_norm_dvd_conjugate_coordinates hbeta).mp hdiv
    norm_num [norm_eisensteinCoord] at hcoord

end DkMath.Lib.NumberTheory

#print axioms DkMath.Lib.NumberTheory.eisensteinCoord_conj
#print axioms DkMath.Lib.NumberTheory.eisensteinCoord_mul_conj
#print axioms DkMath.Lib.NumberTheory.norm_eisensteinCoord_eq_zero_iff
#print axioms DkMath.Lib.NumberTheory.eisenstein_dvd_iff_norm_dvd_conjugate_coordinates
#print axioms DkMath.Lib.NumberTheory.eisenstein_dvd_iff_norm_dvd_conjugate_coordinates_via_generic
#print axioms DkMath.Lib.NumberTheory.eisenstein_dvd_iff_polynomial_norm_dvd_conjugate_coordinates
#print axioms DkMath.Lib.NumberTheory.eisenstein_dvd_imp_norm_dvd_norm
#print axioms DkMath.Lib.NumberTheory.eisenstein_norm_divisibility_not_sufficient
