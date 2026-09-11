/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.TraceOneQuadratic
import DkMath.Lib.NumberTheory.PadicValNat

#print "file: DkMath.NumberTheory.TraceOneDiscriminantAxis"

namespace DkMath.NumberTheory.TraceOneQuadratic

/-! ## The discriminant axis -/

/-- The integral axis whose trace image is the discriminant coordinate. -/
def discrAxis (s : ℤ) : TraceOneInt s := 2 * tau s - 1

@[simp] theorem discrAxis_eq (s : ℤ) : discrAxis s = ⟨-1, 2⟩ := by
  change (⟨2, 0⟩ : TraceOneInt s) * ⟨0, 1⟩ - ⟨1, 0⟩ = ⟨-1, 2⟩
  ext <;> simp

/-- The square of the discriminant axis is the embedded discriminant. -/
theorem discrAxis_sq (s : ℤ) :
    discrAxis s ^ 2 = ofInt s (discr s) := by
  rw [discrAxis_eq]
  ext <;> simp [ofInt, discr, pow_two]
  ring

/-- Conjugation reverses the discriminant axis. -/
theorem conj_discrAxis (s : ℤ) : conj (discrAxis s) = -discrAxis s := by
  rw [discrAxis_eq]
  ext <;> simp [conj]

/-- The norm of the discriminant axis is the negative discriminant. -/
theorem norm_discrAxis (s : ℤ) : norm (discrAxis s) = -discr s := by
  rw [discrAxis_eq]
  simp [norm, discr]
  ring

/-- Multiplication by the axis has discriminant times the second coordinate as
its trace. -/
theorem trace_discrAxis_mul (s c d : ℤ) :
    trace (discrAxis s * (⟨c, d⟩ : TraceOneInt s)) = discr s * d := by
  rw [discrAxis_eq]
  simp [trace, discr]
  ring

/-- Divisibility by the discriminant axis is exactly divisibility of the trace
by the discriminant.  The converse uses the explicit coordinate witness
`⟨2*s*k-a,k⟩`. -/
theorem discrAxis_dvd_iff_discr_dvd_trace (s : ℤ) (x : TraceOneInt s) :
    discrAxis s ∣ x ↔ discr s ∣ trace x := by
  rcases x with ⟨a, b⟩
  constructor
  · rintro ⟨⟨c, d⟩, h⟩
    refine ⟨d, ?_⟩
    have ht := congrArg trace h
    rw [trace_discrAxis_mul] at ht
    simpa [trace] using ht
  · rintro ⟨k, hk⟩
    refine ⟨(⟨2 * s * k - a, k⟩ : TraceOneInt s), ?_⟩
    apply traceOne_ext
    · rw [discrAxis_eq]
      simp
      ring
    · rw [discrAxis_eq]
      simp [trace] at hk ⊢
      simp [discr] at hk ⊢
      linear_combination hk

/-! ## A prime discriminant packet -/

/-- The small data package used by the generic prime-discriminant lemmas.

The packet records only primality and the absolute value of the discriminant;
it does not assert a cyclotomic realization. -/
structure PrimeDiscriminantPacket (p : ℕ) (s : ℤ) : Prop where
  prime : p.Prime
  discr_natAbs : Int.natAbs (discr s) = p

namespace PrimeDiscriminantPacket

theorem discr_eq_or_neg (P : PrimeDiscriminantPacket p s) :
    discr s = (p : ℤ) ∨ discr s = -(p : ℤ) := by
  rcases Int.natAbs_eq (discr s) with h | h
  · left
    rw [h, P.discr_natAbs]
  · right
    rw [h, P.discr_natAbs]

theorem discr_dvd_iff (P : PrimeDiscriminantPacket p s) (z : ℤ) :
    discr s ∣ z ↔ (p : ℤ) ∣ z := by
  rcases P.discr_eq_or_neg with h | h
  · rw [h]
  · rw [h]
    simp only [neg_dvd]

theorem prime_int (P : PrimeDiscriminantPacket p s) : Prime (p : ℤ) := by
  rw [Int.prime_iff_natAbs_prime]
  simpa using P.prime

theorem prime_ne_two (P : PrimeDiscriminantPacket p s) : p ≠ 2 := by
  intro hp
  subst p
  have hd : ¬ (2 : ℤ) ∣ discr s := by
    rintro ⟨k, hk⟩
    simp [discr] at hk
    omega
  apply hd
  exact (P.discr_dvd_iff (discr s)).mp (dvd_refl _)

theorem norm_dvd_iff_trace_dvd (P : PrimeDiscriminantPacket p s)
    (x : TraceOneInt s) :
    (p : ℤ) ∣ norm x ↔ (p : ℤ) ∣ trace x := by
  have hp : Prime (p : ℤ) := P.prime_int
  have hpdiscr : (p : ℤ) ∣ discr s := by
    exact (P.discr_dvd_iff (discr s)).mp (dvd_refl _)
  have hfour : 4 * norm x = trace x ^ 2 - discr s * x.snd ^ 2 :=
    four_mul_traceOneNorm_eq_discriminant x
  constructor
  · rintro ⟨k, hk⟩
    have hnorm : (p : ℤ) ∣ 4 * norm x := by
      refine ⟨4 * k, ?_⟩
      rw [hk]
      ring
    have hdisc : (p : ℤ) ∣ discr s * x.snd ^ 2 := dvd_mul_of_dvd_left hpdiscr _
    have htrace : (p : ℤ) ∣ trace x ^ 2 := by
      rw [show trace x ^ 2 = 4 * norm x + discr s * x.snd ^ 2 by linarith [hfour]]
      exact dvd_add hnorm hdisc
    exact hp.dvd_of_dvd_pow htrace
  · intro htrace
    have htraceSq : (p : ℤ) ∣ trace x ^ 2 := dvd_pow htrace (by norm_num : 2 ≠ 0)
    have hdisc : (p : ℤ) ∣ discr s * x.snd ^ 2 := dvd_mul_of_dvd_left hpdiscr _
    have hnorm : (p : ℤ) ∣ 4 * norm x := by
      rw [hfour]
      exact dvd_sub htraceSq hdisc
    rcases hp.dvd_mul.mp hnorm with hp4 | hpnorm
    · have htwo : (p : ℤ) ∣ 2 := by
        exact hp.dvd_of_dvd_pow (n := 2) (by simpa using hp4)
      have hpeq : p = 2 := by
        have htwo' : p ∣ 2 := by exact_mod_cast htwo
        have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) htwo'
        have hpge : 2 ≤ p := P.prime.two_le
        omega
      exact False.elim (P.prime_ne_two hpeq)
    · exact hpnorm

theorem discrAxis_dvd_iff_prime_dvd_natAbs_norm
    (P : PrimeDiscriminantPacket p s) (x : TraceOneInt s) :
    discrAxis s ∣ x ↔ p ∣ Int.natAbs (norm x) := by
  constructor
  · intro haxis
    have htrace := discrAxis_dvd_iff_discr_dvd_trace s x |>.mp haxis
    have hptrace := (P.discr_dvd_iff (trace x)).mp htrace
    have hpnorm := (P.norm_dvd_iff_trace_dvd x).mpr hptrace
    exact (Int.natCast_dvd).mp hpnorm
  · intro hnorm
    have hpnorm : (p : ℤ) ∣ norm x := (Int.natCast_dvd).mpr hnorm
    have hptrace := (P.norm_dvd_iff_trace_dvd x).mp hpnorm
    have htrace := (P.discr_dvd_iff (trace x)).mpr hptrace
    exact (discrAxis_dvd_iff_discr_dvd_trace s x).mpr htrace

end PrimeDiscriminantPacket

/-! ## Finite axis powers and the valuation depth -/

/-- The finite depth of a trace-one element at a chosen prime. -/
def discrAxisDepth (p : ℕ) (x : TraceOneInt s) : ℕ :=
  padicValNat p (Int.natAbs (norm x))

namespace PrimeDiscriminantPacket

theorem natAbs_norm_discrAxis (P : PrimeDiscriminantPacket p s) :
    Int.natAbs (norm (discrAxis s)) = p := by
  rw [norm_discrAxis, Int.natAbs_neg, P.discr_natAbs]

theorem natAbs_norm_discrAxis_pow (P : PrimeDiscriminantPacket p s) (n : ℕ) :
    Int.natAbs (norm (discrAxis s ^ n)) = p ^ n := by
  induction n with
  | zero => simp [norm]
  | succ n ih =>
      rw [pow_succ, traceOne_norm_mul, Int.natAbs_mul,
        P.natAbs_norm_discrAxis, ih]
      rw [pow_succ]

theorem natAbs_norm_eq_mul_of_eq_discrAxis_mul
    (P : PrimeDiscriminantPacket p s)
    {x y : TraceOneInt s} (hxy : x = discrAxis s * y) :
    Int.natAbs (norm x) = p * Int.natAbs (norm y) := by
  rw [hxy, traceOne_norm_mul, Int.natAbs_mul, P.natAbs_norm_discrAxis]

theorem discrAxis_pow_dvd_iff_pow_prime_dvd_natAbs_norm
    (P : PrimeDiscriminantPacket p s) (n : ℕ) (x : TraceOneInt s) :
    discrAxis s ^ n ∣ x ↔ p ^ n ∣ Int.natAbs (norm x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      constructor
      · rintro ⟨y, hxy⟩
        refine ⟨Int.natAbs (norm y), ?_⟩
        rw [hxy, traceOne_norm_mul, Int.natAbs_mul,
          P.natAbs_norm_discrAxis_pow, pow_succ]
      · intro hx
        have hone : p ∣ Int.natAbs (norm x) := by
          exact dvd_trans (dvd_pow_self p (by omega)) hx
        rcases (P.discrAxis_dvd_iff_prime_dvd_natAbs_norm x).mpr hone with ⟨y, hxy⟩
        have hnorm : p * Int.natAbs (norm y) = Int.natAbs (norm x) := by
          symm
          exact P.natAbs_norm_eq_mul_of_eq_discrAxis_mul hxy
        have hyNorm : p ^ n ∣ Int.natAbs (norm y) := by
          rcases hx with ⟨k, hk⟩
          refine ⟨k, ?_⟩
          exact Nat.eq_of_mul_eq_mul_left P.prime.pos (by
            rw [hnorm, hk, pow_succ]
            ac_rfl)
        have hyAxis : discrAxis s ^ n ∣ y := (ih y).mpr hyNorm
        rcases hyAxis with ⟨z, hyz⟩
        refine ⟨z, ?_⟩
        rw [hxy, hyz, pow_succ]
        ring

theorem natAbs_norm_ne_zero_of_norm_ne_zero
    {x : TraceOneInt s} (hx : norm x ≠ 0) :
    Int.natAbs (norm x) ≠ 0 := by
  rw [Int.natAbs_ne_zero]
  exact hx

theorem discrAxis_pow_dvd_iff_le_depth
    (P : PrimeDiscriminantPacket p s) {x : TraceOneInt s}
    (hx : norm x ≠ 0) (n : ℕ) :
    discrAxis s ^ n ∣ x ↔ n ≤ discrAxisDepth p x := by
  rw [P.discrAxis_pow_dvd_iff_pow_prime_dvd_natAbs_norm]
  simpa [discrAxisDepth] using (@padicValNat_dvd_iff_le p (Fact.mk P.prime)
    (Int.natAbs (norm x)) n (natAbs_norm_ne_zero_of_norm_ne_zero hx))

theorem discrAxis_pow_depth_dvd
    (P : PrimeDiscriminantPacket p s) {x : TraceOneInt s}
    (hx : norm x ≠ 0) :
    discrAxis s ^ discrAxisDepth p x ∣ x :=
  (P.discrAxis_pow_dvd_iff_le_depth hx _).mpr le_rfl

theorem not_discrAxis_pow_succ_depth_dvd
    (P : PrimeDiscriminantPacket p s) {x : TraceOneInt s}
    (hx : norm x ≠ 0) :
    ¬ discrAxis s ^ (discrAxisDepth p x + 1) ∣ x := by
  rw [P.discrAxis_pow_dvd_iff_le_depth hx]
  omega

theorem discrAxisDepth_discrAxis_pow
    (P : PrimeDiscriminantPacket p s) (n : ℕ) :
    discrAxisDepth p (discrAxis s ^ n) = n := by
  rw [discrAxisDepth, P.natAbs_norm_discrAxis_pow]
  haveI : Fact p.Prime := ⟨P.prime⟩
  rw [padicValNat.pow]
  simp

theorem exists_terminal_discrAxis_core
    (P : PrimeDiscriminantPacket p s) {x : TraceOneInt s}
    (hx : norm x ≠ 0) :
    ∃ y : TraceOneInt s,
      x = discrAxis s ^ discrAxisDepth p x * y ∧
      norm y ≠ 0 ∧
      ¬ discrAxis s ∣ y ∧
      ¬ p ∣ Int.natAbs (norm y) ∧
      Int.natAbs (norm x) = p ^ discrAxisDepth p x * Int.natAbs (norm y) ∧
      1 ≤ Int.natAbs (norm y) := by
  rcases P.discrAxis_pow_depth_dvd hx with ⟨y, hxy⟩
  have hyNorm : norm y ≠ 0 := by
    intro hy
    apply hx
    rw [hxy, traceOne_norm_mul, hy]
    simp
  have hyAxis : ¬ discrAxis s ∣ y := by
    rintro ⟨z, hyz⟩
    apply P.not_discrAxis_pow_succ_depth_dvd hx
    refine ⟨z, ?_⟩
    calc
      x = discrAxis s ^ discrAxisDepth p x * y := hxy
      _ = discrAxis s ^ discrAxisDepth p x * (discrAxis s * z) := by rw [hyz]
      _ = discrAxis s ^ (discrAxisDepth p x + 1) * z := by
        rw [pow_succ]
        ring
  have hyPrime : ¬ p ∣ Int.natAbs (norm y) := by
    intro hp
    apply hyAxis
    exact (P.discrAxis_dvd_iff_prime_dvd_natAbs_norm y).mpr hp
  have hfactor :
      Int.natAbs (norm x) = p ^ discrAxisDepth p x * Int.natAbs (norm y) := by
    have hnormx : norm x = norm (discrAxis s ^ discrAxisDepth p x) * norm y := by
      calc
        norm x = norm (discrAxis s ^ discrAxisDepth p x * y) := congrArg norm hxy
        _ = norm (discrAxis s ^ discrAxisDepth p x) * norm y := traceOne_norm_mul _ _
    calc
      Int.natAbs (norm x) =
          Int.natAbs (norm (discrAxis s ^ discrAxisDepth p x)) *
            Int.natAbs (norm y) := by
              rw [hnormx, Int.natAbs_mul]
      _ = p ^ discrAxisDepth p x * Int.natAbs (norm y) := by
        rw [P.natAbs_norm_discrAxis_pow]
  have hpos : 0 < Int.natAbs (norm y) := Int.natAbs_pos.mpr hyNorm
  exact ⟨y, hxy, hyNorm, hyAxis, hyPrime, hfactor, by omega⟩

end PrimeDiscriminantPacket

end DkMath.NumberTheory.TraceOneQuadratic
