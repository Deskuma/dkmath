/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNValuationExcess
import DkMath.NumberTheory.WeightedGNBridge

#print "file: DkMath.ABC.GNOddPrimeExceptionalExcess"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# The exceptional GN valuation at odd-prime exponents

This module proves the local arithmetic kernel for a prime dividing a GN
kernel whose exponent is that same odd prime.  For coprime boundary
coordinates, such a factor occurs with valuation exactly one.

The original explicit exponent-five specialization is retained as a concrete
local instance.  Exceptional-support finite sums remain in separate bridge
modules.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom

/--
The canonical GN kernel is the geometric quotient between `(a + b)^p` and
`b^p`.
-/
theorem GN_eq_geom_sum₂ (p a b : ℕ) :
    GN p a b =
      ∑ i ∈ Finset.range p,
        (a + b) ^ i * b ^ (p - 1 - i) := by
  by_cases ha : a = 0
  · subst a
    rw [show GN p 0 b = p * b ^ (p - 1) by
      simpa [GN] using
        (DkMath.CosmicFormula.GN_zero_eval (R := ℕ) p b)]
    simpa using (geom_sum₂_self b p).symm
  · let S :=
      ∑ i ∈ Finset.range p,
        (a + b) ^ i * b ^ (p - 1 - i)
    have hGN := cosmic_id_csr p a b
    have hGeom := geom_sum₂_mul_add a b p
    have hEq : S * a = a * GN p a b := by
      dsimp [BigN, BodyN, GapN] at hGN
      dsimp [S]
      omega
    have hMul : a * GN p a b = a * S := by
      simpa [Nat.mul_comm] using hEq.symm
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha) hMul

/--
At a prime exponent, divisibility of the GN kernel by the exponent forces
divisibility of the boundary coordinate.
-/
theorem prime_dvd_boundary_of_dvd_GN_prime
    {p a b : ℕ}
    (hp : Nat.Prime p)
    (hpGN : p ∣ GN p a b) :
    p ∣ a := by
  obtain ⟨B, hGN⟩ :=
    DkMath.NumberTheory.prime_exists_GN_eq_mul_add_rightBoundary
      (x := a) (u := b) hp
  have hpPow : p ∣ a ^ (p - 1) := by
    rw [hGN] at hpGN
    have hpGN' : p ∣ a ^ (p - 1) + p * B := by
      simpa [Nat.add_comm] using hpGN
    exact (Nat.dvd_add_iff_left (dvd_mul_right p B)).mpr hpGN'
  exact hp.dvd_of_dvd_pow hpPow

/--
For an odd prime exponent and coprime boundary coordinates, an exponent-prime
factor in `GN` has exact p-adic valuation one.
-/
theorem padicValNat_GN_prime_eq_one_of_dvd
    {p a b : ℕ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p)
    (hcop : Nat.Coprime a b)
    (hpGN : p ∣ GN p a b) :
    padicValNat p (GN p a b) = 1 := by
  have hpa : p ∣ a :=
    prime_dvd_boundary_of_dvd_GN_prime hp hpGN
  have hpb : ¬ p ∣ b := by
    have hpcopb : Nat.Coprime p b :=
      hcop.coprime_dvd_left hpa
    exact hp.coprime_iff_not_dvd.mp hpcopb
  have hpab : ¬ p ∣ a + b := by
    intro hpab
    apply hpb
    have hpba : p ∣ b + a := by
      simpa [Nat.add_comm] using hpab
    exact (Nat.dvd_add_iff_left hpa).mpr hpba
  have hpInt : Prime (p : ℤ) :=
    Nat.prime_iff_prime_int.mp hp
  have hxyInt : (p : ℤ) ∣ (a + b : ℕ) - (b : ℤ) := by
    simpa using (Int.natCast_dvd_natCast.mpr hpa)
  have hxInt : ¬ (p : ℤ) ∣ (a + b : ℕ) := by
    intro hpabInt
    apply hpab
    exact Int.natCast_dvd_natCast.mp (by simpa using hpabInt)
  have hEmultInt :
      emultiplicity (p : ℤ)
          (∑ i ∈ Finset.range p,
            ((a + b : ℕ) : ℤ) ^ i * (b : ℤ) ^ (p - 1 - i)) = 1 :=
    emultiplicity_geom_sum₂_eq_one hpInt hpOdd hxyInt hxInt
  have hCast :
      ((GN p a b : ℕ) : ℤ) =
        ∑ i ∈ Finset.range p,
          ((a + b : ℕ) : ℤ) ^ i * (b : ℤ) ^ (p - 1 - i) := by
    rw [GN_eq_geom_sum₂]
    norm_cast
  have hEmultNat : emultiplicity p (GN p a b) = 1 := by
    rw [← Int.natCast_emultiplicity, hCast]
    exact hEmultInt
  have hGN0 : GN p a b ≠ 0 := by
    intro hzero
    rw [hzero, emultiplicity_zero] at hEmultNat
    exact WithTop.top_ne_one hEmultNat
  let : Fact p.Prime := ⟨hp⟩
  simp only [← Nat.cast_inj (R := ℕ∞)]
  rw [padicValNat_eq_emultiplicity hGN0, hEmultNat]
  simp

/-- Factorization form of the odd-prime exact local GN valuation. -/
theorem factorization_GN_prime_eq_one_of_dvd
    {p a b : ℕ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p)
    (hcop : Nat.Coprime a b)
    (hpGN : p ∣ GN p a b) :
    (GN p a b).factorization p = 1 := by
  rw [Nat.factorization_def (GN p a b) hp]
  exact padicValNat_GN_prime_eq_one_of_dvd hp hpOdd hcop hpGN

/-- The canonical general `GN` polynomial specialized to exponent five. -/
theorem GN_five_eq_explicit (a b : ℕ) :
    GN 5 a b =
      a ^ 4 + 5 * a ^ 3 * b + 10 * a ^ 2 * b ^ 2 +
        10 * a * b ^ 3 + 5 * b ^ 4 := by
  rw [GN_eq_sum]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

/-- At exponent five, every non-boundary term has a visible factor of five. -/
theorem GN_five_eq_boundary_add_five_mul (a b : ℕ) :
    GN 5 a b =
      a ^ 4 +
        5 * (a ^ 3 * b + 2 * a ^ 2 * b ^ 2 + 2 * a * b ^ 3 + b ^ 4) := by
  rw [GN_five_eq_explicit]
  ring

/--
If the exponent-five GN kernel is divisible by five, then its boundary
coordinate is divisible by five.
-/
theorem five_dvd_boundary_of_dvd_GN_five
    {a b : ℕ} (h5GN : 5 ∣ GN 5 a b) :
    5 ∣ a := by
  have hGNmod : GN 5 a b % 5 = 0 :=
    Nat.mod_eq_zero_of_dvd h5GN
  have haPowMod : a ^ 4 % 5 = 0 := by
    rw [GN_five_eq_boundary_add_five_mul] at hGNmod
    simpa [Nat.add_mod] using hGNmod
  have haPow : 5 ∣ a ^ 4 :=
    Nat.dvd_iff_mod_eq_zero.mpr haPowMod
  exact Nat.prime_five.dvd_of_dvd_pow haPow

/--
After substituting a factor of five in the boundary coordinate, all terms
except `5 * b^4` have a visible factor of twenty-five.
-/
theorem GN_five_five_mul_eq_twentyFive_mul_add (k b : ℕ) :
    GN 5 (5 * k) b =
      25 * (25 * k ^ 4 + 25 * k ^ 3 * b + 10 * k ^ 2 * b ^ 2 +
        2 * k * b ^ 3) + 5 * b ^ 4 := by
  rw [GN_five_eq_explicit]
  ring

/--
For coprime boundary coordinates, divisibility by five cannot lift to
divisibility by twenty-five.
-/
theorem not_twentyFive_dvd_GN_five_of_coprime
    {a b : ℕ}
    (hcop : Nat.Coprime a b)
    (h5GN : 5 ∣ GN 5 a b) :
    ¬ 25 ∣ GN 5 a b := by
  intro h25GN
  obtain ⟨k, rfl⟩ := five_dvd_boundary_of_dvd_GN_five h5GN
  let K :=
    25 * k ^ 4 + 25 * k ^ 3 * b + 10 * k ^ 2 * b ^ 2 +
      2 * k * b ^ 3
  have hdecomp : GN 5 (5 * k) b = 25 * K + 5 * b ^ 4 := by
    simpa [K] using GN_five_five_mul_eq_twentyFive_mul_add k b
  obtain ⟨t, ht⟩ := h25GN
  have hbPow : 5 ∣ b ^ 4 := by
    refine ⟨t - K, ?_⟩
    omega
  have h5b : 5 ∣ b :=
    Nat.prime_five.dvd_of_dvd_pow hbPow
  have h5copb : Nat.Coprime 5 b :=
    hcop.coprime_dvd_left (by exact dvd_mul_right 5 k)
  exact (Nat.prime_five.coprime_iff_not_dvd.mp h5copb) h5b

/--
For coprime boundary coordinates, a factor of five in the exponent-five GN
kernel has exact p-adic valuation one.
-/
theorem padicValNat_five_GN_five_eq_one_of_dvd
    {a b : ℕ}
    (hcop : Nat.Coprime a b)
    (h5GN : 5 ∣ GN 5 a b) :
    padicValNat 5 (GN 5 a b) = 1 := by
  have hNoSquare :=
    not_twentyFive_dvd_GN_five_of_coprime hcop h5GN
  have hGN0 : GN 5 a b ≠ 0 := by
    intro hzero
    apply hNoSquare
    rw [hzero]
    exact dvd_zero 25
  have hOneLe : 1 ≤ padicValNat 5 (GN 5 a b) :=
    padicValNat_one_le_of_prime_dvd Nat.prime_five hGN0 h5GN
  have hLtTwo : padicValNat 5 (GN 5 a b) < 2 := by
    by_contra hNot
    have hTwoLe : 2 ≤ padicValNat 5 (GN 5 a b) :=
      Nat.le_of_not_gt hNot
    apply hNoSquare
    have hPowDvd :=
      (padicValNat_le_iff_dvd Nat.prime_five hGN0 2).mp hTwoLe
    norm_num at hPowDvd ⊢
    exact hPowDvd
  omega

/-- Factorization form of the exact exponent-five exceptional valuation. -/
theorem factorization_five_GN_five_eq_one_of_dvd
    {a b : ℕ}
    (hcop : Nat.Coprime a b)
    (h5GN : 5 ∣ GN 5 a b) :
    (GN 5 a b).factorization 5 = 1 := by
  rw [Nat.factorization_def (GN 5 a b) Nat.prime_five]
  exact padicValNat_five_GN_five_eq_one_of_dvd hcop h5GN

end DkMath.ABC
