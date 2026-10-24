/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.NumberTheory.Multiplicity
import DkMath.Lib.Cosmic.PowerDifferenceCofactorArithmetic
import Mathlib.Algebra.Ring.GeomSum

#print "file: DkMath.Lib.NumberTheory.PowerDifferenceCofactorValuation"

/-!
# Exact cofactor valuations at primes of the sum coordinate

[DkMath.Lib] GN-LIB-005c. Squared bases turn x+y into a divisor of x²-y².
For odd primes the usual LTE applies. At 2, primitive odd bases give
4 | x²-y², so the stronger four-divisible difference version of LTE applies
at every positive exponent. This is how the two-adic correction is retained,
not an assumption that it vanishes for arbitrary unsquared bases.
-/

namespace DkMath.Lib.NumberTheory

open DkMath.Lib.Cosmic

/-- [DkMath.Lib] Two-adic LTE when the base difference is divisible by four.
This Nat/padicValNat adapter reuses Mathlib's integer emultiplicity theorem.
Strict ordering and a nonzero exponent ensure all finite valuations refer to
nonzero differences. It is valid for both odd and even exponents. -/
theorem padicValNat_pow_sub_pow_of_four_dvd
    {a b n : ℕ} (hab : b < a) (hn : n ≠ 0) (h4 : 4 ∣ a - b) (ha : ¬ 2 ∣ a) :
    padicValNat 2 (a ^ n - b ^ n) = padicValNat 2 (a - b) + padicValNat 2 n := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4Z : (4 : ℤ) ∣ (a : ℤ) - (b : ℤ) := by
    rw [← Nat.cast_sub hab.le]
    exact_mod_cast h4
  have haZ : ¬ (2 : ℤ) ∣ (a : ℤ) := by exact_mod_cast ha
  have hi := Int.two_pow_sub_pow' n h4Z haZ
  have he : emultiplicity 2 (a ^ n - b ^ n) =
      emultiplicity 2 (a - b) + emultiplicity 2 n := by
    have hc : ((a ^ n - b ^ n : ℕ) : ℤ) = (a : ℤ) ^ n - (b : ℤ) ^ n := by
      rw [Nat.cast_sub (Nat.pow_le_pow_left hab.le n), Nat.cast_pow, Nat.cast_pow]
    have hc0 : ((a - b : ℕ) : ℤ) = (a : ℤ) - (b : ℤ) := Nat.cast_sub hab.le
    rw [← hc, ← hc0] at hi
    exact_mod_cast hi
  simp only [← Nat.cast_inj (R := ℕ∞), Nat.cast_add]
  rw [padicValNat_eq_emultiplicity (Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_left hab hn)),
    padicValNat_eq_emultiplicity (Nat.sub_ne_zero_of_lt hab), padicValNat_eq_emultiplicity hn]
  exact he

/-- [DkMath.Lib] Valuation reconstruction for the gap times the cofactor.
No prime-support assumption on the gap is needed. Nonzero hypotheses are
proved before using multiplicativity, respecting v_p(0)=0. -/
theorem padicValNat_powerDifferenceCofactor_add_gap
    {q a b n : ℕ} [Fact q.Prime] (hab : b < a) (hn : n ≠ 0) :
    padicValNat q (powerDifferenceCofactor n a b) + padicValNat q (a - b) =
      padicValNat q (a ^ n - b ^ n) := by
  have he : powerDifferenceCofactor n a b * (a - b) = a ^ n - b ^ n :=
    geom_sum₂_mul_of_ge hab.le n
  have hd := Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_left hab hn)
  have hr : powerDifferenceCofactor n a b ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at he
    exact hd he.symm
  have hv := congrArg (padicValNat q) he
  rw [padicValNat.mul hr (Nat.sub_ne_zero_of_lt hab)] at hv
  exact hv

/-- [DkMath.Lib] Ordinary odd-prime LTE for the cofactor itself.
The gap valuation is cancelled from the exact product, leaving v_q(n). -/
theorem padicValNat_powerDifferenceCofactor_of_odd_prime
    {q a b n : ℕ} (hq : q.Prime) (hodd : Odd q) (hab : b < a) (hn : n ≠ 0)
    (hgap : q ∣ a - b) (ha : ¬ q ∣ a) :
    padicValNat q (powerDifferenceCofactor n a b) = padicValNat q n := by
  let : Fact q.Prime := ⟨hq⟩
  have hr := padicValNat_powerDifferenceCofactor_add_gap (q := q) hab hn
  have hl := padicValNat.pow_sub_pow hodd hab hgap ha hn
  omega

/-- [DkMath.Lib] The four-divisible two-adic branch for a cofactor.
The additional four-divisibility guard is essential; ordinary odd bases with
only an even gap can carry an extra sum correction. -/
theorem padicValNat_powerDifferenceCofactor_of_four_dvd
    {a b n : ℕ} (hab : b < a) (hn : n ≠ 0) (h4 : 4 ∣ a - b) (ha : ¬ 2 ∣ a) :
    padicValNat 2 (powerDifferenceCofactor n a b) = padicValNat 2 n := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr := padicValNat_powerDifferenceCofactor_add_gap (q := 2) hab hn
  have hl := padicValNat_pow_sub_pow_of_four_dvd hab hn h4 ha
  omega

/-- [DkMath.Lib] On squared primitive bases, every prime of x+y sees exactly
v_q(m) in R_m(x²,y²). At q=2, both bases are odd and their square difference
is divisible by four. Ordering is used only for the finite natural LTE proof. -/
theorem padicValNat_squared_cofactor_of_dvd_sum
    {q m x y : ℕ} (hq : q.Prime) (hm : m ≠ 0) (hyx : y < x)
    (hxy : x.Coprime y) (hqs : q ∣ x + y) :
    padicValNat q (powerDifferenceCofactor m (x ^ 2) (y ^ 2)) = padicValNat q m := by
  have hsx : (x + y).Coprime x := Nat.coprime_self_add_left.mpr hxy.symm
  have hsy : (x + y).Coprime y := Nat.coprime_add_self_left.mpr hxy
  have hqx : ¬ q ∣ x := hq.coprime_iff_not_dvd.mp (Nat.Coprime.coprime_dvd_left hqs hsx)
  have hqy : ¬ q ∣ y := hq.coprime_iff_not_dvd.mp (Nat.Coprime.coprime_dvd_left hqs hsy)
  have hsq : y ^ 2 < x ^ 2 := by nlinarith
  have hx2 : ¬ q ∣ x ^ 2 := fun h => hqx (hq.dvd_of_dvd_pow h)
  have hgap : q ∣ x ^ 2 - y ^ 2 := by
    rw [Nat.pow_two_sub_pow_two]
    exact dvd_mul_of_dvd_left hqs _
  by_cases hq2 : q = 2
  · subst q
    have hxo : Odd (x : ℤ) := by
      rw [← Int.not_even_iff_odd, even_iff_two_dvd]
      exact_mod_cast hqx
    have hyo : Odd (y : ℤ) := by
      rw [← Int.not_even_iff_odd, even_iff_two_dvd]
      exact_mod_cast hqy
    have h4Z : (4 : ℤ) ∣ (x : ℤ) ^ 2 - (y : ℤ) ^ 2 := by
      rw [Int.dvd_iff_emod_eq_zero, Int.sub_emod,
        Int.sq_emod_four_eq_one_of_odd hxo, Int.sq_emod_four_eq_one_of_odd hyo]
      decide
    have h4 : 4 ∣ x ^ 2 - y ^ 2 := by
      rw [← Int.natCast_dvd_natCast, Nat.cast_sub hsq.le, Nat.cast_pow, Nat.cast_pow]
      exact h4Z
    exact padicValNat_powerDifferenceCofactor_of_four_dvd hsq hm h4 hx2
  · exact padicValNat_powerDifferenceCofactor_of_odd_prime hq (hq.odd_of_ne_two hq2) hsq hm hgap hx2

/-- [DkMath.Lib] Exact valuation at the sum primes of an even-degree cofactor.
The sum contributes v_q(x+y), and the squared cofactor contributes v_q(m).
The formula includes q=2 and does not impose valuation one at the basic layer. -/
theorem padicValNat_even_cofactor_of_dvd_sum
    {q m x y : ℕ} (hq : q.Prime) (hm : m ≠ 0) (hyx : y < x)
    (hxy : x.Coprime y) (hqs : q ∣ x + y) :
    padicValNat q (powerDifferenceCofactor (2 * m) x y) =
      padicValNat q (x + y) + padicValNat q m := by
  let : Fact q.Prime := ⟨hq⟩
  have hs : x + y ≠ 0 := by omega
  have hr : powerDifferenceCofactor m (x ^ 2) (y ^ 2) ≠ 0 := by
    have hx : 0 < x := by omega
    have hh := powerDifferenceCofactor_pos (m - 1) (x ^ 2) (y ^ 2) (pow_pos hx 2)
    simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)] using hh.ne'
  rw [powerDifferenceCofactor_even, padicValNat.mul hs hr,
    padicValNat_squared_cofactor_of_dvd_sum hq hm hyx hxy hqs]

example : padicValNat 2 (powerDifferenceCofactor 4 (5 : ℕ) 3) = 4 := by
  have h := padicValNat_even_cofactor_of_dvd_sum Nat.prime_two (m := 2) (x := 5) (y := 3)
    (by decide) (by decide) (by decide) (by decide)
  rw [h]
  change padicValNat 2 (2 ^ 3) + padicValNat 2 2 = 4
  rw [padicValNat_base_pow (by decide), padicValNat_base (by decide)]

/-- The unsquared two-adic cofactor can carry an extra sum layer. -/
example : padicValNat 2 (powerDifferenceCofactor 2 (3 : ℕ) 1) = 2 ∧ padicValNat 2 2 = 1 := by
  constructor
  · rw [powerDifferenceCofactor_two]
    change padicValNat 2 (2 ^ 2) = 2
    exact padicValNat_base_pow (by decide) 2
  · exact padicValNat_base (by decide)

example : padicValNat 3 (powerDifferenceCofactor 6 (2 : ℕ) 1) = 2 := by
  have h := padicValNat_even_cofactor_of_dvd_sum (by decide : Nat.Prime 3)
    (m := 3) (x := 2) (y := 1) (by decide) (by decide) (by decide) (by decide)
  rw [h]
  simp only [padicValNat_base (by decide : 1 < 3)]

end DkMath.Lib.NumberTheory
