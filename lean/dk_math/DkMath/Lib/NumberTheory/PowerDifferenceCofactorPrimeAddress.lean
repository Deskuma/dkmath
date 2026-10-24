/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.PrimeRatioOrder
import DkMath.Lib.NumberTheory.CyclotomicLayerValuation
import DkMath.Lib.Cosmic.PowerDifferenceCofactor

#print "file: DkMath.Lib.NumberTheory.PowerDifferenceCofactorPrimeAddress"

/-!
# Prime appearance in the whole power-difference cofactor

[DkMath.Lib] GN-LIB-006a. For a nontrivial residue ratio of order r>1, q divides
R_n exactly when r divides n. At order one the cancelled gap contains q,
so the whole cofactor instead detects q dividing n. These are whole-cofactor
criteria; a single cyclotomic layer has the different index law r*q^k.

The neutral order and valuation owners retain their historical namespaces.
This module supplies their textbook interpretation in the R_n vocabulary.
-/

namespace DkMath.Lib.NumberTheory

open DkMath.Lib.Cosmic DkMath.NumberTheory.GapFocusing

/-- [DkMath.Lib] Order one means equality of the two coordinates modulo q.
Only the denominator must be invertible. This identifies the branch in which
the gap cannot be cancelled from the power-difference divisibility test. -/
theorem primeOrder_eq_one_iff_dvd_gap {q : ℕ} [Fact q.Prime]
    (a b : ℤ) (hb : ¬ (q : ℤ) ∣ b) :
    primeOrder q a b = 1 ↔ (q : ℤ) ∣ a - b := by
  have hb0 : (b : ZMod q) ≠ 0 := fun h => hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b q).mp h)
  rw [primeOrder, orderOf_eq_one_iff, primeRatio, mul_inv_eq_one₀ hb0,
    ← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- [DkMath.Lib] Cancelling a prime-free gap gives the whole-cofactor address.
The order test for a^n-b^n is reused after the reconstruction
(a-b)R_n=a^n-b^n. All indices, including zero, are allowed. -/
theorem int_dvd_powerDifferenceCofactor_iff_primeOrder_dvd_of_gap
    {q : ℕ} [Fact q.Prime] (a b : ℤ) (n : ℕ)
    (hb : ¬ (q : ℤ) ∣ b) (hgap : ¬ (q : ℤ) ∣ a - b) :
    (q : ℤ) ∣ powerDifferenceCofactor n a b ↔ primeOrder q a b ∣ n := by
  have hp : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : q.Prime)
  rw [← int_dvd_pow_sub_pow_iff_primeOrder_dvd a b n hb,
    ← sub_mul_powerDifferenceCofactor, hp.dvd_mul, or_iff_right hgap]

/-- [DkMath.Lib] A nontrivial order supplies the prime-free-gap hypothesis.
This is the whole-cofactor law r|n, not the single-layer law n=r*q^k.
No upper bound one on the valuation at the first address is asserted. -/
theorem int_dvd_powerDifferenceCofactor_iff_primeOrder_dvd
    {q : ℕ} [Fact q.Prime] (a b : ℤ) (n : ℕ)
    (hb : ¬ (q : ℤ) ∣ b) (hr : 1 < primeOrder q a b) :
    (q : ℤ) ∣ powerDifferenceCofactor n a b ↔ primeOrder q a b ∣ n := by
  apply int_dvd_powerDifferenceCofactor_iff_primeOrder_dvd_of_gap a b n hb
  intro hgap
  have := (primeOrder_eq_one_iff_dvd_gap a b hb).mpr hgap
  omega

/-- [DkMath.Lib] Natural cofactors inherit the order criterion without ordering
the coordinates. Casting the finite sum avoids truncated natural subtraction. -/
theorem nat_dvd_powerDifferenceCofactor_iff_primeOrder_dvd
    {q : ℕ} [Fact q.Prime] (a b n : ℕ) (hb : ¬ q ∣ b)
    (hr : 1 < primeOrder q a b) :
    q ∣ powerDifferenceCofactor n a b ↔ primeOrder q a b ∣ n := by
  have hbZ : ¬ (q : ℤ) ∣ (b : ℤ) := by exact_mod_cast hb
  have h := int_dvd_powerDifferenceCofactor_iff_primeOrder_dvd (a : ℤ) (b : ℤ) n hbZ hr
  rw [← cast_powerDifferenceCofactor] at h
  simpa only [Int.natCast_dvd_natCast] using h

/-- [DkMath.Lib] The order-one branch detects the index prime itself.
Modulo q the finite sum is n*b^(n-1), because the two coordinates agree and
b is nonzero. This includes n=0 and characteristic two. It cannot be replaced
by the order-divides-index test, since order one divides every index. -/
theorem nat_dvd_powerDifferenceCofactor_iff_dvd_index_of_order_one
    {q : ℕ} [Fact q.Prime] (a b n : ℕ) (hb : ¬ q ∣ b)
    (hr : primeOrder q a b = 1) :
    q ∣ powerDifferenceCofactor n a b ↔ q ∣ n := by
  have hbZ : ¬ (q : ℤ) ∣ (b : ℤ) := by exact_mod_cast hb
  have hgap := (primeOrder_eq_one_iff_dvd_gap (a : ℤ) (b : ℤ) hbZ).mp hr
  have heq : (a : ZMod q) = (b : ZMod q) := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd ((a : ℤ) - (b : ℤ)) q).mpr hgap
    simpa only [Int.cast_sub, Int.cast_natCast, sub_eq_zero] using h
  have hb0 : (b : ZMod q) ≠ 0 := fun h => hb ((ZMod.natCast_eq_zero_iff b q).mp h)
  rw [← ZMod.natCast_eq_zero_iff, cast_powerDifferenceCofactor, heq,
    powerDifferenceCofactor_diagonal, mul_eq_zero, or_iff_left (pow_ne_zero _ hb0),
    ZMod.natCast_eq_zero_iff]

/-! ## Boundary and valuation examples
The first-address valuation can be three. Odd-prime LTE adds one layer at
 each characteristic inflation; two-adic LTE must retain its sum correction.
-/
example (n : ℕ) : 7 ∣ powerDifferenceCofactor n (18 : ℕ) 1 ↔ 3 ∣ n := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hr : primeOrder 7 (18 : ℕ) (1 : ℕ) = 3 := by
    unfold primeOrder primeRatio
    apply orderOf_eq_prime <;> norm_num <;> decide
  simpa only [hr] using nat_dvd_powerDifferenceCofactor_iff_primeOrder_dvd (q := 7)
    18 1 n (by decide) (by rw [hr]; decide)

example (n : ℕ) : 2 ∣ powerDifferenceCofactor n (3 : ℕ) 1 ↔ 2 ∣ n := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hr : primeOrder 2 3 1 = 1 :=
    (primeOrder_eq_one_iff_dvd_gap 3 1 (by decide)).mpr (by decide)
  exact nat_dvd_powerDifferenceCofactor_iff_dvd_index_of_order_one 3 1 n (by decide) hr

example (n : ℕ) : 3 ∣ powerDifferenceCofactor n (4 : ℕ) 1 ↔ 3 ∣ n := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hr : primeOrder 3 4 1 = 1 :=
    (primeOrder_eq_one_iff_dvd_gap 4 1 (by decide)).mpr (by decide)
  exact nat_dvd_powerDifferenceCofactor_iff_dvd_index_of_order_one 4 1 n (by decide) hr

example : padicValNat 2 (3 ^ 2 - 1) = 3 := by
  change padicValNat 2 (2 ^ 3) = 3
  exact padicValNat_base_pow (by decide) 3

example : padicValNat 7 (powerDifferenceCofactor 3 (18 : ℕ) 1) = 3 := by
  rw [show powerDifferenceCofactor 3 (18 : ℕ) 1 = 7 ^ 3 from by decide]
  exact padicValNat_base_pow (by decide) 3

example (k : ℕ) : padicValNat 7 (18 ^ (3 * 7 ^ k) - 1 ^ (3 * 7 ^ k)) =
    padicValNat 7 (18 ^ 3 - 1 ^ 3) + k := by
  exact padicValNat_pow_sub_pow_mul_prime_pow (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) k

example (k : ℕ) : padicValNat 2 (3 ^ (1 * 2 ^ (k + 1)) - 1 ^ (1 * 2 ^ (k + 1))) =
    padicValNat 2 (3 ^ 1 + 1 ^ 1) + padicValNat 2 (3 ^ 1 - 1 ^ 1) + k := by
  exact padicValNat_pow_sub_pow_mul_two_pow_succ (by decide) (by decide) (by decide) (by decide) k

example : ¬ 2 ∣ powerDifferenceCofactor 3 (3 : ℕ) 1 := by decide
example : 2 ∣ powerDifferenceCofactor 4 (3 : ℕ) 1 := by decide
example : ¬ 3 ∣ powerDifferenceCofactor 2 (3 : ℕ) 1 := by decide
example : 3 ∣ powerDifferenceCofactor 0 (3 : ℕ) 1 := by decide
example : ¬ 3 ∣ powerDifferenceCofactor 1 (3 : ℕ) 0 := by decide
example : powerDifferenceCofactor 0 (0 : ℕ) 0 = 0 := by simp

end DkMath.Lib.NumberTheory
