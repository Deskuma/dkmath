/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.PadicValNat
import Mathlib.Data.Nat.Choose.Factorization

#print "file: DkMath.Lib.NumberTheory.BinomialPrimePower"

/-!
# Prime-power Pascal rows: exact coefficient valuations

This neutral arithmetic kernel separates prime support from valuation depth.
The formulas apply to every prime, including 2 and the irregular prime 37.
They detect index divisibility, not class-group regularity. No statement here
supplies a Kummer unit criterion or an FLT contradiction.

The historical filtered and uniform beam structures stay in
`DkMath.NumberTheory.BinomialPrimePower`; its four public arithmetic names
remain compatibility wrappers for the promoted declarations below.
-/

namespace DkMath.Lib.NumberTheory

/--
[DkMath.Lib] Exact valuation of a coefficient in a prime-power Pascal row.

Promoted from `DkMath.NumberTheory.padicValNat_choose_prime_pow` (A34,
GN-LIB-003c). Mathlib's factorization theorem supplies the proof; rewriting
`Nat.factorization_def` exposes the valuation without an ABC dependency.

For `0 < k ≤ p^n`, the coefficient loses precisely the layers already in `k`:
`v_p(choose (p^n) k) = n - v_p(k)`. The subtraction is natural subtraction.
The endpoint `k = p^n` and the degenerate row `n = 0, k = 1` are included.
The nonzero index and upper bound are essential: valuation at zero is defined
as zero, so extending this identity to all indices would be incorrect.
No regularity assumption on the prime is used.
-/
theorem padicValNat_choose_prime_pow
    {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0) :
    padicValNat p (Nat.choose (p ^ n) k) = n - padicValNat p k := by
  have hfac := Nat.factorization_choose_prime_pow hp hkn hk0
  rw [Nat.factorization_def (Nat.choose (p ^ n) k) hp,
    Nat.factorization_def k hp] at hfac
  exact hfac

/--
[DkMath.Lib] Additive conservation of valuation in a prime-power row.

Promoted from `DkMath.NumberTheory.padicValNat_choose_prime_pow_add_index`.
The coefficient valuation plus the index valuation equals the row exponent.
This form avoids truncated subtraction when comparing requested divisibility
layers. Mathlib's additive factorization identity proves it directly.
In particular a row of height `n > 1` need not have uniform coefficient height:
indices divisible by `p` consume some of the available layers.
-/
theorem padicValNat_choose_prime_pow_add_index
    {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0) :
    padicValNat p (Nat.choose (p ^ n) k) + padicValNat p k = n := by
  have hfac := Nat.factorization_choose_prime_pow_add_factorization hp hkn hk0
  rw [Nat.factorization_def (Nat.choose (p ^ n) k) hp,
    Nat.factorization_def k hp] at hfac
  exact hfac

/--
[DkMath.Lib] Extract a requested prime-power divisor from a Pascal coefficient.

Promoted from `DkMath.NumberTheory.prime_power_pow_dvd_choose_of_padicValNat_index`.
The budget `r + v_p(k) ≤ n` leaves at least `r` layers in the coefficient.
The bound on `k` ensures the coefficient is nonzero, which is required by the
valuation-to-divisibility equivalence. This is a plain natural-number theorem;
filtered-beam carriers remain with the original NumberTheory owner.
-/
theorem prime_power_pow_dvd_choose_of_padicValNat_index
    {p n k r : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0)
    (hr : r + padicValNat p k ≤ n) :
    p ^ r ∣ Nat.choose (p ^ n) k := by
  have hchoose_ne : Nat.choose (p ^ n) k ≠ 0 := Nat.choose_ne_zero hkn
  have hvchoose :
      padicValNat p (Nat.choose (p ^ n) k) = n - padicValNat p k :=
    padicValNat_choose_prime_pow hp hkn hk0
  have hr_le : r ≤ padicValNat p (Nat.choose (p ^ n) k) := by
    rw [hvchoose]
    omega
  exact (DkMath.Lib.NumberTheory.padicValNat_le_iff_dvd hp hchoose_ne r).mp hr_le

/--
[DkMath.Lib] A unit index retains all `n` valuation layers.

Promoted from `DkMath.NumberTheory.prime_power_dvd_choose_of_not_dvd_index`.
When `p` does not divide the nonzero index, its valuation vanishes, so the
coefficient is divisible by `p^n`. This is a consequence of the exact formula,
not a claim that every interior coefficient has height `n`.
-/
theorem prime_power_dvd_choose_of_not_dvd_index
    {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0)
    (hpk : ¬ p ∣ k) :
    p ^ n ∣ Nat.choose (p ^ n) k := by
  have hvk : padicValNat p k = 0 :=
    (DkMath.Lib.NumberTheory.padicValNat_eq_zero_iff hp hk0).mpr hpk
  exact prime_power_pow_dvd_choose_of_padicValNat_index hp hkn hk0 (by omega)

/-! ## Textbook boundary checks

The generic endpoint has coefficient one and therefore height zero. Row one
(`n = 0`) is legal. In row four the indices 1 and 2 exhibit different heights;
thus prime-power support must not be confused with uniform depth.
-/

example {p n : ℕ} (hp : p.Prime) :
    padicValNat p (Nat.choose (p ^ n) (p ^ n)) = 0 := by
  rw [padicValNat_choose_prime_pow hp le_rfl (pow_ne_zero _ hp.ne_zero),
    padicValNat_base_pow hp.one_lt n, Nat.sub_self]

example {p : ℕ} (hp : p.Prime) :
    padicValNat p (Nat.choose (p ^ 0) 1) = 0 := by
  rw [padicValNat_choose_prime_pow (n := 0) (k := 1) hp (by simp) (by decide)]
  exact Nat.zero_sub _

example : padicValNat 2 (Nat.choose (2 ^ 2) 1) = 2 := by
  rw [padicValNat_choose_prime_pow (by decide) (by decide) (by decide)]
  simp

example : padicValNat 2 (Nat.choose (2 ^ 2) 2) = 1 := by
  rw [padicValNat_choose_prime_pow (by decide) (by decide) (by decide),
    padicValNat_base (by decide : 1 < 2)]

example : padicValNat 3 (Nat.choose (3 ^ 2) 3) + padicValNat 3 3 = 2 := by
  exact padicValNat_choose_prime_pow_add_index (by decide) (by decide) (by decide)

example : padicValNat 37 (Nat.choose (37 ^ 1) 1) = 1 := by
  rw [padicValNat_choose_prime_pow (by decide) (by decide) (by decide)]
  simp

/-- The omitted zero index really breaks the formula even in the first prime row. -/
example : padicValNat 2 (Nat.choose (2 ^ 1) 0) ≠ 1 - padicValNat 2 0 := by
  simp

example : 3 ^ 2 ∣ Nat.choose (3 ^ 2) 2 := by
  exact prime_power_dvd_choose_of_not_dvd_index (by decide) (by decide)
    (by decide) (by decide)

end DkMath.Lib.NumberTheory
