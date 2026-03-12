/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.Basic
import DkMath.CFBRC.CyclotomicProduct
import DkMath.NumberTheory.Gcd.GN

/-!
# CFBRC Bridge

`cyclotomicPrimeCore` と Zsigmondy / valuation 層（`DkMath.NumberTheory.Gcd.*`）
を接続する再利用 API。
-/

namespace DkMath.CFBRC

open DkMath.CosmicFormulaBinom

/-- `q ∤ x` のもとで、prime `q` に対する差の冪除法と core 除法は同値。 -/
theorem prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat
    {p x u q : ℕ}
    (hq : Nat.Prime q) (hq_not_dvd_x : ¬ q ∣ x) :
    q ∣ ((x + u) ^ p - u ^ p) ↔ q ∣ cyclotomicPrimeCore p x u := by
  constructor
  · intro hsub
    exact prime_dvd_cyclotomicPrimeCore_of_dvd_sub_not_dvd_left
      (p := p) (x := x) (u := u) (q := q) hq hsub hq_not_dvd_x
  · intro hcore
    have hmul : q ∣ x * cyclotomicPrimeCore p x u := dvd_mul_of_dvd_right hcore x
    simpa [sub_eq_mul_cyclotomicPrimeCore_nat p x u] using hmul

/--
public API re-export:
`u ≠ 0` の下で general `d` の divisors product shifted は `GN d x u` と一致する。
-/
theorem cyclotomicDivisorsProductShifted_eq_GN_of_ne_zero_bridge
    {R : Type _} [Field R] {d : ℕ} (hd : 0 < d)
    {x u : R} (hx : x ≠ 0) (hu : u ≠ 0) :
    cyclotomicDivisorsProductShifted d x u = GN d x u :=
  cyclotomicDivisorsProductShifted_eq_GN_of_ne_zero (R := R) hd hx hu

/--
valuation bridge（general `u` 版）:
`q ∤ x` のとき、`(x+u)^d - u^d` の `q`-進付値は `GN d x u` のそれに一致。
-/
theorem padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_boundary
    {d x u q : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hqP : Nat.Prime q) (hq_not_dvd_x : ¬ q ∣ x) :
    padicValNat q ((x + u) ^ d - u ^ d) =
      padicValNat q (GN d x u) := by
  have hval_gap :=
    DkMath.NumberTheory.Gcd.padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_gap
      (p := d) (z := x + u) (y := u) (q := q)
      hd2 (by omega) hu hqP
      (by simpa [Nat.add_sub_cancel_left] using hq_not_dvd_x)
  simpa [Nat.add_sub_cancel_left] using hval_gap

/--
valuation bridge:
`q ∤ x` のとき、`(x+u)^p - u^p` の `q`-進付値は `cyclotomicPrimeCore p x u` のそれに一致。
-/
theorem padicValNat_sub_pow_eq_padicValNat_cyclotomicPrimeCore_of_not_dvd_boundary
    {p x u q : ℕ}
    (hp2 : 2 ≤ p) (hx : 0 < x) (hu : 0 < u)
    (hqP : Nat.Prime q) (hq_not_dvd_x : ¬ q ∣ x) :
    padicValNat q ((x + u) ^ p - u ^ p) =
      padicValNat q (cyclotomicPrimeCore p x u) := by
  have hval_GN :
      padicValNat q ((x + u) ^ p - u ^ p) = padicValNat q (GN p x u) := by
    exact padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_boundary
      (d := p) (x := x) (u := u) (q := q) hp2 hx hu hqP hq_not_dvd_x
  have hcore_eq_GN : cyclotomicPrimeCore p x u = GN p x u :=
    cyclotomicPrimeCore_eq_GN_nat (p := p) (x := x) (u := u) hx
  calc
    padicValNat q ((x + u) ^ p - u ^ p) = padicValNat q (GN p x u) := hval_GN
    _ = padicValNat q (cyclotomicPrimeCore p x u) := by
      rw [hcore_eq_GN]

end DkMath.CFBRC
