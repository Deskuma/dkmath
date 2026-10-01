/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Core
import DkMath.FLT.Prime.AdicPowerSplit

#print "file: DkMath.FLT.Prime.CounterexampleRouting"

/-!
# Generic odd-prime counterexample routing

This module exposes the front-end boundary of the generic prime-adic chain.
The primitive counterexample carries no divisibility choice for `z - y`.
The two possible gap branches are then recorded explicitly:

* the gap-divisible branch enters `PrimeAdicFactorPacket`;
* the away branch yields the coprime factor split into two `p`-th powers.

Neither branch is treated as a contradiction here.  In particular, this is
not a general FLT theorem and does not assert a generic coordinate permutation.
-/

namespace DkMath.FLT.Prime

open DkMath.CosmicFormula

/-! ## Primitive positive input -/

/-- A primitive positive odd-prime FLT counterexample before gap routing. -/
structure PrimitivePrimeCounterexample (p x y z : ℕ) : Prop where
  prime : Nat.Prime p
  odd : 3 ≤ p
  x_pos : 0 < x
  y_pos : 0 < y
  z_pos : 0 < z
  coprime_x_y : Nat.Coprime x y
  equation : x ^ p + y ^ p = z ^ p

namespace PrimitivePrimeCounterexample

/-- Positivity of the left summand forces `y < z`. -/
theorem y_lt_z {p x y z : ℕ} (P : PrimitivePrimeCounterexample p x y z) :
    y < z := by
  have hxpow : 0 < x ^ p := pow_pos P.x_pos p
  have hEq := P.equation
  have hpow : y ^ p < z ^ p := by
    omega
  exact (Nat.pow_lt_pow_iff_left P.prime.ne_zero).mp hpow

/-- The gap `z - y` is positive. -/
theorem gap_pos {p x y z : ℕ} (P : PrimitivePrimeCounterexample p x y z) :
    0 < z - y :=
  Nat.sub_pos_of_lt P.y_lt_z

/-- A primitive counterexample has coprime right-hand coordinates. -/
theorem coprime_y_z {p x y z : ℕ} (P : PrimitivePrimeCounterexample p x y z) :
    Nat.Coprime y z := by
  refine (Nat.coprime_iff_gcd_eq_one).2 ?_
  by_contra hg
  have hg_ne_one : Nat.gcd y z ≠ 1 := by
    simpa using hg
  rcases Nat.exists_prime_and_dvd (n := Nat.gcd y z) hg_ne_one with
    ⟨q, hq, hqgcd⟩
  have hqy : q ∣ y := hqgcd.trans (Nat.gcd_dvd_left y z)
  have hqz : q ∣ z := hqgcd.trans (Nat.gcd_dvd_right y z)
  have hqyp : q ∣ y ^ p := hqy.trans (dvd_pow_self y P.prime.ne_zero)
  have hqzp : q ∣ z ^ p := hqz.trans (dvd_pow_self z P.prime.ne_zero)
  have hqxpow : q ∣ x ^ p := by
    have hqsum : q ∣ x ^ p + y ^ p := by
      rw [P.equation]
      exact hqzp
    exact (Nat.dvd_add_left hqyp).mp hqsum
  have hqx : q ∣ x := hq.dvd_of_dvd_pow hqxpow
  exact (Nat.not_coprime_of_dvd_of_dvd hq.one_lt hqx hqy) P.coprime_x_y

/-- The gap is coprime to the second coordinate. -/
theorem coprime_gap_y {p x y z : ℕ} (P : PrimitivePrimeCounterexample p x y z) :
    Nat.Coprime (z - y) y := by
  have hyz : y ≤ z := P.y_lt_z.le
  have h := (Nat.coprime_sub_self_right hyz).2 P.coprime_y_z
  simpa [Nat.coprime_comm] using h

/-- The FLT equation in the normalized `gap * GTail` form. -/
theorem gap_mul_GTail_eq {p x y z : ℕ}
    (P : PrimitivePrimeCounterexample p x y z) :
    (z - y) * GTail p 1 (z - y) y = x ^ p := by
  exact (DkMath.pow_eq_sub_mul_GN_of_add_pow_eq
    p x y z P.y_lt_z.le P.equation).symm

end PrimitivePrimeCounterexample

/-! ## The gap-divisible branch -/

/-- The exact front door from a gap-divisible counterexample to the generic packet. -/
theorem primeAdicFactorPacket_of_counterexample_of_prime_dvd_gap
    {p x y z : ℕ}
    (P : PrimitivePrimeCounterexample p x y z)
    (hgap : p ∣ z - y) :
    PrimeAdicFactorPacket p (z - y) y x :=
  { prime := P.prime
    odd := P.odd
    gap_pos := P.gap_pos
    distinguished_pos := P.x_pos
    coprime_gap_unit := P.coprime_gap_y
    prime_dvd_gap := hgap
    factor_eq := P.gap_mul_GTail_eq }

/-! ## The away branch -/

/-- In the away branch, the two normalized factors are coprime. -/
theorem away_branch_coprime_gap_GTail
    {p x y z : ℕ}
    (P : PrimitivePrimeCounterexample p x y z)
    (hgap : ¬ p ∣ z - y) :
    Nat.Coprime (z - y) (GTail p 1 (z - y) y) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  exact DkMath.CosmicFormula.gcd_GN_prime_eq_one_of_not_dvd
    P.prime P.coprime_gap_y hgap

/-- The away branch splits the gap and normalized residual into `p`-th powers. -/
theorem away_branch_power_factor_split
    {p x y z : ℕ}
    (P : PrimitivePrimeCounterexample p x y z)
    (hgap : ¬ p ∣ z - y) :
    (∃ a : ℕ, z - y = a ^ p) ∧
      (∃ b : ℕ, GTail p 1 (z - y) y = b ^ p) := by
  exact DkMath.Lib.NumberTheory.power_factor_split
    (away_branch_coprime_gap_GTail P hgap) P.gap_mul_GTail_eq

/-! ## Honest route sum -/

/-- The exact two-branch routing of a primitive odd-prime counterexample. -/
inductive PrimeCounterexampleRoute (p x y z : ℕ) : Prop
  | away
      (hgap : ¬ p ∣ z - y)
      (gapPow : ∃ a : ℕ, z - y = a ^ p)
      (residualPow : ∃ b : ℕ, GTail p 1 (z - y) y = b ^ p)
  | ramified
      (packet : PrimeAdicFactorPacket p (z - y) y x)

/-- Every primitive input is routed without hiding the branch condition. -/
theorem counterexampleRoute_of_primitive
    {p x y z : ℕ} (P : PrimitivePrimeCounterexample p x y z) :
    PrimeCounterexampleRoute p x y z := by
  by_cases hgap : p ∣ z - y
  · exact .ramified (primeAdicFactorPacket_of_counterexample_of_prime_dvd_gap P hgap)
  · rcases away_branch_power_factor_split P hgap with ⟨hgapPow, hresidualPow⟩
    exact .away hgap hgapPow hresidualPow

end DkMath.FLT.Prime
