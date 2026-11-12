/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.CompletionDefect
import DkMath.Lib.Cosmic.GNSupport
import DkMath.Lib.Cosmic.GTailBoundary

#print "file: DkMath.Lib.NumberTheory.PowerDifferenceCofactorGcd"

/-!
# Odd-degree completion deficits and coprimality

[DkMath.Lib] GN-LIB-005a translates existing GN gcd and adjacent-coprime
results, then studies the sum coordinate s=x+y. The second-order recurrence
gives R_(2k+1) ≡ (-xy)^k modulo s in every commutative ring.
Primitive coordinates make xy coprime to s, so the odd cofactor is also
coprime to s. Exact reconstruction then gives gcd(R_n,D_n)=1 over naturals.

The parity and primitive-coordinate hypotheses remain explicit. No strong
divisibility theorem, even-degree precise gcd, ABC conjecture, or FLT
contradiction is supplied by this module.
-/

namespace DkMath.Lib.NumberTheory

open DkMath.Lib.Cosmic

/-- [DkMath.Lib] A10 in cofactor coordinates: the gap gcd is carried by n.
The original `gcd_GN_eq_gcd_of_one_le` supplies the proof. Natural subtraction
needs y≤x, positive degree and primitive coordinates are retained. This gap
gcd is different from the sum gcd used in the odd-degree argument below. -/
theorem gcd_gap_powerDifferenceCofactor_eq_gcd_degree
    {n x y : ℕ} (hn : 1 ≤ n) (hyx : y ≤ x) (hxy : x.Coprime y) :
    Nat.gcd (x - y) (powerDifferenceCofactor n x y) = Nat.gcd (x - y) n := by
  rw [powerDifferenceCofactor_eq_GTail_nat_sub n x y hyx]
  exact DkMath.CosmicFormula.gcd_GN_eq_gcd_of_one_le hn
    ((Nat.coprime_sub_self_left hyx).mpr hxy)

/-- [DkMath.Lib] B04 translated into arbitrary ring cofactor coordinates.
`IsCoprime (x-y) y` is equivalent to the original coordinate primitiveness.
The GN bridge therefore needs no nonzero gap, positivity or degree bound. -/
theorem isCoprime_adjacent_powerDifferenceCofactor
    {R : Type*} [CommRing R] (n : ℕ) (x y : R) (hxy : IsCoprime x y) :
    IsCoprime (powerDifferenceCofactor n x y) (powerDifferenceCofactor (n + 1) x y) := by
  have hgap : IsCoprime (x - y) y := by
    simpa only [mul_one] using
      (IsCoprime.sub_mul_left_left_iff (x := x) (y := y) (z := 1)).mpr hxy
  rw [powerDifferenceCofactor_eq_GTail_sub, powerDifferenceCofactor_eq_GTail_sub]
  exact DkMath.NumberTheory.GapFocusing.isCoprime_adjacent_GN n (x - y) y hgap

/-- [DkMath.Lib] Adjacent natural cofactors are coprime at primitive coordinates.
Cast into integers to reuse the ring theorem; the finite-sum cast bridge
avoids an unnecessary coordinate ordering. Degrees zero and one are included. -/
theorem coprime_adjacent_powerDifferenceCofactor
    (n x y : ℕ) (hxy : x.Coprime y) :
    (powerDifferenceCofactor n x y).Coprime (powerDifferenceCofactor (n + 1) x y) := by
  apply Nat.isCoprime_iff_coprime.mp
  rw [cast_powerDifferenceCofactor, cast_powerDifferenceCofactor]
  exact isCoprime_adjacent_powerDifferenceCofactor n (x : ℤ) (y : ℤ) hxy.isCoprime

/-- [DkMath.Lib] The odd cofactor has residue (-xy)^k modulo x+y.
This divisibility identity is a ring version of a modular observation, with
no primitiveness assumption. The second-order recurrence advances by two;
its multiple of x+y disappears, leaving multiplication by -xy. -/
theorem sum_dvd_powerDifferenceCofactor_odd_sub
    {R : Type*} [CommRing R] (k : ℕ) (x y : R) :
    x + y ∣ powerDifferenceCofactor (2 * k + 1) x y - (-(x * y)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hrec := powerDifferenceCofactor_recurrence (2 * k + 1) x y
    have heq : powerDifferenceCofactor (2 * (k + 1) + 1) x y - (-(x * y)) ^ (k + 1) =
        (x + y) * powerDifferenceCofactor (2 * k + 2) x y -
          x * y * (powerDifferenceCofactor (2 * k + 1) x y - (-(x * y)) ^ k) := by
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by omega, pow_succ]
      linear_combination hrec
    rw [heq]
    exact dvd_sub (dvd_mul_right _ _) (dvd_mul_of_dvd_right ih _)

/-- [DkMath.Lib] Primitive ring coordinates give a coprime odd cofactor and sum.
Modulo x+y the residue (-xy)^k is coprime to x+y. Lifting that residue by a
multiple of the sum preserves a Bezout relation, even in rings with zero
divisors. The index 2k+1 includes degree one. -/
theorem isCoprime_sum_powerDifferenceCofactor_odd
    {R : Type*} [CommRing R] (k : ℕ) (x y : R) (hxy : IsCoprime x y) :
    IsCoprime (x + y) (powerDifferenceCofactor (2 * k + 1) x y) := by
  have hsx : IsCoprime (x + y) x := by
    simpa only [mul_one, add_comm] using hxy.symm.add_mul_left_left 1
  have hsy : IsCoprime (x + y) y := by
    simpa only [mul_one] using hxy.add_mul_left_left 1
  have hpow : IsCoprime (x + y) ((-(x * y)) ^ k) :=
    (hsx.mul_right hsy).neg_right.pow_right
  obtain ⟨a, ha⟩ := sum_dvd_powerDifferenceCofactor_odd_sub k x y
  have heq : powerDifferenceCofactor (2 * k + 1) x y = (-(x * y)) ^ k + (x + y) * a := by
    linear_combination ha
  rw [heq]
  exact hpow.add_mul_left_right a

/-- [DkMath.Lib] The natural odd sum-gcd result, obtained from the ring theorem.
The cofactor cast bridge preserves the original natural values. There is no
positivity or ordering hypothesis; primitiveness is the essential condition. -/
theorem coprime_sum_powerDifferenceCofactor_odd
    (k x y : ℕ) (hxy : x.Coprime y) :
    (x + y).Coprime (powerDifferenceCofactor (2 * k + 1) x y) := by
  apply Nat.isCoprime_iff_coprime.mp
  rw [Nat.cast_add, cast_powerDifferenceCofactor]
  exact isCoprime_sum_powerDifferenceCofactor_odd k (x : ℤ) (y : ℤ) hxy.isCoprime

/-- [DkMath.Lib] Odd-predicate interface to the natural sum-coprime theorem.
This wrapper exposes parity as a hypothesis rather than a chosen index. -/
theorem coprime_sum_powerDifferenceCofactor_of_odd
    {n x y : ℕ} (hn : Odd n) (hxy : x.Coprime y) :
    (x + y).Coprime (powerDifferenceCofactor n x y) := by
  obtain ⟨k, hk⟩ := hn
  have heq : n = 2 * k + 1 := by omega
  rw [heq]
  exact coprime_sum_powerDifferenceCofactor_odd k x y hxy

/-- [DkMath.Lib] Exact deficit reconstruction identifies the gcd for every n.
The earlier upper bound prevents natural subtraction from clipping. No parity
or primitiveness is needed for this reduction to the full power budget. -/
theorem gcd_powerDifferenceCofactor_completionDefect_eq_gcd_budget (n x y : ℕ) :
    Nat.gcd (powerDifferenceCofactor n x y) (completionDefect n x y) =
      Nat.gcd (powerDifferenceCofactor n x y) ((x + y) ^ (n - 1)) := by
  rw [← completionDefect_add_cofactor n x y, Nat.gcd_add_self_right]

/-- [DkMath.Lib] Primitive ring coordinates make an odd cofactor coprime to
its signed completion deficit. The sum-coprime theorem extends to a power;
subtracting one multiple of the cofactor leaves the Bezout relation intact.
Signed deficits may be negative, so positivity is neither assumed nor inferred. -/
theorem isCoprime_powerDifferenceCofactor_signedCompletionDefect_odd
    {R : Type*} [CommRing R] (k : ℕ) (x y : R) (hxy : IsCoprime x y) :
    IsCoprime (powerDifferenceCofactor (2 * k + 1) x y)
      (signedCompletionDefect (2 * k + 1) x y) := by
  have hc : IsCoprime (powerDifferenceCofactor (2 * k + 1) x y)
      ((x + y) ^ (2 * k + 1 - 1)) :=
    (isCoprime_sum_powerDifferenceCofactor_odd k x y hxy).symm.pow_right
  unfold signedCompletionDefect
  simpa only [mul_neg_one, ← sub_eq_add_neg] using hc.add_mul_left_right (-1)

/-- [DkMath.Lib] Primitive natural coordinates give coprime odd cofactor and
completion deficit. This uses the exact gcd reduction and the odd sum theorem.
It does not require strict positivity: degree one and primitive zero-coordinate
pairs are valid boundary cases. -/
theorem coprime_powerDifferenceCofactor_completionDefect_odd
    (k x y : ℕ) (hxy : x.Coprime y) :
    (powerDifferenceCofactor (2 * k + 1) x y).Coprime (completionDefect (2 * k + 1) x y) := by
  change Nat.gcd _ _ = 1
  rw [gcd_powerDifferenceCofactor_completionDefect_eq_gcd_budget]
  exact ((coprime_sum_powerDifferenceCofactor_odd k x y hxy).symm.pow_right _).gcd_eq_one

/-- [DkMath.Lib] Odd-predicate interface for coprime cofactor and deficit. -/
theorem coprime_powerDifferenceCofactor_completionDefect_of_odd
    {n x y : ℕ} (hn : Odd n) (hxy : x.Coprime y) :
    (powerDifferenceCofactor n x y).Coprime (completionDefect n x y) := by
  obtain ⟨k, hk⟩ := hn
  have heq : n = 2 * k + 1 := by omega
  rw [heq]
  exact coprime_powerDifferenceCofactor_completionDefect_odd k x y hxy

/-! ## Textbook examples: hypotheses and boundaries
The even example and nonprimitive example show why those two guards are not
removed from the odd primitive theorem. Separate small gcd identities are not
an even-degree classification or a general common-factor extraction theorem.
-/
example : (powerDifferenceCofactor 3 (5 : ℕ) 3).Coprime (completionDefect 3 5 3) := by
  exact coprime_powerDifferenceCofactor_completionDefect_odd 1 5 3 (by decide)
example : (powerDifferenceCofactor 3 (18 : ℕ) 1).Coprime (completionDefect 3 18 1) := by
  exact coprime_powerDifferenceCofactor_completionDefect_odd 1 18 1 (by decide)
example : (powerDifferenceCofactor 5 (1 : ℕ) 1).Coprime (completionDefect 5 1 1) := by
  exact coprime_powerDifferenceCofactor_completionDefect_odd 2 1 1 (by decide)
example : (powerDifferenceCofactor 3 (1 : ℕ) 0).Coprime (completionDefect 3 1 0) := by
  exact coprime_powerDifferenceCofactor_completionDefect_odd 1 1 0 (by decide)
example : Nat.gcd (powerDifferenceCofactor 2 (2 : ℕ) 1) (completionDefect 2 2 1) = 3 := by decide
example : Nat.gcd (powerDifferenceCofactor 4 (2 : ℕ) 1) (completionDefect 4 2 1) = 3 := by decide
example : Nat.gcd (powerDifferenceCofactor 3 (6 : ℕ) 4) (completionDefect 3 6 4) = 4 := by decide
example : (powerDifferenceCofactor 1 (6 : ℕ) 4).Coprime (completionDefect 1 6 4) := by decide
example : (powerDifferenceCofactor 0 (0 : ℕ) 0).Coprime (completionDefect 0 0 0) := by decide
example : Nat.gcd (5 - 3) (powerDifferenceCofactor 3 (5 : ℕ) 3) = Nat.gcd (5 - 3) 3 := by
  exact gcd_gap_powerDifferenceCofactor_eq_gcd_degree (by decide) (by decide) (by decide)
example : (powerDifferenceCofactor 4 (1 : ℕ) 5).Coprime (powerDifferenceCofactor 5 (1 : ℕ) 5) := by
  exact coprime_adjacent_powerDifferenceCofactor 4 1 5 (by decide)

example : IsCoprime (powerDifferenceCofactor 3 (-2 : ℤ) 3)
    (signedCompletionDefect 3 (-2 : ℤ) 3) := by
  exact isCoprime_powerDifferenceCofactor_signedCompletionDefect_odd 1 (-2) 3 (by decide)

end DkMath.Lib.NumberTheory
