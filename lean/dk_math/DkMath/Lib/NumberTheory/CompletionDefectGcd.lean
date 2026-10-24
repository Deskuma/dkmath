/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.PowerDifferenceCofactorValuation
import DkMath.Lib.NumberTheory.PowerDifferenceCofactorGcd
import DkMath.Lib.NumberTheory.PadicValNat

#print "file: DkMath.Lib.NumberTheory.CompletionDefectGcd"

/-!
# Exact gcd of an even cofactor and its completion deficit

[DkMath.Lib] GN-LIB-005c. At primitive natural coordinates, writing s=x+y,
`gcd(R_(2m),D_(2m)) = s * gcd(m,s^(2m-2))` for m>0.
The proof first reconstructs the full budget, removes the forced s factor,
and compares prime valuations only on the support of s. Two-adic LTE is
handled in the squared-base valuation owner, with its four-divisibility guard.
The final result also includes equal, reversed and primitive zero coordinates.
-/

namespace DkMath.Lib.NumberTheory

open DkMath.Lib.Cosmic

/-- [DkMath.Lib] Equal valuations on the support of a nonzero modulus give
equal gcds with that modulus. Valuations away from its prime support are
irrelevant. The nonzero guards avoid interpreting v_p(0)=0 as a factorization. -/
theorem gcd_eq_of_padicValNat_eq_on_support
    {a b c : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hv : ∀ q : ℕ, q.Prime → q ∣ c → padicValNat q a = padicValNat q b) :
    Nat.gcd a c = Nat.gcd b c := by
  apply Nat.eq_of_factorization_eq (Nat.gcd_ne_zero_left ha) (Nat.gcd_ne_zero_left hb)
  intro q
  by_cases hq : q.Prime
  · rw [Nat.factorization_gcd ha hc, Nat.factorization_gcd hb hc, Finsupp.inf_apply, Finsupp.inf_apply]
    by_cases hqc : q ∣ c
    · rw [Nat.factorization_def a hq, Nat.factorization_def b hq, hv q hq hqc]
    · simp [Nat.factorization_eq_zero_of_not_dvd hqc]
  · rw [Nat.factorization_eq_zero_of_not_prime _ hq, Nat.factorization_eq_zero_of_not_prime _ hq]

/-- [DkMath.Lib] The squared cofactor and its index have the same gcd with
every power of the sum. LTE supplies equal valuations at each relevant prime;
the support lemma then reconstructs the exact integer gcd, not just its support. -/
theorem gcd_squared_cofactor_sum_pow
    {m x y : ℕ} (hm : m ≠ 0) (hyx : y < x) (hxy : x.Coprime y) (N : ℕ) :
    Nat.gcd (powerDifferenceCofactor m (x ^ 2) (y ^ 2)) ((x + y) ^ N) =
      Nat.gcd m ((x + y) ^ N) := by
  have hx : 0 < x := by omega
  have hs : x + y ≠ 0 := by omega
  have hr : powerDifferenceCofactor m (x ^ 2) (y ^ 2) ≠ 0 := by
    have h := powerDifferenceCofactor_pos (m - 1) (x ^ 2) (y ^ 2) (pow_pos hx 2)
    simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)] using h.ne'
  apply gcd_eq_of_padicValNat_eq_on_support hr hm (pow_ne_zero N hs)
  intro q hq hqN
  exact padicValNat_squared_cofactor_of_dvd_sum hq hm hyx hxy (hq.dvd_of_dvd_pow hqN)

/-- [DkMath.Lib] Algebraic even-deficit reduction before any primitive or LTE
hypothesis. One sum factor comes from R_(2m); one comes from the budget.
Degree zero is excluded because the natural exponent n-1 is truncated. -/
theorem gcd_even_cofactor_defect_eq_mul_gcd_squared
    {m : ℕ} (hm : m ≠ 0) (x y : ℕ) :
    Nat.gcd (powerDifferenceCofactor (2 * m) x y) (completionDefect (2 * m) x y) =
      (x + y) * Nat.gcd (powerDifferenceCofactor m (x ^ 2) (y ^ 2))
        ((x + y) ^ (2 * m - 2)) := by
  rw [gcd_powerDifferenceCofactor_completionDefect_eq_gcd_budget, powerDifferenceCofactor_even]
  have he : 2 * m - 1 = (2 * m - 2) + 1 := by omega
  rw [he, pow_succ' (x + y) (2 * m - 2), Nat.gcd_mul_left]

/-- [DkMath.Lib] Exact even gcd in the ordering used for natural LTE.
No positivity of y is required; primitive zero-coordinate pairs are legal.
The common factor can exceed x+y because the index m contributes valuation. -/
theorem gcd_even_cofactor_completionDefect_of_lt
    {m x y : ℕ} (hm : m ≠ 0) (hyx : y < x) (hxy : x.Coprime y) :
    Nat.gcd (powerDifferenceCofactor (2 * m) x y) (completionDefect (2 * m) x y) =
      (x + y) * Nat.gcd m ((x + y) ^ (2 * m - 2)) := by
  rw [gcd_even_cofactor_defect_eq_mul_gcd_squared hm,
    gcd_squared_cofactor_sum_pow hm hyx hxy]

/-- [DkMath.Lib] The even-deficit gcd for all primitive natural coordinate pairs.
The strict-order case uses LTE. Reversal uses the finite-sum symmetry, while
the primitive diagonal forces x=y=1 and is evaluated directly. Thus no hidden
ordering or gap-nonzero assumption remains in this public formula. -/
theorem gcd_even_cofactor_completionDefect
    {m x y : ℕ} (hm : m ≠ 0) (hxy : x.Coprime y) :
    Nat.gcd (powerDifferenceCofactor (2 * m) x y) (completionDefect (2 * m) x y) =
      (x + y) * Nat.gcd m ((x + y) ^ (2 * m - 2)) := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · have hs := gcd_even_cofactor_completionDefect_of_lt hm hlt hxy.symm
    have hR := powerDifferenceCofactor_symm (2 * m) x y
    have hD : completionDefect (2 * m) x y = completionDefect (2 * m) y x := by
      unfold completionDefect
      rw [add_comm x y, hR]
    rw [hR, hD, add_comm x y]
    exact hs
  · subst y
    have hx : x = 1 := by simpa only [Nat.Coprime, Nat.gcd_self] using hxy
    subst x
    rw [gcd_even_cofactor_defect_eq_mul_gcd_squared hm]
    simp [powerDifferenceCofactor_diagonal]
  · exact gcd_even_cofactor_completionDefect_of_lt hm hgt hxy

/-- [DkMath.Lib] The standard even-degree presentation with the half index n/2.
Positive even n includes n=2 (D_2=0), but excludes n=0 where the displayed
formula would fail under the degree-zero convention. -/
theorem gcd_cofactor_completionDefect_of_even
    {n x y : ℕ} (hn : Even n) (hn0 : 0 < n) (hxy : x.Coprime y) :
    Nat.gcd (powerDifferenceCofactor n x y) (completionDefect n x y) =
      (x + y) * Nat.gcd (n / 2) ((x + y) ^ (n - 2)) := by
  obtain ⟨m, he⟩ := hn
  have heq : n = 2 * m := by omega
  have hm : m ≠ 0 := by omega
  rw [heq]
  simpa using gcd_even_cofactor_completionDefect (x := x) (y := y) hm hxy

/-- [DkMath.Lib] Combined odd/even deficit gcd for positive degrees at primitive
coordinates. Odd degrees retain gcd one; even degrees retain the exact half-
index contribution. No claim about new prime existence or FLT descent follows. -/
theorem gcd_cofactor_completionDefect
    {n x y : ℕ} (hn0 : 0 < n) (hxy : x.Coprime y) :
    Nat.gcd (powerDifferenceCofactor n x y) (completionDefect n x y) =
      if Odd n then 1 else (x + y) * Nat.gcd (n / 2) ((x + y) ^ (n - 2)) := by
  split_ifs with ho
  · exact (coprime_powerDifferenceCofactor_completionDefect_of_odd ho hxy).gcd_eq_one
  · exact gcd_cofactor_completionDefect_of_even (Nat.not_odd_iff_even.mp ho) hn0 hxy

/-- [DkMath.Lib] Degree zero is a separate unconditional boundary: R_0=0,
D_0=1. The positive even-degree formula must not be used for this convention. -/
@[simp] theorem gcd_zero_cofactor_completionDefect (x y : ℕ) :
    Nat.gcd (powerDifferenceCofactor 0 x y) (completionDefect 0 x y) = 1 := by simp

/-! ## Textbook values and guards -/
example : Nat.gcd (powerDifferenceCofactor 4 (5 : ℕ) 3) (completionDefect 4 5 3) = 16 := by decide
example : Nat.gcd (powerDifferenceCofactor 6 (5 : ℕ) 3) (completionDefect 6 5 3) = 8 := by decide
example : Nat.gcd (powerDifferenceCofactor 8 (5 : ℕ) 3) (completionDefect 8 5 3) = 32 := by decide
example : Nat.gcd (powerDifferenceCofactor 6 (2 : ℕ) 1) (completionDefect 6 2 1) = 9 := by decide
example : Nat.gcd (powerDifferenceCofactor 4 (3 : ℕ) 5) (completionDefect 4 3 5) = 16 := by decide
example : Nat.gcd (powerDifferenceCofactor 4 (1 : ℕ) 1) (completionDefect 4 1 1) = 4 := by decide
example : Nat.gcd (powerDifferenceCofactor 4 (1 : ℕ) 0) (completionDefect 4 1 0) = 1 := by decide
example : Nat.gcd (powerDifferenceCofactor 2 (5 : ℕ) 3) (completionDefect 2 5 3) = 8 := by decide
example : Nat.gcd (powerDifferenceCofactor 0 (5 : ℕ) 3) (completionDefect 0 5 3) = 1 ∧
    (5 + 3) * Nat.gcd (0 / 2) ((5 + 3) ^ (0 - 2)) = 8 := by decide
example : Nat.gcd (powerDifferenceCofactor 4 (6 : ℕ) 4) (completionDefect 4 6 4) ≠
    (6 + 4) * Nat.gcd 2 ((6 + 4) ^ 2) := by decide

end DkMath.Lib.NumberTheory
