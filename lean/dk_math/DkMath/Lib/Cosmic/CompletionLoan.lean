/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.PowerDifferenceCofactorStrongDivisibility

#print "file: DkMath.Lib.Cosmic.CompletionLoan"

/-!
# Borrowed completion and primitive additive triples

[DkMath.Lib] GN-LIB-005b. For n≥3 the second-order identity is
R_n + xy R_(n-2) = (x+y) R_(n-1). Its common factor h_n is 1 in odd
degree and x+y in even degree at primitive coordinates. This file proves
that exact gcd before dividing all three numerators by h_n.

The resulting positive pairwise-coprime A+B=C is an arithmetic triple;
no radical bound or ABC conjecture is claimed. The borrowed correction
xy R_(n-2) remains distinct from the completion deficit D_n.
-/

namespace DkMath.Lib.Cosmic

open DkMath.Lib.NumberTheory

/-- [DkMath.Lib] The parity-dependent common factor for borrowed completion.
The even branch is x+y and the odd branch is 1. The exact-gcd theorem below
requires primitive coordinates and n≥2; no exactness is implicit in the definition. -/
def completionLoanFactor (n x y : ℕ) : ℕ := if n % 2 = 0 then x + y else 1

/-- [DkMath.Lib] Normalized first numerator R_n/h_n. -/
def completionLoanA (n x y : ℕ) : ℕ := powerDifferenceCofactor n x y / completionLoanFactor n x y

/-- [DkMath.Lib] Normalized borrowed correction xy R_(n-2)/h_n. -/
def completionLoanB (n x y : ℕ) : ℕ :=
  (x * y * powerDifferenceCofactor (n - 2) x y) / completionLoanFactor n x y

/-- [DkMath.Lib] Normalized completed numerator (x+y)R_(n-1)/h_n. -/
def completionLoanC (n x y : ℕ) : ℕ :=
  ((x + y) * powerDifferenceCofactor (n - 1) x y) / completionLoanFactor n x y

/-- [DkMath.Lib] The second-order recurrence at a natural degree with explicit
subtraction guards. No primitiveness is needed for the numerator identity. -/
theorem completionLoan_numerators_add {n : ℕ} (hn : 2 ≤ n) (x y : ℕ) :
    powerDifferenceCofactor n x y + x * y * powerDifferenceCofactor (n - 2) x y =
      (x + y) * powerDifferenceCofactor (n - 1) x y := by
  simpa only [Nat.sub_add_cancel hn, show n - 2 + 1 = n - 1 from by omega] using
    powerDifferenceCofactor_recurrence (n - 2) x y

/-- [DkMath.Lib] The parity factor is exactly the gcd of the first two numerators.
Strong divisibility reduces the gcd to R_gcd(n-2,2). Reducing the index modulo
2 yields R_1=1 or R_2=x+y. This is the gcd with the borrowed correction,
not an even-degree formula for gcd(R_n,D_n). -/
theorem completionLoanFactor_eq_gcd {n x y : ℕ} (hn : 2 ≤ n) (hxy : x.Coprime y) :
    completionLoanFactor n x y =
      Nat.gcd (powerDifferenceCofactor n x y) (x * y * powerDifferenceCofactor (n - 2) x y) := by
  have hg : Nat.gcd (n - 2) 2 = if n % 2 = 0 then 2 else 1 := by
    rw [Nat.gcd_comm, Nat.gcd_rec]
    have hm : (n - 2) % 2 = n % 2 := by omega
    rw [hm]
    split_ifs with he
    · simp [he]
    · have hm1 : n % 2 = 1 := by omega
      simp [hm1]
  have hl := gcd_powerDifferenceCofactor_loan (n - 2) x y hxy
  rw [Nat.sub_add_cancel hn] at hl
  rw [hl, hg]
  unfold completionLoanFactor
  split_ifs <;> simp_all

/-- [DkMath.Lib] A positive coordinate makes the parity factor positive.
This guard excludes the zero denominator in the even branch. -/
theorem completionLoanFactor_pos (n x y : ℕ) (hx : 0 < x) :
    0 < completionLoanFactor n x y := by
  unfold completionLoanFactor
  split_ifs <;> omega

/-- [DkMath.Lib] All three numerators are divisible by the exact parity factor.
The third divisibility follows from the numerator identity, so normalization
never discards a remainder under these hypotheses. -/
theorem completionLoanFactor_dvd_numerators {n x y : ℕ}
    (hn : 2 ≤ n) (hxy : x.Coprime y) :
    completionLoanFactor n x y ∣ powerDifferenceCofactor n x y ∧
    completionLoanFactor n x y ∣ x * y * powerDifferenceCofactor (n - 2) x y ∧
    completionLoanFactor n x y ∣ (x + y) * powerDifferenceCofactor (n - 1) x y := by
  have ha : completionLoanFactor n x y ∣ powerDifferenceCofactor n x y := by
    rw [completionLoanFactor_eq_gcd hn hxy]
    exact Nat.gcd_dvd_left _ _
  have hb : completionLoanFactor n x y ∣ x * y * powerDifferenceCofactor (n - 2) x y := by
    rw [completionLoanFactor_eq_gcd hn hxy]
    exact Nat.gcd_dvd_right _ _
  exact ⟨ha, hb, (completionLoan_numerators_add hn x y) ▸ dvd_add ha hb⟩

/-- [DkMath.Lib] Multiplying each normalized quantity by h_n recovers its full
numerator. These equalities explicitly retain the common factor, rather than
silently treating a divided expression as the original cofactor. -/
theorem completionLoan_reconstruct {n x y : ℕ} (hn : 2 ≤ n) (hxy : x.Coprime y) :
    completionLoanA n x y * completionLoanFactor n x y = powerDifferenceCofactor n x y ∧
    completionLoanB n x y * completionLoanFactor n x y =
      x * y * powerDifferenceCofactor (n - 2) x y ∧
    completionLoanC n x y * completionLoanFactor n x y =
      (x + y) * powerDifferenceCofactor (n - 1) x y := by
  obtain ⟨ha, hb, hc⟩ := completionLoanFactor_dvd_numerators hn hxy
  exact ⟨Nat.div_mul_cancel ha, Nat.div_mul_cancel hb, Nat.div_mul_cancel hc⟩

/-- [DkMath.Lib] The exact normalization preserves A+B=C.
The positive factor permits cancellation only after all three numerators
have been reconstructed. No rational division is used. -/
theorem completionLoan_add {n x y : ℕ} (hn : 2 ≤ n) (hx : 0 < x) (hxy : x.Coprime y) :
    completionLoanA n x y + completionLoanB n x y = completionLoanC n x y := by
  obtain ⟨ha, hb, hc⟩ := completionLoan_reconstruct hn hxy
  have hp := completionLoanFactor_pos n x y hx
  have he := completionLoan_numerators_add hn x y
  nlinarith

/-- [DkMath.Lib] All normalized entries are positive for n≥3 and positive bases.
Divisibility bounds the denominator by each positive numerator. The strict
positivity of xy R_(n-2) explains why degree two is excluded here. -/
theorem completionLoan_pos {n x y : ℕ} (hn : 3 ≤ n) (hx : 0 < x) (hy : 0 < y)
    (hxy : x.Coprime y) :
    0 < completionLoanA n x y ∧ 0 < completionLoanB n x y ∧ 0 < completionLoanC n x y := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨hda, hdb, _⟩ := completionLoanFactor_dvd_numerators hn2 hxy
  have hp := completionLoanFactor_pos n x y hx
  have hra : 0 < powerDifferenceCofactor n x y := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using powerDifferenceCofactor_pos (n - 1) x y hx
  have hrb : 0 < powerDifferenceCofactor (n - 2) x y := by
    simpa only [show n - 3 + 1 = n - 2 from by omega] using powerDifferenceCofactor_pos (n - 3) x y hx
  have ha : 0 < completionLoanA n x y := Nat.div_pos (Nat.le_of_dvd hra hda) hp
  have hb : 0 < completionLoanB n x y :=
    Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos (Nat.mul_pos hx hy) hrb) hdb) hp
  have he := completionLoan_add hn2 hx hxy
  exact ⟨ha, hb, by omega⟩

/-- [DkMath.Lib] Exact gcd normalization gives pairwise-coprime entries.
First A and B are coprime because the denominator is their numerator gcd.
Then the proven sum identity transports that coprimality to A,C and B,C. -/
theorem completionLoan_pairwise_coprime {n x y : ℕ}
    (hn : 2 ≤ n) (hx : 0 < x) (hxy : x.Coprime y) :
    (completionLoanA n x y).Coprime (completionLoanB n x y) ∧
    (completionLoanB n x y).Coprime (completionLoanC n x y) ∧
    (completionLoanA n x y).Coprime (completionLoanC n x y) := by
  have hh := completionLoanFactor_eq_gcd hn hxy
  have hp := completionLoanFactor_pos n x y hx
  have hab : (completionLoanA n x y).Coprime (completionLoanB n x y) := by
    unfold completionLoanA completionLoanB
    rw [hh]
    exact Nat.coprime_div_gcd_div_gcd (by rw [← hh]; exact hp)
  have he := completionLoan_add hn hx hxy
  refine ⟨hab, ?_, ?_⟩
  · rw [← he]
    exact Nat.coprime_add_self_right.mpr hab.symm
  · rw [← he]
    exact Nat.coprime_self_add_right.mpr hab

/-- [DkMath.Lib] The constructed normalized entries form a positive primitive
additive triple. This endpoint packages the reconstruction, positivity and
coprimality pipeline; it asserts no radical inequality or FLT descent. -/
theorem completionLoan_primitive_triple {n x y : ℕ}
    (hn : 3 ≤ n) (hx : 0 < x) (hy : 0 < y) (hxy : x.Coprime y) :
    0 < completionLoanA n x y ∧ 0 < completionLoanB n x y ∧ 0 < completionLoanC n x y ∧
    completionLoanA n x y + completionLoanB n x y = completionLoanC n x y ∧
    (completionLoanA n x y).Coprime (completionLoanB n x y) ∧
    (completionLoanB n x y).Coprime (completionLoanC n x y) ∧
    (completionLoanA n x y).Coprime (completionLoanC n x y) := by
  obtain ⟨ha, hb, hc⟩ := completionLoan_pos hn hx hy hxy
  obtain ⟨hab, hbc, hac⟩ := completionLoan_pairwise_coprime (n := n) (by omega) hx hxy
  exact ⟨ha, hb, hc, completionLoan_add (by omega) hx hxy, hab, hbc, hac⟩

/-! ## Textbook examples
The even row divides all numerators by x+y=8. The odd row leaves them intact.
Positive primitive bases need not be ordered; degree two has B=0 and hence
is outside the positive-triple theorem, though reconstruction still holds.
-/
example : (completionLoanA 3 5 3, completionLoanB 3 5 3, completionLoanC 3 5 3) =
    (49, 15, 64) := by decide
example : (completionLoanA 4 5 3, completionLoanB 4 5 3, completionLoanC 4 5 3) =
    (34, 15, 49) := by decide
example : (completionLoanA 6 5 3, completionLoanB 6 5 3, completionLoanC 6 5 3) =
    (931, 510, 1441) := by decide
example : completionLoanFactor 4 5 3 = 8 := by decide
example : completionLoanB 2 5 3 = 0 := by decide
example : (completionLoanA 3 1 2, completionLoanB 3 1 2, completionLoanC 3 1 2) =
    (7, 2, 9) := by decide

example : Nat.gcd (completionLoanA 3 6 4) (completionLoanB 3 6 4) = 4 := by decide
example : completionLoanB 3 1 0 = 0 := by decide
example : (completionLoanA 3 18 1, completionLoanB 3 18 1, completionLoanC 3 18 1) =
    (343, 18, 361) := by decide

end DkMath.Lib.Cosmic
