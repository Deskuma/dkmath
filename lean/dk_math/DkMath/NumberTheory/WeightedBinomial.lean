/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.BinomialPrime

#print "file: DkMath.NumberTheory.WeightedBinomial"

namespace DkMath
namespace NumberTheory

/-!
## Weighted binomial terms

This layer separates three sources of divisibility in a binomial term:

* the coefficient `Nat.choose d k`;
* the `x`-power `x^k`;
* the `u`-power `u^(d-k)`.

It deliberately avoids expanding into a full binomial theorem bridge. That
bridge belongs to the later CFBRC/GN checkpoint.
-/

/-- The `k`-th weighted term in row `d`: `C(d,k) * x^k * u^(d-k)`. -/
def weightedBinomialTerm (d k x u : ℕ) : ℕ :=
  Nat.choose d k * x ^ k * u ^ (d - k)

/-- Divisibility coming from the binomial coefficient. -/
theorem dvd_weightedBinomialTerm_of_dvd_choose
    {q d k x u : ℕ}
    (h : q ∣ Nat.choose d k) :
    q ∣ weightedBinomialTerm d k x u := by
  unfold weightedBinomialTerm
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h (x ^ k)) (u ^ (d - k))

/-- Divisibility coming from the `x`-power. -/
theorem dvd_weightedBinomialTerm_of_dvd_x
    {q d k x u : ℕ}
    (h : q ∣ x) (hk : 0 < k) :
    q ∣ weightedBinomialTerm d k x u := by
  have hxpow : q ∣ x ^ k := h.pow hk.ne'
  unfold weightedBinomialTerm
  simpa [mul_assoc] using
    dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_left hxpow (u ^ (d - k)))
      (Nat.choose d k)

/-- Divisibility coming from the `u`-power. -/
theorem dvd_weightedBinomialTerm_of_dvd_u
    {q d k x u : ℕ}
    (h : q ∣ u) (hk : k < d) :
    q ∣ weightedBinomialTerm d k x u := by
  have hpow : q ∣ u ^ (d - k) := h.pow (Nat.sub_ne_zero_of_lt hk)
  unfold weightedBinomialTerm
  exact dvd_mul_of_dvd_right hpow (Nat.choose d k * x ^ k)

/-- In a prime row, every inner weighted term is divisible by that prime. -/
theorem prime_dvd_inner_weightedBinomialTerm
    {p k x u : ℕ}
    (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    p ∣ weightedBinomialTerm p k x u :=
  dvd_weightedBinomialTerm_of_dvd_choose
    (prime_dvd_inner_choose hp hk0 hkp)

/-- The left boundary term is `u^d`. -/
theorem weightedBinomialTerm_left
    (d x u : ℕ) :
    weightedBinomialTerm d 0 x u = u ^ d := by
  simp [weightedBinomialTerm]

/-- The right boundary term is `x^d`. -/
theorem weightedBinomialTerm_right
    (d x u : ℕ) :
    weightedBinomialTerm d d x u = x ^ d := by
  simp [weightedBinomialTerm]

end NumberTheory
end DkMath
