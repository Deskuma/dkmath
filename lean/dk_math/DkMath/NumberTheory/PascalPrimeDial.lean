/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.WeightedBinomial

#print "file: DkMath.NumberTheory.PascalPrimeDial"

namespace DkMath
namespace NumberTheory

/-!
## Prime dials on Pascal rows

This file records a lightweight observation layer for Pascal's triangle.

Each coefficient `Nat.choose n k` carries a prime-by-prime height
`padicValNat p (Nat.choose n k)`.  This is the "prime dial" view: the coefficient
mass is still the ordinary binomial coefficient, while the dial height records
how many turns of the prime `p` are visible in that coefficient.

The layer is intentionally thin.  It does not introduce a new arithmetic
semantics; it exposes existing Kummer/binomial facts through names that match
the dial observation.
-/

/-- The raw mass of one Pascal coefficient. -/
def pascalCoeffMass (n k : ℕ) : ℕ :=
  Nat.choose n k

/-- The total mass of row `n`. -/
def pascalRowMass (n : ℕ) : ℕ :=
  2 ^ n

/-- The prime-dial height of one Pascal coefficient. -/
def pascalPrimeDialHeight (p n k : ℕ) : ℕ :=
  padicValNat p (pascalCoeffMass n k)

/-- All inner coefficients in a row have the same prime-dial height. -/
def UniformPrimeDialHeight (d p h : ℕ) : Prop :=
  ∀ k, 0 < k → k < d →
    pascalPrimeDialHeight p d k = h

/-- A filtered layer of indices has a uniform prime-dial height. -/
def FilteredPrimeDialHeight (d p h : ℕ) (P : ℕ → Prop) : Prop :=
  ∀ k, 0 < k → k < d → P k →
    pascalPrimeDialHeight p d k = h

/--
The coefficient masses in row `n` sum to the row mass `2^n`.

This is the mass normalization behind the relative-weight view
`Nat.choose n k / 2^n`, kept here without introducing rational or real
division.
-/
theorem pascalCoeffMass_sum_eq_rowMass
    (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), pascalCoeffMass n k) = pascalRowMass n := by
  simpa [pascalCoeffMass, pascalRowMass, weightedBinomialRowSum,
    weightedBinomialTerm] using (weightedBinomialRowSum_eq_add_pow n 1 1)

/-- Prime-dial height is the same data as the existing beam height. -/
theorem uniformPrimeDialHeight_iff_uniformBeamHeight
    {d p h : ℕ} :
    UniformPrimeDialHeight d p h ↔ UniformBeamHeight d p h := by
  rfl

/-- Filtered prime-dial height is the same data as the existing filtered beam height. -/
theorem filteredPrimeDialHeight_iff_filteredBeamHeight
    {d p h : ℕ} {P : ℕ → Prop} :
    FilteredPrimeDialHeight d p h P ↔ FilteredBeamHeight d p h P := by
  rfl

/--
Prime rows have inner dial height `1` at their own prime.
-/
theorem prime_uniformPrimeDialHeight_self
    {p : ℕ} (hp : p.Prime) :
    UniformPrimeDialHeight p p 1 :=
  (uniformPrimeDialHeight_iff_uniformBeamHeight).mpr
    (prime_uniformBeamHeight_self hp)

/--
Below row `p`, the prime `p` has dial height `0` on every inner coefficient.
-/
theorem below_prime_uniformPrimeDialHeight_zero
    {d p : ℕ} (hp : p.Prime) (hdp : d < p) :
    UniformPrimeDialHeight d p 0 :=
  (uniformPrimeDialHeight_iff_uniformBeamHeight).mpr
    (below_prime_uniformBeamHeight_zero hp hdp)

/--
Kummer's prime-power row formula in prime-dial language.

In row `p^n`, the coefficient dial height plus the dial height already present
in the index is exactly the row exponent `n`.
-/
theorem pascalPrimeDialHeight_prime_pow_add_index
    {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0) :
    pascalPrimeDialHeight p (p ^ n) k + padicValNat p k = n := by
  simpa [pascalPrimeDialHeight, pascalCoeffMass] using
    (padicValNat_choose_prime_pow_add_index hp hkn hk0)

/--
Kummer's prime-power row formula in subtractive prime-dial language.
-/
theorem pascalPrimeDialHeight_prime_pow
    {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0) :
    pascalPrimeDialHeight p (p ^ n) k = n - padicValNat p k := by
  simpa [pascalPrimeDialHeight, pascalCoeffMass] using
    (padicValNat_choose_prime_pow hp hkn hk0)

/--
In a prime-power row, indices not divisible by `p` carry the full row-exponent
dial height.
-/
theorem prime_power_unitFilteredPrimeDialHeight
    {p n : ℕ} (hp : p.Prime) :
    FilteredPrimeDialHeight (p ^ n) p n (fun k => ¬ p ∣ k) :=
  (filteredPrimeDialHeight_iff_filteredBeamHeight).mpr
    (prime_power_unitFilteredBeamHeight hp)

section samples

example {p : ℕ} (hp : p.Prime) :
    UniformPrimeDialHeight p p 1 :=
  prime_uniformPrimeDialHeight_self hp

example {d p : ℕ} (hp : p.Prime) (hdp : d < p) :
    UniformPrimeDialHeight d p 0 :=
  below_prime_uniformPrimeDialHeight_zero hp hdp

example {p n : ℕ} (hp : p.Prime) :
    FilteredPrimeDialHeight (p ^ n) p n (fun k => ¬ p ∣ k) :=
  prime_power_unitFilteredPrimeDialHeight hp

example {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0) :
    pascalPrimeDialHeight p (p ^ n) k + padicValNat p k = n :=
  pascalPrimeDialHeight_prime_pow_add_index hp hkn hk0

end samples

end NumberTheory
end DkMath
