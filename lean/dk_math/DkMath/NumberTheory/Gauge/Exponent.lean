/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PascalPrimeDial

#print "file: DkMath.NumberTheory.Gauge.Exponent"

/-!
# Exponent-side gauge facade

This module gives the existing Pascal prime-dial data a stable exponent-gauge
vocabulary.  Every definition below is an abbreviation or a direct theorem
bridge to the established `DkMath.NumberTheory` owners.  No second valuation,
row-support implementation, or value-side power residue is introduced here.
-/

namespace DkMath.NumberTheory.Gauge

/-! ## Definitionally thin vocabulary -/

/-- The exponent-side gauge height of one Pascal coefficient. -/
abbrev exponentGaugeHeight (p n k : ℕ) : ℕ :=
  DkMath.NumberTheory.pascalPrimeDialHeight p n k

/-- Prime-row exponent support at the row's own prime. -/
abbrev PrimeExponentGauge (p : ℕ) : Prop :=
  DkMath.NumberTheory.InnerRowSupportPrime p p

/-- Prime-power-row exponent support at its base prime and depth. -/
abbrev PrimePowerExponentGauge (p e : ℕ) : Prop :=
  DkMath.NumberTheory.PrimePowerRowSupport p e

/-! ## Prime and prime-power bridge theorems -/

/-- A prime row carries its own prime as an exponent-side support gauge. -/
theorem primeExponentGauge_of_prime
    {p : ℕ} (hp : p.Prime) :
    PrimeExponentGauge p :=
  DkMath.NumberTheory.prime_innerRowSupportPrime_self hp

/-- A prime row has uniform prime-dial height one on its inner indices. -/
theorem primeExponentGauge_uniformPrimeDialHeight
    {p : ℕ} (hp : p.Prime) :
    DkMath.NumberTheory.UniformPrimeDialHeight p p 1 :=
  DkMath.NumberTheory.prime_uniformPrimeDialHeight_self hp

/-- The prime-row height is one at each inner index. -/
theorem primeExponentGauge_height_eq_one
    {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    exponentGaugeHeight p p k = 1 :=
  primeExponentGauge_uniformPrimeDialHeight hp k hk0 hkp

/-- A prime larger than the row has zero exponent-gauge height there. -/
theorem exponentGaugeHeight_eq_zero_of_row_lt
    {p n k : ℕ} (hp : p.Prime) (hnp : n < p) :
    exponentGaugeHeight p n k = 0 :=
  DkMath.NumberTheory.pascalPrimeDialHeight_eq_zero_of_row_lt hp hnp

/-- A positive prime-power row carries its base prime as exponent support. -/
theorem primePowerExponentGauge_of_prime_of_pos
    {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    PrimePowerExponentGauge p e :=
  DkMath.NumberTheory.prime_power_rowSupport hp he

/-- Exact prime-power exponent depth, including the depth already in the index. -/
theorem exponentGaugeHeight_prime_pow_add_index
    {p e k : ℕ} (hp : p.Prime) (hke : k ≤ p ^ e) (hk0 : k ≠ 0) :
    exponentGaugeHeight p (p ^ e) k + padicValNat p k = e :=
  DkMath.NumberTheory.pascalPrimeDialHeight_prime_pow_add_index hp hke hk0

/-- A `p`-unit index in a prime-power row carries the full exponent depth. -/
theorem exponentGaugeHeight_prime_pow_of_not_dvd
    {p e k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hke : k < p ^ e)
    (hpk : ¬ p ∣ k) :
    exponentGaugeHeight p (p ^ e) k = e := by
  exact
    (DkMath.NumberTheory.prime_power_unitFilteredPrimeDialHeight hp)
      k hk0 hke hpk

end DkMath.NumberTheory.Gauge

#print axioms DkMath.NumberTheory.Gauge.primeExponentGauge_of_prime
#print axioms DkMath.NumberTheory.Gauge.primeExponentGauge_uniformPrimeDialHeight
#print axioms DkMath.NumberTheory.Gauge.primeExponentGauge_height_eq_one
#print axioms DkMath.NumberTheory.Gauge.exponentGaugeHeight_eq_zero_of_row_lt
#print axioms DkMath.NumberTheory.Gauge.primePowerExponentGauge_of_prime_of_pos
#print axioms DkMath.NumberTheory.Gauge.exponentGaugeHeight_prime_pow_add_index
#print axioms DkMath.NumberTheory.Gauge.exponentGaugeHeight_prime_pow_of_not_dvd
