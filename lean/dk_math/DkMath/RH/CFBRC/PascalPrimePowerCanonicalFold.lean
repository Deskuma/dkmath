/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalPrimePowerPHZFinite
import DkMath.NumberTheory.PrimitiveSet.VonMangoldtShadow
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.PascalPrimePowerCanonicalFold"

/-!
# Canonical prime-power labels and the finite `q` fold

This module records the arithmetic part of the PPW construction: a positive
prime-power label has one base prime and one exponent, and the corresponding
prime-power mode is the natural-label complex power.  The resulting shadow is
finite and arithmetic.  It is deliberately not identified with an analytic
von Mangoldt function, `-ζ'/ζ`, an infinite series, or RH.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet

local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Equal positive powers of primes have the same base prime. -/
theorem prime_eq_of_pow_eq_pow
    {p q a b : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (ha : 0 < a) (_hb : 0 < b) (hpow : p ^ a = q ^ b) : p = q := by
  have hp_dvd : p ∣ q ^ b := by
    rw [← hpow]
    exact dvd_pow_self p (Nat.ne_of_gt ha)
  have hpq : p ∣ q := (hp.dvd_of_dvd_pow hp_dvd)
  rcases (Nat.dvd_prime hq).mp hpq with hp_one | hp_eq
  · exact False.elim (hp.ne_one hp_one)
  · exact hp_eq

/-- A prime has injective natural powers. -/
theorem prime_pow_exponent_injective
    {p a b : ℕ} (hp : Nat.Prime p) (hpow : p ^ a = p ^ b) : a = b := by
  exact Nat.pow_right_injective hp.one_lt hpow

/-- Positive prime-power witnesses of one natural number are unique. -/
theorem primePower_witness_unique
    {p q a b n : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (ha : 0 < a) (hb : 0 < b) (hpw : n = p ^ a) (hqw : n = q ^ b) :
    p = q ∧ a = b := by
  have hbase : p = q := prime_eq_of_pow_eq_pow hp hq ha hb (hpw.symm.trans hqw)
  refine ⟨hbase, ?_⟩
  apply prime_pow_exponent_injective hp
  simpa [hbase] using hpw.symm.trans hqw

/-- The chosen base prime of a positive prime-power natural number. -/
noncomputable def primePowerBaseShadow (q : ℕ) : ℕ :=
  if hq : IsPrimePowerLabel q then Classical.choose hq else 1

/-- The finite von-Mangoldt shadow cost attached canonically to `q`. -/
noncomputable def canonicalPrimePowerShadowCost (q : ℕ) : ℝ :=
  if _hq : IsPrimePowerLabel q then
    Real.log (primePowerBaseShadow q : ℝ)
  else 0

/-! ### Canonical exponent and finite supports -/

/- The positive exponent selected together with `primePowerBaseShadow`. -/
noncomputable def primePowerExponentShadow (q : ℕ) : ℕ :=
  if hq : IsPrimePowerLabel q then
    Classical.choose (Classical.choose_spec hq)
  else 0

/- The finite `(prime, exponent-index)` support used by the PPW pair sum. -/
def pascalPrimePowerPairSupportUpTo (X : ℕ) : Finset (ℕ × ℕ) :=
  ((pascalPrimeCoordinateSupportUpTo X).product (Finset.range X)).filter
    (fun pk => pk.1 ^ (pk.2 + 1) ≤ X)

/- The finite canonical natural-label support below the cutoff. -/
noncomputable def canonicalPrimePowerSupportUpTo (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter IsPrimePowerLabel

/- The natural label represented by a PPW pair. -/
def primePowerPairLabel (pk : ℕ × ℕ) : ℕ := pk.1 ^ (pk.2 + 1)

/-- The finite canonical `q`-indexed Dirichlet polynomial. -/
noncomputable def pascalPrimePowerPHZCanonicalUpTo
    (X : ℕ) (s : ℂ) : ℂ :=
  ∑ q ∈ Finset.range (X + 1),
    (canonicalPrimePowerShadowCost q : ℂ) * ((q : ℂ) ^ (-s))

@[simp] theorem pascalPrimePowerPHZCanonicalUpTo_zero (s : ℂ) :
    pascalPrimePowerPHZCanonicalUpTo 0 s = 0 := by
  classical
  have hzero : ¬ IsPrimePowerLabel 0 := by
    rintro ⟨p, k, hp, hk, hpow⟩
    have : 0 < p ^ k := pow_pos hp.pos k
    omega
  simp [pascalPrimePowerPHZCanonicalUpTo, canonicalPrimePowerShadowCost, hzero]

end DkMath.RH.CFBRCProjection
