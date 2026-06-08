/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PascalPrimeDial
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Basic

#print "file: DkMath.NumberTheory.AKSBridge"

namespace DkMath
namespace NumberTheory

open Polynomial

/-!
## AKS bridge

This file records the first AKS-facing form of the Pascal/binomial layer.

AKS primality testing is built on the same binomial principle already used by
`BinomialPrimePower`: for prime `p`, the inner binomial coefficients vanish
modulo `p`, so the Frobenius shape

```text
(X + a)^p = X^p + a
```

holds over `ZMod p`.

The full AKS test also uses polynomial reduction modulo `X^r - 1` and a finite
range of shifts `a`.  This file deliberately stops before that heavier layer
and exposes the reusable prime-side bridge.
-/

/--
The inner coefficients of prime row `p` vanish in `ZMod p`.

This is the coefficient-level AKS/Frobenius input.
-/
theorem prime_inner_choose_eq_zero_zmod
    {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    ((Nat.choose p k : ℕ) : ZMod p) = 0 := by
  exact (ZMod.natCast_eq_zero_iff _ _).mpr
    (prime_dvd_inner_choose hp hk0 hkp)

/--
Prime rows make all inner Pascal coefficients disappear modulo their row prime.
-/
theorem prime_inner_pascalCoeffMass_eq_zero_zmod
    {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    ((pascalCoeffMass p k : ℕ) : ZMod p) = 0 := by
  simpa [pascalCoeffMass] using prime_inner_choose_eq_zero_zmod hp hk0 hkp

/--
Freshman's dream over `ZMod p` for a prime modulus.

This is the polynomial form of the prime-row coefficient cancellation used by
AKS before quotienting by `X^r - 1`.
-/
theorem prime_polynomial_X_add_C_pow_eq
    {p a : ℕ} (hp : p.Prime) :
    ((X : (ZMod p)[X]) + C (a : ZMod p)) ^ p =
      X ^ p + C (a : ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  have h :=
    (add_pow_char (X : (ZMod p)[X]) (C (a : ZMod p)) p)
  have hC : (C (a : ZMod p) : (ZMod p)[X]) ^ p = C (a : ZMod p) := by
    rw [← map_pow, ZMod.pow_card]
  rw [hC] at h
  exact h

/--
The same Frobenius bridge with the constant term written as `(C a)^p`.
-/
theorem prime_polynomial_X_add_C_pow_eq_pow_C
    {p a : ℕ} (hp : p.Prime) :
    ((X : (ZMod p)[X]) + C (a : ZMod p)) ^ p =
      X ^ p + (C (a : ZMod p)) ^ p := by
  letI : Fact p.Prime := ⟨hp⟩
  exact add_pow_char (X : (ZMod p)[X]) (C (a : ZMod p)) p

section samples

example {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    ((Nat.choose p k : ℕ) : ZMod p) = 0 :=
  prime_inner_choose_eq_zero_zmod hp hk0 hkp

example {p a : ℕ} (hp : p.Prime) :
    ((X : (ZMod p)[X]) + C (a : ZMod p)) ^ p =
      X ^ p + C (a : ZMod p) :=
  prime_polynomial_X_add_C_pow_eq hp

end samples

end NumberTheory
end DkMath
