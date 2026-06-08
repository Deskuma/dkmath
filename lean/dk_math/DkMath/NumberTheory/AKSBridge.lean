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

/-!
### Universe-form split

The weighted row already gives

```text
(x + u)^d = u^d + positiveTail.
```

For the AKS/Frobenius bridge we also need the symmetric reading

```text
(x + u)^d = x^d + Beam + u^d,
```

where `Beam` is the inner part of the Pascal row, excluding both boundary
vertices.  The congruence target is then obtained by two independent
observations:

* `Beam = 0` modulo the chosen modulus;
* `u^d ≡ u` modulo the chosen modulus.
-/

/-- The weighted inner beam: the terms with indices `1, ..., d - 1`. -/
def weightedBinomialInnerBeamSum (d x u : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (d - 1), weightedBinomialTerm d (k + 1) x u

/--
For a positive row, the positive tail is the inner beam plus the right boundary
vertex `x^d`.
-/
theorem weightedBinomialPositiveTailSum_eq_innerBeam_add_right
    {d x u : ℕ} (hd : 0 < d) :
    weightedBinomialPositiveTailSum d x u =
      weightedBinomialInnerBeamSum d x u + x ^ d := by
  rcases Nat.exists_eq_succ_of_ne_zero hd.ne' with ⟨n, rfl⟩
  unfold weightedBinomialPositiveTailSum weightedBinomialInnerBeamSum
  rw [Finset.sum_range_succ]
  simp [weightedBinomialTerm_right]

/--
The universe-form binomial split:
`Core + Beam + Gap = x^d + Beam + u^d`.
-/
theorem add_pow_eq_right_add_innerBeam_add_left
    {d x u : ℕ} (hd : 0 < d) :
    (x + u) ^ d =
      x ^ d + weightedBinomialInnerBeamSum d x u + u ^ d := by
  rw [add_pow_eq_left_add_positiveTail,
    weightedBinomialPositiveTailSum_eq_innerBeam_add_right hd]
  omega

/-- If every inner beam term is divisible by `m`, then the whole beam is. -/
theorem dvd_weightedBinomialInnerBeamSum_of_allInnerWeightedTermDivisible
    {d m x u : ℕ}
    (h : AllInnerWeightedTermDivisible d m x u) :
    m ∣ weightedBinomialInnerBeamSum d x u := by
  unfold weightedBinomialInnerBeamSum
  refine Finset.dvd_sum ?_
  intro k hk
  have hk_lt : k + 1 < d := by
    have hk' : k < d - 1 := Finset.mem_range.mp hk
    omega
  exact h (k + 1) (Nat.succ_pos k) hk_lt

/-- Prime rows make the weighted inner beam vanish modulo the row prime. -/
theorem prime_dvd_weightedBinomialInnerBeamSum
    {p x u : ℕ} (hp : p.Prime) :
    p ∣ weightedBinomialInnerBeamSum p x u :=
  dvd_weightedBinomialInnerBeamSum_of_allInnerWeightedTermDivisible
    (prime_allInnerWeightedTermDivisible hp)

/-- Prime rows make the inner beam congruent to zero modulo the row prime. -/
theorem prime_innerBeam_modEq_zero
    {p x u : ℕ} (hp : p.Prime) :
    weightedBinomialInnerBeamSum p x u ≡ 0 [MOD p] :=
  Nat.modEq_zero_iff_dvd.mpr (prime_dvd_weightedBinomialInnerBeamSum hp)

/--
Generic congruence assembler for the universe-form split.

This is the reusable AKS-facing shape:
if the beam vanishes modulo `m` and the gap vertex satisfies `u^d ≡ u`, then
`(x + u)^d ≡ x^d + u`.
-/
theorem add_pow_modEq_right_add_u_of_innerBeam_modEq_zero_and_left_modEq
    {m d x u : ℕ} (hd : 0 < d)
    (hbeam : weightedBinomialInnerBeamSum d x u ≡ 0 [MOD m])
    (hleft : u ^ d ≡ u [MOD m]) :
    (x + u) ^ d ≡ x ^ d + u [MOD m] := by
  rw [add_pow_eq_right_add_innerBeam_add_left hd]
  have hright : x ^ d ≡ x ^ d [MOD m] := Nat.ModEq.refl _
  have hsum := (hright.add hbeam).add hleft
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsum

/--
Divisibility version of the congruence assembler.
-/
theorem add_pow_modEq_right_add_u_of_dvd_innerBeam_and_left_modEq
    {m d x u : ℕ} (hd : 0 < d)
    (hbeam : m ∣ weightedBinomialInnerBeamSum d x u)
    (hleft : u ^ d ≡ u [MOD m]) :
    (x + u) ^ d ≡ x ^ d + u [MOD m] :=
  add_pow_modEq_right_add_u_of_innerBeam_modEq_zero_and_left_modEq hd
    (Nat.modEq_zero_iff_dvd.mpr hbeam) hleft

/-- Fermat/Frobenius endpoint: in a prime modulus, `u^p ≡ u`. -/
theorem prime_pow_modEq_self
    {p u : ℕ} (hp : p.Prime) :
    u ^ p ≡ u [MOD p] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  letI : Fact p.Prime := ⟨hp⟩
  simp [Nat.cast_pow, ZMod.pow_card]

/--
Prime gap compression:
the left boundary vertex `u^p` compresses back to `u` modulo `p`.
-/
theorem prime_gap_compress_modEq
    {p u : ℕ} (hp : p.Prime) :
    u ^ p ≡ u [MOD p] :=
  prime_pow_modEq_self hp

/--
Prime-row universe-form Frobenius congruence for natural numbers.

The proof factors through the two intended components:
the inner beam is zero modulo `p`, and the left vertex satisfies
`u^p ≡ u`.
-/
theorem prime_add_pow_modEq_right_add_u
    {p x u : ℕ} (hp : p.Prime) :
    (x + u) ^ p ≡ x ^ p + u [MOD p] :=
  add_pow_modEq_right_add_u_of_dvd_innerBeam_and_left_modEq hp.pos
    (prime_dvd_weightedBinomialInnerBeamSum hp)
    (prime_pow_modEq_self hp)

/--
Prime congruent cosmic formula:
after the prime-row beam vanishes and the gap compresses, the universe-form
binomial body is congruent to `x^p + u`.
-/
theorem prime_congruent_cosmic_formula
    {p x u : ℕ} (hp : p.Prime) :
    (x + u) ^ p ≡ x ^ p + u [MOD p] :=
  add_pow_modEq_right_add_u_of_innerBeam_modEq_zero_and_left_modEq hp.pos
    (prime_innerBeam_modEq_zero hp)
    (prime_gap_compress_modEq hp)

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

example {p x u : ℕ} (hp : p.Prime) :
    (x + u) ^ p ≡ x ^ p + u [MOD p] :=
  prime_congruent_cosmic_formula hp

end samples

end NumberTheory
end DkMath
