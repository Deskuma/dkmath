/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PascalPrimeDial
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
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
The natural-number congruent cosmic formula as an equality in `ZMod p`.
-/
theorem prime_congruent_cosmic_formula_natCast_zmod
    {p x u : ℕ} (hp : p.Prime) :
    (((x + u) ^ p : ℕ) : ZMod p) = ((x ^ p + u : ℕ) : ZMod p) :=
  (ZMod.natCast_eq_natCast_iff _ _ _).mpr
    (prime_congruent_cosmic_formula hp)

/--
Gap compression inside the prime field itself.
-/
theorem prime_zmod_gap_compress
    {p : ℕ} (hp : p.Prime) (u : ZMod p) :
    u ^ p = u := by
  letI : Fact p.Prime := ⟨hp⟩
  exact ZMod.pow_card u

/--
Prime-field cosmic formula.

This is the same endpoint as `prime_congruent_cosmic_formula`, but stated after
moving fully into `F_p = ZMod p`.
-/
theorem prime_zmod_congruent_cosmic_formula
    {p : ℕ} (hp : p.Prime) (x u : ZMod p) :
    (x + u) ^ p = x ^ p + u := by
  letI : Fact p.Prime := ⟨hp⟩
  have h := add_pow_char x u p
  have hu : u ^ p = u := ZMod.pow_card u
  rw [hu] at h
  exact h

/--
Prime congruent cosmic formula in the prime field.

This is the finite-field observation form of

`Big = Core + Beam + GapRaw`

where the prime row kills the beam and Frobenius compresses the gap.
-/
theorem prime_field_congruent_cosmic_formula
    {p : ℕ} (hp : p.Prime) (x u : ZMod p) :
    (x + u) ^ p = x ^ p + u :=
  prime_zmod_congruent_cosmic_formula hp x u

/-!
### AKS cyclic polynomial layer

AKS then moves from `F_p[X]` to the cyclic quotient by `X^r - 1`.
At this layer, `X^r = 1`, so powers of `X` become periodic modulo `r`.
-/

/-- If `a^r = 1`, then adding `r` to an exponent does not change `a^k`. -/
theorem pow_add_period_of_pow_eq_one
    {M : Type*} [Monoid M] {a : M} {r : ℕ}
    (h : a ^ r = 1) (k : ℕ) :
    a ^ (k + r) = a ^ k := by
  rw [pow_add, h, mul_one]

/-- If `a^r = 1`, then adding any multiple of `r` to an exponent changes nothing. -/
theorem pow_add_mul_period_of_pow_eq_one
    {M : Type*} [Monoid M] {a : M} {r : ℕ}
    (h : a ^ r = 1) (k t : ℕ) :
    a ^ (k + r * t) = a ^ k := by
  rw [pow_add, pow_mul, h, one_pow, mul_one]

/-- If `a^r = 1`, then exponents reduce modulo the period `r`. -/
theorem pow_eq_pow_mod_of_pow_eq_one
    {M : Type*} [Monoid M] {a : M} {r : ℕ}
    (h : a ^ r = 1) (k : ℕ) :
    a ^ k = a ^ (k % r) := by
  conv_lhs => rw [← Nat.mod_add_div k r]
  exact pow_add_mul_period_of_pow_eq_one h (k % r) (k / r)

/-- Cyclic observation: exponents collapse to their residue modulo the period. -/
theorem cyclic_pow_eq_pow_mod_of_pow_eq_one
    {M : Type*} [Monoid M] {a : M} {r : ℕ}
    (h : a ^ r = 1) (k : ℕ) :
    a ^ k = a ^ (k % r) :=
  pow_eq_pow_mod_of_pow_eq_one h k

/-- The AKS cyclic polynomial ideal generated by `X^r - 1`. -/
noncomputable def aksCyclicIdeal (R : Type*) [CommRing R] (r : ℕ) : Ideal R[X] :=
  Ideal.span ({(X : R[X]) ^ r - 1} : Set R[X])

/-- The AKS cyclic quotient `R[X] / (X^r - 1)`. -/
abbrev AKSCyclicQuotient (R : Type*) [CommRing R] (r : ℕ) :=
  R[X] ⧸ aksCyclicIdeal R r

/-- The quotient map from polynomials to the AKS cyclic quotient. -/
noncomputable def aksQuotientMap (R : Type*) [CommRing R] (r : ℕ) :
    R[X] →+* AKSCyclicQuotient R r :=
  Ideal.Quotient.mk (aksCyclicIdeal R r)

/-- The image of polynomial `X` in the AKS cyclic quotient. -/
noncomputable def aksQuotientX (R : Type*) [CommRing R] (r : ℕ) :
    AKSCyclicQuotient R r :=
  Ideal.Quotient.mk (aksCyclicIdeal R r) (X : R[X])

/-- The image of a constant polynomial in the AKS cyclic quotient. -/
noncomputable def aksQuotientC (R : Type*) [CommRing R] (r : ℕ) (a : R) :
    AKSCyclicQuotient R r :=
  aksQuotientMap R r (C a)

/--
The AKS cyclic congruence predicate for one modulus `n`, period `r`, and
shift `a`.

It records the quotient-ring form of the AKS/Frobenius test before folding the
exponent of `X` modulo `r`.
-/
def AKSCyclicCongruenceHolds (n r a : ℕ) : Prop :=
  (aksQuotientX (ZMod n) r + aksQuotientC (ZMod n) r (a : ZMod n)) ^ n =
    aksQuotientX (ZMod n) r ^ n + aksQuotientC (ZMod n) r (a : ZMod n)

/--
The folded AKS cyclic congruence predicate.

This is the same quotient-ring test as `AKSCyclicCongruenceHolds`, but with the
right-hand `X^n` term reduced to the residue exponent `n % r`.
-/
def AKSCyclicFoldedCongruenceHolds (n r a : ℕ) : Prop :=
  (aksQuotientX (ZMod n) r + aksQuotientC (ZMod n) r (a : ZMod n)) ^ n =
    aksQuotientX (ZMod n) r ^ (n % r) + aksQuotientC (ZMod n) r (a : ZMod n)

/--
The AKS cyclic congruence predicate for every shift `a < bound`.

This is the first range-based layer: it does not choose the AKS bound yet, but
it packages the repeated shift test as one proposition.
-/
def AKSCyclicCongruenceHoldsForRange (n r bound : ℕ) : Prop :=
  ∀ a, a < bound → AKSCyclicCongruenceHolds n r a

/--
The folded AKS cyclic congruence predicate for every shift `a < bound`.

This is the range version of `AKSCyclicFoldedCongruenceHolds`, where the
right-hand exponent has already been reduced modulo `r`.
-/
def AKSCyclicFoldedCongruenceHoldsForRange (n r bound : ℕ) : Prop :=
  ∀ a, a < bound → AKSCyclicFoldedCongruenceHolds n r a

/--
A single-shift failure of the non-folded AKS cyclic congruence.

This is an observation predicate for the composite side.  It records that a
particular shift `a` breaks the expected quotient-ring identity.
-/
def AKSCyclicCongruenceFails (n r a : ℕ) : Prop :=
  ¬ AKSCyclicCongruenceHolds n r a

/--
A single-shift failure of the folded AKS cyclic congruence.

This is the folded version of `AKSCyclicCongruenceFails`, and is the more AKS
native obstruction because powers of `X` are already reduced modulo `r`.
-/
def AKSCyclicFoldedCongruenceFails (n r a : ℕ) : Prop :=
  ¬ AKSCyclicFoldedCongruenceHolds n r a

/--
There is a non-folded AKS cyclic failure witness below `bound`.

This predicate is intended for the composite side: it packages the existence of
one shift `a < bound` where the congruence fails.
-/
def ExistsAKSCyclicFailureBelow (n r bound : ℕ) : Prop :=
  ∃ a, a < bound ∧ AKSCyclicCongruenceFails n r a

/--
There is a folded AKS cyclic failure witness below `bound`.

This is the folded obstruction predicate that will be most useful when
comparing composite behavior against the prime witness theorems.
-/
def ExistsAKSCyclicFoldedFailureBelow (n r bound : ℕ) : Prop :=
  ∃ a, a < bound ∧ AKSCyclicFoldedCongruenceFails n r a

/-- The quotient map sends polynomial `X` to `aksQuotientX`. -/
theorem aksQuotientMap_X
    (R : Type*) [CommRing R] (r : ℕ) :
    aksQuotientMap R r (X : R[X]) = aksQuotientX R r := by
  rfl

/-- The quotient map sends constants to `aksQuotientC`. -/
theorem aksQuotientMap_C
    (R : Type*) [CommRing R] (r : ℕ) (a : R) :
    aksQuotientMap R r (C a) = aksQuotientC R r a := by
  rfl

/-- A polynomial power `X^k` maps to the corresponding power of the quotient `X`. -/
theorem aksQuotientMap_X_pow
    (R : Type*) [CommRing R] (r k : ℕ) :
    aksQuotientMap R r ((X : R[X]) ^ k) =
      aksQuotientX R r ^ k := by
  rw [map_pow, aksQuotientMap_X]

/-- In the cyclic quotient by `X^r - 1`, the image of `X` satisfies `X^r = 1`. -/
theorem aksQuotientX_pow_r_eq_one
    (R : Type*) [CommRing R] (r : ℕ) :
    aksQuotientX R r ^ r = 1 := by
  unfold aksQuotientX AKSCyclicQuotient aksCyclicIdeal
  rw [← map_pow]
  change Ideal.Quotient.mk (Ideal.span ({(X : R[X]) ^ r - 1} : Set R[X]))
      ((X : R[X]) ^ r) =
    Ideal.Quotient.mk (Ideal.span ({(X : R[X]) ^ r - 1} : Set R[X])) 1
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact Ideal.subset_span (by simp)

/--
In the AKS cyclic quotient, powers of the image of `X` are periodic with
period `r`.
-/
theorem aksQuotientX_pow_add_r_eq_pow
    (R : Type*) [CommRing R] (r k : ℕ) :
    aksQuotientX R r ^ (k + r) = aksQuotientX R r ^ k :=
  pow_add_period_of_pow_eq_one (aksQuotientX_pow_r_eq_one R r) k

/--
In the AKS cyclic quotient, adding any multiple of `r` to the exponent of `X`
does not change the class.
-/
theorem aksQuotientX_pow_add_mul_r_eq_pow
    (R : Type*) [CommRing R] (r k t : ℕ) :
    aksQuotientX R r ^ (k + r * t) = aksQuotientX R r ^ k :=
  pow_add_mul_period_of_pow_eq_one (aksQuotientX_pow_r_eq_one R r) k t

/-- In the AKS cyclic quotient, powers of `X` reduce to their residue exponent modulo `r`. -/
theorem aksQuotientX_pow_eq_pow_mod
    (R : Type*) [CommRing R] (r k : ℕ) :
    aksQuotientX R r ^ k = aksQuotientX R r ^ (k % r) :=
  pow_eq_pow_mod_of_pow_eq_one (aksQuotientX_pow_r_eq_one R r) k

/-- AKS cyclic observation: powers of `X` collapse to residue exponents. -/
theorem aks_cyclic_observation_X_pow_eq_pow_mod
    (R : Type*) [CommRing R] (r k : ℕ) :
    aksQuotientX R r ^ k = aksQuotientX R r ^ (k % r) :=
  aksQuotientX_pow_eq_pow_mod R r k

/--
After passing through the AKS quotient map, powers of `X` fold to residue
exponents modulo `r`.
-/
theorem aksQuotientMap_X_pow_eq_mod
    (R : Type*) [CommRing R] (r k : ℕ) :
    aksQuotientMap R r ((X : R[X]) ^ k) =
      aksQuotientMap R r ((X : R[X]) ^ (k % r)) := by
  rw [aksQuotientMap_X_pow, aksQuotientMap_X_pow]
  exact aksQuotientX_pow_eq_pow_mod R r k

/-- The quotient map sends `X + C a` to the quotient element `Xbar + Cbar a`. -/
theorem aksQuotientMap_X_add_C
    (R : Type*) [CommRing R] (r : ℕ) (a : R) :
    aksQuotientMap R r ((X : R[X]) + C a) =
      aksQuotientX R r + aksQuotientC R r a := by
  rw [map_add, aksQuotientMap_X, aksQuotientMap_C]

/--
The quotient map sends `(X + C a)^n` to the corresponding power of
`Xbar + Cbar a`.
-/
theorem aksQuotientMap_X_add_C_pow
    (R : Type*) [CommRing R] (r n : ℕ) (a : R) :
    aksQuotientMap R r (((X : R[X]) + C a) ^ n) =
      (aksQuotientX R r + aksQuotientC R r a) ^ n := by
  rw [map_pow, aksQuotientMap_X_add_C]

/--
The quotient map sends `X^n + C a` to `Xbar^n + Cbar a`.

This is the right-hand side shape used after applying the prime Frobenius
identity to `(X + C a)^p`.
-/
theorem aksQuotientMap_X_pow_add_C
    (R : Type*) [CommRing R] (r n : ℕ) (a : R) :
    aksQuotientMap R r ((X : R[X]) ^ n + C a) =
      aksQuotientX R r ^ n + aksQuotientC R r a := by
  rw [map_add, aksQuotientMap_X_pow, aksQuotientMap_C]

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

/--
The polynomial prime Frobenius identity after applying the AKS cyclic quotient
map.

This keeps the statement at the polynomial-map level before rewriting the image
as quotient elements `aksQuotientX` and `aksQuotientC`.
-/
theorem prime_aksQuotientMap_X_add_C_pow_eq
    {p r a : ℕ} (hp : p.Prime) :
    aksQuotientMap (ZMod p) r
      (((X : (ZMod p)[X]) + C (a : ZMod p)) ^ p) =
    aksQuotientMap (ZMod p) r
      ((X : (ZMod p)[X]) ^ p + C (a : ZMod p)) := by
  rw [prime_polynomial_X_add_C_pow_eq hp]

/--
Prime Frobenius inside the AKS cyclic quotient.

For prime `p`, the quotient element `Xbar + Cbar a` satisfies the same
Freshman's dream shape as the polynomial before quotienting.
-/
theorem prime_aksQuotient_X_add_C_pow_eq
    {p r a : ℕ} (hp : p.Prime) :
    (aksQuotientX (ZMod p) r + aksQuotientC (ZMod p) r (a : ZMod p)) ^ p =
      aksQuotientX (ZMod p) r ^ p +
        aksQuotientC (ZMod p) r (a : ZMod p) := by
  have h := prime_aksQuotientMap_X_add_C_pow_eq (r := r) (a := a) hp
  rw [aksQuotientMap_X_add_C_pow, aksQuotientMap_X_pow_add_C] at h
  exact h

/--
Prime Frobenius inside the AKS cyclic quotient with the exponent of `X` folded
modulo `r`.
-/
theorem prime_aksQuotient_X_add_C_pow_eq_mod
    {p r a : ℕ} (hp : p.Prime) :
    (aksQuotientX (ZMod p) r + aksQuotientC (ZMod p) r (a : ZMod p)) ^ p =
      aksQuotientX (ZMod p) r ^ (p % r) +
        aksQuotientC (ZMod p) r (a : ZMod p) := by
  rw [prime_aksQuotient_X_add_C_pow_eq hp]
  rw [aksQuotientX_pow_eq_pow_mod]

/-- Prime moduli satisfy the non-folded AKS cyclic congruence predicate. -/
theorem AKSCyclicCongruenceHolds.prime
    {p r a : ℕ} (hp : p.Prime) :
    AKSCyclicCongruenceHolds p r a := by
  unfold AKSCyclicCongruenceHolds
  exact prime_aksQuotient_X_add_C_pow_eq hp

/--
Prime AKS cyclic Frobenius observation.

This is the folded quotient-ring form used by AKS: the prime Frobenius result
and the relation `X^r = 1` combine to replace `X^p` by `X^(p % r)`.
-/
theorem prime_aks_cyclic_frobenius
    {p r a : ℕ} (hp : p.Prime) :
    (aksQuotientX (ZMod p) r + aksQuotientC (ZMod p) r (a : ZMod p)) ^ p =
      aksQuotientX (ZMod p) r ^ (p % r) +
        aksQuotientC (ZMod p) r (a : ZMod p) := by
  exact prime_aksQuotient_X_add_C_pow_eq_mod hp

/--
Alias-style theorem: every prime modulus satisfies
`AKSCyclicCongruenceHolds`.
-/
theorem prime_AKSCyclicCongruenceHolds
    {p r a : ℕ} (hp : p.Prime) :
    AKSCyclicCongruenceHolds p r a := by
  unfold AKSCyclicCongruenceHolds
  exact prime_aksQuotient_X_add_C_pow_eq hp

/--
Alias-style theorem: every prime modulus satisfies the folded AKS cyclic
congruence predicate.
-/
theorem prime_AKSCyclicFoldedCongruenceHolds
    {p r a : ℕ} (hp : p.Prime) :
    AKSCyclicFoldedCongruenceHolds p r a := by
  unfold AKSCyclicFoldedCongruenceHolds
  exact prime_aks_cyclic_frobenius hp

/-- Prime moduli satisfy the non-folded AKS cyclic congruence for every tested shift. -/
theorem AKSCyclicCongruenceHoldsForRange.prime
    {p r bound : ℕ} (hp : p.Prime) :
    AKSCyclicCongruenceHoldsForRange p r bound := by
  intro a _ha
  exact AKSCyclicCongruenceHolds.prime hp

/-- Prime moduli satisfy the folded AKS cyclic congruence for every tested shift. -/
theorem AKSCyclicFoldedCongruenceHoldsForRange.prime
    {p r bound : ℕ} (hp : p.Prime) :
    AKSCyclicFoldedCongruenceHoldsForRange p r bound := by
  intro a _ha
  exact prime_AKSCyclicFoldedCongruenceHolds hp

/--
Alias-style theorem: every prime modulus satisfies
`AKSCyclicCongruenceHoldsForRange`.
-/
theorem prime_AKSCyclicCongruenceHoldsForRange
    {p r bound : ℕ} (hp : p.Prime) :
    AKSCyclicCongruenceHoldsForRange p r bound :=
  AKSCyclicCongruenceHoldsForRange.prime hp

/--
Alias-style theorem: every prime modulus satisfies the folded AKS cyclic
congruence for every tested shift.
-/
theorem prime_AKSCyclicFoldedCongruenceHoldsForRange
    {p r bound : ℕ} (hp : p.Prime) :
    AKSCyclicFoldedCongruenceHoldsForRange p r bound :=
  AKSCyclicFoldedCongruenceHoldsForRange.prime hp

/-- Prime moduli have no non-folded AKS cyclic failure witness below any bound. -/
theorem not_exists_AKSCyclicFailureBelow_of_prime
    {p r bound : ℕ} (hp : p.Prime) :
    ¬ ExistsAKSCyclicFailureBelow p r bound := by
  rintro ⟨a, ha, hfail⟩
  exact hfail ((AKSCyclicCongruenceHoldsForRange.prime hp) a ha)

/-- Prime moduli have no folded AKS cyclic failure witness below any bound. -/
theorem not_exists_AKSCyclicFoldedFailureBelow_of_prime
    {p r bound : ℕ} (hp : p.Prime) :
    ¬ ExistsAKSCyclicFoldedFailureBelow p r bound := by
  rintro ⟨a, ha, hfail⟩
  exact hfail ((AKSCyclicFoldedCongruenceHoldsForRange.prime hp) a ha)

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

example {p : ℕ} (hp : p.Prime) (x u : ZMod p) :
    (x + u) ^ p = x ^ p + u :=
  prime_zmod_congruent_cosmic_formula hp x u

/-- Composite modulus can break the congruent cosmic formula. -/
example :
    ¬ ((1 + 1) ^ 4 ≡ 1 ^ 4 + 1 [MOD 4]) := by
  decide

/-- Another small composite failure witness. -/
example :
    ¬ ((1 + 2) ^ 4 ≡ 1 ^ 4 + 2 [MOD 4]) := by
  decide

/-- But a composite modulus may still pass for some particular witnesses. -/
example :
    (2 + 1) ^ 4 ≡ 2 ^ 4 + 1 [MOD 4] := by
  decide

example (p r k : ℕ) :
    aksQuotientX (ZMod p) r ^ (k + r) =
      aksQuotientX (ZMod p) r ^ k :=
  aksQuotientX_pow_add_r_eq_pow (ZMod p) r k

example (p r k t : ℕ) :
    aksQuotientX (ZMod p) r ^ (k + r * t) =
      aksQuotientX (ZMod p) r ^ k :=
  aksQuotientX_pow_add_mul_r_eq_pow (ZMod p) r k t

example (p r k : ℕ) :
    aksQuotientX (ZMod p) r ^ k =
      aksQuotientX (ZMod p) r ^ (k % r) :=
  aksQuotientX_pow_eq_pow_mod (ZMod p) r k

example (p r k : ℕ) :
    aksQuotientMap (ZMod p) r ((X : (ZMod p)[X]) ^ k) =
      aksQuotientMap (ZMod p) r ((X : (ZMod p)[X]) ^ (k % r)) :=
  aksQuotientMap_X_pow_eq_mod (ZMod p) r k

end samples

end NumberTheory
end DkMath
