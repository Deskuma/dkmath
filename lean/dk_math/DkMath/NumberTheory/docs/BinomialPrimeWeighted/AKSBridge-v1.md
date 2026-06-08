# AKSBridge v1

## Position

`DkMath.NumberTheory.AKSBridge` records the first bridge from the
Pascal/binomial prime-row layer to the AKS cyclic quotient layer.

The goal is not to implement the full AKS primality test yet.  The goal of this
v1 layer is to make the prime-side mechanism explicit:

```text
Pascal prime row
  → beam vanishing
  → Frobenius / gap compression
  → polynomial Frobenius
  → quotient by X^r - 1
  → exponent folding modulo r
```

This gives a reusable Lean route from the weighted universe formula to the AKS
cyclic observation.

## 1. Pascal Prime Row

The starting point is the existing Pascal prime-row theorem:

```text
If p is prime, then every inner coefficient in row p is divisible by p.
```

In Lean this is already available through the `BinomialPrime` and
`WeightedBinomial` layers, and appears in `AKSBridge` as coefficient and
weighted-term cancellation.

Important forms:

```lean
theorem prime_inner_choose_eq_zero_zmod
theorem prime_inner_pascalCoeffMass_eq_zero_zmod
theorem prime_dvd_weightedBinomialInnerBeamSum
theorem prime_innerBeam_modEq_zero
```

Meaning:

```text
The inner beam of row p disappears modulo p.
```

## 2. Weighted Universe Split

`AKSBridge` introduces the inner beam of the weighted binomial row:

```lean
def weightedBinomialInnerBeamSum
```

This separates the two boundary vertices from the inner terms:

```text
(x + u)^d = x^d + Beam + u^d
```

Important theorem:

```lean
theorem add_pow_eq_right_add_innerBeam_add_left
```

This is the universe-form reading used by the later congruence layer.

## 3. Congruent Cosmic Formula

The congruent cosmic formula is obtained by combining two independent facts:

```text
Beam ≡ 0 [MOD p]
u^p ≡ u [MOD p]
```

Therefore:

```text
(x + u)^p ≡ x^p + u [MOD p]
```

Important Lean names:

```lean
theorem prime_innerBeam_modEq_zero
theorem prime_gap_compress_modEq
theorem prime_congruent_cosmic_formula
```

This layer keeps the formula on `ℕ` using `Nat.ModEq`.

## 4. Finite-Field Form

The same statement is then moved into the prime field `ZMod p`.

```text
(x + u)^p = x^p + u
```

Important Lean names:

```lean
theorem prime_congruent_cosmic_formula_natCast_zmod
theorem prime_zmod_gap_compress
theorem prime_zmod_congruent_cosmic_formula
theorem prime_field_congruent_cosmic_formula
```

This is the finite-field form of the same beam-vanishing and gap-compression
principle.

## 5. Polynomial Frobenius

The finite-field Frobenius form is lifted to polynomials over `ZMod p`:

```text
(X + C a)^p = X^p + C a
```

Important Lean names:

```lean
theorem prime_polynomial_X_add_C_pow_eq
theorem prime_polynomial_X_add_C_pow_eq_pow_C
```

This is the polynomial shape used before passing to the AKS quotient.

## 6. AKS Cyclic Quotient

AKS works modulo the polynomial relation:

```text
X^r = 1
```

This is represented by the cyclic quotient:

```text
R[X] / (X^r - 1)
```

Important Lean names:

```lean
noncomputable def aksCyclicIdeal
abbrev AKSCyclicQuotient
noncomputable def aksQuotientMap
noncomputable def aksQuotientX
noncomputable def aksQuotientC
```

The name uses `Cyclic`, not `Cyclotomic`, to avoid confusion with cyclotomic
polynomials and existing `DkMath` cyclotomic APIs.

The quotient gives:

```text
X^r = 1
X^(k + r * t) = X^k
X^k = X^(k % r)
```

Important Lean names:

```lean
theorem aksQuotientX_pow_r_eq_one
theorem aksQuotientX_pow_add_r_eq_pow
theorem aksQuotientX_pow_add_mul_r_eq_pow
theorem aksQuotientX_pow_eq_pow_mod
theorem aks_cyclic_observation_X_pow_eq_pow_mod
```

The generic monoid versions are also recorded:

```lean
theorem pow_add_period_of_pow_eq_one
theorem pow_add_mul_period_of_pow_eq_one
theorem pow_eq_pow_mod_of_pow_eq_one
theorem cyclic_pow_eq_pow_mod_of_pow_eq_one
```

## 7. Prime AKS Cyclic Frobenius

The polynomial Frobenius identity is pushed through the quotient map:

```text
overline{(X + C a)^p} = overline{X^p + C a}
```

Then the quotient elements rewrite this as:

```text
(Xbar + abar)^p = Xbar^p + abar
```

Finally, the cyclic relation folds the exponent:

```text
(Xbar + abar)^p = Xbar^(p % r) + abar
```

Important Lean names:

```lean
theorem aksQuotientMap_X_add_C
theorem aksQuotientMap_X_add_C_pow
theorem aksQuotientMap_X_pow_add_C
theorem prime_aksQuotientMap_X_add_C_pow_eq
theorem prime_aksQuotient_X_add_C_pow_eq
theorem prime_aksQuotient_X_add_C_pow_eq_mod
theorem prime_aks_cyclic_frobenius
```

This is the main v1 AKS cyclic Frobenius endpoint.

## 8. Predicate Layer

The implementation also introduces predicate names for the AKS cyclic
congruence shape.

Non-folded predicate:

```lean
def AKSCyclicCongruenceHolds
```

Meaning:

```text
(Xbar + abar)^n = Xbar^n + abar
```

Folded predicate:

```lean
def AKSCyclicFoldedCongruenceHolds
```

Meaning:

```text
(Xbar + abar)^n = Xbar^(n % r) + abar
```

Prime witnesses:

```lean
theorem AKSCyclicCongruenceHolds.prime
theorem prime_AKSCyclicCongruenceHolds
theorem prime_AKSCyclicFoldedCongruenceHolds
```

These theorems state that every prime modulus satisfies the corresponding AKS
cyclic congruence predicate.

## Current Endpoint

The v1 bridge now has the following formal path:

```text
1. Pascal prime row
   inner coefficients vanish

2. Weighted universe split
   (x + u)^d = x^d + Beam + u^d

3. Congruent cosmic formula
   Beam ≡ 0
   u^p ≡ u
   therefore (x + u)^p ≡ x^p + u [MOD p]

4. Finite-field form
   (x + u)^p = x^p + u in ZMod p

5. Polynomial Frobenius
   (X + C a)^p = X^p + C a

6. AKS cyclic quotient
   R[X] / (X^r - 1)
   X^r = 1
   X^k = X^(k % r)

7. Prime AKS cyclic Frobenius
   (Xbar + abar)^p = Xbar^(p % r) + abar

8. Predicate layer
   AKSCyclicCongruenceHolds
   AKSCyclicFoldedCongruenceHolds
   prime_AKSCyclicCongruenceHolds
   prime_AKSCyclicFoldedCongruenceHolds
```

This completes the first documented bridge from the Pascal prime-row mechanism
to the AKS cyclic quotient observation.
