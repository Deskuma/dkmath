# Codex Instruction — PRIM-C002 Square-Body Bounded Fresh Cofactor / Small×Fresh Normal Form

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-C001 is complete in:

```text
DkMath/NumberTheory/Primitive/SquareBody.lean
```

For a positive point `m` in the square Body

```text
m ≤ squareBody P = P^2 + 2*P = (P+1)^2 - 1,
```

we now have:

- a prime `p > P` cannot satisfy `p^2 ∣ m`;
- two prime divisors above `P` must coincide;
- such a large divisor is a `FreshPrimeDirection` relative to `primeScalesUpTo P`;
- if `p > P` is prime and divides `m`, then with `k = m / p`:
  - `p*k = m`;
  - `¬ p ∣ k`;
  - `Nat.Coprime p k`;
  - `PrimeScaleGeneratedBy (primeScalesUpTo P) k`;
  - `p` is the unique fresh direction of `m`;
- every positive square-Body point is either entirely old-generated or admits one unique fresh direction with an old-generated cofactor.

The next structural fact is stronger than old-generation alone: the cofactor left after removing the unique fresh prime must itself fit below the anchor.

Do not return to Legendre in this checkpoint.  This is a Primitive-core strengthening.

---

# Goal

If

```text
p > P,
p is prime,
p ∣ m,
0 < m ≤ squareBody P,
```

and

```text
k = m / p,
```

then

```text
k ≤ P.
```

Indeed, `p ≥ P+1`; if also `k ≥ P+1`, then

```text
(P+1)^2 ≤ p*k = m,
```

contradicting `m ≤ squareBody P < (P+1)^2`.

Use this to strengthen PRIM-C001 from

```text
old-generated × one fresh prime
```

to the sharper square-Body normal form

```text
small cofactor k ≤ P × one unique fresh prime p > P.
```

The cofactor remains old-generated and may have arbitrary old-prime exponents.

---

# Preferred location

Continue in:

```text
DkMath/NumberTheory/Primitive/SquareBody.lean
```

Do not create a Legendre dependency from Primitive.

---

# Required implementation surface

Names below are preferred, not mandatory.  Report the final declaration names.

## 1. Fresh cofactor is bounded by the anchor

Prove the core size theorem.

Preferred shape:

```lean
theorem div_le_anchor_of_large_prime_dvd_le_squareBody
    {P m p : ℕ}
    (hm : 0 < m)
    (hmUpper : m ≤ squareBody P)
    (hp : Nat.Prime p)
    (hpLarge : P < p)
    (hpd : p ∣ m) :
    m / p ≤ P
```

If `hm` is not logically necessary for the chosen proof, a weaker assumption surface is acceptable, but keep the theorem easy to reuse with PRIM-C001.

The intended proof is order-theoretic, not factorization enumeration:

```text
p*k = m
P+1 ≤ p
if P < k then P+1 ≤ k
therefore (P+1)^2 ≤ p*k = m
but m ≤ squareBody P < (P+1)^2
```

## 2. Positive fresh cofactor

Expose positivity/nonzeroness of the cofactor under the existing hypotheses.

Preferred thin theorem:

```lean
theorem positive_div_of_large_prime_dvd_le_squareBody
    ... :
    0 < m / p
```

or an equivalent `m / p ≠ 0` theorem.

Reuse the reconstruction equation rather than introducing new factorization machinery.

## 3. Exact old-prime support transfer to the bounded cofactor

For every old prime `q ≤ P`, prove that divisibility of the original point is exactly divisibility of the cofactor after removing the large fresh prime.

Preferred shape:

```lean
theorem old_prime_dvd_iff_dvd_large_prime_cofactor
    {P m p q : ℕ}
    (hm : 0 < m)
    (hmUpper : m ≤ squareBody P)
    (hp : Nat.Prime p)
    (hpLarge : P < p)
    (hpd : p ∣ m)
    (hq : Nat.Prime q)
    (hqLe : q ≤ P) :
    q ∣ m ↔ q ∣ m / p
```

The reverse direction is immediate from `p*(m/p)=m`.

For the forward direction, use that `q ≠ p` because `q ≤ P < p`, then primality of `q` to remove the `p` factor from `q ∣ p*(m/p)`.

This theorem is important: it says removing the unique fresh direction preserves the complete old support exactly.

## 4. Fresh split strengthened by the small-cofactor bound

Add a strengthened package theorem, preferably without changing the existing PRIM-C001 theorem types.

Example shape:

```lean
theorem squareBody_large_prime_small_cofactor_split
    {P m p : ℕ}
    (hm : 0 < m)
    (hmUpper : m ≤ squareBody P)
    (hp : Nat.Prime p)
    (hpLarge : P < p)
    (hpd : p ∣ m) :
    let k := m / p
    p * k = m ∧
    0 < k ∧
    k ≤ P ∧
    PrimeScaleGeneratedBy (primeScalesUpTo P) k ∧
    Nat.Coprime p k ∧
    FreshPrimeDirection (primeScalesUpTo P) m p ∧
    (∀ ⦃q : ℕ⦄,
      FreshPrimeDirection (primeScalesUpTo P) m q → q = p)
```

Equivalent conjunction order is fine.

Do not delete or rewrite `squareBody_large_prime_split`; this should be a stronger downstream package unless a trivial refactor preserves the public API exactly.

## 5. Prime/composite criterion inside a specified fresh split

For a specified large prime divisor `p`, the small cofactor detects whether `m` itself is prime.

Preferred theorem:

```lean
theorem prime_iff_large_prime_cofactor_eq_one
    {P m p : ℕ}
    (hm : 0 < m)
    (hmUpper : m ≤ squareBody P)
    (hp : Nat.Prime p)
    (hpLarge : P < p)
    (hpd : p ∣ m) :
    Nat.Prime m ↔ m / p = 1
```

The intended semantics are elementary:

```text
m/p = 1 -> m = p -> prime
m prime and p | m -> p = m -> m/p = 1
```

If the exact Mathlib API makes this theorem disproportionately awkward, a pair of one-way lemmas is acceptable.

## 6. Composite fresh split has a genuinely nontrivial small cofactor

Derive the useful bounded composite form:

```lean
theorem two_le_large_prime_cofactor_of_not_prime
    {P m p : ℕ}
    (hm : 0 < m)
    (hmUpper : m ≤ squareBody P)
    (hp : Nat.Prime p)
    (hpLarge : P < p)
    (hpd : p ∣ m)
    (hmPrime : ¬ Nat.Prime m) :
    2 ≤ m / p
```

Together with item 1 this yields

```text
2 ≤ k ≤ P
```

for every composite square-Body point carrying a fresh prime.

A packaged theorem exposing both bounds is welcome if thin.

## 7. Strengthen the global old-or-fresh dichotomy

Add a new theorem that preserves the PRIM-C001 dichotomy but includes the small-cofactor bound.

Preferred conceptual form:

```lean
theorem primeScaleGeneratedBy_or_uniqueFresh_small_split_of_le_squareBody
    {P m : ℕ}
    (hm : 0 < m)
    (hmUpper : m ≤ squareBody P) :
    PrimeScaleGeneratedBy (primeScalesUpTo P) m ∨
      ∃ p k,
        Nat.Prime p ∧
        P < p ∧
        0 < k ∧
        k ≤ P ∧
        FreshPrimeDirection (primeScalesUpTo P) m p ∧
        p * k = m ∧
        PrimeScaleGeneratedBy (primeScalesUpTo P) k ∧
        Nat.Coprime p k ∧
        (∀ ⦃q : ℕ⦄,
          FreshPrimeDirection (primeScalesUpTo P) m q → q = p)
```

Do not replace the existing theorem; add a strengthened form so downstream users can choose the lighter or stronger package.

## 8. Optional: exact fresh-support/old-support normal form

If it is genuinely thin after item 3, add one theorem saying that under a specified large prime split:

```text
old prime divisors of m
=
prime divisors of k,
```

in predicate form or a Finset form using `primeScalesUpTo P`.

Do not build a new support datatype in this checkpoint.

---

# Interpretation to preserve in docstrings

State clearly:

- PRIM-C001 proved uniqueness and depth one of a fresh prime direction in the square Body;
- PRIM-C002 adds the stronger size statement that the complementary factor lies at or below the anchor;
- therefore a fresh square-Body point is not merely `old-generated × fresh`, but `small ≤ P × unique fresh > P`;
- the small factor may contain repeated old primes;
- the theorem is finite-world freshness only, not Zsigmondy/primitive-origin freshness;
- this is generic Primitive structure and is not a Legendre theorem.

The key geometric reason is the strict square boundary:

```text
m < (P+1)^2.
```

Two factors both exceeding `P` cannot fit inside that Body.

---

# Non-goals

Do **not** add in PRIM-C002:

- a Legendre-specific theorem or import;
- existence of a fresh prime for every square-Body point;
- a proof that a square-cell point is prime;
- a proof of Legendre's conjecture;
- Zsigmondy / `PrimitiveBeam` / primitive-origin language as a theorem;
- valuation summation;
- factorization uniqueness beyond the unique fresh direction already proved;
- analytic prime estimates;
- matching/Hall machinery;
- category theory;
- RH/CFBRC dependencies.

---

# Verification

Run:

```sh
lake build DkMath.NumberTheory.Primitive.SquareBody
lake build DkMath.NumberTheory.Primitive
lake build DkMath.NumberTheory.Legendre
lake build DkMath
git diff --check
```

Audit the touched Lean file for new occurrences of:

```text
sorry
admit
native_decide
axiom
```

---

# Acceptance criteria

PRIM-C002 is complete when:

1. the cofactor after removing a prime `p > P` is proved to satisfy `k ≤ P`;
2. cofactor positivity/nonzeroness is available;
3. old-prime divisibility is preserved exactly between `m` and the cofactor;
4. the PRIM-C001 large-prime split has a strengthened small-cofactor package;
5. prime vs composite behavior is exposed through the cofactor (`k = 1` vs `k ≥ 2`) or an equivalent API;
6. a strengthened global old-generated-or-unique-fresh dichotomy records `0 < k ≤ P`;
7. no Legendre provider, contradiction, or primitive-origin claim is introduced.

After this checkpoint, review whether the Legendre square-cell application can be compressed to the generic normal form:

```text
square-cell point
  = old-only
or
  = small old cofactor × unique fresh prime,
```

and whether PRIM-L016/L017's simple/depth/multi classification is exactly the internal structure of that small cofactor.
