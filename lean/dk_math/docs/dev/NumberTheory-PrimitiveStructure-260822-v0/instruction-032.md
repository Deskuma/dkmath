# Codex Instruction — PRIM-L022 Square-Body Small-Cofactor Bridge / Dual Quotient Normal Form

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-C001/C002 are complete in:

```text
DkMath/NumberTheory/Primitive/SquareBody.lean
```

For every positive `m ≤ squareBody P`, the Primitive layer now gives the exact finite-world alternative:

```text
old-generated
or
unique fresh prime p > P × old-generated cofactor k with 0 < k ≤ P.
```

More precisely, for a specified large prime divisor `p > P`:

- `p` is the unique fresh direction;
- `p^2 ∤ m`;
- `m = p * (m / p)`;
- `0 < m / p ≤ P`;
- the cofactor is old-generated;
- every old prime `q ≤ P` satisfies
  `q ∣ m ↔ q ∣ m / p`;
- `m` is prime iff `m / p = 1`;
- if `m` is composite, then `2 ≤ m / p ≤ P`.

The Legendre application already has the apparently opposite factorization.  If an old support prime `p ≤ n` covers the square point `n^2 + r`, then:

```text
p * squareOffsetSupportQuotient n p r = n^2 + r,
```

and the quotient lies above `n`.

PRIM-L015/L016 classify that large quotient by old support and selected-prime depth.

The purpose of PRIM-L022 is to show that these are two views of the same factor geometry whenever the square point also has the unique fresh factor supplied by PRIM-C002.

Do not attempt to prove that every square point has a fresh factor.  The `old-generated` branch is real and must remain explicit.

---

# Main mathematical picture

Fix a square offset point

```text
m = n^2 + r,
1 ≤ r ≤ 2*n.
```

PRIM-C002 says that if `m` has a fresh prime `ℓ > n`, then

```text
m = ℓ * k,
0 < k ≤ n,
```

with `k` entirely old-generated.

If the offset is coprime to the anchor, then `m` is coprime to `n`; hence every divisor `k` of `m` is also coprime to `n`.  Therefore the small cofactor itself lies in the canonical first-half packet set:

```text
k ∈ squareAnchorCoprimeBaseOffsets n.
```

Now select an old support prime `p ≤ n` dividing `m`.  Since `ℓ > n`, `p ≠ ℓ`, so the exact old-support transfer of PRIM-C002 gives

```text
p ∣ k.
```

Consequently the PRIM-L013 quotient has the dual factorization

```text
squareOffsetSupportQuotient n p r
  = ℓ * (k / p).
```

This compresses the PRIM-L015/L016 obstruction semantics:

```text
quotient is prime
  ↔ k / p = 1
  ↔ k = p.
```

Thus, inside a fresh split, the old statement

```text
singleton old support + selected-prime depth one
```

is exactly the statement

```text
the bounded small cofactor is the selected old prime itself.
```

If `k ≠ p`, the large quotient is composite because some residual small old factor remains after division by `p`.

This is the bridge to formalize.

---

# Preferred module

Create:

```text
DkMath/NumberTheory/Legendre/SmallCofactor.lean
```

Preferred dependency:

```lean
import DkMath.NumberTheory.Legendre.QuotientSupport
```

The Primitive square-body API is already available transitively from `Basic`.

Integrate the new module into:

```text
DkMath/NumberTheory/Legendre/Frontier.lean
```

so that the historical facade

```lean
import DkMath.NumberTheory.Legendre
```

exposes the new theorems.

Do not move the generic PRIM-C001/C002 theorems out of `Primitive/SquareBody.lean`.

---

# Required implementation surface

Names below are preferred, not mandatory.  Report final declaration names.

## 1. Reusable square-point Body bounds

Extract the elementary bridge from `SquareOffset` to the generic square Body.

Preferred theorem:

```lean
theorem squarePoint_le_squareBody_of_squareOffset
    {n r : ℕ}
    (hr : SquareOffset n r) :
    n ^ 2 + r ≤ squareBody n
```

A positivity theorem is also useful if thin:

```lean
theorem squarePoint_pos_of_squareOffset
    {n r : ℕ}
    (hr : SquareOffset n r) :
    0 < n ^ 2 + r
```

Do not duplicate any existing theorem if an exact equivalent already exists.

## 2. Coprime offset gives a square point coprime to the anchor

Preferred theorem:

```lean
theorem coprime_anchor_squarePoint_of_coprimeOffset
    {n r : ℕ}
    (hr : r ∈ squareAnchorCoprimeOffsets n) :
    Nat.Coprime n (n ^ 2 + r)
```

This should be a short Euclidean/coprime transport from

```text
Nat.Coprime n r.
```

It is application geometry, not a new generic Primitive theorem.

## 3. Apply PRIM-C002 directly to one square offset

Add a Legendre-facing wrapper of the global Primitive split.

Preferred conceptual theorem:

```lean
theorem squareOffset_oldGenerated_or_uniqueFresh_small_split
    {n r : ℕ}
    (hr : SquareOffset n r) :
    PrimeScaleGeneratedBy (primeScalesUpTo n) (n ^ 2 + r) ∨
      ∃ ℓ k,
        Nat.Prime ℓ ∧
        n < ℓ ∧
        0 < k ∧
        k ≤ n ∧
        FreshPrimeDirection (primeScalesUpTo n) (n ^ 2 + r) ℓ ∧
        ℓ * k = n ^ 2 + r ∧
        PrimeScaleGeneratedBy (primeScalesUpTo n) k ∧
        Nat.Coprime ℓ k ∧
        (∀ ⦃q : ℕ⦄,
          FreshPrimeDirection (primeScalesUpTo n) (n ^ 2 + r) q → q = ℓ)
```

Reuse `primeScaleGeneratedBy_or_uniqueFresh_small_split_of_le_squareBody`.
Do not reprove fresh uniqueness in Legendre.

Equivalent conjunction order is fine.

## 4. The fresh small cofactor of a coprime square seat is itself a canonical base offset

Given a fresh factorization

```text
ℓ * k = n^2 + r,
0 < k,
k ≤ n,
```

on a coprime square seat, prove:

```lean
theorem smallCofactor_mem_coprimeBase_of_fresh_split
    {n r ℓ k : ℕ}
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hkpos : 0 < k)
    (hkLe : k ≤ n)
    (hfac : ℓ * k = n ^ 2 + r) :
    k ∈ squareAnchorCoprimeBaseOffsets n
```

If the proof needs `0 < ℓ`, `Nat.Prime ℓ`, or a divisibility hypothesis, add the weakest natural assumption surface.

The intended reasoning is:

```text
k | n^2+r
n ⟂ n^2+r
therefore n ⟂ k
and 1 ≤ k ≤ n.
```

This is an important structural return: a large square-shell point sends its fresh cofactor back into the canonical finite base packet world.

## 5. Old support transfers to the small cofactor

For a specified fresh split and an old prime support `p`, prove that `p` divides the bounded small cofactor.

Preferred theorem:

```lean
theorem selectedSupport_dvd_smallCofactor_of_fresh_split
    {n p r ℓ k : ℕ}
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r)
    (hℓ : Nat.Prime ℓ)
    (hℓlarge : n < ℓ)
    (hfac : ℓ * k = n ^ 2 + r) :
    p ∣ k
```

Prefer to reuse `old_prime_dvd_iff_dvd_large_prime_cofactor` from PRIM-C002, together with the identification `k = (n^2+r)/ℓ`, rather than reproving Euclid's lemma from scratch.

A direct short proof via prime divisibility is acceptable if it is cleaner.

## 6. Dual quotient factorization

This is the central new theorem.

Under the same hypotheses, prove:

```lean
theorem squareOffsetSupportQuotient_eq_fresh_mul_smallResidual
    {n p r ℓ k : ℕ}
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r)
    (hℓ : Nat.Prime ℓ)
    (hℓlarge : n < ℓ)
    (hfac : ℓ * k = n ^ 2 + r) :
    squareOffsetSupportQuotient n p r = ℓ * (k / p)
```

The orientation may be reversed if it simplifies rewriting.

Intended proof:

```text
p | k
p * quotient = n^2+r
p * (ℓ * (k/p)) = ℓ*k = n^2+r
p > 0
cancel p.
```

Do not introduce rational division.

## 7. Prime quotient iff the small cofactor is exactly the selected old prime

Prove the exact compressed criterion.

Preferred theorem:

```lean
theorem prime_squareOffsetSupportQuotient_iff_smallCofactor_eq_selectedPrime
    {n p r ℓ k : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r)
    (hℓ : Nat.Prime ℓ)
    (hℓlarge : n < ℓ)
    (hfac : ℓ * k = n ^ 2 + r) :
    Nat.Prime (squareOffsetSupportQuotient n p r) ↔ k = p
```

The assumptions may be minimized if Lean permits.

Use the dual factorization from item 6.  Since `p ∣ k`, the residual `k/p` is the only possible nontrivial factor left beside the large prime `ℓ`.

This theorem should not claim that `ℓ` exists for every seat.

## 8. Identify PRIM-L016 simple/depth-one semantics with the small cofactor

Combine item 7 with the existing exact theorem

```lean
prime_squareOffsetSupportQuotient_iff_singleton_support_and_depth_one
```

to prove:

```lean
theorem singleton_support_and_depth_one_iff_smallCofactor_eq_selectedPrime
    {n p r ℓ k : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r)
    (hℓ : Nat.Prime ℓ)
    (hℓlarge : n < ℓ)
    (hfac : ℓ * k = n ^ 2 + r) :
    (squareOffsetAnchorNondivisorSupport n r = {p} ∧
      ¬ p ^ 2 ∣ n ^ 2 + r) ↔
      k = p
```

This is the conceptual payoff of PRIM-L022:

```text
L016 language:
  singleton direction + depth one

C002 language:
  the entire bounded old cofactor is exactly p.
```

## 9. Covered fresh branch has a nontrivial small cofactor

A covered square offset cannot be the `k = 1` fresh-prime case.

Preferred theorem:

```lean
theorem two_le_smallCofactor_of_covered_fresh_split
    {n r ℓ k : ℕ}
    (hr : SquareOffset n r)
    (hcovered : SquareOffsetCovered n r)
    (hℓ : Nat.Prime ℓ)
    (hℓlarge : n < ℓ)
    (hkpos : 0 < k)
    (hfac : ℓ * k = n ^ 2 + r) :
    2 ≤ k
```

Possible proof: obtain an old prime `p ≤ n` covering the seat, transfer `p ∣ k`, and use `2 ≤ p`.

Do not prove this by assuming the Legendre conclusion.

## 10. Full-cover coprime-seat normal form

Package the new structural frontier.

Under full cover, every coprime seat is either entirely old-generated or has a unique fresh prime times a nontrivial small coprime base cofactor.

Preferred conceptual shape:

```lean
theorem oldGenerated_or_uniqueFresh_nontrivialSmall_of_fullyCovered
    {n r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hfull : SquareOffsetsFullyCovered n) :
    PrimeScaleGeneratedBy (primeScalesUpTo n) (n ^ 2 + r) ∨
      ∃ ℓ k,
        Nat.Prime ℓ ∧
        n < ℓ ∧
        2 ≤ k ∧
        k ≤ n ∧
        k ∈ squareAnchorCoprimeBaseOffsets n ∧
        FreshPrimeDirection (primeScalesUpTo n) (n ^ 2 + r) ℓ ∧
        ℓ * k = n ^ 2 + r ∧
        PrimeScaleGeneratedBy (primeScalesUpTo n) k ∧
        Nat.Coprime ℓ k ∧
        (∀ ⦃q : ℕ⦄,
          FreshPrimeDirection (primeScalesUpTo n) (n ^ 2 + r) q → q = ℓ)
```

Equivalent packaging is acceptable.

This theorem is a necessary normal form under full cover, not a contradiction.

---

# Interpretation to preserve in docstrings

State clearly:

1. PRIM-L013–L016 looked at a square point by first selecting an old support prime `p ≤ n`, producing a large quotient `> n`.
2. PRIM-C001/C002 look at the same point from the opposite side: if a fresh prime `ℓ > n` exists, remove it first and obtain a bounded old-generated cofactor `k ≤ n`.
3. PRIM-L022 identifies these two factorizations.
4. In a fresh split, the large selected-prime quotient is

   ```text
   ℓ * (k/p).
   ```

5. Therefore the L016 `singleton + depth-one` case is exactly `k = p`.
6. If `k ≠ p`, the quotient obstruction is not mysterious: a residual bounded old factor remains in `k/p`.
7. A coprime square seat sends the bounded fresh cofactor back into `squareAnchorCoprimeBaseOffsets n`.
8. The old-generated branch is not eliminated and must remain explicit.
9. `fresh` means only outside `primeScalesUpTo n`; do not identify it with Zsigmondy/PrimitiveBeam origin.

This is a finite factor-geometry bridge, not a proof of Legendre's conjecture.

---

# Non-goals

Do **not** add in PRIM-L022:

- a proof that every square point has a fresh prime;
- elimination of the `PrimeScaleGeneratedBy` branch;
- a proof that every fresh small cofactor equals one selected prime;
- a contradiction from full cover;
- new obstruction counting ledgers;
- third-order inclusion-exclusion;
- Hall/matching machinery;
- analytic prime estimates;
- PNT/Mertens/prime-gap estimates;
- `ZMod` or new modular inverse infrastructure;
- Zsigmondy / `PrimitiveBeam` origin claims;
- continuous/differential generalization of the square Body;
- RH/CFBRC dependencies;
- a proof of Legendre's conjecture.

The recently discussed finite-difference/differential viewpoint remains useful background, but this checkpoint stays in the exact unit-one finite square-Body specialization.  Do not generalize `u` here.

---

# Verification

Run at least:

```sh
lake build DkMath.NumberTheory.Legendre.SmallCofactor
lake build DkMath.NumberTheory.Legendre.Frontier
lake build DkMath.NumberTheory.Legendre
lake build DkMath.NumberTheory.Primitive
lake build DkMath
git diff --check
```

Also audit the changed files for new:

```text
sorry
admit
native_decide
axiom
```

Report:

- final declaration names;
- any theorem whose assumption surface differs materially from the preferred shape;
- whether item 8 closes exactly as an iff;
- whether item 10 remains a pure necessary full-cover normal form;
- build/audit results.

Do not open a PR.
