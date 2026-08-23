# Codex Instruction — PRIM-L007 Exact Local Wave Occupancy

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-L006 is complete.

The Legendre application layer now has both offset-side and prime-wave-side local ledgers:

```text
squareOffsets
card_squareOffsets
squareOffsetPrimeSupport
squareWaveOffsets
squarePrimeWaveOffsets
squarePrimePairOverlapOffsets
squareCoverIncidenceCount
squareCoverIncidenceCount_eq_sum_primeWave_cards
squareCoverOverlapExcess
squareCoverIncidenceCount_eq_two_mul_add_overlapExcess_of_fullyCovered
```

It also has the localization fact:

```text
2*n < m
→ (squareWaveOffsets n m).card ≤ 1
```

and, for distinct primes,

```text
2*n < p*q
→ (squarePrimePairOverlapOffsets n p q).card ≤ 1.
```

Thus the unresolved Legendre frontier is no longer global prime-world abundance.  It is the exact occupancy of anchored residue waves inside the specific local window `1..2*n` and the overlap bookkeeping forced by complete cover.

---

# Goal

Compute the exact number of hits of one anchored modulus wave inside the square window.

The key arithmetic observation is that

```text
r ∈ squareWaveOffsets n m
```

means exactly that the translated point

```text
n^2 + r
```

is a multiple of `m` in the interval

```text
n^2 < x ≤ n^2 + 2*n.
```

For positive `m`, the number of multiples of `m` in `(A,B]` is

```text
B / m - A / m.
```

Therefore the target exact local occupancy formula is

```text
(squareWaveOffsets n m).card
  = (n^2 + 2*n) / m - n^2 / m.
```

This checkpoint should then rewrite the already-established incidence ledger entirely in quotient/floor arithmetic.

Do not use analytic prime-density estimates and do not attempt the Legendre escape proof.

---

# Preferred location

Keep this checkpoint in:

```text
DkMath/NumberTheory/Legendre.lean
```

unless the local counting proof becomes large enough to justify a sibling module.

Do not move existing PRIM-L003/L005/L006 declarations.

---

# Required reconnaissance

Before coding, inspect current Lean 4.32 / Mathlib APIs for finite interval multiples and natural-number division arithmetic.

Search / `#check` useful candidates around:

```text
Finset.Icc
Finset.card_Icc
Finset.filter
Finset.card_congr
Finset.card_image_iff
Nat.div_eq_of_lt_le
Nat.div_lt_iff_lt_mul
Nat.le_div_iff_mul_le
Nat.div_add_div_same
Nat.add_div
Nat.mul_div_cancel_left
Nat.div_mul_le_self
```

The names above are only search hints. Use the current API actually available.

Prefer a direct finite bijection / quotient-interval argument over brute-force enumeration.

Do not add a general new floor-arithmetic library unless genuinely required.

---

# Required implementation surface

Names are preferred, not mandatory. Report final declaration names.

## 1. Exact generic wave-cardinality formula

For positive modulus, prove:

```lean
theorem card_squareWaveOffsets_eq_div_sub_div
    {n m : ℕ}
    (hm : 0 < m) :
    (squareWaveOffsets n m).card =
      (n ^ 2 + 2 * n) / m - (n ^ 2) / m
```

Equivalent parenthesization is acceptable.

Preferred proof semantics:

```text
r ∈ [1,2*n]
and m ∣ n^2+r

↕ translate / divide

k*m ∈ (n^2, n^2+2*n]

↕ quotient bounds

n^2/m < k ≤ (n^2+2*n)/m.
```

A finite bijection between wave seats and the corresponding quotient interval is ideal.

Do not prove the equality by testing residue phases individually for fixed numerical values.

If a cleaner existing Mathlib theorem directly counts multiples in an interval, use it.

## 2. Prime-wave specialization

Expose a thin wrapper for an old prime wave:

```lean
theorem card_squarePrimeWaveOffsets_eq_div_sub_div
    {n q : ℕ}
    (hq : Nat.Prime q) :
    (squarePrimeWaveOffsets n q).card =
      (n ^ 2 + 2 * n) / q - (n ^ 2) / q
```

This should be a rewrite of the generic theorem, not a new proof.

Primality is only used to obtain `0 < q`.

## 3. Generic local occupancy band

Prove the standard interval-length bounds, preferably from the exact formula:

```lean
theorem div_le_card_squareWaveOffsets
    {n m : ℕ}
    (hm : 0 < m) :
    (2 * n) / m ≤ (squareWaveOffsets n m).card
```

and

```lean
theorem card_squareWaveOffsets_le_div_add_one
    {n m : ℕ}
    (hm : 0 < m) :
    (squareWaveOffsets n m).card ≤ (2 * n) / m + 1
```

Equivalent sharp floor/ceiling formulations are acceptable.

The mathematical point is that one residue class in an interval of length `2*n` occurs either `⌊2*n/m⌋` or `⌈2*n/m⌉` times.

If proving both bounds creates disproportionate arithmetic machinery, prioritize the exact formula and report which thin bound was omitted and why.

## 4. Every old prime wave has at least two local hits

Using `q ≤ n` for `q ∈ primeScalesUpTo n`, derive the useful local corollary:

```lean
theorem two_le_card_squarePrimeWaveOffsets_of_mem
    {n q : ℕ}
    (hq : q ∈ primeScalesUpTo n) :
    2 ≤ (squarePrimeWaveOffsets n q).card
```

For very small `n`, the membership assumption itself should rule out impossible primes.

Preferred route:

```text
q ≤ n
→ 2 ≤ (2*n)/q
→ lower occupancy bound.
```

Do not enumerate primes.

## 5. Exact incidence formula in quotient arithmetic

Rewrite the PRIM-L006 transpose theorem using the exact wave count:

```lean
theorem squareCoverIncidenceCount_eq_sum_div_sub_div
    (n : ℕ) :
    squareCoverIncidenceCount n =
      ∑ q ∈ primeScalesUpTo n,
        ((n ^ 2 + 2 * n) / q - (n ^ 2) / q)
```

This is a central deliverable.

The proof should be:

```text
incidence
= sum of prime-wave cards          -- PRIM-L006
= sum of exact floor differences   -- this checkpoint
```

Do not introduce analytic approximations here.

## 6. Full-cover necessary inequality in exact arithmetic form

As a thin corollary, prove:

```lean
theorem two_mul_le_sum_div_sub_div_of_fullyCovered
    {n : ℕ}
    (hfull : SquareOffsetsFullyCovered n) :
    2 * n ≤
      ∑ q ∈ primeScalesUpTo n,
        ((n ^ 2 + 2 * n) / q - (n ^ 2) / q)
```

This is only a necessary condition for full cover.

Do not claim that the right side is too small; in general that has not been established.

## 7. Exact pair-overlap count

Use the existing equality

```text
squarePrimePairOverlapOffsets n p q
= squareWaveOffsets n (p*q)
```

for distinct primes and derive:

```lean
theorem card_squarePrimePairOverlapOffsets_eq_div_sub_div
    {n p q : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hpq : p ≠ q) :
    (squarePrimePairOverlapOffsets n p q).card =
      (n ^ 2 + 2 * n) / (p * q) - (n ^ 2) / (p * q)
```

This should subsume the pair occupancy into the same quotient language.

Do not delete the existing `2*n < p*q → card ≤ 1` theorem; it remains the clean local sparsity corollary.

## 8. Optional exact overlap-excess rewrite

If very thin after the incidence formula, under full cover prove:

```lean
squareCoverOverlapExcess n =
  (∑ q ∈ primeScalesUpTo n,
    ((n ^ 2 + 2 * n) / q - (n ^ 2) / q)) - 2 * n
```

or an equivalent equality avoiding awkward truncated subtraction orientation.

This is optional. Do not spend the checkpoint fighting `Nat` subtraction if the existing

```text
Incidence = 2*n + OverlapExcess
```

plus the new incidence rewrite already exposes the same information cleanly.

---

# Mathematical interpretation to preserve in docstrings

State clearly:

- `squareWaveOffsets n m` counts actual hits in the anchored local window, not density in a full modulus period;
- its exact cardinality is a difference of quotient counts at the two window endpoints;
- the square anchor affects the floor difference even though the coarse occupancy is controlled by window length `2*n` and modulus `m`;
- for every old prime `q ≤ n`, the window is at least two `q`-periods long, so every old prime wave has at least two local hits;
- the incidence ledger is now an exact arithmetic sum of floor differences;
- pair overlaps are the same exact formula with modulus `p*q`;
- none of these cardinality facts alone prove local escape.

---

# Non-goals

Do **not** add in PRIM-L007:

- a proof that the exact incidence sum is `< 2*n`;
- harmonic-prime estimates;
- Mertens / PNT;
- asymptotic density arguments;
- inclusion-exclusion over all prime subsets;
- Möbius inversion;
- Jacobsthal machinery;
- a proof of `SquareAnchoredSupportEscape`;
- a proof of Legendre's conjecture;
- arbitrary numerical enumeration as the generic proof method;
- p-adic depth / valuation multiplicity;
- RH / CFBRC dependencies;
- category theory.

Do not confuse exact incidence count with distinct covered-seat count.

---

# Verification

Run:

```sh
lake build DkMath.NumberTheory.Legendre
lake build DkMath.NumberTheory.Primitive
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

Report unrelated pre-existing occurrences separately and do not broaden scope to repair them.

---

# Acceptance criteria

PRIM-L007 is complete when:

1. one positive-modulus square wave has an exact quotient-difference cardinality formula;
2. prime-wave occupancy is a thin specialization;
3. at least the useful coarse occupancy bounds are exposed, unless a specific Lean arithmetic obstruction is reported;
4. every old prime wave `q ≤ n` is shown to hit the length-`2*n` window at least twice;
5. total incidence is rewritten exactly as a finite sum of quotient differences;
6. full cover gets the corresponding exact-arithmetic necessary inequality;
7. distinct-prime pair overlap gets the same quotient-difference formula at modulus `p*q`;
8. no analytic estimate or Legendre provider is smuggled in;
9. requested builds and audits are clean.

Stop after PRIM-L007. Do not attempt to prove the incidence inequality impossible in this implementation pass.

---

# Review questions after PRIM-L007

The next review must inspect the exact arithmetic ledger rather than guess from density.

In particular, determine which direction is actually supported by the new Lean surface:

```text
A. exploit the special square-anchor floor differences, not generic residue density;
B. compare overlap excess with the exact pair-product floor-difference ledger;
C. generalize pair intersections to arbitrary finite squarefree support products;
D. pivot to Primitive Origin / first-occurrence if the floor ledger is only tautological.
```

Do not choose the next route until the exact local occupancy formula is visible.