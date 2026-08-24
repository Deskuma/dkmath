# Codex Instruction — PRIM-L005 Square-Anchor Prime-Wave Overlap Audit

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-L003 is complete.

The Legendre application layer now contains the exact square-anchor cover language:

```text
SquareCell
SquareOffset
SquareOffsetForbiddenBy
SquareOffsetCovered
squareOffsetCovered_iff_exists_prime_dvd
supportDisjointFrom_primeScalesUpTo_square_add_iff_not_covered
squareAnchorForbiddenResidue
squareOffsetForbiddenBy_iff_mod_eq_forbiddenResidue
squareOffsets
coveredSquareOffsets
escapingSquareOffsets
SquareOffsetsFullyCovered
squareAnchoredSupportEscape_iff_not_fully_covered
legendreConjecture_iff_squareOffsets_not_fully_covered
```

For each positive `n`, Legendre is now exactly the assertion that the finite offset interval

```text
1, ..., 2*n
```

is not completely covered by the old prime waves `q ≤ n`, where the `q`-wave forbids exactly the offsets satisfying

```text
q ∣ n^2 + r
```

and, equivalently for `q > 0`, one residue phase modulo `q`.

The completed generic Primitive stack also already provides finite prime worlds, exact periodic support semantics, fresh-prime refinement, canonical residue spaces, cardinality product formulas, and Euler-totient identification.

The roadmap mandatory stop has therefore been reached: the remaining Legendre frontier is localization / finite cover, not global residue abundance.

---

# Goal

Do **not** try to prove or disprove full cover in this checkpoint.

Instead, audit the overlap structure forced when two or more old prime waves cover the same square offset.

The mathematical observation to expose is:

```text
p ∣ n^2 + r
q ∣ n^2 + r
p ≠ q
p, q prime
```

implies, because distinct primes are coprime,

```text
p*q ∣ n^2 + r.
```

Conversely, divisibility by `p*q` implies divisibility by both factors.

Therefore the intersection of two square-anchor prime waves is not an arbitrary set intersection: it is itself one periodic wave modulo the product modulus `p*q`, with the same square anchor.

This checkpoint should make that structure explicit and provide a finite overlap ledger usable by later counting/localization work.

---

# Preferred location

Prefer keeping this checkpoint in the Legendre application layer.

Two acceptable implementations:

1. extend

```text
DkMath/NumberTheory/Legendre.lean
```

if the additions remain compact; or

2. create a sibling module such as

```text
DkMath/NumberTheory/Legendre/PrimeWaveOverlap.lean
```

that imports `DkMath.NumberTheory.Legendre`.

If using a sibling module, do not introduce an import cycle merely to re-export it from `Legendre.lean`. Report the final public import path instead. A higher aggregator may be updated only if an existing appropriate aggregator already exists.

Do not move existing L003 declarations in this checkpoint.

---

# Required reconnaissance

Before coding, inspect the current Lean 4.32 / Mathlib APIs for:

```text
Nat.Coprime
Nat.Prime.coprime_iff_not_dvd
Nat.Coprime.mul_dvd
Nat.Coprime.dvd_mul
Finset.filter
Finset.card_filter
Finset.sum
Finset.sum_card_image
Finset.card_biUnion
```

The exact theorem names above are only search hints; use the current API actually available.

In particular, find the shortest existing route for:

```text
Nat.Prime p
Nat.Prime q
p ≠ q
p ∣ m
q ∣ m
→ p*q ∣ m
```

Do not build a new coprime/divisibility framework if Mathlib already supplies the needed theorem.

---

# Required implementation surface

Names below are preferred, not mandatory. Report final declaration names.

## 1. Prime-wave support at one offset

Add a finite set recording which old prime directions cover one square offset:

```lean
def squareOffsetPrimeSupport (n r : ℕ) : Finset ℕ :=
  (primeScalesUpTo n).filter (fun q => SquareOffsetForbiddenBy n q r)
```

Expose exact membership:

```lean
@[simp] theorem mem_squareOffsetPrimeSupport
    {n r q : ℕ} :
    q ∈ squareOffsetPrimeSupport n r ↔
      Nat.Prime q ∧ q ≤ n ∧ q ∣ n ^ 2 + r
```

or an equivalent theorem factored through `mem_primeScalesUpTo` and `SquareOffsetForbiddenBy`.

Do not duplicate the semantics already in `squareOffsetCovered_iff_exists_prime_dvd`.

## 2. Covered iff support nonempty

Prove:

```lean
theorem squareOffsetCovered_iff_primeSupport_nonempty
    {n r : ℕ} :
    SquareOffsetCovered n r ↔
      (squareOffsetPrimeSupport n r).Nonempty
```

and, if thin:

```lean
theorem squareOffsetCovered_iff_primeSupport_card_pos
    {n r : ℕ} :
    SquareOffsetCovered n r ↔
      0 < (squareOffsetPrimeSupport n r).card
```

This gives a local multiplicity observer without changing the meaning of coverage.

## 3. Pairwise overlap = product divisibility

For distinct primes, prove the exact pair-intersection theorem:

```lean
theorem squareOffsetForbiddenBy_pair_iff_product_dvd
    {n p q r : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hpq : p ≠ q) :
    SquareOffsetForbiddenBy n p r ∧
      SquareOffsetForbiddenBy n q r ↔
        p * q ∣ n ^ 2 + r
```

Equivalent orientation / naming is acceptable.

The forward direction should use coprimality of distinct primes. The reverse direction should use factor divisibility of a product divisor.

Do not assume `p < q`; only distinctness is mathematically relevant.

## 4. Pairwise overlap is one product-modulus phase

Compose the previous theorem with the already-proved generic positive-modulus phase theorem:

```text
squareOffsetForbiddenBy_iff_mod_eq_forbiddenResidue
```

and prove, for distinct primes:

```lean
theorem squareOffsetForbiddenBy_pair_iff_mod_eq_product_forbiddenResidue
    {n p q r : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hpq : p ≠ q) :
    (SquareOffsetForbiddenBy n p r ∧
      SquareOffsetForbiddenBy n q r) ↔
      r % (p * q) = squareAnchorForbiddenResidue n (p * q)
```

The important semantic result is:

```text
intersection of p-wave and q-wave
= one wave modulo p*q
```

with the same square anchor.

Do not introduce signed residue arithmetic solely for this theorem.

## 5. Overlap predicate / support multiplicity

Expose a small semantic wrapper for repeated coverage, preferably:

```lean
def SquareOffsetOverlap (n r : ℕ) : Prop :=
  2 ≤ (squareOffsetPrimeSupport n r).card
```

Then prove an exact witness form:

```lean
theorem squareOffsetOverlap_iff_exists_two_distinct_primes
    {n r : ℕ} :
    SquareOffsetOverlap n r ↔
      ∃ p q,
        p ≠ q ∧
        p ∈ squareOffsetPrimeSupport n r ∧
        q ∈ squareOffsetPrimeSupport n r
```

An equivalent theorem using explicit `Nat.Prime`, bounds, and divisibility is acceptable if Mathlib's Finset cardinality API makes the membership form awkward.

Do not weaken this to only one implication unless the exact reverse direction is genuinely obstructed; report any obstruction.

## 6. Finite incidence count

Define the total number of prime-wave incidences in the square window:

```lean
def squareCoverIncidenceCount (n : ℕ) : ℕ :=
  ∑ r ∈ squareOffsets n, (squareOffsetPrimeSupport n r).card
```

This counts incidences `(r,q)`, not distinct covered offsets.

Add a theorem showing that full cover forces at least one incidence per offset:

```lean
theorem card_squareOffsets_le_squareCoverIncidenceCount_of_fullyCovered
    {n : ℕ}
    (hfull : SquareOffsetsFullyCovered n) :
    (squareOffsets n).card ≤ squareCoverIncidenceCount n
```

Prefer deriving it pointwise from nonempty support / positive card and summing. Do not use analytic estimates.

If cheap, also expose:

```lean
@[simp] theorem card_squareOffsets (n : ℕ) :
    (squareOffsets n).card = 2 * n
```

provided this is valid with the current `Finset.Icc` convention also at `n = 0`.

Then a thin corollary under full cover may state:

```text
2*n ≤ squareCoverIncidenceCount n.
```

## 7. Optional exact overlap-excess ledger

Only if it remains clean and does not dominate the checkpoint, define:

```lean
def squareCoverOverlapExcess (n : ℕ) : ℕ :=
  ∑ r ∈ squareOffsets n,
    ((squareOffsetPrimeSupport n r).card - 1)
```

and prove under full cover:

```lean
squareCoverIncidenceCount n =
  (squareOffsets n).card + squareCoverOverlapExcess n
```

or, using the cardinality theorem:

```text
squareCoverIncidenceCount n = 2*n + squareCoverOverlapExcess n.
```

This theorem is valuable because it separates:

```text
minimum one incidence required per covered offset
+
all repeated coverage / overlap waste
```

But it is optional. Do not introduce auxiliary machinery solely to force this identity.

---

# Interpretation to preserve in docstrings

State clearly:

- `squareOffsetPrimeSupport n r` records which old prime waves hit one anchored offset;
- support cardinality is cover multiplicity, not prime-factor multiplicity with exponents;
- a pairwise overlap of distinct prime waves is equivalent to divisibility by their product;
- pairwise wave intersection is therefore one product-modulus residue phase, not an arbitrary intersection;
- `squareCoverIncidenceCount` counts wave incidences, so repeated coverage increases it without covering a new offset;
- this checkpoint only exposes necessary structure under full cover; it does not prove that full cover is impossible.

Keep the distinction between:

```text
prime support multiplicity
```

and

```text
p-adic valuation / prime-power depth
```

explicit. PRIM-L005 is squarefree direction overlap only.

---

# Non-goals

Do **not** add in PRIM-L005:

- a proof of `SquareAnchoredSupportEscape`;
- a proof of Legendre's conjecture;
- any assertion that full cover is impossible;
- union-bound or density estimates intended to force escape;
- Mertens / PNT / prime harmonic estimates;
- Jacobsthal-function machinery;
- inclusion-exclusion over all subsets of `primeScalesUpTo n`;
- Möbius inversion;
- Euler-totient re-proofs;
- recursive sieve machinery;
- prime-power valuation / Depth theory;
- RH / CFBRC imports;
- category theory.

Do not use global PHZ residue abundance to infer local square-window escape.

Do not enumerate primes or offsets for fixed numerical `n` as the proof method for generic theorems.

---

# Verification

If modifying `Legendre.lean` directly, run:

```sh
lake build DkMath.NumberTheory.Legendre
lake build DkMath.NumberTheory.Primitive
lake build DkMath
git diff --check
```

If creating a sibling overlap module, also build that module explicitly.

Audit touched Lean files for new occurrences of:

```text
sorry
admit
native_decide
axiom
```

Report any unrelated pre-existing occurrences separately; do not broaden scope to repair them.

---

# Acceptance criteria

PRIM-L005 is complete when:

1. the finite old-prime support set of one square offset is exposed;
2. ordinary coverage is exactly nonempty support;
3. simultaneous coverage by two distinct prime waves is exactly product divisibility;
4. the pairwise intersection is identified with one residue phase modulo the product modulus;
5. repeated coverage has an exact finite support/cardinality witness;
6. a finite incidence-count ledger exists;
7. full cover implies at least one incidence per square offset;
8. no escape provider, density theorem, or Legendre proof is smuggled into the checkpoint;
9. requested builds and audits are clean.

Stop after PRIM-L005. Do not begin an escape proof in this implementation pass.

---

# Review questions after PRIM-L005

The next review must decide what the overlap ledger actually buys mathematically.

In particular, inspect whether full cover forces enough repeated support to make one of these routes meaningful:

```text
A. exact per-wave counts inside 1..2n and overlap-excess accounting
B. higher-order squarefree intersections via products of distinct primes
C. anchored Jacobsthal-type local gap formulation
D. Primitive Origin / first-occurrence contradiction from a fully old-supported block
```

Do not choose the next route before seeing the PRIM-L005 Lean surface.
