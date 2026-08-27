# PRIM-L037 — Reduced-Residue Modulus `2n` / Parity-Safe Quotient Normalization Lean Judgment

Date: 2026-08-26
Target branch: `wip/number-theory-primitive-structure-260822-v2`
Lean / Mathlib: keep v4.32.2

## 0. Motivation and boundary

L034–L036 show that parity-safe seats are the correct finite world for eliminating the prime-`2` fresh-collision exception. L036 also closes the incidence ledger exactly, but the residual `silent < uncovered` condition is not a new arithmetic provider: an uncovered seat already reaches the square-cell prime Frontier directly.

Do **not** continue by adding another silent/uncovered counting wrapper.

The next step is to return to the arithmetic structure of a single repeated active wave and normalize the entire parity-safe world by the modulus `2*n`.

The key expected equivalence is:

```text
r is a parity-safe candidate
  <-> SquareOffset n r
      and Nat.Coprime (2*n) (n^2+r)
```

Indeed `Nat.Coprime n r` is equivalent to coprimality of `n` with `n^2+r`, while oddness of the complete point excludes the factor `2`.

For an active prime `q`, `q` is itself coprime to `2*n`. If `q | n^2+r` and

```text
k = (n^2+r)/q,
```

then `k` should also be coprime to `2*n`. Thus one parity-safe `q`-wave should be equivalent to a short interval of reduced residues modulo `2*n` in quotient coordinates.

This checkpoint is proof-backed reconnaissance. It must implement exact Lean theorems, not merely write a report.

## 1. New module

Suggested file:

```text
DkMath/NumberTheory/Legendre/ParitySafeReducedResidue.lean
```

Add the facade import to `DkMath.NumberTheory.Legendre`.

Prefer imports from the existing Legendre stack, especially:

```text
ParitySafeIncidenceBalance
Quotient
```

Do not modify public theorem statements from L034–L036 or L013–L016.

## 2. Exact `2*n` candidate normalization

Prove an exact arithmetic bridge, with the weakest clean hypotheses Lean permits, of the form:

```lean
Nat.Coprime (2 * n) (n ^ 2 + r)
  <-> Nat.Coprime n r ∧ Odd (n ^ 2 + r)
```

or an equivalent theorem with the conjunction order adjusted for existing Mathlib APIs.

Then derive the parity-safe candidate membership theorem:

```text
r ∈ squareAnchorOddPointCoprimeOffsets n
  <-> SquareOffset n r
      and Nat.Coprime (2*n) (n^2+r)
```

This should replace the conceptual two-condition reading by a single reduced-residue condition. Do not redefine the existing candidate set.

## 3. Exact candidate cardinality

For `0 < n`, prove the exact cardinal theorem:

```text
(squareAnchorOddPointCoprimeOffsets n).card = Nat.totient (2*n)
```

Use a finite interval of length `2*n` and existing Mathlib totient/filter-coprime APIs. Do not prove this by analytic density.

This theorem should subsume the previous piecewise observations:

```text
even n -> candidate.card = 2 * totient n
odd n  -> candidate.card = totient n
```

You may add thin corollaries recovering either identity only if direct and useful; do not duplicate the existing L034 even-anchor theorem unnecessarily.

## 4. Active primes are reduced residues modulo `2*n`

For

```text
q ∈ squareAnchorOddActivePrimes n
```

prove:

```text
Nat.Coprime (2*n) q
```

and record the useful facts already encoded by membership:

```text
Nat.Prime q
q ≤ n
q ≠ 2
¬ q ∣ n
```

Do not create a large structure for this packet.

## 5. Quotient reduced-residue transfer

Reuse the existing

```lean
squareOffsetSupportQuotient n q r
mul_squareOffsetSupportQuotient_eq
coprime_anchor_squareOffsetSupportQuotient_iff
```

from `Quotient.lean`.

For an active prime `q` and a parity-safe wave seat `r`, prove that the quotient

```text
k = squareOffsetSupportQuotient n q r
```

satisfies at least:

```text
n < k
Nat.Coprime (2*n) k
Odd k
q * k = n^2+r
```

The `Odd k` statement should follow from odd complete point and odd prime `q`; if the `Nat.Coprime (2*n) k` theorem makes it redundant, keep only the cleaner theorem surface and derive oddness as a corollary if useful.

## 6. Exact quotient-interval world

Define at most one focused finite set for the quotient side, suggested shape:

```lean
noncomputable def paritySafeReducedQuotientInterval
    (n q : ℕ) : Finset ℕ :=
  (Finset.Ioc ((n^2) / q) ((n^2 + 2*n) / q)).filter
    (fun k => Nat.Coprime (2*n) k)
```

Adjust endpoints only if Lean arithmetic shows a more exact formulation is needed. The intended semantics is exactly:

```text
n^2 < q*k ≤ n^2+2*n
and gcd(2*n,k)=1.
```

For active `q`, prove a bijection/cardinality equality between:

```text
paritySafeActiveWaveOffsets n q
```

and

```text
paritySafeReducedQuotientInterval n q.
```

Preferred theorem surface:

```text
card_paritySafeActiveWaveOffsets_eq_reducedQuotientInterval
```

The map should be the existing support quotient; the inverse is conceptually `q*k - n^2` with the necessary lower-bound proof. Keep Nat subtraction local and justified.

This is the main theorem of the checkpoint.

## 7. Same-wave duplicate rigidity in quotient coordinates

For two distinct parity-safe seats `r < s` in the same active `q` wave, prove the exact quotient difference relation as far as Lean naturally allows.

Target facts:

```text
q ∣ (s-r)
2*q ∣ (s-r)
```

and, writing `k_r`, `k_s` for the two support quotients,

```text
k_r < k_s
2 ≤ k_s-k_r
Even (k_s-k_r)
```

An exact formula such as

```text
q * (k_s-k_r) = s-r
```

is preferred if Nat subtraction side conditions are clean.

Do not overclaim that adjacent *candidate* wave hits always differ by exactly `2*q`: coprimality filtering can skip intermediate raw hits. The theorem should state divisibility / even separation, not false exact adjacency.

## 8. Global incidence rewrite

Using the quotient-interval cardinal theorem, rewrite the L036 parity-safe incidence count as a sum of short reduced-residue interval cardinalities:

```text
paritySafeIncidenceCount n
  = ∑ q ∈ squareAnchorOddActivePrimes n,
      (paritySafeReducedQuotientInterval n q).card
```

This should be an exact finite identity.

Do not introduce PNT, Mertens, sieve asymptotics, or probability.

## 9. Full-cover factorization frontier

Add one concise theorem expressing the finite semantic meaning under full cover:

for every parity-safe candidate `r`, there exist an active prime `q` and a reduced-residue quotient `k` such that

```text
q*k = n^2+r
q ≤ n < k
gcd(q,2*n)=1
gcd(k,2*n)=1.
```

Prefer reusing the existing coverage/support APIs rather than reproving the composite-small-prime lemma.

This theorem is a factorization frontier, not a contradiction.

## 10. Stronger-beam judgment

The report must answer explicitly:

1. Did parity-safe candidate membership collapse exactly to reduced residues modulo `2*n`?
2. Did candidate cardinal become exactly `totient (2*n)`?
3. Did each active `q` wave become exactly a short reduced-residue quotient interval?
4. Does same-wave duplication become an even-separated quotient progression rather than an arbitrary collision?
5. Does this yield a new universal cardinal inequality sufficient for Legendre?

If 1–4 close but 5 does not, stop and classify **Outcome A — EXACT REDUCED-RESIDUE / QUOTIENT NORMALIZATION FRONTIER**. This is a valid A outcome because it replaces the parity/coprime two-condition world and wave duplication by one canonical modulus/factorization coordinate system.

If only partial quotient transfer closes, classify B. If the proposed exact bijection is false, classify C and provide a concrete Lean counterexample/correction.

Do not continue into another report-only reconnaissance checkpoint from inside this task.

## 11. Non-goals

- no claim of Legendre's conjecture;
- no analytic prime counting;
- no Jacobsthal bound;
- no generic graph/matching framework;
- no new silent/uncovered ledger wrapper;
- no descent;
- no RH/CFBRC imports;
- no rewrite of historical L034–L036 reports.

## 12. Validation

Run:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeReducedResidue
lake build DkMath.NumberTheory.Legendre
git diff --check
```

Also audit the new Lean source for trailing whitespace and forbidden placeholders (`sorry`, `admit`, `axiom`, `native_decide`).

## 13. Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-parity-safe-reduced-residue-quotient-normalization-260826.md
```

Record theorem names, exact proved identities, any endpoint correction required by Nat division, the stronger-beam judgment, and the stop boundary.