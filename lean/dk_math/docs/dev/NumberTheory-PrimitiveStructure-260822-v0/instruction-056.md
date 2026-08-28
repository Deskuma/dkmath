# instruction-056 — PRIM-L041 Canonical Star / Residual Pair Decomposition / Triple-Direction Lift

Date: 2026-08-26
Branch: `wip/number-theory-primitive-structure-260822-v2`
Lean / Mathlib: v4.32.2

## 0. Goal

PRIM-L040 transports the L036 support excess exactly to canonical quotient co-support incidences.  Each unit of

```text
paritySafeSupportExcess n
```

is now a distinct old-prime pair attached to one parity-safe candidate.  PRIM-L018 already carries the full unordered pair ledger

```text
squareAnchorCoprimePrimePairOverlapCount n
  = sum_r choose(card support(r), 2).
```

The next checkpoint must connect these two surfaces exactly, not by another loose upper bound.

For one finite support of cardinality `k`, the target identity is

```text
choose k 2 = (k - 1) + choose (k - 1) 2.
```

Interpretation:

```text
all unordered pairs
  = canonical-star pairs from the selected least prime
  + residual pairs among the remaining directions.
```

The residual term must then be lifted to a genuine three-distinct-prime factorization state.

Do not introduce asymptotic estimates, a generic graph framework, descent, or a Legendre theorem in this checkpoint.

## 1. Module / imports

Suggested new module:

```text
DkMath/NumberTheory/Legendre/ParitySafePairResidual.lean
```

Import at least:

```lean
import DkMath.NumberTheory.Legendre.ParitySafeSupportExcessQuotient
import DkMath.NumberTheory.Legendre.LocalizedObstruction
```

Add the module to `DkMath/NumberTheory/Legendre.lean`.

## 2. Parity-safe unordered-pair ledger

Define a parity-safe pair ledger using the same active support as L036/L040.  A sum definition is acceptable:

```lean
noncomputable def paritySafePrimePairOverlapCount (n : ℕ) : ℕ :=
  ∑ r ∈ squareAnchorOddPointCoprimeOffsets n,
    Nat.choose (paritySafeActiveSupport n r).card 2
```

or an equivalent explicit finite incidence set if that makes later reuse cleaner.

Prove that it is bounded by the existing L018 localized pair ledger:

```text
paritySafePrimePairOverlapCount n
  <= squareAnchorCoprimePrimePairOverlapCount n.
```

Use:

```text
candidate subset coprime offsets
active support = anchor-nondivisor support on candidates.
```

Do not replace the parity-safe ledger by the whole L018 ledger.

## 3. Residual higher-order pair mass

Define

```lean
noncomputable def paritySafeResidualPairMass (n : ℕ) : ℕ :=
  ∑ r ∈ squareAnchorOddPointCoprimeOffsets n,
    Nat.choose ((paritySafeActiveSupport n r).card - 1) 2
```

or an equivalent covered-seat / erased-co-support version.

Prove the exact global decomposition:

```text
paritySafePrimePairOverlapCount n
  = paritySafeSupportExcess n + paritySafeResidualPairMass n.
```

This is the main PRIM-L041 theorem.

The proof should reduce pointwise to the finite combinatorial identity

```text
choose k 2 = (k - 1) + choose (k - 1) 2
```

with Nat-safe handling of `k = 0` and `k = 1`.

If useful, add the per-seat theorem explicitly.

## 4. Exact zero / positive criterion

Prove that the residual vanishes exactly when no parity-safe candidate has three or more active directions.

Preferred theorem shape:

```text
paritySafeResidualPairMass n = 0
  <->
forall r, r ∈ squareAnchorOddPointCoprimeOffsets n ->
  (paritySafeActiveSupport n r).card <= 2.
```

Also add a positive/existence form if clean:

```text
0 < paritySafeResidualPairMass n
  <->
exists r,
  r ∈ squareAnchorOddPointCoprimeOffsets n ∧
  3 <= (paritySafeActiveSupport n r).card.
```

Do not weaken this to one-way implication unless Mathlib Nat.choose API makes the iff disproportionately noisy; if so, record the exact blocker in the report.

## 5. Canonical residual-pair / triple incidence

Use the L040 canonical selected prime

```text
p := paritySafeCanonicalSupportPrime n r
```

and the erased quotient co-support

```text
(squareQuotientAnchorNondivisorSupport n p r).erase p
```

to define a finite residual unordered-pair incidence.  For example, per covered candidate use

```text
upperPairs ((squareQuotientAnchorNondivisorSupport n p r).erase p)
```

and assemble a global finite set over covered candidates.

Suggested semantic object:

```text
paritySafeCanonicalTripleIncidences n
```

whose elements encode

```text
(r, q, s)
```

with `q < s`, both surviving after canonical erasure.

Prove its exact cardinality:

```text
(paritySafeCanonicalTripleIncidences n).card
  = paritySafeResidualPairMass n.
```

This is not optional for Outcome A.

## 6. Triple-direction factorization packet

For every canonical triple incidence, prove a reusable packet with:

```text
r ∈ squareAnchorOddPointCoprimeOffsets n
p ∈ squareAnchorOddActivePrimes n
q ∈ squareAnchorOddActivePrimes n
s ∈ squareAnchorOddActivePrimes n
p ≠ q
p ≠ s
q ≠ s
p * q * s ∣ n^2 + r
Nat.Coprime (2*n) (p*q*s)
```

where `p = paritySafeCanonicalSupportPrime n r`.

Ordering such as `q < s` is welcome if inherited from `upperPairs`.

The proof should use L040 quotient co-support transport rather than re-derive support membership from scratch.

For the product-divisibility step, use primality/distinctness to combine `q ∣ quotient` and `s ∣ quotient`, then multiply back by the selected canonical prime `p`.

## 7. Concrete strict witness

Mandatory Lean witness:

```text
n = 16
r = 17
n^2 + r = 273 = 3 * 7 * 13
```

Verify enough of the following to show that the residual mass is genuinely new and nonzero:

```text
17 ∈ squareAnchorOddPointCoprimeOffsets 16
paritySafeActiveSupport 16 17 = {3, 7, 13}
paritySafeCanonicalSupportPrime 16 17 = 3
(card support) - 1 = 2
choose (card support) 2 = 3
choose ((card support) - 1) 2 = 1
```

and, preferably, exhibit the canonical triple incidence with residual pair `(7,13)` and recover

```text
3 * 7 * 13 = 16^2 + 17.
```

This witness is important: it distinguishes

```text
support excess = 2
all pair mass = 3
residual triple mass = 1.
```

## 8. Stronger-beam judgment

The report must answer explicitly:

1. Does L040 support excess embed as the canonical-star part of the L018 unordered-pair ledger?
2. Is the complement exactly `choose(k-1,2)` seatwise and `paritySafeResidualPairMass` globally?
3. Is residual positivity equivalent to the existence of a parity-safe seat with at least three active directions?
4. Does every residual unit lift to three distinct active primes whose product divides the complete point?
5. Does this produce any universal bound, descent, or Legendre proof?  Expected answer for this checkpoint: no unless Lean proves a genuinely new stronger theorem beyond the requested surface.

Interpretation to preserve:

```text
support size 0/1 : no pair obstruction
support size 2   : pair ledger = canonical star mass
support size >=3 : extra residual pair mass = triple-direction structure
```

## 9. Outcome classification

Classify exactly one:

### Outcome A — EXACT STAR/RESIDUAL PAIR DECOMPOSITION / TRIPLE-DIRECTION LIFT

Require all of:

- parity-safe pair ledger;
- exact `pair = supportExcess + residual` decomposition;
- residual zero/positive support-cardinality criterion;
- finite canonical triple incidence with exact cardinality;
- triple-product factorization packet;
- `(16,17)` strict witness.

### Outcome B — EXACT PAIR DECOMPOSITION ONLY

Use if the exact pair/support-excess decomposition closes but the canonical triple incidence or triple-product packet does not close cleanly.

### Outcome C — ONLY LOOSE DOMINATION

Use if the result collapses to

```text
supportExcess <= pairOverlapCount
```

without the exact residual decomposition.

## 10. Stop boundary

Do not in this checkpoint:

- build a generic hypergraph/clique abstraction;
- iterate to arbitrary `k`-tuples;
- introduce PNT, Mertens, Rosser--Schoenfeld, Jacobsthal, analytic sieve, or RH/CFBRC;
- attempt infinite descent;
- assert or prove `LegendreConjecture` unless it follows unexpectedly from the requested finite theorems.

If Outcome A closes, stop and report.  The next step will decide whether the triple-direction residual can be consumed by a localized triple-product wave bound or whether the depth ledger must be joined first.

## 11. Report / validation

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-parity-safe-star-residual-triple-direction-260826.md
```

Validate:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafePairResidual
lake build DkMath.NumberTheory.Legendre
git diff --check
```

Audit the new Lean source for trailing whitespace and forbidden placeholders:

```text
sorry
admit
axiom
native_decide
```

No full repository build unless an unexpected dependency change makes it necessary.
