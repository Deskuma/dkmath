# PRIM-L040 — Canonical Quotient Co-Support / Support-Excess Transport Lean Judgment

Date: 2026-08-26
Branch: `wip/number-theory-primitive-structure-260822-v2`
Environment: Lean / Mathlib v4.32.2

## 0. Goal

PRIM-L036 defined the parity-safe candidate-side support multiplicity excess

```text
paritySafeSupportExcess n
  = Σ r in candidate, (card(activeSupport n r) - 1).
```

PRIM-L039 has now completed the two-adic fold on the wave side.  Do **not** continue by adding another raw-wave estimate in this checkpoint.

Instead, transport the candidate-side excess through the existing PRIM-L015 quotient-support theorem.  After selecting one canonical old prime `p` from a covered parity-safe seat, every *other* old direction survives in the complementary quotient.  Therefore `card support - 1` should be exactly the cardinality of the quotient old-support after erasing the selected direction.

The target is to turn the abstract incidence excess into an exact one-step factorization state:

```text
candidate support excess
  -> choose canonical old prime p
  -> divide point by p
  -> off-diagonal old directions remaining in quotient
  -> distinct old-prime pair p,q
  -> p*q | n^2+r.
```

This is a proof-backed structural checkpoint.  It is **not** a request for a universal estimate, analytic prime counting, graph abstraction, descent, or a proof of Legendre's conjecture.

Suggested module:

```text
DkMath/NumberTheory/Legendre/ParitySafeSupportExcessQuotient.lean
```

Suggested imports:

```lean
import DkMath.NumberTheory.Legendre.ParitySafeMobiusOddCorrection
import DkMath.NumberTheory.Legendre.QuotientSupport
```

Add the module to `DkMath/NumberTheory/Legendre.lean`.

## 1. Canonical selected old prime

Define a canonical selected prime for one parity-safe candidate, using the least active-support member when the support is nonempty and a harmless default otherwise.

Suggested shape:

```lean
noncomputable def paritySafeCanonicalSupportPrime (n r : ℕ) : ℕ :=
  if h : (paritySafeActiveSupport n r).Nonempty then
    (paritySafeActiveSupport n r).min' h
  else 0
```

For a covered parity-safe candidate prove the expected membership packet.  At minimum recover:

```text
p := paritySafeCanonicalSupportPrime n r
p ∈ paritySafeActiveSupport n r
p ∈ squareOffsetAnchorNondivisorSupport n r
p ∈ squareAnchorOddActivePrimes n
```

Reuse

```text
squareOffsetAnchorNondivisorSupport_eq_paritySafeActiveSupport_of_candidate
```

from L036.  Do not duplicate the candidate-support definitions.

## 2. Mandatory per-seat exact transport

For a parity-safe candidate `r` with nonempty active support, let

```text
p = paritySafeCanonicalSupportPrime n r.
```

Prove the exact equality

```text
(paritySafeActiveSupport n r).card - 1
  = ((squareQuotientAnchorNondivisorSupport n p r).erase p).card.
```

This should reuse the PRIM-L015 theorem

```text
erase_squareQuotientSupport_eq_erase_offsetSupport
```

plus the candidate support equality.  The theorem must be an exact equality, not only `≤`.

Interpretation:

```text
support multiplicity beyond the first direction
  = off-diagonal old directions surviving after one canonical division.
```

## 3. Mandatory global support-excess rewrite

Rewrite the complete L036 quantity as a sum over covered candidates only:

```text
paritySafeSupportExcess n
  = Σ r in paritySafeCoveredCandidates n,
      card ((squareQuotientAnchorNondivisorSupport n
        (paritySafeCanonicalSupportPrime n r) r).erase
        (paritySafeCanonicalSupportPrime n r)).
```

The uncovered-candidate terms on the original candidate sum are zero because their active support is empty.  Prove this finitely; do not introduce subtraction in `ℤ` merely to avoid the `Nat` bookkeeping.

This theorem is the primary acceptance theorem of the checkpoint.

## 4. Canonical quotient co-support incidence set

Define a finite incidence set recording the off-diagonal directions counted by the RHS above.  A reasonable shape is a `Finset (ℕ × ℕ)` of `(r,q)` pairs such that:

```text
r ∈ paritySafeCoveredCandidates n
p := paritySafeCanonicalSupportPrime n r
q ∈ (squareQuotientAnchorNondivisorSupport n p r).erase p.
```

If convenient, define it using `Finset.product` + `filter`, `biUnion`, or another elementary finite construction.  Do **not** introduce a general graph library.

Prove exact cardinality:

```text
(paritySafeCanonicalQuotientCoSupportIncidences n).card
  = paritySafeSupportExcess n.
```

The exact name is flexible.

## 5. Mandatory incidence factorization packet

For every incidence `(r,q)` in the canonical co-support incidence set, recover the selected prime

```text
p := paritySafeCanonicalSupportPrime n r
```

and prove, at minimum:

```text
r ∈ squareAnchorOddPointCoprimeOffsets n
p ∈ squareAnchorOddActivePrimes n
q ∈ squareAnchorOddActivePrimes n
p ≠ q
q ∣ squareOffsetSupportQuotient n p r
p * q ∣ n^2 + r
Nat.Coprime (2*n) (p*q)
```

An existential second cofactor is preferred:

```text
∃ t, p * q * t = n^2 + r.
```

Use existing quotient-support transfer; do not reprove unique factorization.

### Product-size compression

If cleanly provable from the active-prime packet, also prove

```text
15 ≤ p * q
```

because `p` and `q` are distinct odd primes.  Then expose the corresponding finite size consequence, e.g.

```text
∃ t, p * q * t = n^2+r ∧ 15 * t ≤ n^2 + 2*n.
```

This is useful but secondary to the exact support-excess transport.  Do not block Outcome A solely on a cumbersome normalization of the constant `15` if the exact pair-factorization layer is complete.

## 6. Mandatory direction/depth false beam

Keep distinct-prime support multiplicity separate from selected-prime depth.

Use the concrete parity-safe seat

```text
n = 5
r = 2
n^2+r = 27 = 3^3.
```

Lean should confirm the material distinction:

```text
2 ∈ squareAnchorOddPointCoprimeOffsets 5
paritySafeActiveSupport 5 2 = {3}
(paritySafeActiveSupport 5 2).card - 1 = 0
3 ∣ squareOffsetSupportQuotient 5 3 2
3 ∈ squareQuotientAnchorNondivisorSupport 5 3 2
((squareQuotientAnchorNondivisorSupport 5 3 2).erase 3).card = 0
```

The point is:

```text
supportExcess does NOT count repeated powers of the selected prime.
```

PRIM-L017 already separates singleton-depth from multi-support.  This checkpoint must preserve that distinction rather than silently merging direction multiplicity with valuation depth.

## 7. Stronger-beam judgment

At the end of the report answer explicitly:

1. Is `paritySafeSupportExcess` exactly transportable to canonical quotient off-diagonal co-support mass?
2. Does every unit of that transported excess produce a distinct-old-prime product divisor `p*q | n^2+r`?
3. Is selected-prime self-depth excluded from this mass exactly as intended?
4. Does the transport yield a genuinely smaller/reusable factorization state, or only a coordinate rewrite?
5. Which existing L017--L019 obstruction/pair ledger is now the nearest reusable consumer of this canonical pair-incidence data?

Do not claim descent unless a smaller state with the required covering/obstruction hypothesis is reconstructed.

## 8. Outcome classification

Classify the checkpoint as:

### Outcome A — EXACT SUPPORT-EXCESS / QUOTIENT CO-SUPPORT TRANSPORT

Require all of:

1. canonical support prime API;
2. per-seat exact `card support - 1 = erased quotient-support card`;
3. global `paritySafeSupportExcess` exact rewrite;
4. finite canonical co-support incidence set with exact cardinality;
5. pair-factorization packet `p ≠ q`, active `p,q`, `p*q | n^2+r`;
6. `(n,r)=(5,2)` direction-vs-depth false beam.

### Outcome B — LOCAL EXACT TRANSPORT ONLY

Use if the per-seat theorem closes but the global incidence/cardinality layer does not.

### Outcome C — NO MATERIAL TRANSPORT

Use if the construction collapses back to the original support definition without a reusable quotient/factorization theorem.

## 9. Stop boundaries

Do not in this checkpoint:

- prove or assume a universal bound for `paritySafeSupportExcess`;
- add PNT / Mertens / Rosser-Schoenfeld estimates;
- add Jacobsthal or generic sieve bounds;
- introduce a graph/matching framework;
- start an infinite descent;
- hand-build special large cliques;
- claim `LegendreConjecture`.

The purpose is to convert the surviving candidate-side multiplicity into exact quotient/factor-pair data and identify the next actual arithmetic consumer.

## 10. Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-parity-safe-support-excess-quotient-transport-260826.md
```

Record the exact theorem surface, direction/depth false beam, strongest factorization consequence, and the next reusable existing ledger.

## 11. Validation

Run:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeSupportExcessQuotient
lake build DkMath.NumberTheory.Legendre
git diff --check
```

Also audit the new Lean source for trailing whitespace and forbidden placeholders (`sorry`, `admit`, `axiom`, `native_decide`).

Do not run the full repository build unless an unexpected dependency change requires it.
