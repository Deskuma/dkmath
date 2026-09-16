# CGE-008 report

## Scope

Implemented the bounded, balanced-window, anchor-local exact identification
requested by `instruction-008.md`.  The attached document was treated as the
stage contract; no global existence or analytic route was added.

## Implementation

- Added `DkMath/NumberTheory/Goldbach/BalancedSignedCRTExact.lean`.
- Exported it from `DkMath.NumberTheory.Goldbach`.
- Extended `DkMathTest/NumberTheory/GoldbachBalancedReflectionAudit.lean`.

The new module proves that a canonical signed CRT progression is exactly one
balanced congruence class in the window.  Since
`goldbachBalancedOffsets n w` is `range (min (n-1) (w+1))`, while the existing
progression count uses the inclusive bound `min (n-2) w`, the public
normalization theorem makes the necessary endpoint condition `2 ≤ n`
explicit.

For strict prime pairs and triples, the module defines the corresponding
balanced support-seat sets and proves cardinal equality with
`goldbachSignedPairCRTCount` and `goldbachSignedTripleCRTCount`.  The proofs
use the CGE-007 raw-forbidden/support equivalence under the finite bound and
anchor, coordinatewise reduction modulo the product modulus, and mutually
inverse finite injections between `(residue, seat)` and seat.

The pair and triple global sums are then double-counted over strict world
pairs/triples and balanced seats.  The local strict-support pair/triple
counts are identified with `Nat.choose support.card 2` and
`Nat.choose support.card 3`, respectively.  The resulting equalities are:

```text
goldbachSignedPairCRTSum n w S = goldbachWindowPairOverlapCount n w S
goldbachSignedTripleCRTSum n w S = goldbachWindowTripleOverlapCount n w S
```

Two provider wrappers now consume these exact equalities, so the previous
comparison hypotheses are no longer required when the explicit finite-world
anchor assumptions are supplied.

## Regressions

The audit kernel-checks:

```text
n=15, w=8, S={2,3,5}: signed pair = pair overlap = 3;
                   signed triple = triple overlap = 0.
n=50, w=10, S={2,3,5,7}: signed pair = pair overlap = 12;
                          signed triple = triple overlap = 2;
                          pair-minus-triple = 10;
                          coarse capacity = 21;
                          21 < 11 + 10 is false.
```

The existing endpoint-one reflection regression remains in the audit, keeping
the proper-divisor endpoint exception visible outside the anchor-local
support bridge.  No center-aligned assumption is used by the new general
equalities.

## Boundary

No Strong Goldbach theorem, universal survivor theorem, universal budget,
analytic/RH/CFBRC input, AKS converse, coprime-to-prime shortcut, hidden
comparison axiom, `sorry`, `admit`, `native_decide`, `unsafe`, or new axiom
was added.  The result is an exact finite counting identification under its
stated hypotheses.

## Verification

Focused build:

```text
lake build DkMath.NumberTheory.Goldbach DkMathTest.NumberTheory.GoldbachBalancedReflectionAudit
```

Result: completed successfully (`8734` jobs).  The audit `#print axioms`
output for the new declarations reports only the repository's existing
logical/classical axioms: `propext`, `Classical.choice`, and `Quot.sound`.
