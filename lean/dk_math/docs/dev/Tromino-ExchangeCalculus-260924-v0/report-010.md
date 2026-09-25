# TRM-011 report: boundary signature / XOR conservation kernel

Date: 2026-09-25
Branch: `research/Tromino-ExchangeCalculus-260924-v0`

## Scope

TRM-011 introduces a finite ordered boundary certificate and proves the
characteristic-two conservation law from its port multiplicities. It reuses
`BoundaryContact`, `forbiddenDelta`, and
`forbiddenDelta_eq_zero_iff` from `PieceExchange`.

No pairing, transition graph, path transport, planar embedding, BoundaryIR,
physical boundary extraction, residual optimization, or Four Color claim was
introduced. The signature is an algebraic certificate supplied independently;
no arbitrary geometric region is claimed to produce one.

## Contact delta and directions

`contactDelta` is the thin readable alias of `forbiddenDelta`:

```text
contactDelta c = c.inside + c.outside
```

The bridge theorem is:

```text
contactDelta c = 0 ↔ c.inside = c.outside
```

The three nonzero directions are named algebraically, without color names:

```text
deltaA = (1,0)
deltaB = (0,1)
deltaC = (1,1)
```

They are nonzero, pairwise distinct, satisfy the cyclic sum laws, and every
nonzero `TrominoState` is exactly one of them.

## Ordered boundary signature

`BoundarySignature` is:

```lean
structure BoundarySignature where
  arity : Nat
  contact : Fin arity → BoundaryContact
  proper : ∀ i, (contact i).inside ≠ (contact i).outside
```

The `Fin arity` index preserves port identity and multiplicity. No `Finset` of
contacts is used as the primary representation. `boundaryDelta` is nonzero at
every port by the contact bridge, and every boundary label is classified as
`deltaA`, `deltaB`, or `deltaC`.

## Sum and multiplicity

```text
boundarySum S = ∑ i : Fin S.arity, boundaryDelta S i
BoundaryConserved S := boundarySum S = 0
```

`boundaryLabelCount S delta` is the cardinality of the filtered port index
set. The implementation proves the zero-label count and:

```text
countA + countB + countC = S.arity
```

The coordinate formulas are:

```text
(boundarySum S).1 = (countA + countC : ZMod 2)
(boundarySum S).2 = (countB + countC : ZMod 2)
```

They are obtained from finite-sum indicator functions and retain repeated
ports.

## Main parity theorem

The central theorem is:

```text
BoundaryConserved S ↔
  countA % 2 = countC % 2 ∧
  countB % 2 = countC % 2
```

Thus the three nonzero labels occur with the same parity. The derived
`boundaryConserved_even_or_odd` theorem gives the two possible classes:

```text
all three counts even ∨ all three counts odd
```

No pairing theorem is included yet.

## Relation to piece rescue

The same `contactDelta` has two deliberately different uses:

- `forbiddenExchangeSet` stores the image of contact deltas and therefore
  forgets duplicate contacts;
- `BoundarySignature` counts every indexed boundary port and therefore retains
  multiplicity.

The audit includes two identical proper contacts: their signature count for
`deltaA` is `2`, while the corresponding singleton forbidden set has card `1`.
The two semantics are not conflated.

## Regression audit

`DkMathTest/Tromino/BoundarySignatureAxiomAudit.lean` checks:

1. the contact-zero bridge and nonzero directions;
2. cyclic direction sums and per-port nonzero classification;
3. the zero-label count and total multiplicity law;
4. the empty signature;
5. the even signature `A A B B C C`;
6. the odd signature `A A A B B B C C C`;
7. the invalid signature `A A B C` is not conserved;
8. duplicate-contact multiplicity versus `forbiddenExchangeSet` image
   cardinality;
9. the even/odd dichotomy.

## Computability and axiom audit

All signature data and counting definitions are computable. No declaration is
marked `noncomputable`; no new `axiom`, `sorry`, `admit`, or `unsafe`
declaration was added. The substantive audited theorems depend only on the
standard `propext`, `Classical.choice`, and `Quot.sound` dependencies already
present in the reused finite exchange infrastructure.

This checkpoint suggests no boundary-signature invariant for the next step:
the result is purely a multiplicity/conservation statement and contains no
positional, cyclic-order, or orientation data.

## Validation

Focused build:

```text
lake build DkMath.Tromino.PieceExchange \
  DkMath.Tromino.BoundarySignature \
  DkMathTest.Tromino.BoundarySignatureAxiomAudit
```

Result: successful (`Build completed successfully (1494 jobs)`). `git
diff --check` and explicit checks for the new untracked files completed
without whitespace errors. Production and audit sources were scanned for
forbidden constructs; no implementation occurrence was found.

## Stop boundary

TRM-011 stops at the ordered finite boundary certificate and the exact parity
conservation law. Pairing, TransitionGraph, XOR path transport, physical
boundary extraction, residual optimization, and Four Color claims remain
deferred.
