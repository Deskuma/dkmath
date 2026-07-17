# Petal / FloatWindow implementation report: checkpoint 342

## Status

Checkpoint 342 is implemented without adding `sorry`.

This checkpoint corrects the interpretation of the endpoint counter introduced
at checkpoint 341.  The zero-reserve credit is not merely awaiting a local
preservation lemma.  It is refuted as a general signed-counter certificate by
every root whose first canonical endpoint drift is positive.

The corrected API separates three different questions:

1. whether one reserve works uniformly for every root;
2. whether one fixed root has bounded cumulative canonical width;
3. whether one fixed root has bounded pointwise endpoint drift.

The first statement is false.  The second and third remain open for a general
fixed root, and the second is strictly the stronger target in the current API.

## Corrected zero-reserve diagnosis

The duplicate initial block-state theorem was removed from
`CanonicalAllOnesDrift.lean`.  The all-ones proofs now use the generic theorem

```text
canonicalBlockStartState_zero_eq_root.
```

For the zero-reserve endpoint credit, Lean now proves the exact first-step
identity

```text
canonicalEndpointCounterCredit n 1
  = - endpointAccountingTerm n 0.
```

Therefore positive initial drift gives strictly negative credit after one
transition.  This is a counterexample to the required nonnegativity invariant,
not an unproved guard.

The odd all-ones family makes the failure symbolic:

```text
credit(allOnesOdd(2*r+1), 1) <= -r.
```

Using the positive parameter `r + 1` gives strict negativity.  The new reserve
module consequently proves that no `SignedCounterCertificate` can have both

```text
weight := endpointAccountingTerm n
credit := canonicalEndpointCounterCredit n
```

when the initial endpoint drift is positive.  An explicit no-certificate
theorem is also provided for the positive all-ones subfamily.

## Cumulative width reserve

The new predicate

```text
CanonicalWidthWithinReserve n B
```

states that every canonical block-start width is at most the root width plus
`B`.  Its existential fixed-root form is

```text
RootwiseCanonicalWidthBound n.
```

Lean proves the one-way implication

```text
RootwiseCanonicalWidthBound n
  -> RootwiseEndpointDriftBound n.
```

The reason is structural: each endpoint drift is one difference between two
successive widths, while the cumulative predicate bounds every absolute width
level.  A bound on all cumulative levels bounds every positive increment.

No reverse implication is proved or claimed.  Uniformly bounded one-step
increments do not, by themselves, bound the cumulative level.

## Reserved credit and conditional certificate

The corrected endpoint credit is

```text
reservedCredit(n, B, M)
  = B + rootWidth - blockStartWidth(M).
```

Lean proves:

- initial reserved credit is exactly `B`;
- its successor recurrence subtracts the exact endpoint drift;
- its nonnegativity is equivalent to the current width being inside reserve;
- all-time nonnegativity is equivalent to `CanonicalWidthWithinReserve n B`;
- existence of such a reserve is equivalent to
  `RootwiseCanonicalWidthBound n`.

An explicit width-bound hypothesis now constructs

```text
canonicalEndpointReservedCounterCertificate.
```

This is a conditional certificate.  It does not prove that a reserve exists
for any particular root.  Under that hypothesis, the generic counter theorem
does prove the finite prefix estimate

```text
sum(endpointAccountingTerm, [0, M)) <= B.
```

## Global reserve obstruction

The predicate

```text
GlobalCanonicalWidthReserveBound
```

asks for one natural reserve that works for every odd root.  Lean proves its
negation.  The existing all-ones family supplies roots with initial endpoint
drift larger than any proposed reserve, so the width bound already fails at
the first completed block.

This theorem does not refute a root-dependent reserve.  The quantifier order is
essential:

```text
not (exists B, forall n, widthBound n B)
```

does not imply

```text
forall n, not (exists B, widthBound n B).
```

## Reflected-queue audit

The existing scalar queue is exactly the maximum positive signed suffix drift.
Checkpoint 342 adds the direct block-coordinate bridge

```text
canonicalEndpointWidth n m
  = bitWidth (canonicalBlockStartState n (m + 1)).
```

It then proves

```text
RootwiseCanonicalWidthBound n
  iff
exists C, CanonicalOutstandingClaimQueueUniformUpperBound n C.
```

This is useful, but it does not close the width problem.  The queue theorem is
an exact reformulation of the same cumulative boundedness target.  Existing
queue, source-age, claim-hole, and terminal-valuation bridges do not currently
supply an independent lower bound preventing arbitrarily long positive suffix
drift.

The required next input remains genuinely arithmetic or dynamical, such as:

- an absorption lower bound for claim holes plus terminal valuation relative
  to block length;
- a uniform repayment-lag theorem;
- exclusion of a pumpable positive-drift transition cycle; or
- a finite-state discharge theorem independent of the desired width bound.

Defining another credit as the negative of the target invariant would only
rename this obstruction.

## Pointwise endpoint branch remains open

The exact fixed-root pointwise question is still

```text
exists B, forall m,
  blockLength n m
    <= claimHoles n m + terminalValuation n m + B.
```

This is equivalent to `RootwiseEndpointDriftBound n`.  It is weaker than the
cumulative width-reserve question and must not be replaced by it.

No independent uniform lower bound on

```text
claimHoles + terminalValuation
```

relative to block length was found in the queue audit.  The exact conservation
identity remains the correct local surface for that search.

## Finite high-drift increments

`CanonicalHighDrift.lean` now gives an exact successor description of the
finite event carrier.  Extending the horizon from `M` to `M + 1` either inserts
the new index `M` or leaves the carrier unchanged, according to whether the new
drift reaches threshold `K`.

The corresponding membership theorem is

```text
m in events(M + 1)
  iff m in events(M) or (m = M and K <= drift(M)).
```

The event count therefore satisfies the exact finite update

```text
eventCount(M + 1)
  = eventCount(M) + if K <= drift(M) then 1 else 0.
```

These are finite prefix statements only.  They do not imply infinitely many
events, eventual stabilization, or a finite all-time event count.

## Scaled conservation clarification

The existing `A`-scaled conservation theorem is now documented as algebraic
transport of the exact integer identity.  The parameter `A` is not yet a
spiral-growth coefficient, and no logarithmic or asymptotic interpretation is
introduced in this module.

## Facts fixed by Lean

1. Zero-reserve credit equals negative initial drift after one block.
2. Positive initial drift makes the zero-reserve certificate impossible.
3. The all-ones family gives symbolic, arbitrarily large first-step failure.
4. No finite reserve works uniformly over every odd root.
5. A supplied fixed-root cumulative width reserve gives a valid signed counter.
6. Cumulative width boundedness implies pointwise endpoint-drift boundedness.
7. No converse implication has been established.
8. Fixed-root width boundedness is equivalent to uniform reflected-queue
   boundedness, so the queue does not independently solve the target.
9. Finite high-drift carriers and their counts have exact one-step updates.
10. The fixed-root pointwise endpoint bound remains a separate open branch.

## Branch decision

The zero-reserve branch is closed negatively.  It must not be retried as a
certificate without changing its initial reserve.

The reserved-credit branch is complete as a conditional API.  Its remaining
premise is exactly fixed-root cumulative width boundedness, now also identified
with reflected-queue boundedness.

The next productive branch should seek an independent absorption or discharge
theorem.  Until that input is proved, neither the cumulative width reserve nor
the weaker pointwise endpoint bound should be promoted to an unconditional
theorem.

## Verification

The checkpoint was checked with targeted and aggregate builds:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalHighDrift
lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointReserve
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
git diff --check
```

