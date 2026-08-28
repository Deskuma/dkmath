# PRIM-L065 — Full-cover capacity frontier / high-support bottleneck

## Outcome

Outcome A+ — FULL-COVER CAPACITY FRONTIER COMPLETE.

The existing finite ledgers are combined into the controlled upper frontier

```text
2*PairOverlap + 3*Collision
  <= 3*SupportExcess + 2*LowCostCapacity + 2*DepthResidualCapacityExcess.
```

Under the hypothesis `SquareOffsetsFullyCovered n`, support excess is
eliminated by the exact candidate/incidence balance, yielding the candidate,
totient, and reduced-quotient forms.

## Implemented module

The new module
`DkMath.NumberTheory.Legendre.ParitySafeFullCoverCapacityFrontier` provides:

- residual-pair-mass compression into `paritySafeLowCostResidualCapacity`;
- the support-charged doubled pair-overlap frontier;
- `paritySafeUncoveredCandidates_eq_empty_of_fullyCovered`;
- the full-cover exact balance
  `Candidate.card + SupportExcess = IncidenceCount`;
- support-free candidate and `Nat.totient (2*n)` frontiers;
- the exact reduced quotient-interval rewrite consumer.

The public facade `DkMath.NumberTheory.Legendre` imports this module.
Module and theorem docstrings state the upper-bound direction and the formal
boundary explicitly.

## Proof spine

The residual compression uses the existing L058 residual upper bound together
with the L063 Near-wave and L064 Fourth-gated cardinality bounds:

```text
ResidualPairMass <= LowCostCapacity + Terminal + DepthResidualCapacityExcess.
```

Combining this with

```text
PairOverlap = SupportExcess + ResidualPairMass
2*Terminal + 3*Collision <= SupportExcess
```

gives the primary charged inequality without discarding the `3*Collision`
term.

For full cover, an uncovered candidate would be a candidate whose associated
`SquareOffset` is not covered, contradicting `SquareOffsetsFullyCovered n`.
Thus the existing covered/uncovered card split reduces to
`Candidate.card + SupportExcess = IncidenceCount`.  The candidate card is
then rewritten exactly as `Nat.totient (2*n)`, and incidence count exactly as
the reduced quotient-interval sum.

## Formal boundary

The full-cover predicate is assumed; it is not proved here.  The resulting
frontier is an upper-control statement and is not used to replace the
left-hand side of the L062 lower frontier by `LowCostCapacity`.  No
contradiction or claim of numerical/asymptotic smallness follows from this
checkpoint.

The remaining raw structural term is
`paritySafeRechargeExactDepthResidualPairCapacityExcess`.

## Non-goals

New bounds for depth residual capacity, fifth direction, `Nat.minFac`
injectivity, Near asymptotics, prime-counting estimates, descent, full-cover
contradiction, Legendre's conjecture, and RH remain outside scope.

## Validation

- `lake build DkMath.NumberTheory.Legendre.ParitySafeFullCoverCapacityFrontier`
  passed.
- `lake build DkMath.NumberTheory.Legendre` passed.
- `git diff --check` passed.
- Changed Lean source was checked for `sorry`, `admit`, `axiom`,
  `native_decide`, and global `maxHeartbeats` additions.
