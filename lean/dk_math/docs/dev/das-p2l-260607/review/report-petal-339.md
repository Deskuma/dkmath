# Petal / Collatz implementation report: checkpoint 339

Date: 2026-07-17

## Status

Checkpoint 339 reached the finite-certificate boundary and stopped at an
exactly identified arithmetic obligation.  All new Lean declarations compile
without `sorry`.

The implementation is in:

```text
DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceAgeFiniteCertificate.lean
DkMath/Collatz/PetalBridge/FloatWindow.lean
```

The new `CanonicalSourceAgeFiniteCertificate` module keeps the certificate
preparation work out of the already large horizon arithmetic module.

## Padded carry word

The new finite word

```text
canonicalPreBlockCarryWord n H m : Fin H -> Bool
```

represents the `H` source addresses immediately before block `m`.  Offset `r`
represents `start - (r + 1)` only when `r + 1 <= start`; invalid offsets are
false.  Thus early blocks do not duplicate source zero through natural-number
underflow.

The following all-regime identity is proved:

```text
canonicalPreBlockCarryWordTrueCount n H m
  = card (canonicalPreBlockCarryCarrier n H m).
```

In the mature regime this also gives the requested direct mass bridge:

```text
canonicalRecentCarryMassBeforeStart n H m
  = card (canonicalPreBlockCarryCarrier n H m)
  = canonicalPreBlockCarryWordTrueCount n H m.
```

The true-bit population is proved to lie between `0` and `H`.

## Window coboundary

Every mature block window satisfies:

```text
frontierWindowSum(H,q,L)
  = frontierWindowSum(0,q,L)
      + recentMass(H,q)
      - recentMass(H,q+L).
```

Equal padded carry words at both endpoints imply equal word populations and
therefore equality of the horizon-`H` and horizon-zero window weights.

This is an endpoint correction, not an independent source of accumulated
weight.

## Generic coboundary API

`FiniteSignedTransition.lean` now contains a generic finite-path API:

```text
weight'(a,b) = weight(a,b) + correction(a) - correction(b).
```

Lean proves:

- path weights differ only by endpoint correction;
- state-closed path weights are invariant;
- signature-closed path weights are invariant when the correction is
  determined by the signature;
- a positive closed-signature path remains positive after such reweighting.

Thus a positive-horizon carry correction cannot erase a positive closed cycle
when the endpoint carry state is part of the signature.

## Pointwise necessity of finite potentials

Every

```text
CanonicalFiniteSourceAgeFrontierPotentialCertificate n H Signature
```

now yields an integer `B` such that every actual frontier increment is at most
`B`.  The proof takes a minimum of the potential on the finite signature type.

This pointwise bound is necessary for the current finite-potential method.  It
does not follow merely from nonpositive prefixes for an arbitrary signed flow.

## Frontier boundedness audit

This checkpoint obtained a stronger reduction than a numerical audit.

For every mature block:

```text
frontier(H,m) <= frontier(0,m) + H
frontier(0,m) <= frontier(H,m) + H.
```

Because block `m` starts no earlier than source time `m`, only the first `H`
blocks can be non-mature.  Every finite integer prefix has an upper bound, so
Lean proves the global equivalence:

```text
CanonicalSourceAgeFrontierIncrementUniformUpperBound n H
  <->
CanonicalSourceAgeFrontierIncrementUniformUpperBound n 0.
```

The exact reflected max normal form at horizon zero then gives:

```text
CanonicalSourceAgeFrontierIncrementUniformUpperBound n 0
  <->
CanonicalEndpointAccountingTermUniformUpperBound n.
```

Therefore, for every fixed finite horizon:

```text
frontier increments are uniformly bounded above
  <->
raw endpoint drifts are uniformly bounded above.
```

This separates the branches precisely:

- saturated blocks are already bounded, with horizon-zero value `1`;
- zero-drift blocks have horizon-zero value `0`;
- positive-pressure blocks transmit raw endpoint drift unchanged at horizon
  zero;
- a fixed positive horizon adds only a bounded coboundary and cannot hide an
  unbounded positive-pressure family.

No symbolic unbounded endpoint-drift family was proved in this checkpoint.
Accordingly, the report does not claim that a finite certificate is
impossible.

## Exact collisions versus upper projections

The generic API now distinguishes:

```text
FiniteSignatureDeterministicallyRecoversEdgeWeight
FiniteSignatureExactWeightCollision
FiniteSignatureProjectedUpperWeightSound
```

An exact collision formally refutes deterministic exact-weight recovery.
However, if a sound projected upper table is supplied, both unequal concrete
weights remain bounded by their common projected edge entry.  Therefore an
ordinary collision is diagnostic only; it is not a certificate impossibility
theorem.

The stronger generic theorem is:

```text
exists finite successor upper-weight table
  <->
exists uniform upper bound on concrete successor weights.
```

The forward proof bounds all finite table entries by a finite sum of their
absolute values.  The reverse proof uses a constant upper table.

## Horizon-one residual and saturated word update

For a saturated predecessor the following nonnegative scalar residuals were
defined:

```text
successorNonfinalDemand
successorExtraConsumed.
```

The exact identity is:

```text
frontier(1,m+1)
  = successorNonfinalDemand - successorExtraConsumed.
```

This is scalar accounting only.  It does not identify the saturated final
source as the concrete source consumed by the successor.

For a mature saturated block, the successor pre-block word extended by two
bits has:

- first bit true;
- second bit true;
- remaining tail equal to the old word shifted by two positions.

The frontier weight is the sum of the two crossing extended-word bits minus
one.  This single formula recovers horizon-zero weight `1` and mature
horizon-one weight `0`.

## First candidate signature

The finite type

```text
CanonicalSourceAgeFrontierSignature H queueCap
```

contains:

- the padded carry word;
- a capped queue coordinate with `queueCap + 1` as an overflow marker;
- negative, zero, or positive endpoint-drift class;
- saturated-block indicator;
- final-source carry indicator.

The cap is only an observable.  It does not assume a queue bound.

For this concrete candidate Lean proves:

```text
exists sound projected successor upper-weight table
  <->
CanonicalEndpointAccountingTermUniformUpperBound n.
```

The same theorem holds for every finite candidate signature.  Refining the
signature may improve collision diagnostics and cycle visibility, but it
cannot manufacture the missing arithmetic ceiling.

## Facts now fixed

1. The padded carry word is correct even at the origin and exactly counts the
   finite pre-block carrier.
2. Positive horizon is a bounded endpoint coboundary of horizon zero.
3. All fixed finite horizons have the same pointwise upper-boundedness status.
4. That status is exactly uniform upper boundedness of raw endpoint drift.
5. Every current finite-potential certificate implies the endpoint-drift
   bound as a necessary consequence.
6. Exact signature collisions refute only deterministic exact recovery.
7. A sound finite upper-weight table exists exactly when the concrete edge
   sequence is uniformly bounded above.
8. The first finite signature candidate is genuinely finite and noncircular,
   but its sound upper-weight obligation is not yet discharged.

## Honest stopping boundary

Stages A-G, J, K, and the Stage-L candidate signature are implemented.
Stages H-I were not instantiated unconditionally.

The reason is now a theorem rather than a design concern: before any finite
reachable projected graph can receive a sound integer upper weight on all
realized successor edges, one must prove

```text
CanonicalEndpointAccountingTermUniformUpperBound n.
```

Supplying that upper table without this proof would hide the main arithmetic
obligation inside the certificate.  Using the queue cap as if it were an
actual queue bound would likewise assume the desired conclusion.

This is not a proof of unboundedness and not a proof that finite certificates
cannot exist.  It is the exact dependency boundary for the present method.

## Suggested next implementation

Attack the endpoint-drift ceiling directly, especially the positive-pressure
branch.  Two honest routes remain:

1. prove a symbolic global upper bound for `endpointAccountingTerm n m` at
   fixed `n`;
2. construct a symbolic unbounded family, which would refute every finite
   projected upper table for that root and every fixed horizon.

Only after the first route succeeds should the reachable projected graph and
potential verification stages be instantiated.  If the second route
succeeds, the current pointwise finite-potential shape must be replaced rather
than refined by more signature bits.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeFiniteCertificate
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b|\badmit\b" \
  DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean \
  DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceAgeFiniteCertificate.lean
git diff --check
```

The `rg` check returned no matches.
