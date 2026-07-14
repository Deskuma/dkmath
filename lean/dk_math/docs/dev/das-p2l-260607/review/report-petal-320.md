# Petal / Float Window Report - Checkpoint 320

## Status

`cp-320` replaces the coarse depth-zero pressure branch by a positive-depth
carrier construction and closes Stages A-G without `sorry`.

New module:

```text
DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSelectedCarrier
```

It is exported by `DkMath.Collatz.PetalBridge.FloatWindow`.

## Full claims and saturation

Lean proves the strengthened exponential estimate

```text
3 <= L -> 3^L + 2^(L-1) <= 2^(2*L-1).
```

Combined with the exact block normal form and bit-width drift, it makes full
claims rigid:

```text
positive drift + claimCount = length
  <-> saturated border block.
```

For `L >= 3`, full claims would force the next start both below and above
`2^(L-v-1) * start`.  Hence the block has `L = 2`, and the existing rigidity
theorems give `v = 1` and saturation.

## Positive selected depth

The refined depth is

```text
v = 1 -> 1
v != 1 -> v - 1.
```

It is always at least one.  A positive nonsaturated block satisfies

```text
drift <= pressure(selectedPositiveDepth).
```

The `v = 1` proof now uses full-claim rigidity: nonsaturation forces
`claimCount < length`, so `claimCount - 1 <= length - 2`, exactly the depth-one
pressure.  A saturated block instead has

```text
drift = selected pressure + 1,
selected carrier = empty,
saturated token = 1.
```

Thus the refined API no longer uses depth zero.

## Actual incidence carriers

For every positive interior depth, pressure is exactly the cardinality of the
continuation fiber one level deeper.  This defines the selected carrier

```text
continuationFiber(block, selectedPositiveDepth + 1).
```

For positive nonsaturated blocks its cardinality dominates drift.

The cp-319 obstruction report is corrected: selected carriers from different
canonical blocks are disjoint.  Lean proves this from unique canonical-block
membership, then proves each selected carrier is a subset of its block.

The finite global sigma carrier retains both the block and source incidence.
Its cardinality is exactly the sum of all local selected-carrier cardinalities.
Source-incidence multiplicity is therefore closed.

## Finite injection

Positive drift units are represented anonymously by

```text
Sigma block, Fin (Int.toNat drift(block)).
```

Lean proves a finite embedding into

```text
global selected-pressure incidences
  Sum
saturated block tokens.
```

This is an incidence certificate.  It is not a future payment allocation and
does not identify a later repayment event.

## Finite-window bound

On every closed block interval, and hence on an open positive excursion,

```text
sum positive drift
  <= globalCarrier.card + saturatedIndices.card
  <= globalCarrier.card + (m - q + 2) / 2.
```

The sums are stated in `Nat` after `Int.toNat`, valid because the selected
blocks have positive drift.  The second inequality is the isolated-saturation
packing theorem.  This is not a uniform bound as `m` varies.

## Dynamic-to-fixed depth bridge

The implementation defines:

```text
selectedPressureBlocksAtDepth d
selectedPressureDepthSupport
selectedPressureBucketCarrier d.
```

The support is finite, and Lean proves the exact Fubini identity

```text
globalCarrier.card
  = sum d in depthSupport, bucketCarrier(d).card.
```

Every incidence in bucket `d` belongs to the existing canonical continuation
fiber at fixed depth `d + 1`.  Therefore the dynamic carrier has now reached
the existing endpoint-aligned fixed-depth counting API honestly.

## Genuine stopping obstruction

The remaining gap is not overlap and not depth zero.  Existing pressure APIs
count fixed-depth continuation and recovery fibers and control separated local
pulses, but they do not currently prove that every selected incidence:

1. consumes a distinct finite boundary resource;
2. creates a pressure separator when a bucket is large;
3. creates a `NoLift` obstruction when a bucket is unbounded; or
4. can be transported to an upper-zero boundary unit with bounded reuse.

Saturated tokens also remain unresolved.  A nonpositive successor can have
zero drift, so it does not necessarily repay the token.

The next theorem must be contribution-preserving transport from a fixed-depth
bucket to a bounded resource or explicit obstruction.  An upper-boundary
injection additionally requires exact bit-position preservation.  Neither is
asserted prematurely.

## Verification

The focused new-module build passes with no `sorry`.  Aggregate and top-level
build gates are recorded in the completion result after this report is added.
