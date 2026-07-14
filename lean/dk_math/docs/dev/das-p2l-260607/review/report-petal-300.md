# Petal implementation report 300

## Result

The Float/Pressure branch now uses a time/depth incidence relation rather than
an invalid single-valued map from orbit time to pressure depth.

## Proven surfaces

- `OrbitDepthRetainedAt`: exact membership in the parent all-ones cell.
- `OrbitDepthContinuesBeyond`: membership in the deeper all-ones child.
- `OrbitDepthRecoversExactlyAt`: exact exit depth.
- Pointwise equivalences with all three existing power-of-two residue cells.
- Fiber counts identified exactly with retention, continuation, and recovery
  mass.
- Exact fiber partition: retention = recovery + continuation.
- Integer pressure identity:

```text
SourcePressureMarginInt = continuation fiber - exact recovery fiber.
```

- Positive pressure iff continuation incidences outnumber exact recoveries.

## Generic delayed horizon

Exact all-ones depth decreases by one under each recovery transition.  For an
exact-depth witness `d >= 2`, the first forced extra-height payment occurs at
the exact index:

```text
i + d - 1
```

Every strict binary-width growth debt therefore has a proof-carrying delayed
Petal payment witness.  The implementation keeps this as a relation.

## Collision surface and stopping point

`FloatPaymentCollisionAt n j` records two distinct growth debts selecting the
same payment index.  It implies an actual `height >= 2` payment and exposes
both debt sources.

What does not yet follow is positive pressure.  That conclusion needs a bound
relating the fiber of debts over a payment index to the exact-depth recovery
and continuation fibers.  Existing APIs prove existence of discharge, but no
injectivity or multiplicity-accounting theorem.  This unmatched multiplicity
is preserved explicitly instead of being erased by a function choice.

## Signature work

The value-free signature now has a validity-aware disjoint/overlap case split.
The overlap branch remains intentionally conditional on a future shared-bit
consistency predicate.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.PressureIncidenceBridge
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
git diff --check
```

No `sorry` or `axiom` was added under `FloatWindow`.
