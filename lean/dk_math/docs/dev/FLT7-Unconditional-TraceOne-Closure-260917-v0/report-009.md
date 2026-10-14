# FLT7TC-005R4 — Primitive second-case classification and global ramified resolution

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

The attached `instruction-009.md` was treated as the bounded implementation
contract, separately from the user's request.  This checkpoint normalizes
every primitive exponent-seven counterexample into one common ramified summit
surface; it does not prove an FLT7 contradiction.

## Checked primitive classification

`PrimitiveSevenDivisibleEndpoint` records the three possible unique
seven-divisible endpoints.  The theorem
`primitiveSevenDivisibleEndpoint_of_counterexample` uses the existing
`sevenEndpointResidueSector_of_counterexample` classification.  Its ramified,
away-right, and away-left branches yield the `x`, `y`, and `z` constructors,
respectively.  The remaining sum sector supplies `7 ∣ y + z` and is discharged
by `no_counterexample_of_seven_dvd_y_add_z`.

Thus the checked reduction is only:

```text
CounterexamplePack x y z -> exactly one of x, y, z is divisible by 7.
```

## Common provenance-preserving resolution

`PrimitiveCounterexampleRamifiedResolution source` retains the chosen
original endpoint, its divisibility witness, a
`PrimitiveRamifiedSummitPacket`, and the exact equality between that endpoint
and `summit.distinguished`.

- In the `x` case, `seven_dvd_gap_of_seven_dvd_first` derives `7 ∣ z - y`;
  the existing quadratic seventh-power packet then supplies the summit.
- In the `y` case, the public 005R3 right-chart summit builder is reused.
- In the `z` case, the public 005R3 left-chart signed extraction is reused.

The primary theorem is
`nonempty_primitiveCounterexampleRamifiedResolution`; the bare-summit
corollary is only a convenience projection.  No terminal provenance is
introduced in any branch.

## Exact depth laws and U1.6 calculation

The common summit API now exposes:

```text
v7(|distinguished|) = 1 + v7(gapRoot)
v7(|root.snd|) + 2 = 7 * v7(|distinguished|).
```

The resolution pulls the second identity back to the original distinguished
endpoint.  Under the pre-existing U1.6 reconstruction obligation, the
depth-four carrier therefore forces a recovered summit with
`v7(gapRoot) = 3`, `v7(|root.snd|) = 26`, and `7 ∣ gapRoot`.

These are conditional depth consequences only.  They neither inhabit the
reconstruction obligation nor contradict an arbitrary ramified summit.

## Boundary and next target

The away branch is absorbed into the ramified second-case surface, so FLT7TC-006
no longer needs a separate away contradiction.  The remaining honest target is
an exclusion of a ramified summit with counterexample provenance, such as
`PrimitiveCounterexampleRamifiedResolution source -> False`.  No claim is made
that `PrimitiveRamifiedSummitPacket` itself is impossible, and no unconditional
FLT7 theorem is obtained here.

## Validation

The following focused builds completed successfully:

```text
lake build DkMath.FLT.Seven.PrimeTraceOnePrimitiveRamifiedResolution
lake build DkMath.FLT.Seven.PrimeTraceOnePrimitiveRamifiedResolutionU16
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOnePrimitiveRamifiedResolutionApiAudit
lake build DkMathTest.FLT.SevenPrimeTraceOnePrimitiveRamifiedResolutionAxiomAudit
```

The target axiom audit reports only inherited
`[propext, Classical.choice, Quot.sound]`.  No new `sorry`, `admit`, or
`unsafe` proof is used.

**Outcome A for FLT7TC-005R4:** the requested primitive classification and
provenance-preserving ramified normalization are implemented and audited.
