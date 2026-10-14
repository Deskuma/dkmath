# FLT7TC-005R3 — Prescribed-carrier chart to common ramified summit resolution

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

The attached `instruction-008.md` was treated as the bounded implementation
contract, separately from the user's request to read, reason, and implement.
This checkpoint de-terminalizes the prescribed-carrier chart resolution and
constructs the common `PrimitiveRamifiedSummitPacket` wrapper.  It does not
construct a chart from divisibility alone and does not attempt FLT7TC-006.

## 1. Files changed

Production:

- `DkMath/FLT/Seven/PrimeTraceOneReconstructionChart.lean`
- `DkMath/FLT/Seven/PrimeTraceOneReconstructionRamifiedResolution.lean`
- `DkMath/FLT/Seven/PrimeTraceOneReconstructionRamifiedResolutionU16.lean`
- `DkMath/FLT/Seven/SevenBaseTerminalRamifiedSummit.lean`
- `DkMath/FLT/Seven.lean` (facade exports)

Audits:

- `DkMathTest/FLT/SevenPrimeTraceOneReconstructionRamifiedResolutionApiAudit.lean`
- `DkMathTest/FLT/SevenPrimeTraceOneReconstructionRamifiedResolutionAxiomAudit.lean`

Documentation:

- this report;
- `ROADMAP.md` status update.

The attached `instruction-008.md` was preserved unchanged.

## 2. Sum chart elimination

The chart layer now exposes:

```lean
no_counterexample_of_seven_dvd_y_add_z
  (source : CounterexamplePack x y z) (7 ∣ y + z) : False

AwayCarrierFermatChart.sum_impossible
  (pack : CounterexamplePack x y z) (y + z = carrier) (7 ∣ carrier) : False
```

The proof uses only the four mod-seven endpoint sectors, the Fermat linear
relation, primitivity, and the existing coordinate route.  In the final
`awaySum` sector it exchanges the two positive summands, rejects the ramified
gap channel, and rejects every away endpoint factor using the universal away
divisibility theorem.  No terminal row profile, terminal carrier, or provider
is used.

## 3. General right chart

For an actual chart

```lean
pack : CounterexamplePack x carrier z
7 ∣ carrier
```

`nonempty_ramified_of_seven_dvd_second` proves

```lean
Nonempty (RamifiedCoordinateNormalForm carrier x z)
```

The proof applies the summand exchange, uses the mod-seven Fermat relation to
obtain `7 ∣ z - x`, and rules out the away coordinate route by its recorded
gap nondivisibility.  It does not assume a terminal provenance.

## 4. General left chart and exact signed extraction

The new structures

```lean
PrescribedCarrierAlternatingPowerSplit source hz
PrescribedCarrierSignedResidualCore source hz
```

generalize the Row-Z arithmetic to any
`source : CounterexamplePack x y z` with `7 ∣ z`.  The checked arithmetic
provides:

- `7 ∣ x + y` from the mod-seven Fermat equation;
- `¬ 7 ∣ y` from primitivity;
- the exact gcd-seven alternating factorization;
- the split
  `x + y = 7^6*a^7`, `alternatingCyclotomicSeven x y = 7*b^7`,
  `z = 7*a*b`;
- a signed residual core with exact norm `b^7`;
- an exact quadratic seventh-power root for that residual core.

The signed extraction is therefore stated at the natural prescribed-carrier
level.  It does not import or require an `AwaySevenBaseTerminal...` profile.
The reusable norm-root transfer was promoted as the public theorem
`root_norm_eq_of_residual_power` in the existing summit module.

## 5. Common summit wrapper

The public wrapper is:

```lean
structure PrescribedCarrierRamifiedSummit (carrier : ℕ) : Type where
  summit : PrimitiveRamifiedSummitPacket
  distinguished_eq : summit.distinguished = (carrier : ℤ)
```

The right chart uses the existing generic
`SevenQuadraticSeventhPowerPacket.toPrimitiveRamifiedSummitPacket` bridge.
The left chart packages the generalized alternating split and signed residual
root into the same primitive summit record.  The main theorem is:

```lean
nonempty_prescribedCarrierRamifiedSummit_of_fermatChart
  (h : AwayCarrierFermatChart carrier) :
  Nonempty (PrescribedCarrierRamifiedSummit carrier)
```

The sum constructor is discharged by `sum_impossible`.  The reconstruction
corollary follows through the existing exact equivalence:

```lean
nonempty_prescribedCarrierRamifiedSummit_of_awayCarrierReconstruction
```

The U1.6 facade additionally exposes the same conditional result at
`internalDepthFourCarrier`, assuming the named
`InternalDepthFourCounterexampleReconstructionObligation`.

## 6. Boundaries retained

This checkpoint does not prove that any `AwayCarrierFermatChart carrier`
exists from `7 ∣ carrier`, does not construct a new
`AwayValuationTransferPacket`, and does not turn a common summit into a new
primitive counterexample.  It also does not provide the missing recursive
state/measure bridge.  FLT7TC-006 remains a separate closure task.

## Outcome

**Outcome A for FLT7TC-005R3 — the requested chart-to-summit resolution is
implemented and audited.**  The result is conditional on an actual prescribed
carrier chart; no unconditional FLT7 theorem is claimed.

## Validation

Focused builds completed successfully for:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneReconstructionRamifiedResolution
lake build DkMath.FLT.Seven.PrimeTraceOneReconstructionRamifiedResolutionU16
lake build DkMathTest.FLT.SevenPrimeTraceOneReconstructionRamifiedResolutionApiAudit
lake build DkMathTest.FLT.SevenPrimeTraceOneReconstructionRamifiedResolutionAxiomAudit
```

The public axiom audit reports only inherited
`[propext, Classical.choice, Quot.sound]`; no `sorryAx`, `sorry`, `admit`, or
`unsafe` proof was added.
