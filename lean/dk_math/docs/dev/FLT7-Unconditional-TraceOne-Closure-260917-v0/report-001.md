# FLT7TC-001 — Seventh-power coordinate bridge and 7-unit consequences

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

## User-request scope

The attached `instruction-001.md` was treated as the bounded implementation
contract.  The implementation stops at the specialized p=7 residual receiver;
it does not attempt the parent-coordinate provenance problem in FLT7TC-002 or
any final FLT7 contradiction.

## Implemented surface

Added `DkMath.FLT.Seven.PrimeTraceOneClosureBridge` and exported it from the
`DkMath.FLT.Seven` facade.

The new leaf proves the recurrence-to-polynomial identities

```text
(traceOnePowCoords (-2) u v 7).1 = seventhPowerFst u v
(traceOnePowCoords (-2) u v 7).2 = seventhPowerSnd u v
```

by composing the existing `traceOne_pow_coordinates` and
`traceOne_pow_seven_eq` APIs.  No seventh-power expansion is duplicated in the
new file.

For a `PrimeTraceOneStrippedIdealPacket` at p=7, the leaf now provides:

- `¬ 7 ∣ Int.natAbs (norm Q.residual)` from `residual_axis_terminal`;
- the corresponding integer-norm statement `¬ (7 : ℤ) ∣ norm Q.residual`;
- explicit residual coordinate witnesses in `seventhPowerFst` and
  `seventhPowerSnd` form;
- an exact same-root seventh-power witness with
  `¬ (7 : ℤ) ∣ norm delta`;
- a combined coordinate/root theorem preserving the same root coordinates;
- direct consequences that the residual second coordinate is divisible by 7,
  its `seventhPowerSndCore` is not divisible by 7, and
  `49 ∣ residual.snd ↔ 7 ∣ root.snd`.

The same-root theorem retains the packet's canonical carrier
`TraceOneInt (signedPrimeParameter 7)` so its equality to `Q.residual` is
typed directly.  The recurrence bridge identifies this carrier's p=7
coordinates with the specialized `TraceOneInt (-2)` polynomial API.  This is
the smallest checked normalization compatible with the existing packet
definition; no parent provenance or orientation claim was added.

## Validation

The following focused builds completed successfully:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneClosureBridge
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.Seven.PrimeTraceOneClosureBridgeApiAudit
lake build DkMathTest.FLT.Seven.PrimeTraceOneClosureBridgeAxiomAudit
```

The API audit checks the recurrence identities, residual receiver, terminal
norm statements, same-root theorem, coordinate-preserving theorem, and direct
p=7 consequences.  The axiom audit reports only the existing foundational
dependencies (`propext`, `Classical.choice`, and `Quot.sound`) inherited by the
underlying arithmetic/ideal APIs.  No new unsafe or admitted proof construct
was introduced.

## Boundary and outcome

The generic parent-to-`cyclotomicSevenToTraceOne` provenance bridge remains
open and is carried forward as FLT7TC-002.  No contradiction and no
unconditional FLT7 theorem is claimed here.

Outcome: **A — P=7 EXPLICIT SEVENTH-POWER / SAME-ROOT 7-UNIT BRIDGE GREEN**.
