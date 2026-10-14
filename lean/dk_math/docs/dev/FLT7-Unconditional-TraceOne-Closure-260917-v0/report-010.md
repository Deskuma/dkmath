# FLT7TC-005R5 — Counterexample-origin ramified provenance and terminalization criterion

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

The attached `instruction-010.md` was treated as the bounded implementation
contract, separately from the user's request.  This checkpoint preserves
counterexample-specific ramified data and compares it with the historical
terminal packet.  It does not construct a descent or an FLT7 contradiction.

## Three distinct surfaces

`PrimitiveRamifiedSummitPacket` is an arbitrary common summit record.
`PrimitiveCounterexampleRamifiedProvenance source` is stronger: it arises from
one fixed `CounterexamplePack`, retains the exact x/y/z orientation, and keeps
`Nat.Coprime summit.gapRoot summit.residualRoot`.  A
`TerminalPrimitiveRamifiedSummitPacket` is different again: it has a terminal
carrier unit and therefore a seven-unit gap root.

The provenance packet adapts to the existing 005R4 resolution through
`toResolution`, and `toResolution_summit` proves that this is the same summit,
not an independently selected record.

## Checked counterexample-origin facts

The construction follows all three existing checked branches:

- x-divisible: endpoints `(z, y)` and the ordinary quadratic split;
- y-divisible: endpoints `(z, x)` after the summand exchange;
- z-divisible: endpoints `(x, -y)` from the signed alternating split.

All branches prove the root coprimality and that both oriented endpoints and
their oriented sum are not divisible by seven.  These unit statements are
compatible with the ramified factorization; they do not yield a contradiction.

## Same-summit terminalization

`CounterexampleOriginTerminalizable r` means that there exists a
`TerminalPrimitiveRamifiedSummitPacket` whose `summit` equals `r.summit`.
The exact criterion is checked:

```text
terminalizable r
  <-> 7 does not divide r.summit.gapRoot
  <-> v7(r.distinguishedEndpoint) = 1.
```

The reverse construction uses the explicit terminal carrier
`gapRoot * residualRoot`, its positive product, the two seven-unit root
facts, and the retained root coprimality.  It neither fabricates terminal row
provenance nor identifies separately selected summits.

Every distinguished endpoint is divisible by seven, so its depth splits into
exactly `1` or at least `2`.  In the latter branch Lean proves
`7 ∣ gapRoot` and non-terminalizability.  This is the precise new
higher-depth ramified frontier.

## Historical reachability and direct audit

In the depth-one branch, the same-summit terminal packet immediately reaches
the existing `RamifiedSecondCoordinateRoutingPacket` via
`nonempty_secondCoordinateRouting_of_endpoint_depth_eq_one`.  The first
additional old input not supplied is the explicit
`RamifiedCubicGapSeventhShapeReceiver`; it is not constructed here.

The direct bounded audit used the summit identities, depth laws, orientation,
endpoint-unit facts, and root coprimality.  No contradiction follows from the
current checked arithmetic.  In particular, the U1.6 reconstruction
obligation is not inhabited or claimed solved.

## Outcome

**Outcome B — COUNTEREXAMPLE PROVENANCE GREEN; TERMINALIZATION IFF DEPTH ONE;
HIGHER-DEPTH RAMIFIED BRANCH IS THE PRECISE OPEN FRONTIER.**

No arbitrary `PrimitiveRamifiedSummitPacket` is declared impossible, and no
unconditional FLT7 theorem is claimed.

## Validation

Focused builds completed successfully for:

```text
lake build DkMath.FLT.Seven.PrimeTraceOnePrimitiveRamifiedProvenance
lake build DkMathTest.FLT.SevenPrimeTraceOnePrimitiveRamifiedProvenanceApiAudit
lake build DkMathTest.FLT.SevenPrimeTraceOnePrimitiveRamifiedProvenanceAxiomAudit
lake build DkMath.FLT.Seven
```

The axiom audit reports only inherited `[propext, Classical.choice, Quot.sound]`.
No new `sorry`, `admit`, or `unsafe` proof is used.
