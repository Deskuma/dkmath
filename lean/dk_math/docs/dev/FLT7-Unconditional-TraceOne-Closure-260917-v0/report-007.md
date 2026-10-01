# FLT7TC-005R2 — Prescribed-carrier additive Fermat chart normalization

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

The attached `instruction-007.md` was treated as the bounded implementation
contract, separately from the user's request to read, reason, and implement.
`report-006.md` and FLT7TC-005R were used as fixed checked input.  This
checkpoint removes route/root packaging from the reconstruction statement,
but does not attempt FLT7TC-006 or assume a counterexample.

## 1. Files changed

Production:

- `DkMath/FLT/Seven/PrimeTraceOneReconstructionChart.lean`
- `DkMath/FLT/Seven/PrimeTraceOneReconstructionChartU16.lean`
- `DkMath/FLT/Seven.lean` (facade exports)

Audits:

- `DkMathTest/FLT/SevenPrimeTraceOneReconstructionChartApiAudit.lean`
- `DkMathTest/FLT/SevenPrimeTraceOneReconstructionChartAxiomAudit.lean`

Documentation:

- this report;
- `ROADMAP.md` status update.

The attached `instruction-007.md` was preserved unchanged.

## 2. Additive prescribed-carrier chart

The light chart module defines the inductive proposition
`AwayCarrierFermatChart carrier` with three constructors:

```lean
| right (pack : CounterexamplePack x carrier z) (7 ∣ carrier)
| left  (pack : CounterexamplePack x y carrier) (7 ∣ carrier)
| sum   (pack : CounterexamplePack x y z) (y + z = carrier) (7 ∣ carrier)
```

The constructor names follow the existing away exceptional-factor source:
`right` means the prescribed carrier is `y`, `left` means it is `z`, and
`sum` means it is `y + z`.  Every chart retains an actual positive primitive
`CounterexamplePack`; no bare Fermat equality or isolated modular solution is
accepted.

## 3. Main equivalence

The central theorem is:

```lean
awayCarrierReconstruction_iff_fermatChart
  : AwayCarrierReconstruction carrier ↔ AwayCarrierFermatChart carrier
```

The forward direction opens the existing
`AwayExceptionalCarrierSource`, rewrites its exact carrier equality, and
uses `route.normal.counterexample`.

For the reverse direction, each chart case follows the existing checked
route:

```text
CounterexamplePack
  -> coordinateCounterexampleRoute_of_pack
  -> away coordinate normal form
  -> nonempty_awayValuationTransferPacket.
```

The ramified branch is rejected locally.  For the `carrier = y` chart,
ramified `7 ∤ y` contradicts `7 ∣ carrier`.  For the `carrier = z` chart,
ramified `7 ∣ z-y` together with `7 ∣ z` forces `7 ∣ y`, contradicting the
ramified `7 ∤ y`.  For the `carrier = y+z` chart, the same gap divisibility
and `7 ∣ (y+z)` force `7 ∣ 2y`, hence `7 ∣ y`, again a contradiction.
These are proved in Lean using the existing ramified packet facts and natural
divisibility arithmetic; no new algebraic theorem or FLT contradiction is
introduced.

After the away packet is obtained, its
`AwayExceptionalCarrierSource` is case-split.  The two incompatible source
constructors are discharged by their recorded nondivisibility fields, and the
matching constructor supplies the exact equality `route.carrier = carrier`.

## 4. Additive decomposition and size bounds

The theorem `awayCarrierReconstruction_additive_decomposition` exposes:

```text
AwayCarrierReconstruction carrier ->
  (∃ x z, CounterexamplePack x carrier z) ∨
  (∃ x y, CounterexamplePack x y carrier) ∨
  (∃ x y z, CounterexamplePack x y z ∧ y + z = carrier).
```

The chart-specific bounds are:

```lean
AwayCarrierFermatChart.left_bounds
  (pack : CounterexamplePack x y carrier) : x < carrier ∧ y < carrier

AwayCarrierFermatChart.sum_bounds
  (pack : CounterexamplePack x y z) (y + z = carrier) :
  x < carrier ∧ y < carrier ∧ z < carrier

AwayCarrierFermatChart.right_bounds
  (pack : CounterexamplePack x carrier z) : carrier < z ∧ x < z
```

Thus the `carrier = z` and `carrier = y+z` charts are finite-coordinate
charts for a fixed carrier.  The `carrier = y` chart has only the honest
bounds `carrier < z` and `x < z`; no bound `z < carrier` is claimed.

## 5. Symmetry audit

The existing checked `CounterexamplePack.swapXY` preserves positivity,
primitivity, and the Fermat equation while preserving the numerical `z`
coordinate.  Therefore it preserves the `carrier = z` chart proposition
(the chart's two summands are simply exchanged).

It does not preserve the prescribed carrier of the `carrier = y` chart in
general: after swapping, the distinguished second summand is `x`.  It also
does not preserve the `carrier = y+z` expression in general: it becomes
`x+z`.  Consequently the three prescribed-carrier positions cannot be
collapsed into one global chart by `swapXY`.  No terminal Row-Y/Row-Z/Row-Sum
theorem was imported or generalized here.

## 6. Existing boundary transport

The theorem `AwayValuationTransferPacket.no_fermatChart_at_depth_one`
transports the previous kernel result:

```text
padicValNat 7 p.carrier = 1
  -> ¬ AwayCarrierFermatChart (Int.natAbs p.normal.root.snd).
```

This remains a terminal classification, not an FLT contradiction.

The heavy leaf proves `internalDepthFourReconstruction_iff_fermatChart` by
composing the existing U1.6-to-`AwayCarrierReconstruction` equivalence with
the new additive chart equivalence.  No U1.6 arithmetic is duplicated.
Thus U1.6 is precisely the existence of an additive primitive FLT7 chart at
the prescribed depth-four carrier, but that chart is not inhabited by this
checkpoint.

## 7. Answers to the checkpoint questions

1. **YES.** `AwayCarrierReconstruction carrier` is exactly equivalent to
   `AwayCarrierFermatChart carrier`.
2. The reverse implication needs no new algebraic theorem: it uses existing
   counterexample routing, away packet construction, and checked one-hot
   mod-seven/divisibility facts.
3. **Not globally.** `swapXY` preserves only the `carrier = z` chart among
   these prescribed positions; the `carrier = y` and `carrier = y+z` charts
   retain different carrier data.
4. The `carrier = z` and `carrier = y+z` charts have all coordinates bounded
   strictly below the fixed carrier.  The `carrier = y` chart has only
   `carrier < z` and `x < z`.
5. **NO.** No previously missing counterexample, provider, or chart witness
   was constructed from a mere divisibility condition.
6. **YES, as a normalization.** U1.6 is the same prescribed-carrier
   additive FLT7 chart problem with its exact depth-four carrier.  Existence
   remains open.

## Outcome

**Outcome B — RECONSTRUCTION = PRESCRIBED-CARRIER ADDITIVE FLT7 CHART; NO NEW
COUNTEREXAMPLE**.

FLT7TC-006 remains blocked.  No primitive FLT7 closure or unconditional FLT7
theorem is claimed.

## Validation

Focused builds completed successfully for:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneReconstructionKernel
lake build DkMath.FLT.Seven.CoordinateNormalForm
lake build DkMath.FLT.Seven.ModSevenSectors
lake build DkMath.FLT.Seven.AwayValuationTransfer
lake build DkMath.FLT.Seven.PrimeTraceOneReconstructionChart
lake build DkMath.FLT.Seven.PrimeTraceOneReconstructionChartU16
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneReconstructionChartApiAudit
lake build DkMathTest.FLT.SevenPrimeTraceOneReconstructionChartAxiomAudit
```

The public theorem axiom audit reports only the inherited
`[propext, Classical.choice, Quot.sound]` surface.  No project axiom,
`sorryAx`, `sorry`, `admit`, or `unsafe` proof was added.  The forbidden-source
scan and `git diff --check` were run; the new report and untracked Lean files
were also checked with `git diff --no-index --check`.
