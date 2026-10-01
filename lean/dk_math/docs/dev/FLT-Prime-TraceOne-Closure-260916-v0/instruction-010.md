# FPTC-010 — Public facade and bounded closeout

Branch: `research/FLT-Prime-TraceOne-Closure-260916-v0`

This is the final checkpoint of the current campaign.  Its job is **not** to
prove general FLT or to reopen the arithmetic frontiers found in FPTC-007/008/009.
It should expose the stable generic odd-prime/TraceOne architecture through a
small public facade, add end-to-end API regressions for the calibrated exponents,
and write a precise closeout report that distinguishes proved infrastructure
from remaining mathematical obligations.

## 1. Current checked status

Treat the following checkpoint classifications as fixed input:

```text
FPTC-000  Outcome A  class-group structural discharge + p=7
FPTC-001  Outcome A  finite class-group cardinality criterion
FPTC-002  Outcome A  arbitrary-power TraceOne coordinates
FPTC-003  Outcome A  arbitrary-power TraceOne landing iff
FPTC-004  Outcome A  imaginary residual coordinate receiver
FPTC-005  Outcome A  p=3 Eisenstein generic sector closure
FPTC-006  Outcome A  p=5 Golden/TraceOne ring bridge + sector closure
FPTC-007  Outcome C  class-number coprimality frontier isolated
FPTC-008  Outcome B  real sector receiver green; p=5 packet bridge frontier
FPTC-009  Outcome A  generic two-branch counterexample routing
```

Do not relabel Outcome B/C checkpoints as completed general mathematics.  They
are successful frontier-isolation checkpoints.

## 2. Public facade

Audit whether a facade already exists for the current `DkMath.FLT.Prime.*`
architecture.  If not, create:

```text
lean/dk_math/DkMath/FLT/Prime.lean
```

as a **thin import-only discovery facade**.

It should expose the stable production modules from this campaign and the
existing generic TraceOne chain, in dependency-respecting order.  At minimum
audit/import the following where they are production modules and do not create
an import cycle:

```lean
DkMath.FLT.Prime.CounterexampleRouting
DkMath.FLT.Prime.AdicPowerSplit
DkMath.FLT.Prime.PrimeTraceOneCoordinateCoprime
DkMath.FLT.Prime.PrimeTraceOneStrippedIdeal
DkMath.FLT.Prime.PrimeTraceOneConditionalDescent
DkMath.FLT.Prime.PrimeTraceOneClassGroupClosure
DkMath.FLT.Prime.PrimeTraceOneCoordinateReceiver
DkMath.FLT.Prime.PrimeTraceOneThreeSectorClosure
DkMath.FLT.Prime.PrimeTraceOneFiveSectorClosure
DkMath.FLT.Prime.PrimeTraceOneRealSectorReceiver
```

If another production `DkMath.FLT.Prime.*` module is required for the checked
chain and is clearly part of the same architecture, include it and explain why
in `report-010.md`.

Do **not** turn the facade into a theorem-owning module.  It should normally
contain imports, a `#print "file: DkMath.FLT.Prime"`, and a concise module doc.

The module doc must state explicitly:

- this is a generic odd-prime FLT/TraceOne **architecture facade**;
- it is not a proof of Fermat's Last Theorem for arbitrary prime exponent;
- the current front end is an honest two-branch route;
- the ramified branch enters `PrimeAdicFactorPacket`;
- the away branch currently stops at a simultaneous `p`-th-power split;
- imaginary generic closure remains conditional on the class-number
  coprimality frontier outside calibrated cases;
- real generic closure retains a sector and has the p=5 generic/specialized
  packet-bridge frontier.

### `DkMath.FLT` broad aggregator

`DkMath.FLT.lean` is a historical broad aggregator and already documents that
`DkMath.FLT.Prime.*` is the current generalization architecture.  Do not add the
new facade as an import if doing so changes/bloats historical import semantics
or creates undesirable cycles.  A small documentation update pointing to

```lean
import DkMath.FLT.Prime
```

as the canonical discovery import is acceptable and preferred if clean.

Do not modify `DkMath.FLT.Three` or `DkMath.FLT.Five` public proof endpoints.

## 3. Facade API audit

Add a focused test, suggested path:

```text
DkMathTest/FLT/Prime/PrimeFacadeApiAudit.lean
```

It should import **only** the new facade (plus no specialized imports unless a
regression genuinely needs a specialized input constructor) and check that the
important campaign declarations are visible.

At minimum pin examples or `#check`s for:

```text
PrimitivePrimeCounterexample
PrimeCounterexampleRoute
counterexampleRoute_of_primitive
PrimeAdicFactorPacket
PrimeAdicPowerSplit
PrimeTraceOneStrippedIdealPacket
classGroupPTorsionFreeAt_of_coprime_card
traceOnePowCoords
traceOne_pow_coordinates
traceOne_pow_core_landing_iff
```

and the stable FLT-prime endpoints added by this campaign, including the p=3,
p=5, imaginary-coordinate, and real-sector receiver declarations.

Avoid fragile tests that merely duplicate implementation proofs.

## 4. Calibrated regression matrix

Add a closeout regression test, either in the facade audit or a separate file
such as:

```text
DkMathTest/FLT/Prime/PrimeClosureCalibrationAudit.lean
```

Record the following checked calibration points without invoking the completed
FLT3/FLT5 final contradiction theorems as black boxes.

### p = 3

Confirm the generic route can see the existing Eisenstein carrier/sector
closure:

```text
signedPrimeParameter 3 = -1
EisensteinInt = TraceOneInt (-1)       -- definitional/carrier audit
class-group structural discharge
existing cube sector system
generic p=3 sector-weighted cube endpoint
```

Do not reprove FLT3.

### p = 5

Confirm:

```text
signedPrimeParameter 5 = 1
GoldenInt ≃+* TraceOneInt 1
class-group structural discharge
explicit Fin 5 Golden sector system
generic p=5 sector endpoint
p=5 real coordinate/base-norm receiver
```

Do not claim generic nonzero-sector elimination.  The missing
`PrimeTraceOneStrippedIdealPacket` -> `SignedGoldenRamifierStrippedPacket`
bridge remains open.

### p = 7

Confirm:

```text
signedPrimeParameter 7 = -2
classGroupPTorsionFreeAt (TraceOneInt (-2)) 7
imaginary exact-power endpoint
imaginary coordinate receiver
```

Also check that the p=7 specialized counterexample vocabulary can still feed
the same `PrimeAdicFactorPacket 7 (z-y) y x` target when the ramified branch is
selected.  Do not use the specialized final FLT7 contradiction as a substitute
for a generic theorem.

### Optional p = 11 / p = 13 boundary checks

If they are cheap, retain the existing normalization/conditional regressions:

```text
p=11 : signedPrimeParameter 11 = -3, class-group coprimality still required
p=13 : signedPrimeParameter 13 = 3, real class-group hypothesis still required
```

These are boundary witnesses, not unconditional closure claims.

## 5. Axiom audit

Add a closeout axiom audit, suggested path:

```text
DkMathTest/FLT/Prime/PrimeFacadeAxiomAudit.lean
```

Print axioms for representative public theorems covering:

- generic counterexample route;
- arbitrary-power TraceOne landing;
- p=3 sector closure;
- p=5 sector closure;
- p=7 imaginary exact-power/coordinate closure;
- generic real sector receiver/base-norm obstruction;
- class-number coprimality -> p-torsion-free bridge.

Expected acceptable foundational surface is the already observed ordinary
Lean/Mathlib set such as:

```text
propext
Classical.choice
Quot.sound
```

as applicable.  Any `sorryAx`, project `axiom`, or unexpected new axiom is a
failure and must be traced before classifying Outcome A.

## 6. Forbidden-source audit

Scan all **new/modified campaign production and test files** for fresh uses of:

```text
sorry
sorryAx
admit
axiom
unsafe
```

Use a token-aware or context-aware scan if necessary so comments documenting
forbidden terms do not produce a false conclusion.  The closeout report must
distinguish:

- fresh campaign source cleanliness;
- pre-existing legacy/provider `sorryAx` contamination elsewhere in the repo.

Do not claim the whole historical repository is axiom-clean merely because the
campaign surface is clean.

Run `git diff --check`.

## 7. Final closeout report

Create:

```text
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/report-010.md
```

This report is a required deliverable and should be usable as the canonical
summary of this branch.

It must contain the following sections.

### A. Campaign result table

List FPTC-000 through FPTC-010 with exact Outcome/status and one-sentence result.
Do not flatten B/C into A.

### B. Strongest checked generic architecture

Record the strongest actual theorem flow, conceptually:

```text
PrimitivePrimeCounterexample
  -> PrimeCounterexampleRoute

ramified branch:
  PrimeAdicFactorPacket
  -> PrimeAdicPowerSplit
  -> arbitrary-prime TraceOne coordinates
  -> primitive/coprime coordinates
  -> prime-discriminant stripped residual
  -> residual ideal = idealRoot^p
  -> class-group / unit-sector conditional closure
  -> integer-coordinate receivers

away branch:
  gap = a^p
  and
  GTail = b^p
  -> separate arithmetic frontier
```

Only include arrows that are actually checked in production.

### C. Unconditional calibrated results

State exactly what is unconditional in this architecture at the calibrated
indices, especially:

- p=3: structural generic Eisenstein sector closure;
- p=5: Golden/TraceOne bridge, class-group discharge, explicit sectors, generic
  sector closure and receiver, but **not** generic nonzero-sector elimination;
- p=7: class-group discharge and generic imaginary exact-power/coordinate
  closure for an existing stripped packet.

Do not confuse these structural/conditional-chain results with the separate
completed specialized FLT3 and FLT5 final proofs.

### D. Remaining frontiers

Name the exact theorem-shaped blockers separately.

1. **Imaginary class-number frontier**

    ```text
    ∀ p, p.Prime -> p % 4 = 3 ->
      Nat.Coprime p
        (NumberField.classNumber
          (TraceOneRat (signedPrimeParameter p)))
    ```

    or the exact equivalent checked formulation produced by FPTC-007.

2. **Real p=5 packet bridge frontier**

    A checked correspondence from generic p=5
    `PrimeTraceOneStrippedIdealPacket` data to the specialized Golden
    `SignedGoldenRamifierStrippedPacket` data sufficient to invoke
    `signedGolden_nonzero_unitSector_false`.

3. **Away-branch frontier**

    The generic route only proves

    ```text
    z-y = a^p
    GTail p 1 (z-y) y = b^p
    ```

    when `p ∤ z-y`.  No generic contradiction for this branch is currently
    established by this campaign.

4. Any additional exact blocker found during closeout, but do not invent one.

### E. What this branch does not prove

Include a prominent statement that this branch does **not** prove general FLT.
It also does not prove a uniform class-number formula, a uniform real-sector
elimination theorem, or the generic away-branch contradiction.

### F. Axiom/build audit

Record exact build commands and representative `#print axioms` results.

## 8. ROADMAP closeout

After successful implementation, update `ROADMAP.md` to:

```text
FPTC-009: completed — Outcome A
FPTC-010: completed — Outcome A
```

if and only if all facade/regression/audit/report requirements above are green.

Keep FPTC-007 and FPTC-008 recorded as their actual Outcome C/B classifications.
Their frontiers remain open even though the campaign itself is closed.

## 9. Suggested builds

At minimum:

```text
lake build DkMath.FLT.Prime
lake build DkMathTest.FLT.Prime.PrimeFacadeApiAudit
lake build DkMathTest.FLT.Prime.PrimeClosureCalibrationAudit
lake build DkMathTest.FLT.Prime.PrimeFacadeAxiomAudit
lake build DkMath.FLT.Prime.CounterexampleRouting
lake build DkMath.FLT.Prime.PrimeTraceOneRealSectorReceiver
lake build DkMath.FLT.Prime.PrimeTraceOneThreeSectorClosure
lake build DkMath.FLT.Prime.PrimeTraceOneFiveSectorClosure
git diff --check
```

If the test layout differs cleanly, document the exact commands in
`report-010.md`.

## 10. Outcome classification

Use exactly one of:

```text
Outcome A — PRIME TRACEONE PUBLIC FACADE AND BOUNDED CLOSEOUT GREEN
Outcome B — CLOSEOUT AUDITS GREEN; PUBLIC FACADE IMPORT SURFACE NEEDS NORMALIZATION
Outcome C — DOCUMENTATION CLOSEOUT GREEN; BUILD/API ISSUE BLOCKS PUBLIC FACADE
```

Outcome A requires:

- clean public `DkMath.FLT.Prime` facade (or an already-existing equivalent
  clearly justified in the report);
- p=3/5/7 calibration regressions;
- representative axiom audit with no unexpected project axioms;
- forbidden-source audit and `git diff --check` clean;
- `report-010.md` with exact remaining frontiers and no general-FLT overclaim;
- ROADMAP updated only after all the above pass.

## Hard boundaries

Do **not** in FPTC-010:

- assert or add a theorem `FermatLastTheoremFor p` for arbitrary prime `p`;
- reuse the completed FLT3/FLT5 theorem as a fake generic closure theorem;
- use specialized FLT7 final contradiction to close the generic route;
- assume the FPTC-007 class-number coprimality theorem;
- fabricate the missing generic-to-Golden stripped-packet bridge;
- discard the real `Fin p` sector index without a checked elimination theorem;
- declare the away branch impossible from the mere p-th-power split;
- import legacy `sorryAx` provider routes into the new facade merely to make a
  global theorem typecheck;
- turn the facade into a broad replacement for the historical `DkMath.FLT`
  aggregator.

The purpose of this checkpoint is a truthful, kernel-checked architectural
closeout.
