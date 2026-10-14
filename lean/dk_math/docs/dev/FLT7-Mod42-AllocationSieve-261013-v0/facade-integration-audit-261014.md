# Facade / CI integration audit — 2026-10-14

> **2026-10-14 REVISION — USER MAINTENANCE DECISION.** This file preserves the original audit findings, but the proposed mandatory `DkMathTest` integration and PR CI test-suite addition **have been withdrawn**. `DkMathTest` is an opt-in research scratchpad; maintain existing production-only GitHub CI and do not import the 19 old tests into `DkMathTest.lean`. The original CI recommendation below is **historical and superseded**, not an instruction to implement. The authoritative replacement is [instruction-closeout-facade-261014.md](instruction-closeout-facade-261014.md). The **production Facade missing import finding remains valid**.

Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Comparison basis: `develop...research/FLT7-Mod42-AllocationSieve-261013-v0`, before closing edits.
Observed base-relative state: ahead 99 commits, behind 0, **139 files added**, including **17 DkMath/FLT/Seven production** modules and **19 DkMathTest/FLT/Seven test** modules. These are facts from the GitHub compare endpoint at the time of audit; the closing documentation commits subsequently advance the branch.

## Decision: a Facade repair is required before the develop merge PR

`DkMath/FLT/Seven.lean` currently imports the pre-existing
`SevenRamifiedFusionCenteredPolynomial`,
`SevenRamifiedFusionSixthPowerAllocationSieve`,
`SevenRamifiedFusionCenteredGnomonGap`, etc.,
**but none of the 17 new production imports** for this branch.
All 17 files are newly added; older facade imports cannot
depend on newly added files unless changed, and none were.
The new theorem endpoints are consequently **not reachable**
via `import DkMath.FLT.Seven` and its historical
`DkMath.FLT` / `DkMath` import chain.

`DkMathTest.lean` does not reference the 19 new tests.
Unit/target builds from gate reports do not test
the main aggregator's export route.

Production new files (17):

```text
SevenRamifiedFusionCenteredImage589
SevenRamifiedFusionCenteredModFiveImage
SevenRamifiedFusionCenteredThirteenSupport
SevenRamifiedFusionCompositeCore9653618
SevenRamifiedFusionGeneralGapModFiveImage
SevenRamifiedFusionModFortyTwoAllocationSieve
SevenRamifiedFusionModFortyTwoCheapAllocation
SevenRamifiedFusionModFortyTwoCheapBoundaryAudit
SevenRamifiedFusionModSixResidues
SevenRamifiedFusionParametricMixedExclusion
SevenRamifiedFusionPermutationPrimeSupport
SevenRamifiedFusionPrimePowerPrimitiveExclusion
SevenRamifiedFusionSmallCoefficientPrimePowerOwnership
SevenRamifiedFusionSmallCoefficientPrimeSupport
SevenRamifiedFusionSourcePermutationPrimeObstruction
SevenRamifiedFusionSourcePrimeValuationLedger
SevenRamifiedFusionThirteenPowerPrimitiveExclusion
```

The new production module graph has precisely **nine
leaf imports**: importing these nine directly
covers all 17 via transitive imports, while keeping
the public facade short:

```lean
import DkMath.FLT.Seven.SevenRamifiedFusionCenteredImage589
import DkMath.FLT.Seven.SevenRamifiedFusionCenteredModFiveImage
import DkMath.FLT.Seven.SevenRamifiedFusionCompositeCore9653618
import DkMath.FLT.Seven.SevenRamifiedFusionParametricMixedExclusion
import DkMath.FLT.Seven.SevenRamifiedFusionPrimePowerPrimitiveExclusion
import DkMath.FLT.Seven.SevenRamifiedFusionSmallCoefficientPrimePowerOwnership
import DkMath.FLT.Seven.SevenRamifiedFusionSourcePermutationPrimeObstruction
import DkMath.FLT.Seven.SevenRamifiedFusionSourcePrimeValuationLedger
import DkMath.FLT.Seven.SevenRamifiedFusionThirteenPowerPrimitiveExclusion
```

Do not interpret nine as nine public theorems: these are
**nine import graph roots** that reach the 17 files,
not a replacement for the full module inventory.
The nine leaves and graph coverage were computed
from actual branch source imports.

Additional test-only module:
`SevenRamifiedFusionSourceAllocationChartAudit`
has no matching production module — correctly a
research/audit test, and still part of the
**19-test** integration inventory.
`SevenRamifiedFusionSourceConstraintSeparation`
(gate 019) is also test-only.

## Current CI gate: insufficient for new tests

Actual `.github/workflows/lean_action_ci.yml`:

- `pull_request` trigger includes `lean/dk_math/**`;
- single `Build DkMath` job uses
  `leanprover/lean-action@v1` with
  `lake-package-directory: lean/dk_math`,
  `build: true`, **`test: false`**, `lint: false`;
- push triggers target `main`/`develop`, not the research branch.
  A GitHub PR will trigger CI once opened.

Even if the facade is fixed, build-only CI would
not necessarily compile the 19 new tests.
A small targeted verification step or reviewed CI test
configuration is required. Do not blindly turn on
every unrelated historical test if that has not been
validated. The closer should ensure a command on PR CI
actually compiles the new suite, ideally via
`lake build DkMathTest.FLT.Seven.ModFortyTwoAllocationSieveSuite`.

## Closing sequence — no PR yet

1. Codex closes the Facade and test routing following
   [instruction-closeout-facade-261014.md](instruction-closeout-facade-261014.md),
   only code/test/CI/doc edits and local validation,
   **no Git commits/push/PR/merge**.
2. User reviews and integrates/pushes tested changes.
3. Wise Wolf checks the new branch head and
   same-version CI/test coverage, then publishes
   the final research summary and opens
   `develop`-targeted PR **if closure verified**.
4. Examine the **actual triggered GitHub Actions run**,
   its jobs/conclusions and PR mergeability; report
   pending/failing state exactly. Do not represent
   a local build as GitHub CI green.

No claim of unconditional FLT7 completion follows.
Gates 001–019 produced important **conditional**
and **abstract-core** results, with source/chart
constructive existence still unsupplied.

Outcome: **FACADE REQUIRED / PR DEFERRED until closing validation**.
