# Closing instruction — FLT7 Mod42 production Facade and local checks (REVISED 2026-10-14)

Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Owner: local Codex, implementation and verification only
Status: **Facade closeout required before develop PR; DkMathTest is NOT promoted to CI**
Revision: **This replaces the original 2026-10-14 instruction, especially former sections 2–4. If Codex already started, take this revision as the current priority; do not throw away completed valid production Facade work.**

## Decision: do not change CI / do not globally integrate DkMathTest

The user's maintenance concern is valid. The default `.github/workflows/lean_action_ci.yml` intentionally builds the production target with `build: true` and `test: false`. Preserve it **unchanged**.

`DkMathTest` is a research scratchpad of temporary regressions, API probes, mathematical diagnostics, and point-in-time axiom audits. Its historical units may need migration after Lean/Mathlib upgrades. There is no stable maintenance owner or established policy committing every old unit to perpetual compatibility.

**Cancel these requirements from the earlier version:**

1. **DO NOT** add a targeted test step to `.github/workflows/lean_action_ci.yml`.
2. **DO NOT** switch `test: false` to `test: true`.
3. **DO NOT** import the new 19-test suite into the global `DkMathTest.lean`.
4. **DO NOT** treat any old `DkMathTest` module's failure as a blocker to the **production** Facade/PR, except where it reveals an actual flaw in an exported production theorem.
5. If you have made any of these changes locally under the old instruction, **revert only those integration changes** while preserving any legitimate production Facade work and existing test source files. Report them accurately.

Avoid changing unrelated legacy tests or undertaking a large Lean/Mathlib test-package migration merely for this research closeout.

## 1. Connect the new production results to DkMath.FLT.Seven

Create or retain an import-only module, preferably

`DkMath/FLT/Seven/ModFortyTwoAllocationSieveFacade.lean`

with the nine currently sufficient terminal imports:

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

At the audited HEAD these imports transitively cover all **17**
new production modules; recheck the current dependency graph
and do not accidentally omit new production modules.
Import this facade once from `DkMath/FLT/Seven.lean`
beside the existing exact-allocation/centered modules.
The existing `DkMath.FLT` and `DkMath` chains
already import `DkMath.FLT.Seven`; do not add
duplicate imports to `DkMath.FLT.Prime`,
`DkMath.FLT`, `DkMath` or `DkMath.Lib`.

This promotes **already proved conditional sieves and
source-indexed necessary results**, not unconditional FLT7.
Avoid proof refactoring or new research.

## 2. Keep research tests independent of default maintenance

Keep all **19** original added `DkMathTest/FLT/Seven` files
as evidence-bearing research modules; do not delete them.
Their direct individual imports and per-gate successful
kernel checks remain documented as *point-in-time* evidence.

A lightweight production import smoke check is useful,
e.g. a DkMathTest file importing **only**
`DkMath.FLT.Seven`, containing `#check` probes
for representative exported declarations from early
and late gates and a few `#print axioms` audits.
Build it **explicitly locally**, not via global test
driver or CI.

A separate local test suite importing all 19 old tests
is **optional** if useful to demonstrate this branch's
current test coverage. It must remain **opt-in**:
not imported by `DkMathTest.lean`, not referenced
by the GitHub workflow, and not mandatory for the
production closeout. Prefer the gate-specific
already-reported builds over a large risky test
migration. Failures in historical scratch tests
are documented, not concealed; they do not justify
modifying proved production declarations solely
to preserve a transient test harness.

This policy is deliberate: tests are independently
usable, but the main library and its CI do not
promise that every archived research probe will
compile indefinitely.

## 3. Local production verification and optional research checks

**Required:**

```text
lake build DkMath.FLT.Seven.ModFortyTwoAllocationSieveFacade
lake build DkMath.FLT.Seven
lake build DkMath
```

And run an explicit import-only smoke check
(e.g. `lake env lean DkMathTest/FLT/Seven/ModFortyTwoAllocationSieveFacade.lean`)
if a smoke file is created. Confirm that at least
the following exports resolve from the public facade:

```text
nestedAllocation_excluded_of_mod_fortyTwo
sixthPowerSieved_two_prime_pow_excluded
sixthPowerSieved_smallCoefficient_permutation_prime_excluded
internalDepthFour_no_reconstruction_of_permutation_prime_core
internalDepthFour_source_prime_exclusive_valuation
```

Use correct namespaces and `#print axioms` on
representative exports. Check `git diff --check`.
Verify actual production import closure of **17/17**.
No `sorryAx`, new axioms, `sorry`, `admit`
or unsafe proof substitutes.

**Optional, best-effort local-only:**
compile individual branch test modules, an opt-in
19-module suite, or a full `DkMathTest` batch
*when practical*. Clearly distinguish their
success/failures from required production checks.
Do not migrate the whole scratch package solely
to make optional compilation pass.

The **existing GitHub CI** after opening the PR
will check production `DkMath` by its unchanged
workflow. That is a real and sufficient PR CI
claim for this closeout, **not** a claim that
`DkMathTest` was run in CI.

## 4. Summary, status, PR handoff

Write `branch-closeout-summary-261014.md`:
briefly summarize gate 001–019 results and accurate
Outcome B frontiers, describe 17 production/19
research test files, the Facade path, observed
production build checks, and this **intentional**
test/CI maintenance boundary. Do not promise
future compatibility of all scratch tests.
Do not assert an unconditional FLT7 result or
construct a missing additive endpoint.

Write `report-closeout-facade-261014.md` and
compact verification evidence with exact commands
and exit status. Update project README/ROADMAP
only after verifying source state.

Mark **CLOSEOUT READY** if the production Facade,
`DkMath.FLT.Seven` and `DkMath` build
successfully and selected facade exports resolve,
even if opt-in archived research tests
remain unmaintained. Mark **CLOSEOUT BLOCKED**
only for real production build/Facade/axiom
failures, or unverified mandatory checks.

Upon a user-controlled push of verified work,
Wise Wolf can open a `develop` PR and inspect
the actual **production-only** GitHub CI run.
Do not claim CI passed before a run exists.

## Stop / permissions

Codex: source/Facade edits, local testing, report
and summary only. **No git add/stage/commit/push,
branch creation, PR or merge.** No
`instruction-020.md` or new research gate.
Stop after reporting.
