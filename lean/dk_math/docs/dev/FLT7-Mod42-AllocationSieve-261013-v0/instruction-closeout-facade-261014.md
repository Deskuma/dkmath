# Closing instruction — FLT7 Mod42 Facade, tests, CI, and develop PR readiness (2026-10-14)

Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Prerequisite: [facade-integration-audit-261014.md](facade-integration-audit-261014.md)
Owner: local Codex, implementing/testing/reporting ONLY
Status: **CLOSEOUT REQUIRED; do NOT open a PR before successful validation**

## 0. Scope and objective

Research gates 001–019 are closed. This instruction is
**not gate 020** and does **not** authorize more
number-theory research.

The implementation branch has 17 added
`DkMath/FLT/Seven/SevenRamifiedFusion*.lean`
production modules and 19 added
`DkMathTest/FLT/Seven/SevenRamifiedFusion*.lean`
test modules. The current root
`DkMath.FLT.Seven` does **not** import the new
production group; `DkMathTest.lean` does not import
the new tests. The current GitHub workflow builds
`DkMath` but has `test: false`.

Close exactly these integration holes, preserve source
proofs and their mathematical assumptions, validate
locally, and report the result. No new FLT7 proof claim.

## 1. Wire a small dedicated research facade into DkMath.FLT.Seven

Create, at a suitable concise filename such as

```text
DkMath/FLT/Seven/ModFortyTwoAllocationSieveFacade.lean
```

an **import-only** module. The nine terminal
imports below transitively cover all 17 new
production modules according to the actual current
branch import graph:

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

Recompute coverage from live imports in the checkout,
in case new source was added after the audit, and add
a missing leaf only if needed. Include the normal
copyright/header marker style. State explicitly that
the exports are **exact sieves / conditional source
obstructions**, not an FLT7 closure.

Add ONE import to the existing
`DkMath/FLT/Seven.lean` near the existing
`SevenRamifiedFusionCenteredPolynomial` /
`SevenRamifiedFusionSixthPowerAllocationSieve`
imports:

```lean
import DkMath.FLT.Seven.ModFortyTwoAllocationSieveFacade
```

Do **not** import `DkMath.FLT.Seven` from its
own subordinate facade (would create an import cycle).
Do **not** change `DkMath/FLT/Prime.lean`,
`DkMath/FLT.lean`, `DkMath.lean` or
`DkMath.Lib` merely to duplicate the import:
the existing path `DkMath → DkMath.FLT →
DkMath.FLT.Seven` already reaches it. Check this
under the actual current source to confirm.

Do not promote the branch-specific theorems into
neutral `DkMath.Lib` simply to make them reachable.
Keep historical broad aggregator semantics intact.

## 2. Make tests genuinely accessible and kernel-checked

There are **19** added DkMathTest modules, including
`SevenRamifiedFusionSourceAllocationChartAudit`
and the gate-019
`SevenRamifiedFusionSourceConstraintSeparation`.
They must not be silently dropped just because a
production module of the same name does not exist.

Create a light public-import smoke test, e.g.

```text
DkMathTest/FLT/Seven/ModFortyTwoAllocationSieveFacade.lean
```

that imports ONLY
`DkMath.FLT.Seven` (not individual new
production modules), uses `#check` or simple
direct-use type probes for representative
declarations from early, middle and late gates,
and audits the final exported dependencies
with `#print axioms`. Suggested smoke endpoints:

- `nestedAllocation_excluded_of_mod_fortyTwo`;
- `sixthPowerSieved_two_prime_pow_excluded`;
- `sixthPowerSieved_smallCoefficient_permutation_prime_excluded`;
- `internalDepthFour_no_reconstruction_of_permutation_prime_core`;
- `internalDepthFour_source_prime_exclusive_valuation`.

Respect their namespaces and theorem types; the
point is to check **reachability through
the actual top-level facade** with no direct
side imports. A simple `#check` does not
independently recheck the underlying theorem
implementation; the full build remains essential.

Create a separate test suite aggregator, e.g.

```text
DkMathTest/FLT/Seven/ModFortyTwoAllocationSieveSuite.lean
```

which imports that smoke test and **all 19
branch-added DkMathTest modules**.
Use a deterministic 1:1 inventory against the
actual compare diff; do not rely on only
the latest gate's tests. Import test-only
source audit modules into this suite, never into
production.

Add ONE import of this test suite in
`DkMathTest.lean`, near the existing
`DkMathTest.FLT.Seven.GTailFacade`.
Do not add 19 imports individually to
`DkMathTest.lean` unless there is a compelling
compatibility reason.

## 3. Guarantee PR CI checks these Lean tests

The existing `.github/workflows/lean_action_ci.yml`
runs on `pull_request` and builds the default
DkMath target, but `test: false` means a
green build **does not** prove the new tests ran.

After the existing `leanprover/lean-action@v1`
build step, add a targeted workflow step,
on the same job/environment, that runs:

```yaml
- name: Build FLT7 Mod42 allocation-sieve tests
  working-directory: lean/dk_math
  run: lake build DkMathTest.FLT.Seven.ModFortyTwoAllocationSieveSuite
```

Validate exact YAML placement, availability of
`lake` after lean-action, and current
repository CI style. If that route is unsupported
in the installed action, choose a proven
equivalent that compiles the exact suite; report
the reason. Avoid globally enabling every
unrelated test via `test: true` unless baseline
compatibility is verified and there is a
clear purpose. Preserve the existing PR trigger,
job permissions and build stage.

The smoke test must also be a dependency of this
suite. CI must fail if the new facade or a
previously added test module no longer elaborates.

This workflow edit **does not itself run GitHub CI**;
the actual remote CI outcome must be checked
after the user integrates/pushes the closure and
the develop PR is opened.

## 4. Local verification — mandatory before asking for PR

Run actual checkout commands and log their
observed exit codes:

```text
lake build DkMath.FLT.Seven.ModFortyTwoAllocationSieveFacade
lake build DkMath.FLT.Seven
lake build DkMath
lake build DkMathTest.FLT.Seven.ModFortyTwoAllocationSieveSuite
lake env lean DkMathTest/FLT/Seven/ModFortyTwoAllocationSieveFacade.lean
```

Use local resource-aware build choices as needed,
but do not omit the top facade, root project and
test suite checks. If a command is too expensive
or cannot run, report a blocker (Outcome B),
not a fabricated pass. The CI job will be the
independent PR-side check, not a substitute for
the available local audit.

Verify import closure of **17/17 production** and
**19/19 tests**, correctly distinguishing
direct from transitive imports. Prefer a small
mechanically reproduced inventory in the
report over eyeballing the import list.

Run `#print axioms` for representative exports,
check no `sorryAx` or prohibited substitutes,
`git diff --check`, and validate the YAML
syntax/step. Do not alter mathematical theorem
statements to make the Facade build.

## 5. Final research summary and PR handoff

Create a concise `branch-closeout-summary-261014.md`
under the **existing docs/dev branch directory**:

- origin: mod42 necessity;
- cheap versus exact countermodels;
- mod5/mod13 and seventh-power
  permutation-prime polynomial image obstructions;
- generic eligible prime-power ownership and
  unbounded abstract-core exclusion families;
- conditional source-indexed reconstruction
  consequences;
- genuine source-only N>1 / prime valuation
  facts versus derived readouts;
- **known open** source→natural additive
  endpoint bridge, and absence of an unconditional
  FLT7 closure;
- list 17 production / 19 test units, Facade
  links, build/check and axiom audit outcomes;
- no falsified claim about all actual M.

Update this branch's `README.md` and `ROADMAP.md`
with closure status and link the summary
only after local validation. Do not erase gate
005/017/019 Outcome B negative evidence.
If a programmatic facade closure is blocked,
mark `CLOSEOUT BLOCKED`, not `READY`.

Report either:
- **CLOSEOUT READY**: all requested source/test
  wiring and local checks successful; CI
  workflow coverage configured. The user can
  integrate/push and Wise Wolf can create the
  `develop` PR and check actual CI.
- **CLOSEOUT BLOCKED**: exact missing import,
  test/build failure or CI configuration issue,
  including reproducible error logs and proposed
  narrow remedy. No PR yet.

Create `report-closeout-facade-261014.md`
and a compact `evidence/closeout-facade-verification.md`
with exact commands, timings if known, exit status,
import inventory and observed axiom sets.
Keep bulky logs ignored, as in prior gates.

## Stop and permissions

**Codex: code edits, Facade wiring, CI YAML,
local testing and reporting ONLY.**

**DO NOT** run `git add`, `git commit`,
`git push`, create/switch branches, open a PR,
merge, or change unrelated proof architecture.
The user handles local integration/push;
Wise Wolf performs later PR creation and
independent remote CI review on user request.

No `instruction-020.md` / research gate 020 is
authorized. Stop here after closeout reporting.
