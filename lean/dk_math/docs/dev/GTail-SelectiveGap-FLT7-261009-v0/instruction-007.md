# Instruction 007 — GTail public façade, cross-layer integration and release audit

Date: 2026-10-09
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisite: `review-006.md` / `report-006.md`
Scope: **Step 007 integration only; no new arithmetic theorems and no branch merge.**

## Mission

Complete the public API/aggregator promotion of the new **GTail selection, factor, transport, degree-seven calibration, neutral arithmetic, and FLT7 conditional receiver** implemented in Steps 001–006. Keep the reusable library and the Fermat research owner strictly separated. Update accurate docs and perform focused-to-broader compilation plus axiom/forbidden-dependency audit.

Do **not** resume the unproved valuation/prime-order/Norm/unit-gauge conjectures in `report-006.md`. Their status remains frontier proposals even if the new façade builds cleanly.

## Phase 0 — clean worktree and source inventory

1. Confirm the current branch is `feature/GTail-SelectiveGap-FLT7-261009-v0` and the worktree is clean. Compare it to `develop`. Preserve all prior commits and do not reset/merge/rebase without explicit owner authorization.
2. Read the actual current versions of:
   - `DkMath/Lib.lean`, `DkMath/Lib/README.md`, `DkMath.lean`;
   - `DkMath/FLT/Seven.lean` and `DkMath/FLT.lean`;
   - `DkMathTest.lean` and any existing test/facade conventions;
   - new `DkMath/Lib/Cosmic/GTailSelection.lean`, `GTailFactor.lean`, `GTailTransport.lean`, `GTailSeven.lean`, `GTailSevenArithmetic.lean`;
   - new `DkMath/FLT/Seven/GTailBridge.lean` and `GTailConstraintAudit.lean`;
   - focused `DkMathTest` modules and `report-001.md` ... `report-006.md`;
   - `review-001.md` ... `review-006.md`, `constraint-ledger-006.md`, current project `README.md` / `ROADMAP.md`.
3. Record current import closure and any direct-public import conventions in `source-inventory-007.md`. Confirm there are no pre-existing equivalent façade imports/duplicate entries.
4. Review existing Lean build targets and memory limitations before a broad build. Do not start a destructive clean build as the first validation.

## Phase 1 — reusable DkMath.Lib exports

In `DkMath/Lib.lean`, promote the complete new **neutral** family through suitable explicit imports, respecting existing conventions:

```text
DkMath.Lib.Cosmic.GTailSelection
DkMath.Lib.Cosmic.GTailFactor
DkMath.Lib.Cosmic.GTailTransport
DkMath.Lib.Cosmic.GTailSeven
DkMath.Lib.Cosmic.GTailSevenArithmetic
```

The exact minimal import set may be consolidated if the current façade intentionally relies on transitive imports; if so document precisely which import exposes which endpoint. Prefer obvious explicit public coverage if that matches current style.

**Hard boundary:** neither `DkMath.FLT.Seven.GTailBridge` nor `DkMath.FLT.Seven.GTailConstraintAudit` may be imported into `DkMath.Lib` or any neutral Lib module. Keep the dependency graph acyclic and independent of hypothetical FLT7 solutions.

Update `DkMath/Lib/README.md`: actual promoted module list, selective index/Gap/Body semantics, forced monomial factor, coefficient gcd, conditional modular transport, degree-seven norm-shaped *polynomial* factor, and neutral coprimality/exact-seven-layer premises. Correct outdated aggregator coverage if observed; no broad rewrite of unrelated docs.

## Phase 2 — FLT7 owner façade, minimal exposure

Inspect actual `DkMath/FLT/Seven.lean`. Append/import the two **domain-specific** modules:

```text
DkMath.FLT.Seven.GTailBridge
DkMath.FLT.Seven.GTailConstraintAudit
```

Ensure no import cycles. If the FLT7 façade intentionally does not directly import a newly added owner, document the existing convention and expose through the smallest correct route instead. **Do not** bulk rewrite this very large existing façade; add only necessary imports and comments.

Record:
- reusable structure enters via `DkMath.Lib`;
- theorem-owner hypotheses enter via `DkMath.FLT.Seven.Basic` and the two new FLT7 owner files;
- no reverse import back into Lib;
- the conditional `Fermat7Equation` / `CounterexamplePack` theorems are not a proof of nonexistence.

Optionally add a tiny facade-import smoke-test module under `DkMathTest` to check access to representative APIs solely from `import DkMath.Lib` and `import DkMath.FLT.Seven` **in separate smoke tests**. If a single owner-import test reaches a huge graph, prefer a focused type-check and record the dependency cost.

## Phase 3 — test discoverability and documentation

Check existing `DkMathTest.lean` aggregator conventions before editing. Its import list is large. If adding the new test modules to the test driver is current repository practice and safe, do so with **minimal new lines**, taking care not to import cyclic test trees. Otherwise retain the existing focused direct test targets and explain how all new tests are invoked by Lake.

In the research project's existing `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/README.md` and `ROADMAP.md`:
- Mark which mathematical APIs are now exposed by the public aggregator and which remain owner-private/owner-specific.
- Summarize Steps 001–006 as **Outcome B** without presenting unproved q-adic / mod-49 / order-21 conjectures as established.
- Keep the `constraint-ledger-006.md` intact as the arithmetic frontier, with links.
- Preserve correct `GTail` indexing (k is the exponent of x) and selected Gap=terms *not* in active S.
- Note no genuine global Norm map to FLT7's cyclotomic carrier and no constructive descent or FLT7 closure.
- Update a project-wide top-level README only if the current repository convention actually requires it and the change is narrow; otherwise do not touch unrelated root docs.

## Phase 4 — compile and regression checks

Run builds **sequentially, incrementally and with low parallelism** if needed for the local RAM constraint. Capture actual exit statuses and reproducible commands.

Minimum focused suite (existing target names, no inferred aliases):

```text
lake build DkMath.Lib.Cosmic.GTailSelection DkMathTest.CosmicFormula.GTailSelection
lake build DkMath.Lib.Cosmic.GTailFactor DkMathTest.CosmicFormula.GTailFactor
lake build DkMath.Lib.Cosmic.GTailTransport DkMathTest.CosmicFormula.GTailTransport
lake build DkMath.Lib.Cosmic.GTailSeven DkMathTest.CosmicFormula.GTailSeven
lake build DkMath.Lib.Cosmic.GTailSevenArithmetic
lake build DkMath.FLT.Seven.GTailBridge DkMathTest.FLT.Seven.GTailBridge
lake build DkMath.FLT.Seven.GTailConstraintAudit DkMathTest.FLT.Seven.GTailConstraintAudit
lake build DkMath.Lib
```

After the above passes, attempt the new or modified FLT7 façade as appropriate:

```text
lake build DkMath.FLT.Seven
```

If feasible with available local resources and cache, proceed to wider `lake build DkMath` and `lake build DkMathTest` **one at a time**. Follow established memory limits (e.g. avoid expensive parallel clean rebuild on the 16 GiB setup). If wider builds are too expensive, time out, exhaust RAM or find unrelated pre-existing failures, **stop and report accurately**. Do not claim full build success from focused results alone. Do not silently change system memory, Lake configuration or unrelated source to force a green result.

For each added public import:
- A smoke test of a real theorem (not merely `#check`) should type-check through the promoted façade, e.g. selected balance, prime interior gcd/body divisor, conditional mod preservation, seven-square balance and neutral coprimality. Keep it small.
- For the owner-facing import, confirm the nonvacuous shell and focused-gap theorem are accessible, but do **not** introduce contradictory positive Fermat samples.
- Confirm earlier Steps 001–006 test modules still pass.
- Re-run `#print axioms` on representative public endpoints and all newly added theorem endpoints if any; expected foundations only, with no `sorryAx`.
- Scan source for `sorry` / `admit` / unintended `axiom` / `unsafe`, circular FLT7 impossibility references, and unwanted owner-to-Lib imports.
- `git diff --check`, targeted file review and changed-path summary.

## Phase 5 — produce integration decision

Write `report-007.md` with:

1. Exact changed files; all import changes; actual API exposure paths.
2. The staged build table (command / exit status / duration if available / successes and failures / local resource constraints).
3. Any regression or axiom output and dependency-cycle audit.
4. The final theorem family inventory for all Step 001–006 public endpoints (no need to duplicate entire source, but include links and counts).
5. Correct outcome classification:
   - **B: integration complete, arithmetic obstruction remains open** (expected).
   - **C: integration dependency/compilation failure**, with smallest blocker and honest scope.
   - **A** may **not** be assigned merely because a public façade compiles or a necessary congruence is proved.
6. Precise frontier links to `constraint-ledger-006.md`: pending v7(g), q² allocation, order-21, Norm/unit class, and next-packet construction.
7. Whether `develop` can be proposed for a PR under the **engineering** acceptance criteria; do not conflate with an FLT7 closure endorsement.

Update `ROADMAP.md` with truthful checked completion; if a whole-build gate is incomplete, show a partial Step 007 with the exact reason. Do not falsify build coverage to mark COMPLETE.

## Stop boundary

Deliver source/docs/tests and `source-inventory-007.md` / `report-007.md`, then **STOP**.

Do **not** merge to `develop`, open a merge PR unless the repository owner explicitly asks, launch large external proof searches, implement the speculative 7-adic/q-adic/order-21 targets, invent a descent provider, or announce unconditional FLT7.

The success criterion is a tidy, independently importable, correctly layered GTail research instrument with validated tests and explicit open arithmetic frontiers.
