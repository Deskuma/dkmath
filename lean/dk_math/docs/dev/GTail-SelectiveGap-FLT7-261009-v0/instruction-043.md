# Instruction 043 — GTail release engineering, public facade verification, and PR readiness (NO new research)

Date: 2026-10-11
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Previous state: Step042 **COMPLETE (docs-only) / STOP042**, mathematical Outcome B; no independently grounded Step043 FLT7 proof target.
Task category: **RELEASE / PR CLOSEOUT ONLY**. This instruction number is NOT a renewed FLT7 proof step and does not supersede the STOP042 proof-development decision.

## Preface — source inventory / staged changes already authored

Read and check the branch's **actual** current files:
- `DkMath/FLT/Seven/GTail.lean` — newly staged **dedicated research facade**, with explicit imports of all **30** added `DkMath/FLT/Seven/GTail*.lean` owners. No new Lean theorem is defined in the file;
- `DkMathTest/FLT/Seven/GTailResearchFacade.lean` — newly staged dedicated public API `#check` and selected `#print axioms` smoke, importing **only** the scoped facade;
- `DkMath/Lib.lean` — preexisting (Step007) neutral aggregator, previously imported five selection/degree-seven modules plus `GTailSevenArithmetic`;
- `DkMath/FLT/Seven.lean` — enormous preexisting historical FLT7 facade, has the Step007 imports `GTailBridge` and `GTailConstraintAudit` but does **not** explicitly import the new scoped facade; **do not add it casually**;
- `DkMathTest/FLT/Seven/GTailFacade.lean` and `DkMathTest/CosmicFormula/GTailLibFacade.lean` — original Step007 public entrance smokes;
- `PR-CLOSEOUT.md` and `PR-DRAFT.md` — staged scientific closeout and PR text. `README.md` is now current (STOP042 + pending new-facade validation), while `ROADMAP.md` retains historical progress through Step042.

The reviewer created the new facade and dedicated smoke with GitHub file commits but **could not run Lean/Lake**. These files are **NOT yet kernel-checked at this HEAD**. Do not treat the text's presence as a successful build. Import and statement correctness must be checked on the user's **real local** Lean toolchain.

## Gate 0 — exact release scope, branch safety, and static source ownership

1. `git status --short` and `git branch --show-current`; confirm the target feature branch and no uncommitted work belonging to the user. **Do not discard unrelated user edits.**
2. `git fetch origin` and inspect `git log --oneline --left-right origin/develop...HEAD`, and the actual one-commit develop difference. Branch was **diverged ahead128/behind1 before the closeout files**; this count is an older snapshot and will grow after closeout commits. Do **not** automatically rebase, merge, force-push or open PR; report integration risk and recommended strategy, leaving the decision to the user.
3. List all new GTail **production** and **test** modules from `git diff --name-status origin/develop...HEAD` or `git ls-files`. Do not mistake the 30 dedicated FLT modules for the 17 neutral added owners or the 48 pre-closeout test modules. Check the actual imported modules in `DkMath.FLT.Seven.GTail` match every intended specialized public owner **once**; verify no stale filename/module, non-existent import or hidden additional module. A narrower facade using a few leaf owners is allowed if measured import cost is lower, but **document which 30 endpoints remain accessible** and justify selective vs explicit imports.
4. Audit the direct imports and module dependencies: neutral `DkMath.Lib.*` MUST NOT import `DkMath.FLT.Seven.*`; specialized GTail owners may import neutral ones; no cycle `DkMath.FLT.Seven→...→GTail→DkMath.FLT.Seven` may be created.
5. Check existing release/build configuration: `DkMathTest.lean` was edited only to list the early Step007 tests, while Lake's `DkMathTest.+` glob may discover later modules. Record actual `lakefile` test spec and whether the new `GTailResearchFacade` is discovered in the **default** suite. Add a single root-driver import only if required and checked; do not blindly append ~50 imports to a giant root.
6. Confirm current README/PR draft scope and document that Step042 **corrects an old false “Row-Z extraction open” claim**: `SevenBaseTerminalRowZSignedResidualCore` has a real constructed signed root, `SevenBaseTerminalRamifiedSummit` has the common summit. Do not regress this correction by reading only TERM-009 declaration.

Produce `source-inventory-043.md` or a concise equivalently named release inventory: exact added vs changed files, new facade import closure, old imported smoke coverage, build/test discovery mechanism, known reuse vs absent FLT7 theorem, actual ahead/behind and Git status. Record the HEAD SHA and scope baseline **as run**.

## Gate 1 — compile the NEW dedicated facade and its public smoke

Use **sequential**, process-local low-memory execution, never a full clean build first:

```sh
cd lean/dk_math
lake build DkMath.FLT.Seven.GTail
lake build DkMathTest.FLT.Seven.GTailResearchFacade
lake build DkMath.Lib
lake build DkMathTest.CosmicFormula.GTailLibFacade
lake build DkMathTest.FLT.Seven.GTailFacade
```

For each command record exact exit code, emitted errors/warnings, elapsed time and memory problems if known, and whether Lake replayed cached artifacts. `#check` names may have **exact namespace corrections**; fix the new smoke only after inspecting actual source symbols. Do not alter theorem types or install assumed axioms to suppress a failing `#check`. Avoid unnecessary Mathlib umbrella imports, broad `DkMath.FLT.Seven` import inside the **new** facade, or resource-limit hacks.

**Facade integration policy:** The new explicit public import `DkMath.FLT.Seven.GTail` is already a valid public entrance *once built*. The old huge `DkMath.FLT.Seven` facade may remain a historical broad entrance. Optionally adding `import DkMath.FLT.Seven.GTail` to it requires a second recorded focused build and measured import-cycle/cost checks; **do not make that umbrella change by default**. Likewise retain the existing neutral `DkMath.Lib` curated subset; do not bulk-promote extra specialized number-theory owners into Lib without owner/layer evidence.

## Gate 2 — final focused regression/axiom/source audit

After Gate1 passes, test the **actual changed/new production/test matrix** rather than relying solely on Step041 reports:
- Begin with Step041/040/039/038 and Step042's corrected old terminal sources as appropriate:
  `GTailFocusedCapacityIndependence`,
  `GTailFocusedDefectGlobalCapacity`,
  `GTailFocusedDefectSquareFirewall`,
  `GTailFocusedPrimeRoute`,
  `GTailFocusedGenericPrimeReceiver`,
  `GTailEisensteinCyclotomicPrimeJoin`,
  `GTailEisensteinCyclotomicPrimeGrid`,
  `GTailEisensteinCyclotomicCommonReceiver`,
  `GTailEisensteinCyclotomicNoDirectHom`,
  `GTailGlobalBalanceFirewall`, and exact corresponding `DkMathTest.FLT.Seven.` modules.
- For every **added FLT owner** not explicitly in the list, prove it is imported successfully by the new facade (transitive Lean compile) and that its **new test file** has either been executed directly or is in the verified default test glob. Record a 30×test-coverage matrix.
- For each of the **17 added neutral Lib owners**, verify its focused build or transitive imported build and actual dedicated \`DkMathTest\` test coverage. Do not call them all directly exposed by `DkMath.Lib` when some remain direct-import APIs.
- Collect all selected public `#print axioms` outputs from the new facade smoke and key theorem owners. Only ordinary Lean foundations `propext, Classical.choice, Quot.sound` are acceptable; no new nonstandard axiom, `sorry`, `admit`, `unsafe`, `native_decide` or unverified acceptance shortcut.
- Run source/owner/facade dependency DAG and grep audits, `git diff --check`, Markdown links and whitespace validation. Confirm Step042 corrected Row-Z status and the signed discriminant−7 vs Eisenstein discriminant−3 difference are accurate.
- If safe and cost-bounded, run `./lb -T` or `lake test`; the historical Step007 full-test gate was interrupted and a later validation addendum logged all tests at a different point. **The current final HEAD's complete suite is not known to have passed.** If stopped, state the actual number of completed/replayed targets, explicit failing/stopped portion and cost. Do not invent a complete run.
- Do **not** rewrite the 42 historical reports, old mathematical owners or the prior correction; only amend release-facing documents, Facade and test driver as needed.

## Gate 3 — source-level PR content and honest scientific classification

Verify/update `PR-CLOSEOUT.md`, `PR-DRAFT.md` and research `README.md`:
1. Layered deliverables: neutral semiring selected-Gap, degree-seven scalar shell; q-prime Gap/Tail necessary conditions; discriminant−3 Eisenstein vs degree-six cyclotomic order (no direct unital homs) and common receiver; generic native kernel/ideal joins; signed defect hEq-free square routing; finite capacity and independent-premise countermodels.
2. Explain **why this is valuable, but not an FLT7 proof**. Some module names contain “Firewall”, “Obstruction”, “Depth” but any real nonexistence theorem is restricted to its literal hypotheses; no unconditional positive natural exponent-seven no-solution theorem is exported.
3. **Directionality** of Step040: `all p²|Δ ∧ |Δ|<M→Δ=0→Fermat7Equation`, **not** FLT impossibility. Step041 models show insufficient hypotheses in actual primitive focus.
4. Correct Step042 terminal frontier: Row-Z extraction and common ramified summit completed; terminal exponent1 seed/prov. nonexistence; lifted explicit primitive nextX/Y/Z and original CRT independent bound/row contradiction still unresolved.
5. Preserve historical Step032 calibration correction: (5,8,9,4) is additive-focused even though it is not Fermat.
6. Include exact \`import\` snippets for `DkMath.Lib` and dedicated `DkMath.FLT.Seven.GTail`, new smoke test target and build outputs **as actually observed**.
7. Describe changed file counts, that this is a **large research PR**, and whether neutral/research PR split would be more reviewable. Do not proactively split or rewrite the existing feature history without user authorization.

Optionally update a single link/brief paragraph in `DkMath/FLT/README.md` or project index to mention the dedicated facade, but **only after its build passes**; keep old public claims for FLT3/FLT5 untouched. A separate `CHANGELOG` is not required if `PR-CLOSEOUT.md` and `PR-DRAFT.md` are accurate.

## Gate 4 — present an actual PR handoff, NOT a PR opened by default

Produce `report-043.md` and append a **post-042 release-closeout** entry to `ROADMAP.md`, with:
- **Ready / Blocked** boolean verdict, backed by command logs and warning/axiom statuses;
- exact HEAD SHA, changed files, source/test matrix, all failed and repaired steps, rationale for any unverified full test;
- final contents of PR title/body and its base/head;
- GitHub branch ahead/behind and concrete remaining merge/integration action;
- unresolved math research explicitly marked **STOP042**;
- list of new facade and smoke files and which older facades remain unchanged.

If the only missing gate is an oversized all-suite run, **do not silently claim full success**: label PR as “focused-validation complete / full-suite pending” and explicitly ask the user for review of the risk when they decide to open the PR. If required focused Facade or test build fails, verdict **BLOCKED**.

**DO NOT call `gh pr create`, open a GitHub PR, merge/rebase, force-push, retarget the branch, tag a release, or claim CI GREEN** without a separate explicit user request. Here the user asked to **prepare for** a PR.

## Non-goals and STOP

- No Step043 FLT7 arithmetic theorem, no new GN/GTail identity, no q-adic depth increments, no new defect support examples or branch-specific receiver;
- no imaginary primitive descent, signed extraction hypothesis, global FLT7 theorem, new axiom/placeholder, massive refactor or name migration;
- no claim that an unused conditional packet is inhabited just because its type is exposed;
- no direct E(-1)↔R unital RingHom or accidental substitution of the older E(-2) order.

**Release ACCEPTANCE:** all focused Facade/API and test targets exit0, the source/test/axiom/import provenance audit passes, current README/PR narrative states Outcome B and STOP042 without out-of-date Row-Z claims, and Git integration risk is explicitly reported. The user can then decide whether to open one large PR or split neutral and FLT7 research. **STOP after preparing the reviewable PR handoff.**
