# Source inventory 007 — public integration

Date: 2026-10-09. Initial branch: feature/GTail-SelectiveGap-FLT7-261009-v0. Initial worktree clean. HEAD 4df305de96d3395bc69d26a853a1ecc36cf38076; local develop 7f94a8913e48b289c1366648fedbf1586b77bf79. `git rev-list --left-right --count develop...HEAD`: 0 / 21. Branch is 21 commits ahead of local develop, with no develop-only commits. Comparison is local; no network refresh or branch operation performed. Diff vs develop has 41 files / 4893 inserted lines belonging to preceding steps and their documentation.

Reviews 001–006 all APPROVED / Outcome B. Review 006 explicitly keeps valuation allocation, order-21, norm/unit transport and next-packet reconstruction open. Current reports, test contracts and ledger were inspected. Ledger bytes are recorded before edits and will be preserved.

## Existing entrance and test conventions

- DkMath.Lib uses ordinary explicit `import` lines; it does not use `public import` or export aliases. Add five explicit neutral imports alongside the existing Cosmic family. No matching import exists yet.
- DkMath.FLT.Seven uses a large explicit owner list (198 imports); add the two owner imports near the end of that list before its file-print marker. Neither is present initially.
- DkMath.lean already imports DkMath.Lib and DkMath.FLT; FLT.lean already imports Seven. No root production aggregator change is required.
- DkMathTest.lean lists selected direct test imports, while lakefile.toml sets testDriver=DkMathTest and DkMathTest library glob DkMathTest.+. Add six earlier focused tests plus two new separate facade smoke tests with minimal lines. The library glob discovers the individual files even without root import; the root additions additionally expose them through the explicit root test aggregator; the configured library test driver independently uses the submodule glob.
- New smoke modules will use only `import DkMath.Lib` and only `import DkMath.FLT.Seven`, respectively, and prove examples by actual public theorem application. No mathematical owner theorem is added.
- Existing Lib README promoted list is incomplete relative to actual direct imports (e.g. FiniteIdealPowerAggregation, PowerSubgroup, HomogeneousPowerQuotient and GNProductDegree/CyclicDeterminant are already imported). Synchronize that list precisely, without rewriting unrelated mathematical sections.
- Project README still describes planning/instruction 001. Update to completed kernels/receivers and truthful integration status; preserve the ledger and indexing conventions. No unrelated top-level README is required.

## Pre-change source import closures

Recursive parsing includes ordinary/public/private imports in local DkMath and installed Mathlib source. Counts are module names (including external terminal names), not Lake jobs or evidence of compiled scope.

| Entrance | Direct imports | Recursive module names | Local production DkMath modules |
| --- | --- | --- | --- |
| `DkMath.Lib` | 24 | 8809 | 29 |
| `DkMath.FLT.Seven` | 198 | 9144 | 364 |
| `DkMathTest` | 107 | 9479 | 584 |

The exact direct lists and recursive name sets are retained locally in `.lake/build/gtail-step007/before.json`; final closure comparison is recorded in report-007. The Lib closure must contain no DkMath.FLT owner. New owners point to neutral modules and Basic, never the Seven facade; proposed smoke tests are downstream only. No reverse import or duplicate facade entry is intended.

## Resource/build plan

Lake 5 / Lean 4.34.1; live host total RAM ~31 GiB, available ~22 GiB, swap ~63 GiB (no memory/swap changes). Standard cgroup memory.max/current paths are absent in this session; host readings are not a container limit guarantee. Lake help exposes no jobs-count switch. Installed Lean runtime contains LEAN_NUM_THREADS; run staged commands with `LEAN_NUM_THREADS=2`, sequentially and incrementally, and monitor actual process/memory behavior for broader graphs. No clean, configuration, dependency-update or system-memory operation is planned.

First run the eight required focused/Lib commands. Then build Seven and separate smoke modules. Broaden to DkMath and DkMathTest one at a time if cache/resources allow, stopping on unrelated failure or excessive resource consumption and reporting exact scope. Store raw local build outputs plus exit/duration summaries under `.lake/build/gtail-step007/`; do not treat old logs as fresh validation.

## Final export and cycle audit

| Entrance | Direct imports before/after | Recursive names before/after | Added names |
| --- | --- | --- | --- |
| `DkMath.Lib` | 24 / 29 | 8809 / 8814 | 5 |
| `DkMath.FLT.Seven` | 198 / 200 | 9144 / 9152 | 8 |
| `DkMathTest` | 107 / 115 | 9479 / 9577 | 98 |

DFS cycle audit of the three entrance closures: PASS (796 local production/test modules). The Lib closure has zero DkMath.FLT modules. All three modified import lists are duplicate-free. Complete before/after lists remain in local before.json / after.json. The frontier ledger SHA256 is unchanged: `020ba87e6b8a481c448aadd0d4dccb985aab406a6071ea5110ad2e42205d178c`.

The smoke owner entrance adds the existing broad Seven graph to the root test driver: 98 additional recursive names, not merely its eight direct additions. This is an explicit dependency cost, separate from the narrow focused test graphs. Source closure does not prove that every reachable declaration has no placeholders; representative/new endpoint axiom checks remain necessary.

## Lake scope clarification

Toolchain LeanLibConfig defaults globs to Glob.one of roots; thus `lake build DkMath` validates the DkMath root and its import closure, not every standalone .lean under DkMath. The configured `DkMathTest.+` glob selects all submodules and excludes DkMathTest.lean itself (Glob.submodules). Consequently the edited root test file also needs a separate file elaboration check. No configuration changes are needed. This distinction will be quantified in the final report.

## Count-method correction and quantified scope

The first lexical import scan also saw import examples inside module documentation and words after inline comments. The final audit removes nested block/line comments, limits imports to the module header, and recognizes ordinary/public/private/meta modifiers. Counts in this Step 007 inventory/report are the corrected results, replayable with `.lake/build/gtail-step007/audit_imports.py`. Before-state entrances are read from initial HEAD, while unchanged owner sources are live. External package names outside local DkMath/installed Mathlib source remain terminal names; implicit compiler/native dependencies are not included in these source counts.

Current production DkMath entrance: 10314 recursive source names, 1534 local DkMath production modules. Test submodule glob: 683 Lean files; edited root test driver is separate, with 9577 recursive source names. Local scope.json records these numbers. Earlier checkpoint source counts are historical lexical counts, not a substitute for this refined import-header audit.

## Root test-file command repair

`LEAN_NUM_THREADS=2 lake build +DkMathTest` failed (exit 1, unknown module DkMathTest). With the explicit submodule-only glob, the root file is not a registered module build target. No Lake configuration change is needed: official `lake lean --help` specifies that `lake lean DkMathTest.lean` builds that file's imports then elaborates it in the workspace. Use that supported command for the edited root-file gate. This repair changes no Lean theorem or import.

Final edited-file validation: `LEAN_NUM_THREADS=2 lake lean DkMathTest.lean`, exit 0, 30.08s. The optional all-test-submodule run was interrupted for cost; Ctrl-C ended the runner but initially left its Lake child. Exact same-user/cwd/command cleanup terminated that child, and no build/compile child remains (editor servers preserved). Source closure/cycle/ledger checks are unaffected. Full test coverage is not claimed.
