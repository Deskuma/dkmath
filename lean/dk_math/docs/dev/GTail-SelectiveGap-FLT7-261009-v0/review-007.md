# Review 007 — GTail public API integration, build-scope and cost audit

Date: 2026-10-09
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED for scoped public API integration — Outcome B**.
Recorded Step 007 status remains **PARTIAL for the optional all-test-submodule gate**, pending a reproducible log/command for the subsequent full-build success reported by the repository owner.

## Review basis

Static inspection of pushed GitHub source, `report-007.md` and `source-inventory-007.md`:
- `DkMath/Lib.lean`, `DkMath/FLT/Seven.lean` and `DkMathTest.lean` import changes;
- `DkMathTest/CosmicFormula/GTailLibFacade.lean` (8 theorem-applying examples);
- `DkMathTest/FLT/Seven/GTailFacade.lean` (5 theorem-applying examples);
- `DkMath/Lib/README.md` and project documentation;
- `DkMathTest/NumberTheory/LegendreMergedCRT.lean`, independently inspected for high-heartbeat finite proofs.

No independent Lean build was executed by this reviewer. Codex supplied exact successful command/status records in report 007; the repository owner additionally stated that the full build passes, but the exact subsequent command/log and coverage were not supplied for updating report 007. Do not silently equate a `DkMath` production-root success, `lake lean DkMathTest.lean` root-file elaboration, and `lake build DkMathTest` with all 683 test submodules.

## Scope and dependency findings

1. `DkMath.Lib` explicitly imports all five new neutral modules, and its transitive source closure contains no `DkMath.FLT` modules.
2. `DkMath.FLT.Seven` imports `GTailBridge` and `GTailConstraintAudit`. The dependency remains **Lib -> FLT owner**, never the reverse.
3. The two new smoke tests access endpoints from their **sole respective façade imports**; 8 + 5 = 13 real, compiled example proofs, not just `#check`.
4. Existing new neutral/FLT mathematical sources are unchanged; Step 007 adds zero theorem endpoints. Report inventories 8 new definitions and **66 mathematical public theorem endpoints**: 58 neutral, 8 owner-specific.
5. All 66 reported axiom lists contain only Lean's standard foundational axioms; three use a strict subset. No new `sorryAx`. Historical research workspace warnings involving `sorry` in untouched modules do **not** imply that the entire repository is hole-free.
6. Codex recorded passing focused tests, public façade builds, `lake build DkMath`, and `lake lean DkMathTest.lean` (edited test root), all exit 0. `lake build DkMathTest` was manually interrupted after 400 of 683 test submodules had completed/replayed, not because of a demonstrated compiler error.
7. `git diff --check` and new-file whitespace/line-ending checks passed in the reported local environment. No PR/merge was made.

## Subsequent owner verification and honest status

The owner reports a later successful **full build**. Accept this as user-supplied additional evidence, not as a test command or execution log personally observed here. Before writing `Step 007 COMPLETE / all 683 tests checked` to source history, record the exact command (e.g. `lake build DkMathTest` versus `lake build DkMath`), exit status, git HEAD and whether all 683 test modules were actually covered. That is a documentation/evidence closeout, not a request to blindly spend another long all-suite run.

Public integration itself is approved, and this documentation gap does not block planning the next narrow research experiment. Merge into `develop` requires a separate explicit owner request.

## LegendreMergedCRT performance observation

Inspection of `DkMathTest/NumberTheory/LegendreMergedCRT.lean` confirms:
- `set_option maxRecDepth 100000` at module scope.
- Several `set_option maxHeartbeats 12000000 in` proof checks.
- `set_option maxHeartbeats 20000000 in` for `checkpoint_restricted_saturation_checked` and `extra_caps_checked`.
- These heavy proofs use `decide +kernel` on concrete finite checkpoint data, selected controlled bases, bounded ranges and certificate unions.

**maxHeartbeats is an allowance, not a measured heartbeat count or elapsed seconds.** These checks are pre-existing Legendre certificates, not changed GTail sources; report 007 notes a 67-second unchanged Legendre calibration during the optional full-test attempt, without proving that this single file accounts for the entire slowdown. Benchmark candidates are individual `decide +kernel` proofs, grouped certificate-splitting, and cached exact subproofs. Measure before optimizing, and avoid replacing checked computation with an untrusted oracle or a new axiom. Any optimization belongs to a separate performance task/branch, not a retroactive GTail theorem patch.

## Mathematical frontier

Step 006's `constraint-ledger-006.md` remains accurate. The positive focused gap, 7-divisibility, neutral coprimality, and exact residual 7-layer are proved; val_7(g) conservation, q-square allocation, residue order 21, typed Norm/unit-gauge transfer and next primitive Fermat packet are **not yet proved**.

Outcome B records a reusable and publicly accessible GTail instrument, not FLT7 closure.

## Review decision

**APPROVED** for mathematics/architecture/public API integration, without claiming independently verified all-test coverage. Next task may develop a narrow valuation calibration after recording the owner's full-build evidence. No authorization to merge or to edit unrelated Legendre proof certificates follows from this review.
