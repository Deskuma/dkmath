# Step043 release source inventory

Date: 2026-10-12. Research: **Outcome B / STOP042**. Release: **READY for review**.

## Exact checkout and comparison

Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`; validated HEAD `caebaf0ec98c12e1e570b6e2e9aefb2aa2362f7e`.
After successful `git fetch origin`, `git rev-list --left-right --count origin/develop...HEAD`
returned `1 136`: behind1 / ahead136. HEAD merge-base diff contains **287 files = 283 additions + 4 modifications**.

| Added category | Files |
| --- | ---: |
| Specialized FLT owners | 30 |
| Dedicated FLT facade | 1 |
| Neutral Lib owners | 17 |
| Tests (including all three entrance smokes) | 49 |
| Research documents | 186 |

The four existing changed files are `DkMath/FLT/Seven.lean`, `DkMath/Lib.lean`,
`DkMath/Lib/README.md`, `DkMathTest.lean`, relative to `lean/dk_math`.
The checkout initially had one user-staged edit, `instruction-043.md`; it is preserved.
Concurrent README header edits/staging were also retained; the final index includes
README and instruction-043. The latter has staged blob
`42e6dedbb9a8daecf58cad2a4caf7a274d7daf16` with no unstaged difference.
This release step adds `report-043.md` and this inventory, updates only PR-CLOSEOUT,
PR-DRAFT and README, and appends ROADMAP. The HEAD counts above exclude those new
working changes; two new files make the prospective comparison 289 files (285A/4M)
without changing the 97-file added Lean inventory.

The develop-only commit `ad8526451` adds
`docs/not_implements/261010-CF2D-Multiplicative-Quadratic-Norm-Generalization.md`.
It does not change this Lean source matrix. Separate authorized integration is still required.

## Facade, imports and default discovery

[Dedicated facade](../../../DkMath/FLT/Seven/GTail.lean) imports all 30 specialized
owners in the table below exactly once, with no extra or missing import. It defines no
new mathematical declaration. [Dedicated smoke](../../../DkMathTest/FLT/Seven/GTailResearchFacade.lean)
imports only this facade and checks 12 API names / five selected axiom outputs.
Both retain the existing MIT header and import-following module `#print` convention.
No Lean file was edited in Step043.

Source-level import closures (local + Mathlib + terminal core names, not Lake job counts):

| Entrance | Reachable names | Local DkMath modules |
| --- | ---: | ---: |
| DkMath.FLT.Seven.GTail | 8962 | 182 |
| DkMath.Lib | 8814 | 34 |
| DkMath.FLT.Seven | 9152 | 372 |

The scoped closure does not contain `DkMath.FLT.Seven`; no new umbrella cycle
is introduced. The union of audited local production/test closures has 473 vertices
and zero cycles. All 17 added neutral closures and the complete Lib closure have
zero FLT reachability. Specialized owners may import neutral owners. All 17 neutral
owners are reached by the scoped facade; only the five initial neutral owners are
reached by `DkMath.Lib`. No broader promotion or aggregator change was made.

The older [FLT facade](../../../DkMath/FLT/Seven.lean), [Lib facade](../../../DkMath/Lib.lean)
and [root test driver](../../../DkMathTest.lean) remain unchanged in Step043.
The root has the early Step007 imports; `lakefile.toml` uses
`testDriver = "DkMathTest"` and `globs = ["DkMathTest.+"]` for the test library.
All 49 new tests were executed directly, then all 49 were observed again in the
actual default `lake test` log. No root import addition is necessary. The full run
exited0; its last progress counter was 11284/11284, with 2197 replay event lines
and no Built event lines. This validates a cache-reusing invocation, not a clean build.

The closure size and the recorded cached timings do not measure clean compilation
or intrinsic import performance. Keeping the scoped entrance avoids broad-facade
reachability and the old placeholder-warning dependencies.

## 30 specialized production × test coverage

Production paths are `DkMath.FLT.Seven.*`; matching test paths are
`DkMathTest.FLT.Seven.*`. Every row is imported by the scoped facade (01-build),
executed directly in the indicated test batch, and observed in 08-test.
Logs are local ignored files under `.lake/build/gtail-step043/`.

| Production owner | Test | Direct log / result |
| --- | --- | --- |
| [GTailBridge](../../../DkMath/FLT/Seven/GTailBridge.lean) | [GTailBridge](../../../DkMathTest/FLT/Seven/GTailBridge.lean) | 07-build.log / exit0 |
| [GTailConstraintAudit](../../../DkMath/FLT/Seven/GTailConstraintAudit.lean) | [GTailConstraintAudit](../../../DkMathTest/FLT/Seven/GTailConstraintAudit.lean) | 07-build.log / exit0 |
| [GTailCyclotomicLocalEval](../../../DkMath/FLT/Seven/GTailCyclotomicLocalEval.lean) | [GTailCyclotomicLocalEval](../../../DkMathTest/FLT/Seven/GTailCyclotomicLocalEval.lean) | 07-build.log / exit0 |
| [GTailCyclotomicPrimeAddress](../../../DkMath/FLT/Seven/GTailCyclotomicPrimeAddress.lean) | [GTailCyclotomicPrimeAddress](../../../DkMathTest/FLT/Seven/GTailCyclotomicPrimeAddress.lean) | 07-build.log / exit0 |
| [GTailCyclotomicSixRootInterpolation](../../../DkMath/FLT/Seven/GTailCyclotomicSixRootInterpolation.lean) | [GTailCyclotomicSixRootInterpolation](../../../DkMathTest/FLT/Seven/GTailCyclotomicSixRootInterpolation.lean) | 07-build.log / exit0 |
| [GTailCyclotomicSixRootOrbit](../../../DkMath/FLT/Seven/GTailCyclotomicSixRootOrbit.lean) | [GTailCyclotomicSixRootOrbit](../../../DkMathTest/FLT/Seven/GTailCyclotomicSixRootOrbit.lean) | 07-build.log / exit0 |
| [GTailCyclotomicTailDepthFour](../../../DkMath/FLT/Seven/GTailCyclotomicTailDepthFour.lean) | [GTailCyclotomicTailDepthFour](../../../DkMathTest/FLT/Seven/GTailCyclotomicTailDepthFour.lean) | 07-build.log / exit0 |
| [GTailCyclotomicTailDepthOne](../../../DkMath/FLT/Seven/GTailCyclotomicTailDepthOne.lean) | [GTailCyclotomicTailDepthOne](../../../DkMathTest/FLT/Seven/GTailCyclotomicTailDepthOne.lean) | 07-build.log / exit0 |
| [GTailCyclotomicTailDepthThree](../../../DkMath/FLT/Seven/GTailCyclotomicTailDepthThree.lean) | [GTailCyclotomicTailDepthThree](../../../DkMathTest/FLT/Seven/GTailCyclotomicTailDepthThree.lean) | 07-build.log / exit0 |
| [GTailCyclotomicTailDepthTwo](../../../DkMath/FLT/Seven/GTailCyclotomicTailDepthTwo.lean) | [GTailCyclotomicTailDepthTwo](../../../DkMathTest/FLT/Seven/GTailCyclotomicTailDepthTwo.lean) | 07-build.log / exit0 |
| [GTailCyclotomicTailDerivative](../../../DkMath/FLT/Seven/GTailCyclotomicTailDerivative.lean) | [GTailCyclotomicTailDerivative](../../../DkMathTest/FLT/Seven/GTailCyclotomicTailDerivative.lean) | 07-build.log / exit0 |
| [GTailCyclotomicTailFactorProduct](../../../DkMath/FLT/Seven/GTailCyclotomicTailFactorProduct.lean) | [GTailCyclotomicTailFactorProduct](../../../DkMathTest/FLT/Seven/GTailCyclotomicTailFactorProduct.lean) | 07-build.log / exit0 |
| [GTailCyclotomicTailSecondDigit](../../../DkMath/FLT/Seven/GTailCyclotomicTailSecondDigit.lean) | [GTailCyclotomicTailSecondDigit](../../../DkMathTest/FLT/Seven/GTailCyclotomicTailSecondDigit.lean) | 07-build.log / exit0 |
| [GTailCyclotomicTailTaylorLift](../../../DkMath/FLT/Seven/GTailCyclotomicTailTaylorLift.lean) | [GTailCyclotomicTailTaylorLift](../../../DkMathTest/FLT/Seven/GTailCyclotomicTailTaylorLift.lean) | 07-build.log / exit0 |
| [GTailEisensteinCyclotomicCommonReceiver](../../../DkMath/FLT/Seven/GTailEisensteinCyclotomicCommonReceiver.lean) | [GTailEisensteinCyclotomicCommonReceiver](../../../DkMathTest/FLT/Seven/GTailEisensteinCyclotomicCommonReceiver.lean) | 06-build.log / exit0 |
| [GTailEisensteinCyclotomicNoDirectHom](../../../DkMath/FLT/Seven/GTailEisensteinCyclotomicNoDirectHom.lean) | [GTailEisensteinCyclotomicNoDirectHom](../../../DkMathTest/FLT/Seven/GTailEisensteinCyclotomicNoDirectHom.lean) | 06-build.log / exit0 |
| [GTailEisensteinCyclotomicPrimeGrid](../../../DkMath/FLT/Seven/GTailEisensteinCyclotomicPrimeGrid.lean) | [GTailEisensteinCyclotomicPrimeGrid](../../../DkMathTest/FLT/Seven/GTailEisensteinCyclotomicPrimeGrid.lean) | 06-build.log / exit0 |
| [GTailEisensteinCyclotomicPrimeJoin](../../../DkMath/FLT/Seven/GTailEisensteinCyclotomicPrimeJoin.lean) | [GTailEisensteinCyclotomicPrimeJoin](../../../DkMathTest/FLT/Seven/GTailEisensteinCyclotomicPrimeJoin.lean) | 06-build.log / exit0 |
| [GTailFocusedCapacityIndependence](../../../DkMath/FLT/Seven/GTailFocusedCapacityIndependence.lean) | [GTailFocusedCapacityIndependence](../../../DkMathTest/FLT/Seven/GTailFocusedCapacityIndependence.lean) | 06-build.log / exit0 |
| [GTailFocusedDefectGlobalCapacity](../../../DkMath/FLT/Seven/GTailFocusedDefectGlobalCapacity.lean) | [GTailFocusedDefectGlobalCapacity](../../../DkMathTest/FLT/Seven/GTailFocusedDefectGlobalCapacity.lean) | 06-build.log / exit0 |
| [GTailFocusedDefectSquareFirewall](../../../DkMath/FLT/Seven/GTailFocusedDefectSquareFirewall.lean) | [GTailFocusedDefectSquareFirewall](../../../DkMathTest/FLT/Seven/GTailFocusedDefectSquareFirewall.lean) | 06-build.log / exit0 |
| [GTailFocusedGenericPrimeReceiver](../../../DkMath/FLT/Seven/GTailFocusedGenericPrimeReceiver.lean) | [GTailFocusedGenericPrimeReceiver](../../../DkMathTest/FLT/Seven/GTailFocusedGenericPrimeReceiver.lean) | 06-build.log / exit0 |
| [GTailFocusedNormCyclotomicDepthBridge](../../../DkMath/FLT/Seven/GTailFocusedNormCyclotomicDepthBridge.lean) | [GTailFocusedNormCyclotomicDepthBridge](../../../DkMathTest/FLT/Seven/GTailFocusedNormCyclotomicDepthBridge.lean) | 07-build.log / exit0 |
| [GTailFocusedPrimeRoute](../../../DkMath/FLT/Seven/GTailFocusedPrimeRoute.lean) | [GTailFocusedPrimeRoute](../../../DkMathTest/FLT/Seven/GTailFocusedPrimeRoute.lean) | 06-build.log / exit0 |
| [GTailGlobalBalanceFirewall](../../../DkMath/FLT/Seven/GTailGlobalBalanceFirewall.lean) | [GTailGlobalBalanceFirewall](../../../DkMathTest/FLT/Seven/GTailGlobalBalanceFirewall.lean) | 06-build.log / exit0 |
| [GTailNormReadoutAudit](../../../DkMath/FLT/Seven/GTailNormReadoutAudit.lean) | [GTailNormReadoutAudit](../../../DkMathTest/FLT/Seven/GTailNormReadoutAudit.lean) | 07-build.log / exit0 |
| [GTailPrimeAllocationAudit](../../../DkMath/FLT/Seven/GTailPrimeAllocationAudit.lean) | [GTailPrimeAllocationAudit](../../../DkMathTest/FLT/Seven/GTailPrimeAllocationAudit.lean) | 07-build.log / exit0 |
| [GTailPrimeOrderAudit](../../../DkMath/FLT/Seven/GTailPrimeOrderAudit.lean) | [GTailPrimeOrderAudit](../../../DkMathTest/FLT/Seven/GTailPrimeOrderAudit.lean) | 07-build.log / exit0 |
| [GTailSevenUnitAudit](../../../DkMath/FLT/Seven/GTailSevenUnitAudit.lean) | [GTailSevenUnitAudit](../../../DkMathTest/FLT/Seven/GTailSevenUnitAudit.lean) | 07-build.log / exit0 |
| [GTailValuationAudit](../../../DkMath/FLT/Seven/GTailValuationAudit.lean) | [GTailValuationAudit](../../../DkMathTest/FLT/Seven/GTailValuationAudit.lean) | 07-build.log / exit0 |

## 17 neutral production × test coverage

Each production owner was compiled transitively by the successful scoped entrance
and its indicated direct test. `GTailSevenArithmetic` is exercised by the original
Lib facade smoke rather than a nonexistent same-name test. Number-theory tests use
`DkMathTest.NumberTheory.*`; cosmic tests use `DkMathTest.CosmicFormula.*`.

| Production owner | Exposed by Lib | Test | Direct log / result |
| --- | --- | --- | --- |
| [GTailFactor](../../../DkMath/Lib/Cosmic/GTailFactor.lean) | yes | [GTailFactor](../../../DkMathTest/CosmicFormula/GTailFactor.lean) | 07-build.log / exit0 |
| [GTailSelection](../../../DkMath/Lib/Cosmic/GTailSelection.lean) | yes | [GTailSelection](../../../DkMathTest/CosmicFormula/GTailSelection.lean) | 07-build.log / exit0 |
| [GTailSeven](../../../DkMath/Lib/Cosmic/GTailSeven.lean) | yes | [GTailSeven](../../../DkMathTest/CosmicFormula/GTailSeven.lean) | 07-build.log / exit0 |
| [GTailSevenArithmetic](../../../DkMath/Lib/Cosmic/GTailSevenArithmetic.lean) | yes | [GTailLibFacade](../../../DkMathTest/CosmicFormula/GTailLibFacade.lean) | 04-build.log / exit0 |
| [GTailSevenPrimeAllocation](../../../DkMath/Lib/Cosmic/GTailSevenPrimeAllocation.lean) | direct-import API | [GTailSevenPrimeAllocation](../../../DkMathTest/CosmicFormula/GTailSevenPrimeAllocation.lean) | 07-build.log / exit0 |
| [GTailSevenValuation](../../../DkMath/Lib/Cosmic/GTailSevenValuation.lean) | direct-import API | [GTailSevenValuation](../../../DkMathTest/CosmicFormula/GTailSevenValuation.lean) | 07-build.log / exit0 |
| [GTailTransport](../../../DkMath/Lib/Cosmic/GTailTransport.lean) | yes | [GTailTransport](../../../DkMathTest/CosmicFormula/GTailTransport.lean) | 07-build.log / exit0 |
| [GTailSevenEisensteinResidue](../../../DkMath/Lib/NumberTheory/GTailSevenEisensteinResidue.lean) | direct-import API | [GTailSevenEisensteinResidue](../../../DkMathTest/NumberTheory/GTailSevenEisensteinResidue.lean) | 07-build.log / exit0 |
| [GTailSevenIdealSquareAddress](../../../DkMath/Lib/NumberTheory/GTailSevenIdealSquareAddress.lean) | direct-import API | [GTailSevenIdealSquareAddress](../../../DkMathTest/NumberTheory/GTailSevenIdealSquareAddress.lean) | 07-build.log / exit0 |
| [GTailSevenNormReadout](../../../DkMath/Lib/NumberTheory/GTailSevenNormReadout.lean) | direct-import API | [GTailSevenNormReadout](../../../DkMathTest/NumberTheory/GTailSevenNormReadout.lean) | 07-build.log / exit0 |
| [GTailSevenPairedResidue](../../../DkMath/Lib/NumberTheory/GTailSevenPairedResidue.lean) | direct-import API | [GTailSevenPairedResidue](../../../DkMathTest/NumberTheory/GTailSevenPairedResidue.lean) | 07-build.log / exit0 |
| [GTailSevenPrimeOrder](../../../DkMath/Lib/NumberTheory/GTailSevenPrimeOrder.lean) | direct-import API | [GTailSevenPrimeOrder](../../../DkMathTest/NumberTheory/GTailSevenPrimeOrder.lean) | 07-build.log / exit0 |
| [GTailSevenRamifiedThreeIdeal](../../../DkMath/Lib/NumberTheory/GTailSevenRamifiedThreeIdeal.lean) | direct-import API | [GTailSevenRamifiedThreeIdeal](../../../DkMathTest/NumberTheory/GTailSevenRamifiedThreeIdeal.lean) | 07-build.log / exit0 |
| [GTailSevenRealTraceResidue](../../../DkMath/Lib/NumberTheory/GTailSevenRealTraceResidue.lean) | direct-import API | [GTailSevenRealTraceResidue](../../../DkMathTest/NumberTheory/GTailSevenRealTraceResidue.lean) | 07-build.log / exit0 |
| [GTailSevenResidueIdeal](../../../DkMath/Lib/NumberTheory/GTailSevenResidueIdeal.lean) | direct-import API | [GTailSevenResidueIdeal](../../../DkMathTest/NumberTheory/GTailSevenResidueIdeal.lean) | 07-build.log / exit0 |
| [GTailSevenSplitIdeal](../../../DkMath/Lib/NumberTheory/GTailSevenSplitIdeal.lean) | direct-import API | [GTailSevenSplitIdeal](../../../DkMathTest/NumberTheory/GTailSevenSplitIdeal.lean) | 07-build.log / exit0 |
| [SevenUnitAllocation](../../../DkMath/Lib/NumberTheory/SevenUnitAllocation.lean) | direct-import API | [SevenUnitAllocation](../../../DkMathTest/NumberTheory/SevenUnitAllocation.lean) | 07-build.log / exit0 |

## Remaining facade/test entries and corrected old source

The 30 + 16 matching owner tests above plus these three smokes exhaust all 49 added tests:

| Entry | Result |
| --- | --- |
| DkMath.FLT.Seven.GTail (new production aggregator) | 01-build / exit0 / Replayed |
| DkMathTest.FLT.Seven.GTailResearchFacade | 02-build / exit0 / Built |
| DkMathTest.CosmicFormula.GTailLibFacade | 04-build / exit0 / Replayed |
| DkMathTest.FLT.Seven.GTailFacade | 05-build / exit0 / Replayed / four existing warnings |

The two old source owners `SevenBaseTerminalRowZSignedResidualCore` and
`SevenBaseTerminalRamifiedSummit` were also direct targets in 06-build / exit0.
The former constructs the Row-Z signed discriminant−7 root (TERM-010); the latter
constructs the common primitive ramified summit. They are existing sources, not
added GTail owners. This correction does not construct lifted primitive nextX/Y/Z
or close the CRT original-coordinate independent-bound and row-mismatch obligations.
The new Eisenstein source is `TraceOneInt(-1)` (discriminant−3), distinct from
old `TraceOneInt(-2)` (discriminant−7). Neither source is replaced by the other.

No unconditional positive-natural Fermat exponent-seven no-solution theorem is
exported by this new research facade. Step040 certifies Δ=0 and hence equality
under support + independent magnitude assumptions, not Fermat impossibility.
Step041 countermodels separate those assumptions. (5,8,9,4) is focused but non-Fermat.

## Complete added document list at validated HEAD (186)

The list is relative to this research-document directory. Historical instructions,
reports and reviews are retained byte-for-byte in this release step.

```text
PR-CLOSEOUT.md
PR-DRAFT.md
README.md
ROADMAP.md
constraint-ledger-006.md
frontier-032.md
frontier-033.md
frontier-034.md
frontier-035.md
frontier-036.md
frontier-037.md
frontier-038.md
frontier-039.md
frontier-040.md
frontier-041.md
instruction-001.md
instruction-002.md
instruction-003.md
instruction-004.md
instruction-005.md
instruction-006.md
instruction-007.md
instruction-008.md
instruction-009.md
instruction-010.md
instruction-011.md
instruction-012.md
instruction-013.md
instruction-014.md
instruction-015.md
instruction-016.md
instruction-017.md
instruction-018.md
instruction-019.md
instruction-020.md
instruction-021.md
instruction-022.md
instruction-023.md
instruction-024.md
instruction-025.md
instruction-026.md
instruction-027.md
instruction-028.md
instruction-029.md
instruction-030.md
instruction-031.md
instruction-032.md
instruction-033.md
instruction-034.md
instruction-035.md
instruction-036.md
instruction-037.md
instruction-038.md
instruction-039.md
instruction-040.md
instruction-041.md
instruction-042.md
instruction-043.md
report-001.md
report-002.md
report-003.md
report-004.md
report-005.md
report-006.md
report-007.md
report-008.md
report-009.md
report-010.md
report-011.md
report-012.md
report-013.md
report-014.md
report-015.md
report-016.md
report-017.md
report-018.md
report-019.md
report-020.md
report-021.md
report-022.md
report-023.md
report-024.md
report-025.md
report-026.md
report-027.md
report-028.md
report-029.md
report-030.md
report-031.md
report-032.md
report-033.md
report-034.md
report-035.md
report-036.md
report-037.md
report-038.md
report-039.md
report-040.md
report-041.md
report-042.md
research-decision-042.md
review-001.md
review-002.md
review-003.md
review-004.md
review-005.md
review-006.md
review-007.md
review-008.md
review-009.md
review-010.md
review-011.md
review-012.md
review-013.md
review-014.md
review-015.md
review-016.md
review-017.md
review-018.md
review-019.md
review-020.md
review-021.md
review-022.md
review-023.md
review-024.md
review-025.md
review-026.md
review-027.md
review-028.md
review-029.md
review-030.md
review-031.md
review-032.md
review-033.md
review-034.md
review-035.md
review-036.md
review-037.md
review-038.md
review-039.md
review-040.md
review-041.md
review-042.md
source-inventory-001.md
source-inventory-002.md
source-inventory-003.md
source-inventory-004.md
source-inventory-005.md
source-inventory-006.md
source-inventory-007.md
source-inventory-008.md
source-inventory-009.md
source-inventory-010.md
source-inventory-011.md
source-inventory-012.md
source-inventory-013.md
source-inventory-014.md
source-inventory-015.md
source-inventory-016.md
source-inventory-017.md
source-inventory-018.md
source-inventory-019.md
source-inventory-020.md
source-inventory-021.md
source-inventory-022.md
source-inventory-023.md
source-inventory-024.md
source-inventory-025.md
source-inventory-026.md
source-inventory-027.md
source-inventory-028.md
source-inventory-029.md
source-inventory-030.md
source-inventory-031.md
source-inventory-032.md
source-inventory-033.md
source-inventory-034.md
source-inventory-035.md
source-inventory-036.md
source-inventory-037.md
source-inventory-038.md
source-inventory-039.md
source-inventory-040.md
source-inventory-041.md
source-inventory-042.md
validation-addendum-007.md
```
