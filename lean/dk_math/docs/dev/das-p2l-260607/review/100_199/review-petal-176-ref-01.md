# Git diff / Report / Review

## Add: docs: Pressure Adjacent Diagnosis Split Plan

gch: 9d35feb03f3c31d167e2b629cb681f6057bd3cd7

## Report

cp175 完了です。今回は指示通り Lean 宣言は動かさず、refactor preflight の docs だけ追加しました。

追加:

- [pressure-adjacent-diagnosis-split-plan.md](/lean/dk_math/docs/dev/das-p2l-260607/refactor/pressure-adjacent-diagnosis-split-plan.md:1)
- [report-petal-175.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-175.md:1)

内容は、`PressureAccounting.lean` が約 3773 行になっている現状、adjacent-diagnosis cluster の候補、依存関係、段階的な module split 案、import cycle などのリスク、非目標を整理しています。次の推奨は、いきなり bounded wrapper を動かすより、依存が軽い `SourcePressureLocalIslandWitnessAdjacentPairInList` 周辺から切り出せるか確認する流れです。

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureAccounting` PASS
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier` PASS
- `lake build DkMath.Collatz.PetalBridge` PASS
- 対象2ファイルの `sorry` 検索ヒットなし
- `git diff --check` PASS

既存の無関係 warning として `DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6 declaration uses sorry` は引き続き表示されています。

## Director

Alright. From this point on, the work consists solely of refactoring; I will proceed according to plan—maintaining a buildable state throughout—without requiring further reviewer intervention.

I will use `176` as the base checkpoint number and increment the `ref-01` suffix as I progress.

While the refactoring is considered complete once the limit of 2,000 lines is reached, I am setting an additional target of 1,000 to 1,500 lines to account for future supplementary lemmas.

It would be a good idea to enhance the comments and docstrings during refactoring. Incorporating the mathematical semantics might also be beneficial.

Let’s get started according to the plan.

## Diff

`````md
````diff
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/refactor/pressure-adjacent-diagnosis-split-plan.md b/lean/dk_math/docs/dev/das-p2l-260607/refactor/pressure-adjacent-diagnosis-split-plan.md
new file mode 100644
index 00000000..577c0293
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/refactor/pressure-adjacent-diagnosis-split-plan.md
@@ -0,0 +1,280 @@
+# Pressure Adjacent Diagnosis Split Plan
+
+## Current State
+
+`DkMath/Collatz/PetalBridge/PressureAccounting.lean` currently has about 3773
+lines.
+
+The adjacent-diagnosis declarations have become a coherent cluster.  They now
+cover:
+
+- pair-local recovered budget evidence;
+- enclosing-list adjacent-overlap obstruction evidence;
+- ordered adjacent-pair addresses inside explicit witness lists;
+- list-level adjacent diagnosis carriers;
+- bounded three-, four-, and five-witness wrappers.
+
+This cluster is still local to explicitly supplied witness lists.  It does not
+claim coverage, maximality, uniqueness, prefix behavior, union accounting, or
+Collatz convergence.
+
+The declarations are currently concentrated around `PressureAccounting.lean`
+lines 3163-3674.  That makes them a plausible future extraction target, but the
+dependencies below should be checked before any declaration movement.
+
+## Candidate Cluster
+
+### Adjacent Diagnosis Carrier
+
+Candidate declarations:
+
+- `SourcePressureLocalIslandWitnessAdjacentDiagnosis`
+- `SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered`
+- `SourcePressureLocalIslandWitnessAdjacentDiagnosis.overlap`
+- `SourcePressureLocalIslandWitnessAdjacentDiagnosis.elim`
+- `SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered_or_listFailure`
+- `SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail`
+
+Role:
+
+This is the pair-local/enclosing-list carrier.  The recovered branch remains
+attached to the adjacent pair `A, B`; the overlap branch remains an obstruction
+on the enclosing list `L`.
+
+### Adjacent Pair Address Predicate
+
+Candidate declarations:
+
+- `SourcePressureLocalIslandWitnessAdjacentPairInList`
+- `SourcePressureLocalIslandWitnessAdjacentPairInList.head`
+- `SourcePressureLocalIslandWitnessAdjacentPairInList.tail`
+- `SourcePressureLocalIslandWitnessAdjacentPairInList.head_or_tail`
+- `SourcePressureLocalIslandWitnessAdjacentPairInList.cons_iff_head_or_tail`
+- `SourcePressureLocalIslandWitnessAdjacentPairInList.nil_false`
+- `SourcePressureLocalIslandWitnessAdjacentPairInList.singleton_false`
+
+Role:
+
+This is the ordered address layer for neighboring pairs only.  It is not
+arbitrary pair membership and does not sort or classify a list.
+
+### List-Level Adjacent Diagnosis Carrier
+
+Candidate declarations:
+
+- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis`
+- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_adjacent`
+- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.elim`
+- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_head`
+- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail`
+- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail_tail`
+- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail_tail_tail`
+- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_listFailure`
+- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_overlap`
+- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.nil_false`
+- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.singleton_false`
+
+Role:
+
+This is the public carrier for "some adjacent pair in this explicit list has a
+diagnosis".  The carrier hides which adjacent pair was selected while still
+preserving pair-local recovered evidence through projections.
+
+### Bounded Diagnosis Wrappers
+
+Candidate declarations:
+
+- `sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_carrier`
+- `sourcePressureLocalIslandWitnessList_failure_fourDiagnosis_carrier`
+- `sourcePressureLocalIslandWitnessList_failure_three_hasAdjacentDiagnosis`
+- `sourcePressureLocalIslandWitnessList_failure_four_hasAdjacentDiagnosis`
+- `sourcePressureLocalIslandWitnessList_failure_five_hasAdjacentDiagnosis`
+
+Role:
+
+These are bounded wrappers for explicit lists of length three, four, and five.
+They are observation tools, not a recursive algorithm.
+
+### Projection And Propagation Helpers
+
+Candidate declarations:
+
+- `SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered_or_listFailure`
+- `SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail`
+- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.elim`
+- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_head`
+- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail`
+- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail_tail`
+- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail_tail_tail`
+- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_listFailure`
+- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_overlap`
+
+Role:
+
+These declarations make the bounded carrier usable by downstream files without
+opening the full nested branch structure.
+
+## Upstream Dependencies
+
+### Carrier And Constructor Dependencies
+
+Major dependencies:
+
+- `SourcePressureLocalIslandWitness`
+- `SourcePressureLocalIslandWitnessBefore`
+- `SourcePressureIntervalNetDrop`
+- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair`
+- `SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction`
+
+These must remain available before extracting
+`SourcePressureLocalIslandWitnessAdjacentDiagnosis`.
+
+### Address Predicate Dependencies
+
+Major dependencies:
+
+- `SourcePressureLocalIslandWitness`
+- Lean `List`
+
+This group is low-risk to extract once the witness carrier is available.  It
+does not depend on pressure budgets or overlap obstruction.
+
+### List-Level Carrier Dependencies
+
+Major dependencies:
+
+- `SourcePressureLocalIslandWitness`
+- `SourcePressureLocalIslandWitnessAdjacentPairInList`
+- `SourcePressureLocalIslandWitnessAdjacentDiagnosis`
+- `SourcePressureLocalIslandWitnessBefore`
+- `SourcePressureIntervalNetDrop`
+- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair`
+- `SourcePressureLocalIslandWitnessListHasSortedBeforeFailure`
+- `SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction`
+
+This group should be extracted only after the adjacent-pair address predicate
+and adjacent-diagnosis carrier are available.
+
+### Bounded Wrapper Dependencies
+
+Major dependencies:
+
+- `sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis`
+- `sourcePressureLocalIslandWitnessList_failure_threeDiagnosis`
+- `sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_carrier`
+- `sourcePressureLocalIslandWitnessList_failure_fourDiagnosis_carrier`
+- `SourcePressureLocalIslandWitnessListHasSortedBeforeFailure`
+- `sourcePressureIntervalPulseAddress_of_localIslandWitness`
+- `SourcePressureLocalIslandWitnessAdjacentDiagnosis`
+- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis`
+
+These wrappers are the highest-risk extraction group because they depend on
+the surrounding order-failure and bounded-diagnosis layer.
+
+## Candidate Module Layout
+
+### Current Compatibility Surface
+
+Keep:
+
+```text
+DkMath.Collatz.PetalBridge.PressureAccounting
+```
+
+as the compatibility surface for now.  Existing downstream imports should keep
+working through this module.
+
+### Future Low-Risk Module
+
+Possible future module:
+
+```text
+DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
+```
+
+Potential contents:
+
+- adjacent pair address predicate;
+- adjacent diagnosis carrier;
+- list-level adjacent diagnosis carrier;
+- projection and propagation helpers;
+- eventually bounded wrappers, but only after dependency checks.
+
+### If Direct Extraction Is Blocked
+
+If `PressureAdjacentDiagnosis.lean` creates an import cycle, split earlier
+stable upstream declarations first.  Likely candidates:
+
+- witness carrier and address conversion definitions;
+- sorted-before failure carrier;
+- adjacent-overlap obstruction carrier;
+- pair recovered-budget theorem wrappers.
+
+The bounded wrappers should move last, because they depend on the one-step and
+three-/four-witness diagnosis theorems.
+
+## Migration Plan
+
+### Stage 1: Preflight Only
+
+- Move no Lean declarations.
+- Record dependency boundaries.
+- Keep theorem names stable.
+- Keep review diffs small.
+
+This checkpoint is Stage 1.
+
+### Stage 2: Extract Stable Low-Risk Declarations
+
+- Extract only declarations whose dependencies already live earlier in the
+  import graph.
+- Keep declaration names unchanged.
+- Add imports from `PressureAccounting.lean` to preserve the compatibility
+  surface.
+- Verify:
+  - `lake build DkMath.Collatz.PetalBridge.PressureAccounting`
+  - `lake build DkMath.Collatz.PetalBridge.PressureFrontier`
+  - `lake build DkMath.Collatz.PetalBridge`
+
+The best first extraction candidate is the adjacent-pair address predicate,
+because it depends only on `SourcePressureLocalIslandWitness` and `List`.
+
+### Stage 3: Move Carriers And Helpers
+
+- Move `SourcePressureLocalIslandWitnessAdjacentDiagnosis` after confirming
+  the overlap-obstruction and pair-budget dependencies are stable.
+- Move `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis` after both
+  the pair address predicate and adjacent diagnosis carrier are imported.
+- Move bounded wrappers only after the carrier/address predicates are stable.
+
+## Risks
+
+- Import cycles if the new module imports `PressureAccounting` while
+  `PressureAccounting` also imports the new module.
+- Downstream files may import `PressureAccounting` and expect these names
+  there.
+- Bounded wrapper theorem order may depend on earlier local theorems in the
+  same file.
+- Namespace and name stability must be preserved; names should not change in
+  the split.
+- Large declaration movement can create line-number churn in review diffs.
+- Moving bounded wrappers too early may pull most of `PressureAccounting` into
+  the new module, defeating the split.
+
+## Non-Goals
+
+This refactor plan does not introduce:
+
+- arbitrary-length classifier;
+- fuel-indexed diagnosis;
+- sorting;
+- coverage;
+- maximality;
+- uniqueness;
+- prefix behavior;
+- union accounting;
+- interval merging;
+- Collatz convergence.
+
+Recovered budgets remain pair-local.  Overlap remains an adjacent obstruction
+on the enclosing list.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-175.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-175.md
new file mode 100644
index 00000000..3e37b393
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-175.md
@@ -0,0 +1,110 @@
+# Report Petal 175
+
+## Checkpoint
+
+`cp: 175`
+
+Main root only: adjacent-diagnosis split preflight report.
+
+## Result
+
+This checkpoint is a refactor preflight only.
+
+No Lean declarations were moved.  No new Lean module was created.  No
+declaration names were changed.
+
+Created:
+
+```text
+docs/dev/das-p2l-260607/refactor/pressure-adjacent-diagnosis-split-plan.md
+```
+
+## Split Plan Summary
+
+`PressureAccounting.lean` currently has about 3773 lines.
+
+The adjacent-diagnosis surface is concentrated around the following cluster:
+
+- `SourcePressureLocalIslandWitnessAdjacentDiagnosis`
+- `SourcePressureLocalIslandWitnessAdjacentPairInList`
+- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis`
+- bounded wrappers for three-, four-, and five-witness lists;
+- projection and propagation helpers.
+
+The proposed future direction is staged:
+
+1. Keep `PressureAccounting.lean` as the compatibility surface.
+2. Extract low-risk declarations only after dependency checks.
+3. Prefer extracting the adjacent-pair address predicate first, because it has
+   the smallest dependency surface.
+4. Move the adjacent diagnosis carrier only after overlap-obstruction and
+   pair-budget dependencies are stable.
+5. Move bounded wrappers last.
+
+## Key Risk
+
+The main technical risk is import cycles.  The bounded wrappers depend on
+one-step and bounded diagnosis theorems already in `PressureAccounting.lean`,
+so moving them too early may drag most of the file into the new module.
+
+## Recommended Next Checkpoint
+
+Recommended next checkpoint:
+
+```text
+Design or implement the first low-risk extraction:
+SourcePressureLocalIslandWitnessAdjacentPairInList and its immediate API.
+```
+
+This should be done only if the upstream witness carrier is already available
+without importing `PressureAccounting.lean` back into the new module.  If that
+dependency boundary is not clean, the next checkpoint should instead identify
+the smallest upstream witness/address module needed before extraction.
+
+## Boundary
+
+This checkpoint did not introduce:
+
+- arbitrary-length classifier;
+- fuel-indexed diagnosis;
+- sorting;
+- coverage;
+- maximality;
+- uniqueness;
+- prefix behavior;
+- union accounting;
+- interval merging;
+- Collatz convergence.
+
+Recovered budgets remain pair-local.  Overlap remains an adjacent obstruction
+on the enclosing list.
+
+## Verification
+
+Builds completed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureAccounting
+lake build DkMath.Collatz.PetalBridge.PressureFrontier
+lake build DkMath.Collatz.PetalBridge
+```
+
+No-sorry checks completed for:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+```
+
+Whitespace check completed:
+
+```text
+git diff --check
+```
+
+The build still reports the existing unrelated warning:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
````
`````
