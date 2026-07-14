# Git diff / Report / Review

## Add: docs: report 193

gch: e3e040fc404358312c2e431c4cc233bffc10af44

## Report

cp193 を閉じました。

今回は監査のみです。指定5ファイルを検索し、bounded pair-cases API を既存下流証明へ statement-preserving に置換できる箇所は見つかりませんでした。`PressureAdjacentDiagnosis.lean` 側には固定長の `hasAdjacentDiagnosis` 系がありますが、仮定・結論が今回の recovered pair-local API と違うため、無理に差し替えない判断にしています。

追加した成果物:

- `lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-193.md`

確認:

- 指定された `lake build` 6本は通過
- 指定4ファイルの no-sorry check は一致なし
- `git diff --check` 通過
- 既知の unrelated warning: `ZsigmondyCyclotomicResearch.lean` の `sorry`

Lean ソース変更はありません。現在の差分は cp193 レポートのみです。

## Review

## 結論

うむ、Checkpoint 193 は **採用** じゃ 👍️
今回は **audit-only** として正しい判断になっている。

指定 5 ファイルを調べたうえで、bounded pair-cases API を既存 downstream theorem に **statement-preserving** に置換できる箇所は見つからなかった、という結論じゃな。Lean ソース変更なし、追加は `report-petal-193.md` のみ。これはよい。

## 実装レビュー

## 1. 無理に置換しなかったのが正しい

特に重要なのはここじゃ。

既存の fixed-length theorem 群、

```lean id="1t3p28"
sourcePressureLocalIslandWitnessList_failure_three_hasAdjacentDiagnosis
sourcePressureLocalIslandWitnessList_failure_four_hasAdjacentDiagnosis
sourcePressureLocalIslandWitnessList_failure_five_hasAdjacentDiagnosis
```

は、`hasAdjacentDiagnosis` を返す層。

一方で、今回整えた API は、

```lean id="yet1jy"
SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
```

を返す recovered pair-local accounting 層。

この二つは似ているが、同じ層ではない。

置換しようとすると、

```text id="kjd85g"
noAdjacentOverlap 仮定を追加する
結論を変える
diagnosis 生成層から recovered accounting 層へ飛ぶ
```

のどれかが必要になる。
それは statement-preserving refactor ではない。

ここで止まった判断はとても良い。

## 2. bounded pair-cases API の現在位置が明確になった

今回の監査で、API の利用形がはっきりした。

今の consumer-friendly な形は、

```lean id="whngus"
sourcePressureLocalIslandWitnessList_failure_two_pairDiagnostic_cases_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_three_pairDiagnostic_cases_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_four_pairDiagnostic_cases_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_cases_of_noAdjacentOverlap
```

じゃ。

つまり、自然な呼び出し条件は、

```text id="nru2mo"
fixed list length 2..5
sorted-before failure
noAdjacentOverlap
```

そして結論は、

```text id="0sw8lk"
その固定窓内のどれかの adjacent pair が
pair-local recovered diagnostic を持つ
```

となる。

これはかなり明瞭じゃ。

## 3. report-only checkpoint として意味がある

Lean ソース変更がない checkpoint は、場合によっては弱く見える。
だが今回は違う。

ここでは、

```text id="9i8crz"
使える API がある
しかし既存 theorem の statement を壊さずには差し替えられない
```

という境界が確認された。

これは重要な設計情報じゃ。
「ここはまだ bridge が足りない」と分かった。

## 数学的意味

今回見えた構造はこうじゃ。

```text id="fpzdgs"
hasAdjacentDiagnosis 層:
  failure から adjacent diagnosis が出る

recovered pairDiagnostic 層:
  failure + noAdjacentOverlap から recovered pair-local accounting が出る
```

つまり、現在の差は、

```text id="ujd2pf"
overlap branch をどう扱うか
```

にある。

`hasAdjacentDiagnosis` はまだ「診断がある」段階。
`pairDiagnostic` は「overlap branch を排除して recovered accounting に落ちた」段階。

ここを混ぜると過大主張になる。
だから今回の audit-only は正しい。

## 次の checkpoint 方針

次は、いきなり length-six ではなく、**層の橋を設計する checkpoint** が良い。

狙いは、

```text id="ca6qgl"
hasAdjacentDiagnosis / adjacent diagnosis
から
recovered pairDiagnostic
へ行くには、どの仮定が必要か
```

を明示することじゃ。

特に候補は、

```text id="2i6vxv"
fixed length 3..5
hasAdjacentDiagnosis
noAdjacentOverlap
  -> pairDiagnostic cases
```

ではなく、まずは既存の `failure + noAdjacentOverlap` theorem との関係を整理する。

より安全な次手は、**ドキュメント + 小さな bridge naming theorem** じゃな。

## 次の Codex 指示

```text id="x4493h"
Checkpoint 194: Bridge design only — relate adjacent-diagnosis layer and recovered pair-cases layer without changing existing theorem strength.

Scope:
Work in the Collatz/PetalBridge pressure diagnostic area.

Primary files to inspect:
- DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
- DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
- DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
- DkMath/Collatz/PetalBridge/PressureAccounting.lean
- DkMath/Collatz/PetalBridge/PressureFrontier.lean

Preferred target file for any small theorem:
- DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean

Do not modify:
- OneCycle.lean
- ValuationFlowBridge.lean
- ABC files
- NumberTheory files

Context:
Checkpoint 193 audited downstream uses of the bounded pair-cases API and found
no statement-preserving replacement.

The important layer distinction is:

1. Existing fixed-length `hasAdjacentDiagnosis` theorems:
   - produce `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis`;
   - do not assume no-adjacent-overlap;
   - remain at the adjacent-diagnosis layer.

2. New bounded pair-cases theorems:
   - require sorted-before failure plus no-adjacent-overlap;
   - produce `SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic`;
   - live at the recovered pair-local accounting layer.

Main goal:
Do not add length-six.
Do not force a downstream replacement.
Instead, clarify the bridge policy between the adjacent-diagnosis layer and the
recovered pair-cases layer.

Part A: inspect existing bridge theorems.

Search for the following declarations and nearby APIs:

- sourcePressureLocalIslandWitnessList_failure_exists_recovered_or_overlap
- sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_noAdjacentOverlap
- sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
- SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
- SourcePressureLocalIslandWitnessAdjacentDiagnosis
- SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
- SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic

Determine whether there is already a clean theorem stating:

  failure + noAdjacentOverlap
    -> recovered diagnostic

and whether the bounded pair-cases API is already the best consumer surface for
fixed lengths.

Part B: if a genuinely useful naming bridge is missing.

Add at most one small wrapper theorem in `PressureDiagnosticDecomposition.lean`
or `PressureAdjacentDiagnosis.lean`.

The wrapper should not strengthen any result.  It should only give a clearer
name to an existing path.

Candidate shape, only if not already present in equivalent form:

  theorem sourcePressureLocalIslandWitnessList_failure_recoveredPairCases_of_noAdjacentOverlap_len_five
      ...
      : finite pairDiagnostic cases ...

But avoid adding this if it duplicates the existing:
  sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_cases_of_noAdjacentOverlap

Part C: if no small non-duplicative theorem is justified.

Make no Lean source changes.
Create a design report only.

The report should state:
- the adjacent-diagnosis layer and recovered-accounting layer are intentionally distinct;
- no-overlap is the extra branch-cut hypothesis needed to move to recovered accounting;
- existing bounded pair-cases theorems are already the correct fixed-window consumer API;
- no source theorem should be added until a concrete downstream proof needs it.

Part D: optional documentation note.

If useful, add a short documentation-only note:

  docs/dev/das-p2l-260607/review/report-petal-194.md

or, if the repository has a pressure design docs location, use the existing
review report location only.

Part E: do not introduce new mathematical strength.

Do not add:
- length-six decomposition;
- arbitrary-list decomposition;
- arbitrary-list recursion;
- aggregation over multiple recovered diagnostics;
- list-wide interval union accounting;
- coverage;
- maximality;
- uniqueness for arbitrary lists;
- sorting theorems;
- canonical first diagnosis for arbitrary lists;
- diagnostic enumeration beyond fixed finite disjunctions;
- overlap repair;
- disjointness between multiple recovered families;
- Collatz convergence.

Part F: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-194.md

Include:
- searched declarations;
- whether an additional bridge theorem was added;
- if no theorem was added, explain why existing APIs are sufficient;
- the precise distinction between:
  - adjacent diagnosis;
  - overlap obstruction;
  - recovered pair-local accounting;
- explicit note that no length-six, arbitrary-list decomposition, aggregation,
  union accounting, coverage, maximality, uniqueness for arbitrary lists,
  sorting, canonical first diagnosis for arbitrary lists, enumeration beyond
  fixed finite disjunctions, overlap repair, or Collatz convergence was introduced;
- verification results.

Verification:

  lake build DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
  lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
  lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
  lake build DkMath.Collatz.PetalBridge.PressureAccounting
  lake build DkMath.Collatz.PetalBridge.PressureFrontier
  lake build DkMath.Collatz.PetalBridge

Run no-sorry checks:

  rg -n "\\bsorry\\b" \
    DkMath/Collatz/PetalBridge/PressureAccounting.lean \
    DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
    DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
    DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean

Also run:

  git diff --check
```

## 総評

cp193 は地味だが大事じゃ。

「どこにも使えなかった」のではなく、

```text id="qmgwf9"
今の API は recovered accounting 層であり、
既存 downstream theorem は adjacent diagnosis 層にある
```

と分かった。

この差は、まさに overlap branch の扱いの差じゃ。
次はこの層構造を明文化するのがよい。
焦って length-six へ進むより、橋の設計を固める方が強い。

## Diff

`````md
````diff
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-193.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-193.md
new file mode 100644
index 00000000..77e1b095
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-193.md
@@ -0,0 +1,194 @@
+# Report Petal 193
+
+## Checkpoint
+
+Checkpoint 193 audited the first downstream use site for the bounded
+pair-cases API added in checkpoints 191 and 192.
+
+This was an audit-only checkpoint.  No Lean source change was made for cp193.
+
+Primary inspected files:
+
+- `DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean`
+- `DkMath/Collatz/PetalBridge/PressureFrontier.lean`
+- `DkMath/Collatz/PetalBridge/PressureAccounting.lean`
+- `DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean`
+- `DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean`
+
+## Search Patterns
+
+Searched for:
+
+```text
+SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
+sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
+sourcePressureLocalIslandWitnessList_failure_three_diagnostic_head_or_tail_of_noAdjacentOverlap
+sourcePressureLocalIslandWitnessList_failure_four_diagnostic_head_or_tail_of_noAdjacentOverlap
+sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_or_tail_of_noAdjacentOverlap
+HasAdjacentDiagnosis
+RecoveredAdjacentAccountedFamilyDiagnostic
+```
+
+Also checked whether the compact bounded API was already used outside
+`PressureDiagnosticDecomposition.lean`:
+
+```text
+three_iff_pairDiagnostic_cases
+four_iff_pairDiagnostic_cases
+five_iff_pairDiagnostic_cases
+sourcePressureLocalIslandWitnessList_failure_two_pairDiagnostic_cases_of_noAdjacentOverlap
+sourcePressureLocalIslandWitnessList_failure_three_pairDiagnostic_cases_of_noAdjacentOverlap
+sourcePressureLocalIslandWitnessList_failure_four_pairDiagnostic_cases_of_noAdjacentOverlap
+sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_cases_of_noAdjacentOverlap
+```
+
+## Audit Result
+
+No direct downstream proof replacement was found.
+
+The compact pair-cases API currently appears only in
+`PressureDiagnosticDecomposition.lean`.  The other inspected modules provide
+earlier layers:
+
+- `PressureAccounting.lean`: interval-family and pair-local accounting tools;
+- `PressureLocalWitnessObstruction.lean`: sorted-before failure and local
+  obstruction tools;
+- `PressureAdjacentDiagnosis.lean`: adjacent diagnosis, no-overlap, and
+  recovered accounted-family carriers;
+- `PressureFrontier.lean`: pressure frontier layer.
+
+The most relevant downstream-looking fixed-length theorems are in
+`PressureAdjacentDiagnosis.lean`, for example:
+
+```lean
+theorem sourcePressureLocalIslandWitnessList_failure_three_hasAdjacentDiagnosis
+theorem sourcePressureLocalIslandWitnessList_failure_four_hasAdjacentDiagnosis
+theorem sourcePressureLocalIslandWitnessList_failure_five_hasAdjacentDiagnosis
+```
+
+However, these theorems produce `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis`
+from positive length assumptions and sorted-before failure.  They do not assume
+`SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction`, and
+their conclusion is a diagnosis carrier, not the recovered pair-local
+accounted-family diagnostic exposed by the compact pair-cases API.
+
+Therefore replacing their internals with the new pair-cases API would either:
+
+- add a new no-adjacent-overlap assumption;
+- change the theorem's conclusion;
+- or move across layer boundaries from diagnosis generation to recovered
+  accounted-family decomposition.
+
+That would not be a statement-preserving refactor.
+
+## API Readiness
+
+The current bounded pair-cases API is ready for future concrete consumers.
+
+The most useful future caller shape is expected to be:
+
+```text
+fixed list length 2..5
++ sorted-before failure
++ no-adjacent-overlap
+-> explicit adjacent pair-local recovered accounted-family diagnostic
+```
+
+That caller can now use one of:
+
+```lean
+sourcePressureLocalIslandWitnessList_failure_two_pairDiagnostic_cases_of_noAdjacentOverlap
+sourcePressureLocalIslandWitnessList_failure_three_pairDiagnostic_cases_of_noAdjacentOverlap
+sourcePressureLocalIslandWitnessList_failure_four_pairDiagnostic_cases_of_noAdjacentOverlap
+sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_cases_of_noAdjacentOverlap
+```
+
+No extra wrapper was added because the existing length-five theorem is already
+the consumer-friendly form requested by the checkpoint.
+
+## Guardrails
+
+This checkpoint introduced no new mathematical strength.
+
+It did not introduce:
+
+- length-six decomposition;
+- arbitrary-list decomposition;
+- arbitrary-list recursion;
+- aggregation over multiple recovered diagnostics;
+- list-wide interval union accounting;
+- coverage;
+- maximality;
+- uniqueness for arbitrary lists;
+- sorting theorems;
+- canonical first diagnosis for arbitrary lists;
+- diagnostic enumeration beyond fixed finite disjunctions;
+- overlap repair;
+- disjointness between multiple recovered families;
+- Collatz convergence.
+
+The audit preserves the current policy: bounded pair-cases are explicit
+finite windows only, and recovered budgets remain pair-local.
+
+## File Size Watch
+
+Line counts at the audit point:
+
+```text
+  1027 lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
+  1356 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+  1391 lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
+  1896 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+  1517 lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+  7187 total
+```
+
+No file crossed the 2,000-line split threshold during this checkpoint.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
+lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
+lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
+lake build DkMath.Collatz.PetalBridge.PressureAccounting
+lake build DkMath.Collatz.PetalBridge.PressureFrontier
+lake build DkMath.Collatz.PetalBridge
+```
+
+No-sorry check over the requested pressure files produced no matches:
+
+```text
+rg -n "\bsorry\b" \
+  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
+  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
+  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
+  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
+```
+
+Known unrelated warning still appears during builds:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+That warning is outside this checkpoint and was not modified.
+
+## Next Inference
+
+The next implementation should remain consumer-driven.
+
+Good candidates are:
+
+- a concrete theorem in a later pressure module that already has both
+  sorted-before failure and no-adjacent-overlap hypotheses;
+- a fixed-size recovered-accounting consumer for length five or smaller;
+- or a new small theorem that explicitly states the missing bridge between
+  adjacent diagnosis and recovered accounted-family diagnostics, if the extra
+  no-overlap branch is already naturally available.
+
+Do not add length six until an actual downstream caller asks for it.
````
`````
