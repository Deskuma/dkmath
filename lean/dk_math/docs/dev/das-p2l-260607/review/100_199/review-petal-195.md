# Git diff / Report / Review

## Add: docs: report 194

gch: daf89020c3b007f3d3ed96fca66368cdf02f62b8

## Report

cp194 を閉じました。

今回は設計確認のみで、Lean ソース変更はありません。既存 API を確認した結果、`failure + noAdjacentOverlap -> recovered diagnostic` の橋はすでに `PressureAdjacentDiagnosis.lean` にあり、固定長 2〜5 の pair-cases consumer は `PressureDiagnosticDecomposition.lean` に揃っていました。重複する wrapper theorem は追加していません。

追加した成果物:

- `lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-194.md`

確認:

- 指定された `lake build` 6本は通過
- 指定4ファイルの no-sorry check は一致なし
- `git diff --check` 通過
- 既知の unrelated warning: `ZsigmondyCyclotomicResearch.lean` の `sorry`

現在の差分は cp194 レポートのみです。

## Review

## 結論

うむ、Checkpoint 194 は **採用** じゃ 👍️
今回は **design-only / report-only checkpoint** として正しい。

確認された要点は、

```text id="rqfew2"
failure + noAdjacentOverlap -> recovered diagnostic
```

の橋はすでに `PressureAdjacentDiagnosis.lean` にあり、固定長 2〜5 の pair-cases consumer API も `PressureDiagnosticDecomposition.lean` に揃っている、ということじゃ。したがって、重複 wrapper theorem を追加しなかった判断は妥当。Lean ソース変更なし、差分は `report-petal-194.md` のみ。

## 実装レビュー

## 1. 既存 bridge chain の確認が良い

今回の report で、層の道筋が明確になった。

```text id="7xay2e"
sorted-before failure
  -> recovered pair OR adjacent-overlap obstruction

sorted-before failure + no-adjacent-overlap
  -> recovered pair

sorted-before failure + no-adjacent-overlap
  -> recovered adjacent accounted-family diagnostic
```

この橋はすでに既存 API として存在している。
ここにさらに同じ意味の theorem を足すと、名前だけ違う重複が増える。今回それを避けたのは良い。

## 2. 層の区別がかなり整理された

report で整理された三層は重要じゃ。

```text id="vwm1de"
Adjacent Diagnosis:
  recovered OR overlap

No-overlap:
  overlap branch を除去する branch-cut

Recovered Pair-Local Accounting:
  one explicit adjacent pair with one accounted family
```

この区別が曖昧だと、`hasAdjacentDiagnosis` をそのまま recovered accounting と誤読しやすい。
今回の設計確認で、それを防げている。

## 3. pair-cases API の現在の使いどころも明確

固定長 2〜5 については、consumer はすでに次を使える。

```lean id="jpamvk"
sourcePressureLocalIslandWitnessList_failure_two_pairDiagnostic_cases_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_three_pairDiagnostic_cases_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_four_pairDiagnostic_cases_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_cases_of_noAdjacentOverlap
```

これらは、

```text id="qx55ac"
fixed list length
sorted-before failure
no-adjacent-overlap
```

を持つ caller に対して、explicit adjacent pair diagnostics の有限分岐を返す。
現在の fixed-window consumer surface としては十分じゃ。

## 数学的意味

今回の checkpoint は、証明力を増やしたというより、

```text id="hdbhi7"
どの仮定で、どの層へ進めるか
```

を明確にした。

特に重要なのは、

```text id="7u1vpf"
Adjacent diagnosis は recovered と overlap の分岐を含む。
Recovered accounting へ進むには no-overlap が必要。
```

という点じゃ。

つまり、現在の構図はこう。

```text id="fr6x81"
failure:
  局所破綻

adjacent diagnosis:
  recovered / overlap の分岐検出

no-overlap:
  overlap 分岐の切断

pair-local accounting:
  recovered pair の負会計
```

これが明文化されたので、次に theorem を足すときも、どの層にいるのかを間違えにくい。

## 注意点

## 1. まだ overlap repair ではない

`noAdjacentOverlap` は overlap を修復するものではなく、単にその branch を除外する仮定じゃ。

したがって、次はまだ言えない。

```text id="kian0c"
overlap があっても recovered できる
overlap を分解して修復できる
overlap を union accounting に吸収できる
```

ここは未到達。

## 2. fixed pair-cases と general existential は別物

固定長 2〜5 の pair-cases はかなり便利だが、任意 list の分解ではない。

一方で、既存の recovered diagnostic carrier は任意 list に対して「どこかに recovered pair がある」ことを保持している。

ここから次に進むなら、任意 list を列挙するのではなく、

```text id="yvqwp5"
diagnostic carrier から named pair diagnostic を存在として取り出す
```

薄い projection がちょうどよい。

## 次の checkpoint 方針

次は **named pairDiagnostic existential projection** を推す。

目的は、新しい数学的主張を増やすことではなく、cp189 で作った

```lean id="qaqkcf"
SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
```

を、任意 list の diagnostic carrier から直接取り出せるようにすることじゃ。

今ある diagnostic carrier は、すでに

```text id="ugx1qq"
A B
AdjacentPairInList L A B
hrev : B before A
budget ≤ -2
sum < 0
length = 2
```

を持っている。
これを named pair predicate として再包装するだけ。

これは arbitrary-list decomposition ではない。
「全部列挙する」でも「最初を選ぶ」でもない。
単に carrier が保持している一つの pair を、名前付き predicate で取り出す projection じゃ。

## 次の Codex 指示

```text id="jc17au"
Checkpoint 195: Main root only — named pairDiagnostic existential projection from recovered diagnostic carrier.

Scope:
Work in the Collatz/PetalBridge pressure diagnostic decomposition layer.

Primary target file:
- DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean

Allowed supporting file only if absolutely necessary:
- DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean

Do not modify:
- PressureAccounting.lean
- PressureLocalWitnessObstruction.lean
- PressureFrontier.lean
- OneCycle.lean
- ValuationFlowBridge.lean
- ABC files
- NumberTheory files

Context:
Checkpoint 194 confirmed that the bridge chain already exists:

  sorted-before failure
    -> recovered pair OR adjacent-overlap obstruction

  sorted-before failure + no-adjacent-overlap
    -> recovered adjacent accounted-family diagnostic

and that fixed length 2 through 5 pair-cases consumers already exist in
`PressureDiagnosticDecomposition.lean`.

Checkpoint 189 introduced the named pair-local predicate:

  SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic

Main goal:
Add a small projection that extracts a named pair-local diagnostic from a
list-level recovered diagnostic carrier.

This should not add any new mathematical strength.  It only repackages the
existing witness stored inside the carrier using the named pair-local predicate.

Part A: projection from recovered diagnostic carrier.

In `PressureDiagnosticDecomposition.lean`, prove:

  theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_pairDiagnostic
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h :
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic L) :
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic A B

Suggested proof:
- use `h.exists_pair`;
- unpack `A B hin hrev hbudget hneg hlen`;
- return `A, B, hin`;
- package the named pair predicate with `⟨hrev, hbudget, hneg, hlen⟩`.

Part B: failure + noAdjacentOverlap existential named pairDiagnostic.

Prove:

  theorem sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
      (hno :
        SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L) :
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic A B

Suggested proof:
- obtain recovered diagnostic via:
  `sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap h hno`
- apply `.exists_pairDiagnostic`.

Part C: raw no-overlap compatibility wrapper.

If easy, also prove:

  theorem sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_no_overlap
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
      (hno :
        ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic A B

Suggested proof:
- use existing raw version:
  `sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_no_overlap h hno`
- apply `.exists_pairDiagnostic`.

Part D: optional bridge to fixed pair-cases.

Do not add new fixed length pair-cases unless needed.
The existing fixed length 2 through 5 consumer theorems are already the sharper
bounded finite-disjunction API.

Part E: guardrails.

Do not add:
- length-six decomposition;
- arbitrary-list decomposition;
- arbitrary-list recursion;
- canonical first diagnosis for arbitrary lists;
- enumeration of all diagnostics;
- aggregation over multiple recovered diagnostics;
- list-wide interval union accounting;
- coverage;
- maximality;
- uniqueness for arbitrary lists;
- sorting theorems;
- overlap repair;
- disjointness between multiple recovered families;
- Collatz convergence.

This checkpoint is only an existential projection from an already recovered
diagnostic carrier to the named pair-local predicate.

Part F: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-195.md

Include:
- the new `.exists_pairDiagnostic` projection;
- the named noAdjacentOverlap consumer theorem;
- raw no-overlap compatibility wrapper if added;
- explicit note that this does not enumerate diagnostics, choose a canonical
  pair, aggregate families, repair overlap, or prove coverage;
- explicit note that the theorem only repackages the already stored recovered
  diagnostic witness using the named pair-local predicate;
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

cp194 は良い停止判断じゃ。

ここで明確になったのは、

```text id="7pfckd"
既存 bridge は足りている。
足りないのは重複 wrapper ではなく、
named pairDiagnostic を任意 list の recovered carrier から取り出す薄い projection。
```

ということじゃな。

次はこの projection を入れると、fixed-length consumer と arbitrary-list existential consumer の両方が揃う。
それでもまだ、任意長の列挙・正準選択・合算には踏み込まない。

## Diff

`````md
````diff
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-194.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-194.md
new file mode 100644
index 00000000..6eada933
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-194.md
@@ -0,0 +1,230 @@
+# Report Petal 194
+
+## Checkpoint
+
+Checkpoint 194 reviewed the bridge policy between the adjacent-diagnosis layer
+and the recovered pair-cases layer.
+
+This was a design-only checkpoint.  No Lean source theorem was added.
+
+Primary inspected files:
+
+- `DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean`
+- `DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean`
+- `DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean`
+- `DkMath/Collatz/PetalBridge/PressureAccounting.lean`
+- `DkMath/Collatz/PetalBridge/PressureFrontier.lean`
+
+## Searched Declarations
+
+Searched for:
+
+```text
+sourcePressureLocalIslandWitnessList_failure_exists_recovered_or_overlap
+sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_noAdjacentOverlap
+sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
+SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
+SourcePressureLocalIslandWitnessAdjacentDiagnosis
+SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
+SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+```
+
+## Existing Bridge Chain
+
+The clean bridge already exists in `PressureAdjacentDiagnosis.lean`.
+
+The layer path is:
+
+```text
+sorted-before failure
+  -> recovered pair OR adjacent-overlap obstruction
+
+sorted-before failure + no-adjacent-overlap
+  -> recovered pair
+
+sorted-before failure + no-adjacent-overlap
+  -> recovered adjacent accounted-family diagnostic
+```
+
+The key declarations are:
+
+```lean
+theorem sourcePressureLocalIslandWitnessList_failure_exists_recovered_or_overlap
+theorem sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_noAdjacentOverlap
+theorem sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
+```
+
+This is already the exact branch-cut policy needed to move from adjacent
+diagnosis to recovered pair-local accounting.
+
+## Layer Distinction
+
+### Adjacent Diagnosis
+
+The adjacent-diagnosis layer is represented by:
+
+```lean
+def SourcePressureLocalIslandWitnessAdjacentDiagnosis
+def SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
+```
+
+This layer says that an adjacent pair in the explicit list has a local
+diagnosis.  The diagnosis may be:
+
+```text
+recovered pair-local budget evidence
+or adjacent-overlap obstruction
+```
+
+It does not require no-overlap.  Therefore it is intentionally weaker and more
+branch-aware than recovered accounting.
+
+### Overlap Obstruction
+
+The overlap branch is represented by:
+
+```lean
+def SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+def SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
+```
+
+The named no-overlap predicate is a thin wrapper around negating the adjacent
+overlap obstruction.  It is not a global coverage, maximality, sortedness, or
+repair statement.  It only removes the obstruction branch for the explicit
+list under discussion.
+
+### Recovered Pair-Local Accounting
+
+The recovered-accounting layer is represented by:
+
+```lean
+def SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+def SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+```
+
+This layer stores one recovered adjacent pair, its reversed-before witness, a
+pair-local accounted interval family, budget evidence, strict negativity, and
+length-two structure.
+
+It remains pair-local.  It does not aggregate multiple recovered pairs or
+produce a list-wide union.
+
+## Bounded Pair-Cases Surface
+
+The fixed-window consumer API is already present in
+`PressureDiagnosticDecomposition.lean`.
+
+For lengths two through five, the consumer can use:
+
+```lean
+theorem sourcePressureLocalIslandWitnessList_failure_two_pairDiagnostic_cases_of_noAdjacentOverlap
+theorem sourcePressureLocalIslandWitnessList_failure_three_pairDiagnostic_cases_of_noAdjacentOverlap
+theorem sourcePressureLocalIslandWitnessList_failure_four_pairDiagnostic_cases_of_noAdjacentOverlap
+theorem sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_cases_of_noAdjacentOverlap
+```
+
+These theorems are the correct current bridge endpoint when the caller has:
+
+```text
+fixed list length
++ sorted-before failure
++ no-adjacent-overlap
+```
+
+They expose the recovered branch as a finite disjunction of explicit adjacent
+pair diagnostics.
+
+## No New Wrapper Added
+
+No additional bridge theorem was added.
+
+Reason:
+
+- `failure + noAdjacentOverlap -> recovered diagnostic` already exists.
+- fixed length two through five pair-cases already exist.
+- adding a name such as a length-five recovered-pair-cases bridge would only
+  duplicate
+  `sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_cases_of_noAdjacentOverlap`.
+
+The next theorem should be added only when a concrete downstream proof needs a
+specific consumer shape that is not already covered by the existing API.
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
+The distinction remains:
+
+```text
+adjacent diagnosis:
+  recovered OR overlap
+
+no-overlap:
+  removes the overlap branch
+
+recovered pair-local accounting:
+  one explicit adjacent pair with one accounted family
+```
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
+The bridge design is now explicit enough to guide the next implementation.
+
+The next safe move should be consumer-driven:
+
+- if a downstream proof has no-overlap, use the bounded pair-cases API;
+- if it only has adjacent diagnosis, keep the recovered-or-overlap branch;
+- if it needs recovered accounting, make the no-overlap branch-cut explicit.
+
+Do not add length six or arbitrary-list machinery until a concrete downstream
+proof needs it.
````
`````
