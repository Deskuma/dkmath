# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition

gch: 8ee19cd2602aa3355b0b42706676ccd766ad99d2

## Report

cp195 を閉じました。

実装:

- `SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_pairDiagnostic`
- `sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap`
- `sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_no_overlap`

どれも既存 carrier に格納済みの recovered diagnostic witness を named pair-local predicate に詰め直すだけです。任意リスト分解、列挙、正準選択、集約、coverage、overlap repair、Collatz convergence には踏み込んでいません。

追加レポート:

- `lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-195.md`

確認:

- 指定された `lake build` 6本は通過
- 指定4ファイルの no-sorry check は一致なし
- `git diff --check` 通過
- 既知の unrelated warning: `ZsigmondyCyclotomicResearch.lean` の `sorry`

変更ファイルは `PressureDiagnosticDecomposition.lean` と cp195 レポートです。

## Review

## 結論

うむ、Checkpoint 195 は **採用** じゃ 👍️
これは狙い通りの **薄い projection checkpoint** になっている。

追加された中心は、

```lean id="gss1wc"
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_pairDiagnostic
sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_no_overlap
```

じゃな。どれも既存 carrier に格納済みの recovered diagnostic witness を、cp189 で導入した named pair-local predicate に詰め直しているだけで、任意リスト分解・列挙・正準選択・集約・coverage・overlap repair・Collatz convergence には踏み込んでいない。境界管理は良い。

## 実装レビュー

## 1. `.exists_pairDiagnostic` はちょうど欲しかった projection

今回の主役はこれじゃ。

```lean id="br3nas"
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_pairDiagnostic
```

これは list-level recovered diagnostic carrier から、

```lean id="m3zsky"
∃ A B,
  SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic A B
```

を取り出す。

意味としては、

```text id="wwhj64"
この list のどこかの隣接 pair が、
named pair-local recovered diagnostic を持つ
```

じゃ。

これは任意長 list を「分解」しているわけではない。
carrier がすでに持っていた一つの pair witness を、名前付き predicate として露出しただけじゃ。

この薄さが良い。

## 2. noAdjacentOverlap consumer も自然

```lean id="erlskh"
sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
```

により、

```text id="fgb8v9"
sorted-before failure
noAdjacentOverlap
```

から、任意 list 内のどこかに named pairDiagnostic があることを直接得られる。

固定長 2〜5 では finite disjunction の pair-cases API がある。
一方、任意 list では列挙せずに existential に留める。
この切り分けがかなり綺麗じゃ。

## 3. raw no-overlap compatibility wrapper も妥当

```lean id="g9ti7x"
sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_no_overlap
```

は、古い raw negation 形式、

```lean id="lln0kw"
¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
```

から同じ結論へ行く wrapper じゃな。

既存コードの移行や互換性を考えると、これはあってよい。
ただし今後の主 API は named predicate の `SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction` 側を優先するのが良い。

## 数学的意味

今回で、任意 list 側の recovered accounting surface がこう読めるようになった。

```text id="zt9bvd"
failure + noAdjacentOverlap
  -> some adjacent pair in L has pair-local recovered accounting
```

固定長では、

```text id="iem5q9"
which pair?
```

まで finite disjunction で出す。

任意長では、

```text id="gj7eoh"
some pair exists
```

に留める。

これは強さの配分として正しい。
任意長でいきなり全列挙・最初の pair・合算へ進まないので、過大主張になっていない。

## 注意点

## 1. まだ branch split の named 版はない

cp195 で得たのは、

```text id="zatjhj"
noOverlap を仮定した後の recovered pairDiagnostic extraction
```

じゃ。

しかし、noOverlap を仮定する前の自然な分岐、

```text id="0m48ql"
failure
  -> pairDiagnostic exists OR adjacentOverlap obstruction
```

は、named pairDiagnostic 版としてまだ整えていない。

既存の `failure_exists_recovered_or_overlap` はあるが、cp189 の named predicate へ寄せた consumer surface としては、次にここを揃えるのがよい。

## 2. 任意 list の「列挙」には行かない

今回の existential projection は安全じゃが、ここからすぐに、

```text id="00l641"
all pairDiagnostics in L
canonical first pair
pairDiagnostic count
sum over pairDiagnostics
```

へ行くのはまだ早い。

それをやるには、重複・隣接 overlap・family disjointness・coverage の設計が要る。

## 次の checkpoint 方針

次は **named branch split checkpoint** を推す。

目的は、既存の

```text id="x7h68w"
failure -> recovered OR overlap
```

を、cp189/cp195 の named pairDiagnostic surface に合わせて、

```text id="sklszk"
failure
  -> (exists adjacent pairDiagnostic)
     OR adjacentOverlap obstruction
```

として出すことじゃ。

これは新しい数学的主張ではなく、既存 branch theorem の API 整理。
noOverlap をまだ仮定していない段階の consumer surface を整える。

## 次の Codex 指示

```text id="w2pkn8"
Checkpoint 196: Main root only — named pairDiagnostic branch split before applying no-overlap.

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
Checkpoint 195 added the arbitrary-list existential projection:

  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_pairDiagnostic

and consumer wrappers:

  sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
  sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_no_overlap

These expose the named pair-local predicate:

  SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic

after the no-overlap branch has been cut.

Main goal:
Add a named pairDiagnostic branch-split theorem before applying no-overlap.

This should repackage the existing branch theorem:

  failure -> recovered OR adjacent-overlap obstruction

into the newer named surface:

  failure -> exists adjacent pairDiagnostic OR adjacent-overlap obstruction

Do not add new mathematical strength.

Part A: arbitrary-list named branch split.

Prove:

  theorem sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L) :
      (∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic A B) ∨
        SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L

Suggested proof:
- use existing:
  sourcePressureLocalIslandWitnessList_failure_exists_recovered_or_overlap
- recovered branch:
  obtain the existing recovered carrier or recovered pair witness.
  If it yields `SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic L`,
  apply `.exists_pairDiagnostic`.
  If it yields the older recovered adjacent accounted-family carrier, repackage it into the named predicate directly.
- overlap branch:
  return the overlap obstruction unchanged.

Part B: named no-overlap theorem can be reproved or left as-is.

Do not replace the existing cp195 theorem unless the proof becomes simpler.
If useful, add a short theorem alias showing that Part A plus named no-overlap yields Part B:

  theorem sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap_from_branchSplit
      ...

But avoid duplicate aliases unless they have clear naming value.

Part C: raw no-overlap version from branch split, optional.

The existing cp195 raw wrapper is already sufficient.
Do not add another raw wrapper unless it avoids proof duplication.

Part D: fixed-length branch split wrappers, optional and only if clearly useful.

Do not add fixed length 2 through 5 branch split wrappers in this checkpoint.
The fixed-length noOverlap pair-cases API already exists.
The new theorem should be the arbitrary-list existential branch split only.

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

This checkpoint only names the recovered side of the existing failure branch split
using the pair-local diagnostic predicate.

Part F: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-196.md

Include:
- the new named pairDiagnostic-or-overlap branch split theorem;
- how it was derived from the existing recovered-or-overlap bridge;
- explicit note that no-overlap is not assumed in this branch split;
- explicit note that overlap is not repaired, only exposed as the alternative branch;
- explicit note that this does not enumerate diagnostics, choose a canonical pair,
  aggregate families, prove coverage, or prove Collatz convergence;
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

cp195 は良い。
これで任意 list 側にも、named pairDiagnostic を取り出す existential consumer ができた。

固定長では finite pair-cases。
任意長では existential pairDiagnostic。
この棲み分けが整った。

次は noOverlap を仮定する前の branch split を named surface に揃えるとよい。これで、

```text id="0tdyyx"
failure
  -> pairDiagnostic exists OR overlap obstruction
```

が直接読めるようになる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
index 110cce1f..c35d44f6 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
@@ -65,6 +65,28 @@ theorem SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnosti
     sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length
       W1 W2 hrev⟩

+set_option linter.style.longLine false in
+/--
+Project the named pair-local recovered diagnostic from a list-level recovered
+diagnostic carrier.
+
+This only repackages the pair already stored in the carrier using the named
+pair-local predicate.  It does not enumerate diagnostics, choose a canonical
+pair, aggregate recovered families, repair overlap, or prove coverage.
+-/
+theorem
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_pairDiagnostic
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic L) :
+    ∃ A B,
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+        SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+          A B := by
+  rcases h.exists_pair with ⟨A, B, hin, hrev, hbudget, hneg, hlen⟩
+  exact ⟨A, B, hin, hrev, hbudget, hneg, hlen⟩
+
 /--
 In a two-element explicit witness list, the only adjacent-pair address is the
 head pair.
@@ -767,6 +789,54 @@ theorem
   (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
     h hno).exists_reversed_of_two

+set_option linter.style.longLine false in
+/--
+Failure plus named no-adjacent-overlap yields some named pair-local recovered
+diagnostic inside the explicit list.
+
+This is the arbitrary-list existential consumer surface corresponding to the
+fixed length-two through length-five pair-cases API.  It exposes one pair that
+is already stored in the recovered diagnostic carrier; it does not enumerate
+all recovered diagnostics or choose a canonical pair.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
+    (hno :
+      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L) :
+    ∃ A B,
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+        SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+          A B :=
+  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
+    h hno).exists_pairDiagnostic
+
+set_option linter.style.longLine false in
+/--
+Raw-negation compatibility wrapper for the named pair-local recovered
+diagnostic existential projection.
+
+This is the same result as the named no-adjacent-overlap theorem, with the
+older raw negation form of the no-overlap branch.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_no_overlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
+    (hno :
+      ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
+    ∃ A B,
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+        SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+          A B :=
+  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_no_overlap
+    h hno).exists_pairDiagnostic
+
 set_option linter.style.longLine false in
 /--
 Compact two-element consumer form using the named pair-local recovered branch.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-195.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-195.md
new file mode 100644
index 00000000..dad9f814
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-195.md
@@ -0,0 +1,209 @@
+# Report Petal 195
+
+## Checkpoint
+
+Checkpoint 195 added the main-root existential projection from a list-level
+recovered diagnostic carrier to the named pair-local recovered diagnostic
+predicate.
+
+Primary file:
+
+- `DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean`
+
+No supporting Lean file was modified.
+
+## Implemented
+
+### List carrier projection to named pair diagnostic
+
+Added:
+
+```lean
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_pairDiagnostic
+```
+
+Shape:
+
+```lean
+SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic L
+  ->
+∃ A B,
+  SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic A B
+```
+
+This theorem uses the existing `h.exists_pair` projection from the bundled
+list-level diagnostic carrier and repackages the stored fields:
+
+```text
+hin
+hrev
+hbudget
+hneg
+hlen
+```
+
+into the named pair-local predicate:
+
+```lean
+SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic A B
+```
+
+No new mathematical information is introduced.
+
+### Named noAdjacentOverlap consumer
+
+Added:
+
+```lean
+theorem sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
+```
+
+Shape:
+
+```lean
+SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L
+  ->
+SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L
+  ->
+∃ A B,
+  SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic A B
+```
+
+This composes the existing bridge:
+
+```lean
+sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
+```
+
+with the new `.exists_pairDiagnostic` projection.
+
+### Raw no-overlap compatibility wrapper
+
+Added:
+
+```lean
+theorem sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_no_overlap
+```
+
+This is the same existential named pair-diagnostic result, but for callers that
+still carry no-overlap as:
+
+```lean
+¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
+```
+
+It composes the existing raw bridge:
+
+```lean
+sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_no_overlap
+```
+
+with `.exists_pairDiagnostic`.
+
+## Meaning
+
+The checkpoint completes the thin arbitrary-list existential consumer surface:
+
+```text
+fixed length 2..5:
+  finite pair-cases disjunction API
+
+arbitrary explicit list:
+  existential named pairDiagnostic API
+```
+
+The arbitrary-list theorem is existential only.  It says that the already
+recovered carrier contains some adjacent pair whose pair-local recovered
+accounted-family diagnostic can be named directly.
+
+## Guardrails
+
+This checkpoint only repackages an already stored recovered diagnostic witness.
+
+It did not introduce:
+
+- length-six decomposition;
+- arbitrary-list decomposition;
+- arbitrary-list recursion;
+- canonical first diagnosis for arbitrary lists;
+- enumeration of all diagnostics;
+- aggregation over multiple recovered diagnostics;
+- list-wide interval union accounting;
+- coverage;
+- maximality;
+- uniqueness for arbitrary lists;
+- sorting theorems;
+- overlap repair;
+- disjointness between multiple recovered families;
+- Collatz convergence.
+
+In particular, the new existential theorem does not choose a canonical pair,
+does not enumerate diagnostics, does not aggregate families, does not repair
+overlap, and does not prove coverage.
+
+## File Size Watch
+
+Current line counts:
+
+```text
+  1097 lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
+  1356 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+  1391 lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
+  1896 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+  1517 lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+  7257 total
+```
+
+`PressureDiagnosticDecomposition.lean` remains below the 2,000-line split
+threshold.
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
+The pressure diagnostic layer now has two complementary consumer surfaces:
+
+```text
+bounded fixed windows:
+  explicit finite disjunction over adjacent pairs
+
+arbitrary explicit list:
+  existential named recovered pair diagnostic
+```
+
+The next safe move remains consumer-driven.  A later theorem can use the
+existential projection when it only needs one recovered pair-local diagnostic,
+while fixed small-window callers should continue to use the sharper pair-cases
+API.
````
`````
