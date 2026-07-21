# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis

gch: 1146a9d80e4523a2ec49fa98a08a40d3dc18fe40

## Report

cp187 完了です。

[PressureAdjacentDiagnosis.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean:332) に四要素リスト `[W1, W2, W3, W4]` 用の bounded head-or-tail 分解を追加しました。diagnostic carrier の `four_head_or_tail` / `four_iff_head_or_tail` と、failure + no-overlap から同じ分岐を得る consumer theorem も追加済みです。

レポート: [report-petal-187.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-187.md)

確認済み:
`lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis`
`lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction`
`lake build DkMath.Collatz.PetalBridge.PressureAccounting`
`lake build DkMath.Collatz.PetalBridge.PressureFrontier`
`lake build DkMath.Collatz.PetalBridge`
対象3ファイル no-sorry
`git diff --check`

`PressureAdjacentDiagnosis.lean` は 1750 行なので、今回は分割せずに維持しています。既知の `ZsigmondyCyclotomicResearch.lean` の warning は今回も無関係です。

## Review

## 結論

うむ、Checkpoint 187 は **採用** じゃ 👍️
四要素 list `[W1, W2, W3, W4]` に対する bounded head-or-tail decomposition が入り、length 2 / 3 / 4 の局所分解チェーンが揃った。

追加された中心は、

```lean id="92idfj"
SourcePressureLocalIslandWitnessAdjacentPairInList.four_head_or_tail
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_head_or_tail
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_iff_head_or_tail
sourcePressureLocalIslandWitnessList_failure_four_diagnostic_head_or_tail_of_noAdjacentOverlap
```

じゃな。主張は四要素の明示 list 限定で、任意 list の coverage、uniqueness、enumeration、union accounting、Collatz convergence には踏み込んでいない。`PressureAdjacentDiagnosis.lean` は 1750 行で、今回は分割せず維持したとのこと。ここも妥当じゃ。

## 実装レビュー

## 1. length-four decomposition は自然

今回の構造は、cp186 の length-three と完全に同じ型じゃ。

```text id="cvxgrv"
diagnostic [W1, W2, W3, W4]
  -> head pair W1,W2
     or diagnostic [W2,W3,W4]
```

これは bounded decomposition としてきれいじゃ。

長い list を勝手に探索しているのではなく、明示 list の head-or-tail を一段だけ開いている。
この安全な一段分解を積む方針は良い。

## 2. `four_iff_head_or_tail` も安定 API

forward で分解し、reverse で head case を直接構成、tail case を `of_tail` で持ち上げる。
既存の流れと揃っている。

```lean id="pfujvo"
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail
```

をうまく使えておるな。

## 3. failure + no-overlap consumer theorem も良い

```lean id="nixmvu"
sourcePressureLocalIslandWitnessList_failure_four_diagnostic_head_or_tail_of_noAdjacentOverlap
```

により、

```text id="yqawsl"
failure [W1,W2,W3,W4]
noAdjacentOverlap [W1,W2,W3,W4]
  -> head recovered branch
     or tail diagnostic [W2,W3,W4]
```

まで consumer-facing に読めるようになった。

これは下流で使いやすい。

## 数学的意味

これで bounded decomposition はこうなった。

```text id="4gp7jp"
length 2:
  diagnostic [W1,W2]
    ↔ W2 before W1

length 3:
  diagnostic [W1,W2,W3]
    ↔ head pair W1,W2
       or diagnostic [W2,W3]

length 4:
  diagnostic [W1,W2,W3,W4]
    ↔ head pair W1,W2
       or diagnostic [W2,W3,W4]
```

つまり、diagnostic は bounded list の中で、

```text id="jsuv9x"
head に現れるか、
tail に保存される
```

という構文保存則を持つようになった。

これは「回収可能な局所会計」が list のどこに埋もれていても、bounded decomposition で一段ずつ見える、という足場じゃ。

## 注意点

## 1. report の略記だけ注意

report 内でまた、

```lean id="dgb9yz"
sourcePressureAccountedIntervalFamilyOfPair W1 W2
```

という説明略記が出ているが、実 Lean 名は、

```lean id="pgt5iz"
sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
```

じゃな。

説明文としては読めるが、今後の report では実名に寄せた方がよい。

## 2. そろそろ分割検討

`PressureAdjacentDiagnosis.lean` が 1750 行まで来た。
まだ 2000 行未満ではあるが、length-five を足すと 1900 行に近づく可能性が高い。

ここから先は、length-five を足す前に、

```text id="elywfj"
bounded diagnostic decomposition
```

を別 module に逃がす方が安全じゃ。

## 次の checkpoint 方針

わっちは次は **length-five 追加ではなく、分割 checkpoint** を推す。

目的は、新理論を増やさず、

```text id="anl37b"
Diagnostic carrier 本体
bounded decomposition 補題
```

を分けることじゃ。

候補 module 名は、

```lean id="zf95ul"
DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
```

または短く、

```lean id="j2jhfq"
DkMath.Collatz.PetalBridge.PressureAdjacentDecomposition
```

じゃが、内容は diagnostic carrier の bounded decomposition なので、前者が分かりやすい。

## 次の Codex 指示

```text id="iu47cs"
Checkpoint 188: Refactor only — split bounded diagnostic decomposition helpers into a new module.

Scope:
Refactor the Collatz/PetalBridge pressure diagnostic modules without changing theorem statements or theorem meanings.

Primary source file:
- DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean

New target file:
- DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean

Public import update:
- DkMath/Collatz/PetalBridge.lean

Allowed supporting files:
- DkMath/Collatz/PetalBridge/PressureFrontier.lean only if it needs an import update
- DkMath/Collatz/PetalBridge.lean for public import update

Do not modify:
- PressureAccounting.lean, except no change is expected
- PressureLocalWitnessObstruction.lean, except no change is expected
- OneCycle.lean
- ValuationFlowBridge.lean
- ABC files
- NumberTheory files

Main goal:
Move bounded diagnostic decomposition helpers out of
`PressureAdjacentDiagnosis.lean` into a new module
`PressureDiagnosticDecomposition.lean`.

This is a refactor-only checkpoint.  Do not add new mathematical claims.

Move these declarations if dependency order permits:

Address-level bounded decomposition:
- SourcePressureLocalIslandWitnessAdjacentPairInList.two_iff_head
- SourcePressureLocalIslandWitnessAdjacentPairInList.two_eq
- SourcePressureLocalIslandWitnessAdjacentPairInList.three_head_or_tail
- SourcePressureLocalIslandWitnessAdjacentPairInList.four_head_or_tail

Diagnostic length-two normal form:
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_two_reversed
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_reversed_of_two
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.two_iff
- sourcePressureLocalIslandWitnessList_failure_two_exists_reversed_of_noAdjacentOverlap

Diagnostic length-three bounded decomposition:
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_head_or_tail
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_iff_head_or_tail
- sourcePressureLocalIslandWitnessList_failure_three_diagnostic_head_or_tail_of_noAdjacentOverlap

Diagnostic length-four bounded decomposition:
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_head_or_tail
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_iff_head_or_tail
- sourcePressureLocalIslandWitnessList_failure_four_diagnostic_head_or_tail_of_noAdjacentOverlap

Keep in `PressureAdjacentDiagnosis.lean`:
- core adjacent-pair-in-list constructors and general API;
- list-level adjacent diagnosis carrier;
- no-adjacent-overlap predicate;
- recovered adjacent accounted-family carrier;
- diagnostic carrier definition;
- diagnostic constructors/conversions/projections;
- nil/singleton false;
- tail lift helpers;
- failure + noAdjacentOverlap diagnostic carrier theorem;
- raw no-overlap compatibility wrappers.

Import plan:
1. Create:
   DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
2. The new module should import:
   DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
3. Move the bounded decomposition declarations into the new module.
4. Update the public umbrella import:
   DkMath/Collatz/PetalBridge.lean
   to import:
   DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
5. If any downstream pressure module expected those declarations through
   `PressureAdjacentDiagnosis`, update its imports explicitly.  Prefer importing
   the new module rather than re-exporting from `PressureAdjacentDiagnosis`.

Guardrails:
- Refactor only.
- Do not change theorem names.
- Do not change theorem statements.
- Do not strengthen or weaken any theorem.
- Do not add length-five decomposition in this checkpoint.
- Do not add arbitrary-list decomposition.
- Do not claim global local-island coverage.
- Do not claim maximality.
- Do not claim uniqueness for arbitrary lists.
- Do not claim prefix behavior.
- Do not claim arbitrary list sorting.
- Do not claim canonical first diagnosis for arbitrary lists.
- Do not enumerate all diagnostics.
- Do not claim union accounting.
- Do not claim overlap repair.
- Do not claim Collatz convergence.
- Do not aggregate multiple recovered pairs.
- Do not create a list-wide accounted interval union.

File-size goal:
After the split, aim for:
- PressureAdjacentDiagnosis.lean comfortably below its current 1750 lines;
- PressureDiagnosticDecomposition.lean containing the bounded two/three/four list helpers.

Report:
Create:

  docs/dev/das-p2l-260607/review/report-petal-188.md

Include:
- that this is refactor-only;
- new module name;
- declarations moved;
- imports updated;
- current line counts for:
  - PressureAdjacentDiagnosis.lean
  - PressureDiagnosticDecomposition.lean
  - PressureLocalWitnessObstruction.lean
  - PressureAccounting.lean
- explicit note that no new theorem strength was added;
- explicit note that no aggregation, union accounting, coverage, maximality,
  uniqueness for arbitrary lists, sorting, canonical first diagnosis for
  arbitrary lists, enumeration, overlap repair, or Collatz convergence was introduced;
- verification results.

Verification:

  lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
  lake build DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
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

cp187 は良い到達点じゃ。

bounded decomposition は、

```text id="y61j9o"
length 2
length 3
length 4
```

まで揃った。

ここでいったん足場を整理するのが賢い。
length-five に進む前に module を分ければ、以後の bounded decomposition を安心して伸ばせる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
index 3766fc44..c5782340 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
@@ -322,6 +322,21 @@ theorem SourcePressureLocalIslandWitnessAdjacentPairInList.three_head_or_tail
       SourcePressureLocalIslandWitnessAdjacentPairInList [W2, W3] A B :=
   h

+/--
+In a four-element explicit witness list, an adjacent-pair address is either
+the head pair or an adjacent-pair address in the three-element tail.
+
+This is a bounded four-element decomposition only.  It does not enumerate
+diagnostics in arbitrary lists.
+-/
+theorem SourcePressureLocalIslandWitnessAdjacentPairInList.four_head_or_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 W4 A B : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureLocalIslandWitnessAdjacentPairInList [W1, W2, W3, W4] A B) :
+    (A = W1 ∧ B = W2) ∨
+      SourcePressureLocalIslandWitnessAdjacentPairInList [W2, W3, W4] A B :=
+  h
+
 /--
 A list-level carrier for "some adjacent pair in this explicit list has an
 adjacent diagnosis".
@@ -1171,6 +1186,87 @@ theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyD
         SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail
           htail

+set_option linter.style.longLine false in
+/--
+Four-element bounded decomposition for the bundled diagnostic carrier.
+
+A diagnostic on `[W1, W2, W3, W4]` is either carried by the head pair `W1, W2`,
+or it is already a diagnostic on the three-element tail `[W2, W3, W4]`.
+This theorem only decomposes the explicit four-element list; it does not
+enumerate diagnostics in arbitrary lists.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_head_or_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r}
+    (h :
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        [W1, W2, W3, W4]) :
+    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
+      let F :=
+        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+          W1 W2 hrev
+      (((F.items).map
+        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
+        (((F.items).map
+          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
+        F.items.length = 2)
+    ∨
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        [W2, W3, W4] := by
+  rcases h.exists_pair with ⟨A, B, hin, hrev, hbudget, hneg, hlen⟩
+  rcases SourcePressureLocalIslandWitnessAdjacentPairInList.four_head_or_tail
+      hin with hhead | htail
+  · rcases hhead with ⟨rfl, rfl⟩
+    exact Or.inl ⟨hrev, hbudget, hneg, hlen⟩
+  · exact Or.inr
+      (SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
+        htail hrev hbudget hneg hlen)
+
+set_option linter.style.longLine false in
+/--
+Iff form of the four-element diagnostic decomposition.
+
+The reverse direction either builds the head-pair diagnostic directly from the
+reversed witness, or lifts an existing tail diagnostic.  This is still bounded
+to `[W1, W2, W3, W4]`.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_iff_head_or_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r} :
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+      [W1, W2, W3, W4] ↔
+    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
+      let F :=
+        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+          W1 W2 hrev
+      (((F.items).map
+        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
+        (((F.items).map
+          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
+        F.items.length = 2)
+    ∨
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        [W2, W3, W4]) := by
+  constructor
+  · exact
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_head_or_tail
+  · intro h
+    rcases h with hhead | htail
+    · rcases hhead with ⟨hrev, _hbudget, _hneg, _hlen⟩
+      exact
+        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
+          SourcePressureLocalIslandWitnessAdjacentPairInList.head
+          hrev
+          (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two
+            W1 W2 hrev)
+          (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
+            W1 W2 hrev)
+          (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length
+            W1 W2 hrev)
+    · exact
+        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail
+          htail
+
 /--
 Expose the actual pair-local accounted interval family object stored by the
 recovered adjacent-family carrier.
@@ -1417,6 +1513,39 @@ theorem
   (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
     h hno).three_head_or_tail

+set_option linter.style.longLine false in
+/--
+Four-element consumer form: failure plus named no-adjacent-overlap yields
+either the head-pair recovered branch or a diagnostic on the three-element tail.
+
+This remains a bounded decomposition for `[W1, W2, W3, W4]`; it does not
+enumerate or aggregate diagnostics in longer lists.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_failure_four_diagnostic_head_or_tail_of_noAdjacentOverlap
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        [W1, W2, W3, W4])
+    (hno :
+      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
+        [W1, W2, W3, W4]) :
+    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
+      let F :=
+        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+          W1 W2 hrev
+      (((F.items).map
+        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
+        (((F.items).map
+          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
+        F.items.length = 2)
+    ∨
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        [W2, W3, W4] :=
+  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
+    h hno).four_head_or_tail
+
 set_option linter.style.longLine false in
 /--
 Failure plus named no-adjacent-overlap, projected directly to the pair-local
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-187.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-187.md
new file mode 100644
index 00000000..e28a2bf5
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-187.md
@@ -0,0 +1,163 @@
+# report-petal-187
+
+Date: 2026-07-06
+
+## Scope
+
+Checkpoint 187 adds a length-four bounded decomposition for the bundled
+recovered accounted-family diagnostic carrier in
+`DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis`.
+
+The result is local to the explicit witness list `[W1, W2, W3, W4]`.  It says
+that a diagnostic is either carried by the head pair `[W1, W2]`, or it already
+lives in the tail list `[W2, W3, W4]`.
+
+This is a bounded decomposition theorem, not a global diagnostic search.
+
+## Adjacent-pair decomposition
+
+Added:
+
+```lean
+theorem
+  SourcePressureLocalIslandWitnessAdjacentPairInList.four_head_or_tail
+```
+
+For the explicit list `[W1, W2, W3, W4]`, an adjacent-pair address decomposes
+as:
+
+```lean
+(A = W1 ∧ B = W2) ∨
+  SourcePressureLocalIslandWitnessAdjacentPairInList [W2, W3, W4] A B
+```
+
+This is the raw address-level splitter.  It follows the same bounded-list shape
+as the previous two- and three-element normal forms.
+
+## Diagnostic decomposition
+
+Added:
+
+```lean
+theorem
+  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_head_or_tail
+```
+
+For a bundled diagnostic on `[W1, W2, W3, W4]`, the diagnostic is either:
+
+- the head reversed pair, witnessed by
+  `SourcePressureLocalIslandWitnessBefore W2 W1`; or
+- a bundled diagnostic on the tail `[W2, W3, W4]`.
+
+The head case exposes the pair-local recovered-family facts attached to
+`sourcePressureAccountedIntervalFamilyOfPair W1 W2`: sum bound, strict
+negativity, and length two.
+
+## Iff form
+
+Added:
+
+```lean
+theorem
+  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_iff_head_or_tail
+```
+
+This packages the four-element decomposition into an iff.  The reverse
+direction constructs the head-pair diagnostic directly from the reversed-before
+witness, or lifts an existing diagnostic from the three-element tail.
+
+## Failure + no-overlap corollary
+
+Added:
+
+```lean
+theorem
+  sourcePressureLocalIslandWitnessList_failure_four_diagnostic_head_or_tail_of_noAdjacentOverlap
+```
+
+For `[W1, W2, W3, W4]`, sorted-before failure plus the named no-adjacent-overlap
+predicate yields the same head-or-tail diagnostic alternative.  This is the
+consumer-facing version of the bundled decomposition.
+
+## Optional pair enumeration
+
+The fully bounded four-to-pairs corollary was not added in this checkpoint.
+It would duplicate a long nested statement and is better deferred until there
+is a concrete downstream consumer.  The current head-or-tail form is the more
+stable API.
+
+## File-size watch
+
+Current line counts:
+
+```text
+  1750 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+  1391 lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
+  1896 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+  5037 total
+```
+
+`PressureAdjacentDiagnosis.lean` is below the 1900-line watch threshold, so this
+checkpoint did not start a refactor.  If the next bounded-decomposition layer
+pushes the file toward 1900-2000 lines, the next checkpoint should consider
+extracting bounded diagnostic decomposition helpers to a new module.
+
+## Guardrails preserved
+
+This checkpoint did not introduce:
+
+- global local-island coverage;
+- maximality;
+- uniqueness for arbitrary lists;
+- prefix behavior;
+- arbitrary list sorting;
+- canonical first diagnosis for arbitrary lists;
+- enumeration of all diagnostics;
+- union accounting;
+- overlap repair;
+- Collatz convergence;
+- aggregation of multiple recovered pairs;
+- a list-wide accounted interval union;
+- disjointness between multiple recovered families.
+
+Recovered budgets remain pair-local.  The new theorem only opens a
+four-element explicit list into a head pair or the existing three-element tail
+diagnostic layer.
+
+## Verification
+
+Commands run:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
+lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
+lake build DkMath.Collatz.PetalBridge.PressureAccounting
+lake build DkMath.Collatz.PetalBridge.PressureFrontier
+lake build DkMath.Collatz.PetalBridge
+rg -n "\bsorry\b" DkMath/Collatz/PetalBridge/PressureAccounting.lean DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+```
+
+Results:
+
+- all listed `lake build` commands completed successfully;
+- the targeted `rg` no-sorry check returned no matches.
+
+Known unrelated warning still appears during builds:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+This checkpoint did not modify that file.
+
+## Next inference
+
+The bounded chain now has length two, three, and four forms.  The next natural
+step is not arbitrary-list generalization.  A safe next checkpoint is either:
+
+- a consumer-driven theorem that uses the four-element head-or-tail form; or
+- a small extraction module for bounded diagnostic decompositions before adding
+  a length-five layer.
+
+The second option is preferable if the file-size watch becomes active.
````
`````
