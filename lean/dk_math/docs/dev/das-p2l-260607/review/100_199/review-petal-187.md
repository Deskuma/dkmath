# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis

gch: 3a542fe1c9aaa9911d489ec66d7c4e1ec11164de

## Report

cp186 完了です。

[PressureAdjacentDiagnosis.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean:317) に、三要素リスト `[W1, W2, W3]` 用の head-or-tail 分解を追加しました。診断 carrier も同じ形で分解でき、failure + no-overlap からも同じ分岐を得られます。主張範囲は明確に三要素の明示リスト限定で、任意リストの coverage / uniqueness / union accounting / Collatz convergence には踏み込んでいません。

レポートも追加しました: [report-petal-186.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-186.md)

確認済み:
`lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis`
`lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction`
`lake build DkMath.Collatz.PetalBridge.PressureAccounting`
`lake build DkMath.Collatz.PetalBridge.PressureFrontier`
`lake build DkMath.Collatz.PetalBridge`
`rg` 対象3ファイル no-sorry
`git diff --check`

既知の無関係 warning として `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` は出ていますが、今回の対象外です。

## Review

## 結論

うむ、Checkpoint 186 は **採用** じゃ 👍️
三要素 list `[W1, W2, W3]` に対する bounded head-or-tail 分解が入った。これは cp185 の二要素 normal form から、次の一段へ進む自然な拡張じゃ。

追加された中心は、

```lean id="oh1mmv"
SourcePressureLocalIslandWitnessAdjacentPairInList.three_head_or_tail
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_head_or_tail
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_iff_head_or_tail
sourcePressureLocalIslandWitnessList_failure_three_diagnostic_head_or_tail_of_noAdjacentOverlap
```

じゃな。対象は明確に三要素の明示 list 限定で、任意 list の coverage、uniqueness、enumeration、union accounting、Collatz convergence には踏み込んでいない。境界は守られている。

## 実装レビュー

## 1. `three_head_or_tail` は良い bounded splitter

```lean id="cyazms"
SourcePressureLocalIslandWitnessAdjacentPairInList.three_head_or_tail
```

は、

```text id="2998v5"
[W1, W2, W3] の adjacent pair は、
head pair W1,W2
または
tail list [W2,W3] 内の adjacent pair
```

という分解じゃ。

実装が `:= h` で通っているのは、おそらく `AdjacentPairInList` の定義自体が head-or-tail 型に近い構造を持っているからじゃな。ビルドが通っているなら問題なし。むしろ、既存定義にぴったり沿った薄い theorem になっている。

## 2. diagnostic 側の三要素分解も自然

```lean id="jgpj8h"
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_head_or_tail
```

は、diagnostic を unpack して、address-level splitter に渡している。

分岐は綺麗じゃ。

```text id="aotm0k"
head branch:
  W1,W2 の reversed-before witness と pair-local facts を返す

tail branch:
  [W2,W3] の diagnostic として再包装する
```

これは cp184 の `of_tail` と cp185 の two-element normal form をつなぐ、正しい中間層じゃ。

## 3. iff form も使いやすい

```lean id="xxkivr"
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_iff_head_or_tail
```

まで入ったのは良い。

forward は decomposition。
reverse は、

```text id="r0xoi5"
head case:
  head pair diagnostic を直接構成

tail case:
  tail diagnostic を of_tail で持ち上げる
```

という形じゃ。

これは後続 theorem の `rw` / `cases` に使いやすい。

## 4. failure + no-overlap corollary も適切

```lean id="bdfhe2"
sourcePressureLocalIslandWitnessList_failure_three_diagnostic_head_or_tail_of_noAdjacentOverlap
```

により、

```text id="vubxh1"
failure [W1,W2,W3]
noAdjacentOverlap [W1,W2,W3]
  -> head recovered branch
     or tail diagnostic [W2,W3]
```

が得られた。

これは consumer-facing としてかなり良い。
長い list に一般化しているわけではなく、三要素限定なので安全じゃ。

## 数学的意味

今回で、diagnostic の bounded decomposition がこうなった。

```text id="2u6jje"
二要素:
  [W1,W2] diagnostic
    ↔ W2 before W1

三要素:
  [W1,W2,W3] diagnostic
    -> W2 before W1
       or diagnostic [W2,W3]
```

つまり、三要素 list にある diagnostic は、

```text id="qqe68t"
左端 pair にあるか
一つ右へ送られるか
```

として扱える。

これは、任意 list の探索ではない。
しかし、bounded な list decomposition の雛形としてかなり強い。

DkMath 的には、

```text id="numass"
局所回収会計は、head pair に現れるか、tail 側へ保存される。
```

という構文保存則になっている。

## 注意点

## 1. report 内の表記だけ少し注意

report の説明に、

```lean id="3g6ghw"
sourcePressureAccountedIntervalFamilyOfPair W1 W2
```

という略記があるが、実コード上の本体は、

```lean id="1w8qf9"
sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
```

じゃな。文脈上の説明略記としては読めるが、今後の report では実 Lean 名に寄せた方が混乱が少ない。

## 2. 任意 list の canonical first ではない

今回の分解は三要素限定じゃ。

まだ次は言っていない。

```text id="g5hnig"
長い list で最左 diagnostic を選ぶ
全 diagnostic を列挙する
list 全体で recovered family を集約する
```

ここは未到達。ちゃんと守られている。

## 3. ファイルサイズ注意

`PressureAdjacentDiagnosis.lean` が 1621 行まで来ている。
まだ 2000 行未満だが、cp187〜cp188 で長くなるなら次の refactor 候補になる。

ただし今すぐ分割するより、length-four まで入れてから、

```text id="xvln5j"
Diagnostic normal forms / bounded decomposition
```

を別ファイルへ出すか判断するのがよい。

## 次の checkpoint 方針

次は report の Next inference 通り、**四要素 list の bounded decomposition** が自然じゃ。

狙いは、

```text id="uuc29g"
diagnostic [W1,W2,W3,W4]
  -> head pair W1,W2
     or diagnostic [W2,W3,W4]
```

そして optional で、tail の三要素分解まで押して、

```text id="sbbt5v"
W2 before W1
or W3 before W2
or diagnostic [W3,W4]
```

まで行ける。

ただし、まだ arbitrary list には行かない。
bounded decomposition のままにするのが安全じゃ。

## 次の Codex 指示

```text id="qt59m9"
Checkpoint 187: Main root only — length-four bounded decomposition for the bundled diagnostic carrier.

Scope:
Focus on the refactored Collatz/PetalBridge pressure modules.

Primary target file:
- DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean

Allowed supporting file, only if needed:
- DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean

Do not modify:
- PressureAccounting.lean unless import/order forces a tiny fix
- OneCycle.lean
- ValuationFlowBridge.lean
- ABC files
- NumberTheory files

Do not rename or rewrite previous theorem statements.

Context:
Checkpoint 186 added length-three bounded decomposition:

- SourcePressureLocalIslandWitnessAdjacentPairInList.three_head_or_tail
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_head_or_tail
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_iff_head_or_tail
- sourcePressureLocalIslandWitnessList_failure_three_diagnostic_head_or_tail_of_noAdjacentOverlap

Checkpoint 185 added the length-two normal form.

Global guardrails:
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
- Keep all statements local to explicitly supplied witness lists.
- Recovered budgets remain pair-local.
- Do not aggregate multiple recovered pairs.
- Do not create a list-wide accounted interval union.
- Do not prove disjointness between multiple recovered families.

Main goal:
Add a bounded length-four decomposition for the bundled diagnostic carrier.
For `[W1, W2, W3, W4]`, a diagnostic is either:
- the head pair `W1, W2`, represented by a reversed-before witness
  `SourcePressureLocalIslandWitnessBefore W2 W1`; or
- a diagnostic in the tail list `[W2, W3, W4]`.

Part A: adjacent-pair length-four head-or-tail decomposition.

Prove:

  theorem SourcePressureLocalIslandWitnessAdjacentPairInList.four_head_or_tail
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 W4 A B : SourcePressureLocalIslandWitness n k r}
      (h :
        SourcePressureLocalIslandWitnessAdjacentPairInList
          [W1, W2, W3, W4] A B) :
      (A = W1 ∧ B = W2) ∨
        SourcePressureLocalIslandWitnessAdjacentPairInList [W2, W3, W4] A B

Suggested proof:
- if the inductive structure matches the three-element theorem, `exact h` may work.
- otherwise, cases h:
  - head case: left
  - tail case: right

Part B: diagnostic length-four head-or-tail decomposition.

Prove:

  theorem
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_head_or_tail
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r}
      (h :
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
          [W1, W2, W3, W4]) :
      (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
        let F :=
          sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
            W1 W2 hrev
        (((F.items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
          (((F.items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
          F.items.length = 2)
      ∨
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
          [W2, W3, W4]

Suggested proof:
- same proof shape as `.three_head_or_tail`.
- unpack h.exists_pair.
- split adjacent-pair address using Part A.
- head branch: substitute and return left.
- tail branch: repackage as diagnostic on `[W2,W3,W4]`.

Part C: diagnostic length-four iff, optional.

If easy, prove:

  theorem
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_iff_head_or_tail
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r} :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
        [W1, W2, W3, W4] ↔
      ((∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
        let F :=
          sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
            W1 W2 hrev
        (((F.items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
          (((F.items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
          F.items.length = 2)
       ∨
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
          [W2, W3, W4])

Reverse direction:
- head branch:
  construct `[W1,W2]` diagnostic via `of_two_reversed`, then lift twice:
    `.of_tail_tail`
- tail branch:
  lift with `.of_tail`.

Do not force the iff if statement becomes too noisy.  The head-or-tail extractor
is enough.

Part D: failure + no-overlap length-four corollary.

Only if Part B succeeds, prove:

  theorem
      sourcePressureLocalIslandWitnessList_failure_four_diagnostic_head_or_tail_of_noAdjacentOverlap
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r}
      (h :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
          [W1, W2, W3, W4])
      (hno :
        SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
          [W1, W2, W3, W4]) :
      (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
        let F :=
          sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
            W1 W2 hrev
        (((F.items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
          (((F.items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
          F.items.length = 2)
      ∨
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
          [W2, W3, W4]

Suggested proof:
- obtain diagnostic from
  sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
- apply `.four_head_or_tail`.

Part E: optional fully bounded four-to-pairs corollary.

Only if easy, combine the tail three-element theorem and two-element theorem to
derive:

  either W2 before W1
  or W3 before W2
  or W4 before W3

with corresponding pair-local facts.

Do not force this; it may duplicate very long statements.

Part F: file size watch.

`PressureAdjacentDiagnosis.lean` is now over 1600 lines.  If the file approaches
or exceeds 1900 lines after this checkpoint, do not start a broad refactor in
the same checkpoint.  Instead, mention in the report that the next checkpoint
should consider extracting bounded diagnostic decomposition helpers to a new
module.

Part G: do not introduce aggregation.

Do not prove:
- a list of all diagnostics,
- canonical first diagnosis for arbitrary lists,
- sum over all recovered diagnostics,
- disjointness between multiple recovered families,
- union accounting,
- coverage,
- overlap repair.

Part H: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-187.md

Include:
- adjacent-pair length-four head-or-tail theorem;
- diagnostic length-four head-or-tail theorem;
- optional iff theorem if added;
- optional failure + no-overlap corollary if added;
- file-size watch note;
- explicit note that this is only a four-element explicit-list bounded decomposition;
- explicit note that no aggregation, union accounting, coverage, maximality,
  uniqueness for arbitrary lists, sorting, canonical first diagnosis for
  arbitrary lists, enumeration, overlap repair, or Collatz convergence was
  introduced;
- verification results.

Verification:

  lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
  lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
  lake build DkMath.Collatz.PetalBridge.PressureAccounting
  lake build DkMath.Collatz.PetalBridge.PressureFrontier
  lake build DkMath.Collatz.PetalBridge

Run no-sorry checks:

  rg -n "\\bsorry\\b" \
    DkMath/Collatz/PetalBridge/PressureAccounting.lean \
    DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
    DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean

Also run:

  git diff --check
```

## 総評

cp186 は良い。
これで bounded decomposition は、

```text id="x5bd6u"
length 2:
  reversed pair normal form

length 3:
  head pair or tail length 2 diagnostic
```

まで来た。

次に length 4 を入れれば、

```text id="we1rw7"
head pair or tail length 3 diagnostic
```

となり、bounded decomposition のパターンがかなり明確になる。

ただし、ファイルサイズはそろそろ注意じゃ。
length 4 の次は、実装継続より先に **Diagnostic decomposition module への分割** を検討してよい段階に近づく。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
index 4ee290c3..3766fc44 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
@@ -307,6 +307,21 @@ theorem SourcePressureLocalIslandWitnessAdjacentPairInList.two_eq
     A = W1 ∧ B = W2 :=
   SourcePressureLocalIslandWitnessAdjacentPairInList.two_iff_head.mp h

+/--
+In a three-element explicit witness list, an adjacent-pair address is either
+the head pair or an adjacent-pair address in the two-element tail.
+
+This is a bounded three-element decomposition only.  It does not enumerate
+diagnostics in arbitrary lists.
+-/
+theorem SourcePressureLocalIslandWitnessAdjacentPairInList.three_head_or_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 A B : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureLocalIslandWitnessAdjacentPairInList [W1, W2, W3] A B) :
+    (A = W1 ∧ B = W2) ∨
+      SourcePressureLocalIslandWitnessAdjacentPairInList [W2, W3] A B :=
+  h
+
 /--
 A list-level carrier for "some adjacent pair in this explicit list has an
 adjacent diagnosis".
@@ -1076,6 +1091,86 @@ theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyD
       SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_two_reversed
         hrev

+set_option linter.style.longLine false in
+/--
+Three-element bounded decomposition for the bundled diagnostic carrier.
+
+A diagnostic on `[W1, W2, W3]` is either carried by the head pair `W1, W2`,
+or it is already a diagnostic on the two-element tail `[W2, W3]`.
+This theorem only decomposes the explicit three-element list; it does not
+enumerate diagnostics in arbitrary lists.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_head_or_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
+    (h :
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        [W1, W2, W3]) :
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
+        [W2, W3] := by
+  rcases h.exists_pair with ⟨A, B, hin, hrev, hbudget, hneg, hlen⟩
+  rcases SourcePressureLocalIslandWitnessAdjacentPairInList.three_head_or_tail
+      hin with hhead | htail
+  · rcases hhead with ⟨rfl, rfl⟩
+    exact Or.inl ⟨hrev, hbudget, hneg, hlen⟩
+  · exact Or.inr
+      (SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
+        htail hrev hbudget hneg hlen)
+
+set_option linter.style.longLine false in
+/--
+Iff form of the three-element diagnostic decomposition.
+
+The reverse direction either builds the head-pair diagnostic from the reversed
+witness and lifts it through the tail API, or lifts an existing tail diagnostic.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_iff_head_or_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r} :
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+      [W1, W2, W3] ↔
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
+        [W2, W3]) := by
+  constructor
+  · exact
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_head_or_tail
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
@@ -1290,6 +1385,38 @@ theorem
   (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
     h hno).exists_reversed_of_two

+set_option linter.style.longLine false in
+/--
+Three-element consumer form: failure plus named no-adjacent-overlap yields
+either the head-pair recovered branch or a diagnostic on the two-element tail.
+
+This is still a bounded decomposition for `[W1, W2, W3]`; it does not enumerate
+or aggregate diagnostics in longer lists.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_failure_three_diagnostic_head_or_tail_of_noAdjacentOverlap
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2, W3])
+    (hno :
+      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
+        [W1, W2, W3]) :
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
+        [W2, W3] :=
+  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
+    h hno).three_head_or_tail
+
 set_option linter.style.longLine false in
 /--
 Failure plus named no-adjacent-overlap, projected directly to the pair-local
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-186.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-186.md
new file mode 100644
index 00000000..0af3874c
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-186.md
@@ -0,0 +1,161 @@
+# report-petal-186
+
+Date: 2026-07-06
+
+## Scope
+
+Checkpoint 186 adds a length-three decomposition for the bundled recovered
+accounted-family diagnostic carrier in
+`DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis`.
+
+The new surface is intentionally bounded.  It only analyzes the explicit
+three-witness list `[W1, W2, W3]`.  The result says that a diagnostic is either
+located at the head pair `[W1, W2]`, or it is already a diagnostic in the tail
+list `[W2, W3]`.
+
+This is a local decomposition theorem, not a global search or coverage theorem.
+
+## Adjacent-pair decomposition
+
+Added:
+
+```lean
+theorem
+  SourcePressureLocalIslandWitnessAdjacentPairInList.three_head_or_tail
+```
+
+For the explicit list `[W1, W2, W3]`, an adjacent-pair address decomposes as:
+
+```lean
+(A = W1 ∧ B = W2) ∨
+  SourcePressureLocalIslandWitnessAdjacentPairInList [W2, W3] A B
+```
+
+This is the raw address-level splitter.  It does not claim uniqueness beyond
+what the explicit list structure gives.
+
+## Diagnostic decomposition
+
+Added:
+
+```lean
+theorem
+  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_head_or_tail
+```
+
+For a bundled diagnostic on `[W1, W2, W3]`, the diagnostic is either:
+
+- the head reversed pair, witnessed by
+  `SourcePressureLocalIslandWitnessBefore W2 W1`; or
+- a bundled diagnostic on the tail `[W2, W3]`.
+
+The head case exposes the pair-local recovered-family facts attached to the
+stored diagnostic:
+
+```lean
+sourcePressureAccountedIntervalFamilyOfPair W1 W2
+```
+
+with its sum bound, strict negativity, and length witness.
+
+## Iff form
+
+Added:
+
+```lean
+theorem
+  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_iff_head_or_tail
+```
+
+This packages the constructor and extractor into an iff form:
+
+```lean
+Diagnostic [W1, W2, W3] ↔
+  HeadPairDiagnostic W1 W2 ∨ Diagnostic [W2, W3]
+```
+
+The reverse direction constructs the head case directly from the existing
+reversed-pair accounted-family theorems.  The tail case is lifted with
+`of_tail`.
+
+## Failure + no-overlap corollary
+
+Added:
+
+```lean
+theorem
+  sourcePressureLocalIslandWitnessList_failure_three_diagnostic_head_or_tail_of_noAdjacentOverlap
+```
+
+For `[W1, W2, W3]`, sorted-before failure plus the named no-adjacent-overlap
+predicate yields the same head-or-tail diagnostic alternative.  This is the
+consumer-facing version of the bundled decomposition.
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
+three-element explicit list into a head pair or the already-existing
+two-element tail diagnostic layer.
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
+git diff --check
+```
+
+Results:
+
+- all listed `lake build` commands completed successfully;
+- the targeted `rg` no-sorry check returned no matches;
+- `git diff --check` passed.
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
+## File sizes
+
+```text
+  1621 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+  1391 lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
+  1896 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+  4908 total
+```
+
+## Next inference
+
+The three-element head-or-tail form is now available as a small bounded
+diagnostic normal form.  The next natural extension is not an arbitrary-list
+claim.  A safer next step is a length-four theorem that decomposes
+`[W1, W2, W3, W4]` into either the head pair or the already-proved
+three-element tail.  This keeps the proof chain inductive and explicit while
+avoiding global coverage claims.
````
`````
