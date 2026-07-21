# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition

gch: 24856f415a5398f300d8ad6e9a1f740ed3b5f294

## Report

cp189 完了です。

`PressureDiagnosticDecomposition.lean` に、長かった head-pair branch を名前付き predicate として追加しました。

- `SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic`
- `.of_before`
- `two_iff_pairDiagnostic`
- `three_iff_pairDiagnostic_or_tail`
- `four_iff_pairDiagnostic_or_tail`
- failure + noAdjacentOverlap の compact consumer wrappers

今回の変更は API 圧縮のみです。length-five、任意長 list 分解、aggregation、union accounting、coverage、maximality、Collatz convergence は追加していません。

レポートも作成済みです。

- `lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-189.md`

検証も通過しました。

- `lake build DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition`
- `lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis`
- `lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction`
- `lake build DkMath.Collatz.PetalBridge.PressureAccounting`
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier`
- `lake build DkMath.Collatz.PetalBridge`
- 対象4ファイルの `sorry` 検索: ヒットなし
- `git diff --check`: pass

既知の unrelated warning として `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` 警告だけ出ています。

## Review

## 結論

うむ、Checkpoint 189 は **採用** じゃ 👍️
これは良い **API-compression checkpoint** になっている。

長かった head-pair branch に、

```lean id="ke1n04"
SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
```

という名前が付き、length-two / three / four の decomposition theorem を短く読めるようになった。数学的主張は増やさず、length-five、任意長 list 分解、aggregation、union accounting、coverage、Collatz convergence にも踏み込んでいない。境界は守られている。

## 実装レビュー

## 1. pair-local branch の命名は正解

これまで各 theorem に繰り返し出ていた長い枝、

```lean id="hlfeu4"
∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
  let F :=
    sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
      W1 W2 hrev
  ...
```

が、

```lean id="x9ipl4"
SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W1 W2
```

に圧縮された。

これはかなり効く。
今後 length-five / length-six の bounded decomposition を伸ばすとき、statement の読みやすさが大きく変わる。

## 2. `.of_before` が良い

```lean id="d7iegk"
SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic.of_before
```

は、`W2 before W1` から既存の reversed-pair facts を再包装しているだけじゃ。

使っている既存補題も妥当。

```lean id="qz4swy"
sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two
sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length
```

新しい数学的強化ではなく、公開 API の整理としてきれいじゃ。

## 3. compact iff wrappers が良い

```lean id="mlyivw"
two_iff_pairDiagnostic
three_iff_pairDiagnostic_or_tail
four_iff_pairDiagnostic_or_tail
```

これらにより、bounded decomposition がかなり読みやすくなった。

特に今後は、

```lean id="f3fpif"
Diagnostic [W1, W2, W3, W4]
  ↔ PairDiagnostic W1 W2 ∨ Diagnostic [W2, W3, W4]
```

という構造で読める。

これは「head にあるか、tail に保存されるか」という意図がはっきり出る。

## 4. consumer wrappers も良い

```lean id="emnaav"
sourcePressureLocalIslandWitnessList_failure_two_pairDiagnostic_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_three_pairDiagnostic_or_tail_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_four_pairDiagnostic_or_tail_of_noAdjacentOverlap
```

により、failure + noAdjacentOverlap からも compact branch を得られるようになった。

これは下流利用でかなり助かるはずじゃ。

## 数学的意味

今回で bounded diagnostic decomposition の読みはこうなる。

```text id="9kywga"
length 2:
  diagnostic [W1,W2]
    ↔ pairDiagnostic W1 W2

length 3:
  diagnostic [W1,W2,W3]
    ↔ pairDiagnostic W1 W2
       or diagnostic [W2,W3]

length 4:
  diagnostic [W1,W2,W3,W4]
    ↔ pairDiagnostic W1 W2
       or diagnostic [W2,W3,W4]
```

ここまで来ると、構造がかなり明瞭じゃ。

```text id="1hk9kz"
head pair が回収可能か、
そうでなければ tail に diagnostic が保存される
```

という bounded decomposition の型が見えた。

## 注意点

## 1. predicate 名は長いが、今は良い

```lean id="igj4cu"
SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
```

は長い。
だが、現段階では意味を隠さない方がよい。

短い alias は後で入れられる。

```lean id="j8jt27"
abbrev SourcePressureLocalIslandWitnessPairDiagnostic := ...
```

のようなものは、API が十分安定してからでよい。

## 2. 次は length-five に進める

今回で head branch が名前を持ったので、次は length-five bounded decomposition に進んでよい。

ただし、まだ任意 list には行かない。
length-five もあくまで bounded theorem として、

```text id="0k0yr2"
diagnostic [W1,W2,W3,W4,W5]
  ↔ pairDiagnostic W1 W2
     or diagnostic [W2,W3,W4,W5]
```

を作るのが安全じゃ。

## 次の Codex 指示

```text id="w25frl"
Checkpoint 190: Main root only — length-five bounded decomposition using the named pair-local branch.

Scope:
Work in the refactored bounded diagnostic decomposition module.

Primary target file:
- DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean

Do not modify unless absolutely necessary:
- DkMath/Collatz/PetalBridge.lean
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
Checkpoint 189 added the named pair-local branch:

  SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic

and compact bounded decomposition wrappers:

  two_iff_pairDiagnostic
  three_iff_pairDiagnostic_or_tail
  four_iff_pairDiagnostic_or_tail

Main goal:
Add a length-five bounded decomposition for the bundled diagnostic carrier,
using the named pair-local recovered branch immediately.

For `[W1, W2, W3, W4, W5]`, a diagnostic should decompose as:

  SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W1 W2
  or
  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
    [W2, W3, W4, W5]

This remains bounded and explicit.  Do not add arbitrary-list decomposition.

Part A: adjacent-pair length-five head-or-tail decomposition.

Prove:

  theorem SourcePressureLocalIslandWitnessAdjacentPairInList.five_head_or_tail
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 W4 W5 A B : SourcePressureLocalIslandWitness n k r}
      (h :
        SourcePressureLocalIslandWitnessAdjacentPairInList
          [W1, W2, W3, W4, W5] A B) :
      (A = W1 ∧ B = W2) ∨
        SourcePressureLocalIslandWitnessAdjacentPairInList
          [W2, W3, W4, W5] A B

Suggested proof:
- if the inductive structure matches the previous bounded theorems, `exact h`
  may work.
- otherwise case-split h:
  - head case -> left
  - tail case -> right

Part B: diagnostic length-five head-or-tail decomposition.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.five_head_or_tail
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 W4 W5 : SourcePressureLocalIslandWitness n k r}
      (h :
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
          [W1, W2, W3, W4, W5]) :
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W1 W2 ∨
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
          [W2, W3, W4, W5]

Suggested proof:
- unpack h.exists_pair to get A B hin hrev hbudget hneg hlen.
- split hin with `five_head_or_tail`.
- head branch:
  substitute A = W1, B = W2.
  return `Or.inl ⟨hrev, hbudget, hneg, hlen⟩`.
  This should match the named pair-local predicate.
- tail branch:
  return `Or.inr` by repackaging the same pair-local facts with
  `SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair`.

Part C: diagnostic length-five iff.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.five_iff_pairDiagnostic_or_tail
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 W4 W5 : SourcePressureLocalIslandWitness n k r} :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
        [W1, W2, W3, W4, W5] ↔
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W1 W2 ∨
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
          [W2, W3, W4, W5]

Reverse direction:
- head branch:
  use `SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pairDiagnostic_two`
  to get diagnostic `[W1, W2]`,
  then lift with `.of_tail_tail_tail`.
  If needed, build directly with `.of_pair`.
- tail branch:
  use `.of_tail`.

Part D: failure + noAdjacentOverlap consumer wrapper.

Prove:

  theorem sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_or_tail_of_noAdjacentOverlap
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 W4 W5 : SourcePressureLocalIslandWitness n k r}
      (h :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
          [W1, W2, W3, W4, W5])
      (hno :
        SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
          [W1, W2, W3, W4, W5]) :
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W1 W2 ∨
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
          [W2, W3, W4, W5]

Suggested proof:
- obtain diagnostic via
  sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
- apply `.five_head_or_tail`.

Part E: optional fully bounded five-to-pairs corollary.

Do not force this.
If a downstream consumer clearly needs it later, it can combine:
- `five_iff_pairDiagnostic_or_tail`
- `four_iff_pairDiagnostic_or_tail`
- `three_iff_pairDiagnostic_or_tail`
- `two_iff_pairDiagnostic`

For this checkpoint, prefer the one-step head-or-tail API.

Part F: file-size watch.

Report current line counts for:
- PressureDiagnosticDecomposition.lean
- PressureAdjacentDiagnosis.lean
- PressureLocalWitnessObstruction.lean
- PressureAccounting.lean

If PressureDiagnosticDecomposition.lean becomes large, do not refactor in the
same checkpoint.  Only mention a future split if necessary.

Guardrails:
- Do not add arbitrary-list decomposition.
- Do not add a list of all diagnostics.
- Do not add canonical first diagnosis for arbitrary lists.
- Do not add sum over all recovered diagnostics.
- Do not add disjointness between multiple recovered families.
- Do not add union accounting.
- Do not add coverage.
- Do not add overlap repair.
- Do not add Collatz convergence.
- Do not aggregate multiple recovered pairs.
- Keep the theorem bounded to the explicit five-element list.

Report:
Create:

  docs/dev/das-p2l-260607/review/report-petal-190.md

Include:
- adjacent-pair length-five head-or-tail theorem;
- diagnostic length-five head-or-tail theorem;
- compact length-five iff theorem;
- failure + noAdjacentOverlap consumer wrapper;
- note that the named pair-local predicate was used instead of repeating the
  long head branch;
- explicit note that this is only a five-element explicit-list bounded
  decomposition;
- explicit note that no arbitrary-list decomposition, aggregation, union
  accounting, coverage, maximality, uniqueness for arbitrary lists, sorting,
  canonical first diagnosis for arbitrary lists, enumeration, overlap repair,
  or Collatz convergence was introduced;
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

cp189 は良い整理じゃ。

これで bounded decomposition は、

```text id="bw2o9x"
head pair branch = named predicate
tail branch = remaining diagnostic
```

としてかなり読みやすくなった。

次は length-five に進んでよい。
ただし、まだ任意長 generalization には飛ばない。
五要素の bounded decomposition まで、同じ型で積むのが安全じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
index 41f16698..4c081266 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
@@ -21,6 +21,50 @@ enumeration, union accounting, overlap repair, aggregation, or Collatz
 convergence.
 -/

+set_option linter.style.longLine false in
+/--
+Named pair-local recovered head branch used by the bounded diagnostic
+decomposition theorems.
+
+This is only a name for the long head-branch expression already used by the
+length-two, length-three, and length-four diagnostic decompositions.  It remains
+pair-local to `W1, W2`: no list-wide family, aggregation, coverage, or
+canonical arbitrary-list diagnostic is introduced here.
+-/
+def SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+    {n : OddNat} {k r : ℕ}
+    (W1 W2 : SourcePressureLocalIslandWitness n k r) : Prop :=
+  ∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
+    let F :=
+      sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        W1 W2 hrev
+    (((F.items).map
+      (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
+      (((F.items).map
+        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
+      F.items.length = 2
+
+set_option linter.style.longLine false in
+/--
+A reversed-before witness directly produces the named pair-local recovered
+diagnostic branch.
+
+The proof repackages the existing reversed-pair accounted-family facts; it does
+not add any new mathematical strength.
+-/
+theorem SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic.of_before
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
+    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W1 W2 :=
+  ⟨hrev,
+    sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two
+      W1 W2 hrev,
+    sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
+      W1 W2 hrev,
+    sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length
+      W1 W2 hrev⟩
+
 /--
 In a two-element explicit witness list, the only adjacent-pair address is the
 head pair.
@@ -161,6 +205,36 @@ theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyD
       SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_two_reversed
         hrev

+set_option linter.style.longLine false in
+/--
+Compact two-element normal form using the named pair-local recovered branch.
+
+This is definitionally the same statement as `two_iff`, with the long head
+branch named for downstream readability.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.two_iff_pairDiagnostic
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r} :
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+      [W1, W2] ↔
+    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W1 W2 := by
+  exact
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.two_iff
+
+set_option linter.style.longLine false in
+/-- Build the two-element diagnostic from the named pair-local branch. -/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pairDiagnostic_two
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (h :
+      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+        W1 W2) :
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+      [W1, W2] :=
+  let hiff :=
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.two_iff_pairDiagnostic
+  hiff.mpr h
+
 set_option linter.style.longLine false in
 /--
 Three-element bounded decomposition for the bundled diagnostic carrier.
@@ -241,6 +315,25 @@ theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyD
         SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail
           htail

+set_option linter.style.longLine false in
+/--
+Compact three-element decomposition using the named pair-local recovered branch.
+
+This is the same bounded decomposition as `three_iff_head_or_tail`; only the
+long head branch has been named.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_iff_pairDiagnostic_or_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r} :
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+      [W1, W2, W3] ↔
+    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+      W1 W2 ∨
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        [W2, W3] := by
+  exact
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_iff_head_or_tail
+
 set_option linter.style.longLine false in
 /--
 Four-element bounded decomposition for the bundled diagnostic carrier.
@@ -322,6 +415,25 @@ theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyD
         SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail
           htail

+set_option linter.style.longLine false in
+/--
+Compact four-element decomposition using the named pair-local recovered branch.
+
+This is the same bounded decomposition as `four_iff_head_or_tail`; only the
+long head branch has been named.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_iff_pairDiagnostic_or_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r} :
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+      [W1, W2, W3, W4] ↔
+    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+      W1 W2 ∨
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        [W2, W3, W4] := by
+  exact
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_iff_head_or_tail
+
 set_option linter.style.longLine false in
 /--
 Two-element consumer form: failure plus named no-adjacent-overlap yields the
@@ -350,6 +462,26 @@ theorem
   (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
     h hno).exists_reversed_of_two

+set_option linter.style.longLine false in
+/--
+Compact two-element consumer form using the named pair-local recovered branch.
+
+This is only the named form of
+`sourcePressureLocalIslandWitnessList_failure_two_exists_reversed_of_noAdjacentOverlap`.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_failure_two_pairDiagnostic_of_noAdjacentOverlap
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2])
+    (hno :
+      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction [W1, W2]) :
+    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+      W1 W2 :=
+  sourcePressureLocalIslandWitnessList_failure_two_exists_reversed_of_noAdjacentOverlap
+    h hno
+
 set_option linter.style.longLine false in
 /--
 Three-element consumer form: failure plus named no-adjacent-overlap yields
@@ -382,6 +514,29 @@ theorem
   (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
     h hno).three_head_or_tail

+set_option linter.style.longLine false in
+/--
+Compact three-element consumer form using the named pair-local recovered branch.
+
+This is the same head-or-tail result as the long consumer theorem, with the
+head branch named.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_failure_three_pairDiagnostic_or_tail_of_noAdjacentOverlap
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2, W3])
+    (hno :
+      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
+        [W1, W2, W3]) :
+    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+      W1 W2 ∨
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        [W2, W3] :=
+  sourcePressureLocalIslandWitnessList_failure_three_diagnostic_head_or_tail_of_noAdjacentOverlap
+    h hno
+
 set_option linter.style.longLine false in
 /--
 Four-element consumer form: failure plus named no-adjacent-overlap yields
@@ -415,4 +570,28 @@ theorem
   (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
     h hno).four_head_or_tail

+set_option linter.style.longLine false in
+/--
+Compact four-element consumer form using the named pair-local recovered branch.
+
+This is the same head-or-tail result as the long consumer theorem, with the
+head branch named.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_failure_four_pairDiagnostic_or_tail_of_noAdjacentOverlap
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        [W1, W2, W3, W4])
+    (hno :
+      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
+        [W1, W2, W3, W4]) :
+    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+      W1 W2 ∨
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        [W2, W3, W4] :=
+  sourcePressureLocalIslandWitnessList_failure_four_diagnostic_head_or_tail_of_noAdjacentOverlap
+    h hno
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-189.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-189.md
new file mode 100644
index 00000000..707aaa5f
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-189.md
@@ -0,0 +1,141 @@
+# Report Petal 189
+
+## Checkpoint
+
+Checkpoint 189 was an API-compression pass for the bounded diagnostic
+decomposition layer.
+
+Primary file:
+
+- `DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean`
+
+No other Lean source file was changed.
+
+## Implemented
+
+### Named pair-local recovered branch
+
+Added:
+
+```lean
+def SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+```
+
+This names the long recovered head-pair branch that was repeated in the
+length-two, length-three, and length-four decomposition statements.
+
+The predicate is strictly pair-local to `W1, W2`.  It packages:
+
+- a reversed-before witness `W2` before `W1`;
+- the recovered accounted interval family for that reversed pair;
+- the existing `sum ≤ -2` budget fact;
+- the existing `sum < 0` negativity fact;
+- the existing `items.length = 2` fact.
+
+### Constructor
+
+Added:
+
+```lean
+theorem SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic.of_before
+```
+
+This constructor repackages the already-existing reversed-pair facts:
+
+- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two`
+- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg`
+- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length`
+
+No new mathematical strength is introduced.
+
+### Compact decomposition wrappers
+
+Added compact wrappers:
+
+```lean
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.two_iff_pairDiagnostic
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pairDiagnostic_two
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_iff_pairDiagnostic_or_tail
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_iff_pairDiagnostic_or_tail
+```
+
+These are readability wrappers around the existing bounded decomposition API.
+They replace the repeated long head branch with the named pair-local predicate.
+
+### Compact consumer wrappers
+
+Added compact failure/no-adjacent-overlap consumer wrappers:
+
+```lean
+theorem sourcePressureLocalIslandWitnessList_failure_two_pairDiagnostic_of_noAdjacentOverlap
+theorem sourcePressureLocalIslandWitnessList_failure_three_pairDiagnostic_or_tail_of_noAdjacentOverlap
+theorem sourcePressureLocalIslandWitnessList_failure_four_pairDiagnostic_or_tail_of_noAdjacentOverlap
+```
+
+These expose the same results as the existing long consumer theorems, but with
+the head branch expressed using
+`SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic`.
+
+## Guardrails
+
+This checkpoint intentionally did not add:
+
+- length-five decomposition;
+- arbitrary-list decomposition;
+- aggregation over multiple recovered diagnostics;
+- list-wide interval union accounting;
+- coverage;
+- maximality;
+- uniqueness for arbitrary lists;
+- sorting theorems;
+- canonical first diagnosis for arbitrary lists;
+- diagnostic enumeration;
+- overlap repair;
+- disjointness between multiple recovered families;
+- Collatz convergence.
+
+The theorem strength is unchanged.  The long recovered head branch was only
+given a stable public name.
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
+git diff --check
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
+The bounded diagnostic layer is now easier to extend because the head-pair
+branch has a stable name.  If the next checkpoint grows length-five or another
+bounded decomposition, it should use the new pair-local predicate immediately
+instead of repeating the long branch expression.
+
+The next step should still remain bounded unless a separate design checkpoint
+introduces a sound arbitrary-list decomposition policy.
````
`````
