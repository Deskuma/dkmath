# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition

gch: 8aab375934032e60bce4d55d35128029e76ef34f

## Report

cp190 完了です。

`PressureDiagnosticDecomposition.lean` に five-element bounded decomposition を追加しました。追加した主な定理は以下です。

- `SourcePressureLocalIslandWitnessAdjacentPairInList.five_head_or_tail`
- `SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.five_head_or_tail`
- `SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.five_iff_pairDiagnostic_or_tail`
- `sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_or_tail_of_noAdjacentOverlap`

head branch は cp189 の named predicate を使い、長い式の再展開は避けています。任意長 list 分解、aggregation、union accounting、coverage、canonical diagnosis、Collatz convergence などは追加していません。

レポートも作成済みです。

- `lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-190.md`

検証はすべて通過しました。

- 指定された 6 build: pass
- 対象4ファイルの `sorry` 検索: ヒットなし
- `git diff --check`: pass

既知の unrelated warning として `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` 警告だけ出ています。

## Review

## 結論

うむ、Checkpoint 190 は **採用** じゃ 👍️
`PressureDiagnosticDecomposition.lean` に five-element bounded decomposition が入り、bounded chain が length 5 まで伸びた。

追加された中心は、

```lean id="sq95ht"
SourcePressureLocalIslandWitnessAdjacentPairInList.five_head_or_tail
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.five_head_or_tail
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.five_iff_pairDiagnostic_or_tail
sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_or_tail_of_noAdjacentOverlap
```

じゃな。head branch は cp189 の named predicate `SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic` を使っており、長い recovered-family 式を再展開していない。任意長 list 分解、aggregation、union accounting、coverage、canonical diagnosis、Collatz convergence には踏み込んでいない。境界管理はよい。

## 実装レビュー

## 1. length-five decomposition は自然

今回の形は、これまでの流れと完全に揃っている。

```text id="39m5qa"
diagnostic [W1,W2,W3,W4,W5]
  ↔ pairDiagnostic W1 W2
     or diagnostic [W2,W3,W4,W5]
```

この一段 head-or-tail 分解は安全じゃ。
長い list を探索しているのではなく、明示された五要素 list を一段だけ開いている。

## 2. named predicate を使ったのが良い

cp189 の成果がすぐ効いている。

以前なら head branch は、

```lean id="6q3vi5"
∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
  let F := ...
  ...
```

という長い形になっていた。
今回は、

```lean id="sc9mj7"
SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W1 W2
```

として読める。

これは今後の bounded decomposition を伸ばすうえで大きい。

## 3. consumer wrapper も正しい

```lean id="zv3ai8"
sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_or_tail_of_noAdjacentOverlap
```

により、

```text id="h8z0cd"
failure [W1,W2,W3,W4,W5]
noAdjacentOverlap [W1,W2,W3,W4,W5]
  -> pairDiagnostic W1 W2
     or diagnostic [W2,W3,W4,W5]
```

が得られた。

これは consumer-facing theorem として十分使いやすい。

## 数学的意味

bounded chain はここまで来た。

```text id="wysob5"
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

length 5:
  diagnostic [W1,W2,W3,W4,W5]
    ↔ pairDiagnostic W1 W2
       or diagnostic [W2,W3,W4,W5]
```

構造がかなり明確じゃ。

```text id="n6luia"
head pair が回収可能か、
そうでなければ tail に diagnostic が保存される。
```

この形は、将来的な list recursion の原型に見える。
ただし、まだ任意長 theorem ではない。そこを急がなかったのがよい。

## 注意点

## 1. そろそろ「次に何を証明したいか」を選ぶ段階

length 2〜5 まで bounded decomposition が揃った。
ここからさらに length 6, 7 と伸ばすことはできるが、同じ型の反復になる。

次は、単に長さを伸ばすより、

```text id="3i5uqc"
この decomposition を何に使うのか
```

を決める方がよい。

たとえば、

```text id="6s7ueq"
failure + noAdjacentOverlap から、
bounded list 内のどこかの pairDiagnostic を得る
```

という consumer theorem が欲しいなら、length-five から tail をさらに分解して、

```text id="lqcb7j"
pairDiagnostic W1 W2
or pairDiagnostic W2 W3
or pairDiagnostic W3 W4
or pairDiagnostic W4 W5
```

へ正規化する bounded theorem が候補になる。

## 2. 任意長 generalization は別設計が必要

今回の report にある通り、任意長 list decomposition にはまだ飛ばない方がよい。

任意長にすると、すぐに次の設計判断が必要になる。

```text id="e5xebp"
最初の diagnostic を選ぶのか
全 diagnostic を列挙するのか
tail recursion で存在だけ返すのか
coverage を仮定するのか
```

ここを曖昧にすると過大主張になりやすい。

## 次の checkpoint 方針

次は **length-five の fully bounded pair-normalization** を推す。

任意長には行かず、五要素限定で tail を完全に開く。

目標は、

```text id="g6lfwl"
diagnostic [W1,W2,W3,W4,W5]
  ->
pairDiagnostic W1 W2
or pairDiagnostic W2 W3
or pairDiagnostic W3 W4
or pairDiagnostic W4 W5
```

じゃ。

これなら bounded theorem のまま、consumer が「どの隣接 pair が回収可能か」を直接使える。
aggregation ではない。列挙でもない。五要素 list の有限分岐を展開するだけじゃ。

## 次の Codex 指示

```text id="l2ot91"
Checkpoint 191: Main root only — fully bounded five-to-pairs normalization.

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
Checkpoint 190 added the length-five one-step bounded decomposition:

- SourcePressureLocalIslandWitnessAdjacentPairInList.five_head_or_tail
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.five_head_or_tail
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.five_iff_pairDiagnostic_or_tail
- sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_or_tail_of_noAdjacentOverlap

Checkpoint 189 added the compact named pair-local branch:

- SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic

Main goal:
For the explicit five-element witness list `[W1, W2, W3, W4, W5]`, add a
fully bounded pair-normalization theorem that expands the tail chain into a
finite disjunction of adjacent pair diagnostics.

This is still bounded to five elements.  Do not add arbitrary-list
decomposition.

Part A: diagnostic five-to-pairs theorem.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.five_pairDiagnostic_cases
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 W4 W5 : SourcePressureLocalIslandWitness n k r}
      (h :
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
          [W1, W2, W3, W4, W5]) :
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W1 W2 ∨
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W2 W3 ∨
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W3 W4 ∨
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W4 W5

Suggested proof:
- apply `h.five_head_or_tail`.
- head branch: return first disjunct.
- tail branch: apply `four_iff_pairDiagnostic_or_tail.mp` or `.four_head_or_tail`
  to the tail diagnostic `[W2,W3,W4,W5]`.
- continue with `three_iff_pairDiagnostic_or_tail` and `two_iff_pairDiagnostic`.
- Keep the disjunction right-associated as written.

Part B: iff form, optional.

Only if easy, prove:

  theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.five_iff_pairDiagnostic_cases
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 W4 W5 : SourcePressureLocalIslandWitness n k r} :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
        [W1, W2, W3, W4, W5] ↔
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W1 W2 ∨
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W2 W3 ∨
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W3 W4 ∨
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W4 W5

Reverse direction:
- first disjunct:
  build `[W1,W2]` diagnostic via `.of_pairDiagnostic_two`,
  then lift with `.of_tail_tail_tail`.
- second disjunct:
  build `[W2,W3]` diagnostic, then lift with `.of_tail_tail`.
- third disjunct:
  build `[W3,W4]` diagnostic, then lift with `.of_tail`.
  Be careful: to place `[W3,W4]` into `[W1,W2,W3,W4,W5]`, it may need two
  lifts depending on how the tail list is represented.
- fourth disjunct:
  build `[W4,W5]` diagnostic and lift through three heads.
  If lift composition is awkward, skip the iff and keep Part A only.

Do not force the iff if the lift bookkeeping is noisy.

Part C: failure + noAdjacentOverlap consumer theorem.

Prove:

  theorem sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_cases_of_noAdjacentOverlap
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 W4 W5 : SourcePressureLocalIslandWitness n k r}
      (h :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
          [W1, W2, W3, W4, W5])
      (hno :
        SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
          [W1, W2, W3, W4, W5]) :
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W1 W2 ∨
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W2 W3 ∨
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W3 W4 ∨
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W4 W5

Suggested proof:
- obtain diagnostic via
  sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
- apply `.five_pairDiagnostic_cases`.

Part D: optional two/three/four pair-cases wrappers.

Only if easy and not too noisy, add analogous pair-cases theorems for length
three and four:

  theorem ...three_pairDiagnostic_cases :
    Diagnostic [W1,W2,W3] ->
      PairDiagnostic W1 W2 ∨ PairDiagnostic W2 W3

  theorem ...four_pairDiagnostic_cases :
    Diagnostic [W1,W2,W3,W4] ->
      PairDiagnostic W1 W2 ∨ PairDiagnostic W2 W3 ∨ PairDiagnostic W3 W4

These may be useful building blocks for Part A.  Prefer proving these first if
they simplify the five-case proof.

Part E: do not introduce arbitrary-list decomposition.

Do not add:
- arbitrary-list recursion;
- list of all diagnostics;
- canonical first diagnosis for arbitrary lists;
- sum over all recovered diagnostics;
- disjointness between multiple recovered families;
- union accounting;
- coverage;
- overlap repair;
- Collatz convergence.

This checkpoint only normalizes a fixed five-element list.

Part F: file-size watch.

Report current line counts for:
- PressureDiagnosticDecomposition.lean
- PressureAdjacentDiagnosis.lean
- PressureLocalWitnessObstruction.lean
- PressureAccounting.lean

Guardrails:
- No aggregation.
- No union accounting.
- No arbitrary-list theorem.
- No global coverage.
- No Collatz convergence.
- Keep all results pair-local and bounded.

Report:
Create:

  docs/dev/das-p2l-260607/review/report-petal-191.md

Include:
- five-to-pairs theorem;
- optional iff theorem if added;
- failure + noAdjacentOverlap consumer theorem;
- optional three/four pair-cases wrappers if added;
- explicit note that this is only a fixed five-element finite disjunction;
- explicit note that no arbitrary-list decomposition, aggregation, union
  accounting, coverage, maximality, uniqueness for arbitrary lists, sorting,
  canonical first diagnosis for arbitrary lists, enumeration beyond this fixed
  finite disjunction, overlap repair, or Collatz convergence was introduced;
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

cp190 は良い。
bounded decomposition は length-five まで来た。

次は任意長に飛ぶのではなく、五要素限定で tail を完全に開いて、

```text id="dc7r1s"
どの隣接 pair が recovered pair diagnostic か
```

を finite disjunction として出すのが良い。

これにより、bounded theorem の実用性が一段上がる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
index 4c081266..f232f711 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
@@ -124,6 +124,24 @@ theorem SourcePressureLocalIslandWitnessAdjacentPairInList.four_head_or_tail
       SourcePressureLocalIslandWitnessAdjacentPairInList [W2, W3, W4] A B :=
   h

+/--
+In a five-element explicit witness list, an adjacent-pair address is either
+the head pair or an adjacent-pair address in the four-element tail.
+
+This is a bounded five-element decomposition only.  It does not enumerate
+diagnostics in arbitrary lists.
+-/
+theorem SourcePressureLocalIslandWitnessAdjacentPairInList.five_head_or_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 W4 W5 A B : SourcePressureLocalIslandWitness n k r}
+    (h :
+      SourcePressureLocalIslandWitnessAdjacentPairInList
+        [W1, W2, W3, W4, W5] A B) :
+    (A = W1 ∧ B = W2) ∨
+      SourcePressureLocalIslandWitnessAdjacentPairInList
+        [W2, W3, W4, W5] A B :=
+  h
+
 set_option linter.style.longLine false in
 /--
 Build the bundled diagnostic directly from a reversed two-witness list.
@@ -434,6 +452,68 @@ theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyD
   exact
     SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_iff_head_or_tail

+set_option linter.style.longLine false in
+/--
+Five-element bounded decomposition for the bundled diagnostic carrier.
+
+A diagnostic on `[W1, W2, W3, W4, W5]` is either carried by the head pair
+`W1, W2`, or it is already a diagnostic on the four-element tail
+`[W2, W3, W4, W5]`.  The head branch uses the named pair-local recovered
+predicate introduced for API compression.
+
+This theorem only decomposes the explicit five-element list; it does not
+enumerate diagnostics in arbitrary lists.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.five_head_or_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 W4 W5 : SourcePressureLocalIslandWitness n k r}
+    (h :
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        [W1, W2, W3, W4, W5]) :
+    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+      W1 W2 ∨
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        [W2, W3, W4, W5] := by
+  rcases h.exists_pair with ⟨A, B, hin, hrev, hbudget, hneg, hlen⟩
+  rcases SourcePressureLocalIslandWitnessAdjacentPairInList.five_head_or_tail
+      hin with hhead | htail
+  · rcases hhead with ⟨rfl, rfl⟩
+    exact Or.inl ⟨hrev, hbudget, hneg, hlen⟩
+  · exact Or.inr
+      (SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
+        htail hrev hbudget hneg hlen)
+
+set_option linter.style.longLine false in
+/--
+Iff form of the five-element diagnostic decomposition.
+
+The reverse direction either builds the head-pair diagnostic directly from the
+named pair-local recovered branch, or lifts an existing tail diagnostic.  This
+is still bounded to `[W1, W2, W3, W4, W5]`.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.five_iff_pairDiagnostic_or_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 W4 W5 : SourcePressureLocalIslandWitness n k r} :
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+      [W1, W2, W3, W4, W5] ↔
+    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+      W1 W2 ∨
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        [W2, W3, W4, W5] := by
+  constructor
+  · exact
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.five_head_or_tail
+  · intro h
+    rcases h with hhead | htail
+    · rcases hhead with ⟨hrev, hbudget, hneg, hlen⟩
+      exact
+        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
+          SourcePressureLocalIslandWitnessAdjacentPairInList.head
+          hrev hbudget hneg hlen
+    · exact
+        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail
+          htail
+
 set_option linter.style.longLine false in
 /--
 Two-element consumer form: failure plus named no-adjacent-overlap yields the
@@ -594,4 +674,29 @@ theorem
   sourcePressureLocalIslandWitnessList_failure_four_diagnostic_head_or_tail_of_noAdjacentOverlap
     h hno

+set_option linter.style.longLine false in
+/--
+Five-element consumer form: failure plus named no-adjacent-overlap yields
+either the head-pair recovered branch or a diagnostic on the four-element tail.
+
+This remains a bounded decomposition for `[W1, W2, W3, W4, W5]`; it does not
+enumerate or aggregate diagnostics in longer lists.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_or_tail_of_noAdjacentOverlap
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 W4 W5 : SourcePressureLocalIslandWitness n k r}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        [W1, W2, W3, W4, W5])
+    (hno :
+      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
+        [W1, W2, W3, W4, W5]) :
+    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+      W1 W2 ∨
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        [W2, W3, W4, W5] :=
+  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
+    h hno).five_head_or_tail
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-190.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-190.md
new file mode 100644
index 00000000..4cc5fb94
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-190.md
@@ -0,0 +1,161 @@
+# Report Petal 190
+
+## Checkpoint
+
+Checkpoint 190 extended the bounded diagnostic decomposition layer to the
+explicit five-witness list case.
+
+Primary file:
+
+- `DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean`
+
+No other Lean source file was changed.
+
+## Implemented
+
+### Adjacent-pair length-five head-or-tail theorem
+
+Added:
+
+```lean
+theorem SourcePressureLocalIslandWitnessAdjacentPairInList.five_head_or_tail
+```
+
+For an adjacent-pair address in `[W1, W2, W3, W4, W5]`, this theorem says the
+address is either the head pair `W1, W2` or an adjacent-pair address in the
+tail `[W2, W3, W4, W5]`.
+
+This is only the bounded five-element address decomposition.
+
+### Diagnostic length-five head-or-tail theorem
+
+Added:
+
+```lean
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.five_head_or_tail
+```
+
+For a recovered adjacent accounted-family diagnostic on
+`[W1, W2, W3, W4, W5]`, this theorem returns either:
+
+- `SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W1 W2`;
+- or a diagnostic on the tail `[W2, W3, W4, W5]`.
+
+The head branch uses the named pair-local predicate from checkpoint 189 instead
+of repeating the long recovered-family expression.
+
+### Compact length-five iff theorem
+
+Added:
+
+```lean
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.five_iff_pairDiagnostic_or_tail
+```
+
+This is the iff form of the one-step five-element decomposition:
+
+```text
+diagnostic [W1, W2, W3, W4, W5]
+  iff
+pair diagnostic W1 W2
+  or
+diagnostic [W2, W3, W4, W5]
+```
+
+The reverse direction builds the head-pair diagnostic directly with `of_pair`
+or lifts the tail diagnostic with `of_tail`.
+
+### Failure + noAdjacentOverlap consumer wrapper
+
+Added:
+
+```lean
+theorem sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_or_tail_of_noAdjacentOverlap
+```
+
+This combines the existing failure plus no-adjacent-overlap theorem with the new
+five-element decomposition.
+
+## Guardrails
+
+This checkpoint is only a five-element explicit-list bounded decomposition.
+
+It did not introduce:
+
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
+Recovered budgets remain pair-local, and the new theorem surface keeps the same
+head-pair-or-tail shape used by the existing three/four bounded API.
+
+## File Size Watch
+
+Current line counts:
+
+```text
+   702 lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
+  1356 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+  1391 lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
+  1896 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+  5345 total
+```
+
+`PressureDiagnosticDecomposition.lean` remains well below the 2,000-line split
+threshold.  No refactor was needed in this checkpoint.
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
+The bounded chain now reaches five elements with the stable shape:
+
+```text
+head pair branch = named pair-local diagnostic
+tail branch = remaining bounded diagnostic
+```
+
+The next safe step would be another bounded theorem only if a concrete consumer
+needs it.  A general arbitrary-list decomposition should remain a separate
+design checkpoint because it would require a clear policy for canonical choice,
+enumeration, or list recursion without overclaiming coverage.
````
`````
