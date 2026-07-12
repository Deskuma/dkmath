# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 67c8190459097d830cba11143e07924d8a78cc6a

## Report

実装完了です。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:1136) に、comparison-ready split を追加しました。

追加 theorem:

- `sourcePressureFailureResolutionState_to_forwardBoxComparison_or_pairOverlap`
- `sourcePressureSortedFailureState_to_forwardBoxComparison_or_pairOverlap`
- `sourcePressureBeamSeedState_to_forwardBoxComparison_or_pairOverlap`

これで狙いの形が揃いました。

```text
FailureResolution + sorted(L)
  -> ForwardBoxComparison ∨ PairOverlapObstruction

SortedFailure + sorted(L)
  -> ForwardBoxComparison ∨ PairOverlapObstruction

BeamSeed + sorted(L)
  -> ForwardBoxComparison ∨ PairOverlapObstruction
```

`Box` 側には以下が入ります。

```text
Box(W,W')
W.val < W'.val
¬ Box(W',W)
```

`PairOverlap` 側は、既存の adjacent pair obstruction をそのまま保持します。

レポート:
[report-petal-260.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-260.md)

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureState` 成功
- `lake build DkMath.Collatz.PetalBridge` 成功
- `git diff --check` 成功

差分は `PressureState.lean` と `report-petal-260.md` です。

## Review

## 判定

採用。
`Box ∨ PO` が **comparison-ready split** まで上がった。

追加：

```lean id="0koh4b"
sourcePressureFailureResolutionState_to_forwardBoxComparison_or_pairOverlap
sourcePressureSortedFailureState_to_forwardBoxComparison_or_pairOverlap
sourcePressureBeamSeedState_to_forwardBoxComparison_or_pairOverlap
```

これで三入口すべてが揃った。

```text id="gnbnar"
FailureResolution + sorted(L) -> ForwardBoxComparison ∨ PairOverlapObstruction
SortedFailure     + sorted(L) -> ForwardBoxComparison ∨ PairOverlapObstruction
BeamSeed          + sorted(L) -> ForwardBoxComparison ∨ PairOverlapObstruction
```

`Box` 側には `Box(W,W')`, `W.val < W'.val`, `¬ Box(W',W)` が入り、`PO` 側は concrete adjacent pair obstruction のまま保持されている。良い分岐面じゃ。

## 増えた事実

状態表はここまで来た。

```text id="dkubgs"
S/R/B + sorted(L)
  -> ForwardBoxComparison
   ∨ PairOverlapObstruction
```

`ForwardBoxComparison` 側は、

```text id="5295pq"
Box(W,W')
W.val < W'.val
¬ Box(W',W)
```

を持つ。つまり、sorted list 上では forward orientation が確定し、reverse box は排除済み。

## 次に攻める定理

次は、この長い branch を predicate 化するのがよい。

今の theorem は中身が長いので、次段 caller が毎回、

```lean id="n2h7my"
SourcePressureOrientedNeighborBoxState L W W' ∧
  W.val < W'.val ∧
    ¬ SourcePressureOrientedNeighborBoxState L W' W
```

を直接扱うことになる。ここを名前にする。

狙い：

```lean id="ytrtlu"
def SourcePressureForwardBoxComparisonState
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (W W' : SourcePressureLocalIslandWitness n k r) : Prop :=
  SourcePressureOrientedNeighborBoxState L W W' ∧
    W.val < W'.val ∧
      ¬ SourcePressureOrientedNeighborBoxState L W' W
```

そして constructor：

```lean id="f1gi0j"
theorem SourcePressureOrientedNeighborBoxState.to_forwardComparisonState_of_sorted
```

さらに既存 theorem の named 版：

```lean id="z8fa6d"
sourcePressureFailureResolutionState_to_forwardBoxComparisonState_or_pairOverlap
sourcePressureSortedFailureState_to_forwardBoxComparisonState_or_pairOverlap
sourcePressureBeamSeedState_to_forwardBoxComparisonState_or_pairOverlap
```

これで状態表が、

```text id="r5t5h0"
S/R/B + sorted(L)
  -> FBC ∨ PO
```

として読める。

## Codex 指示

```text id="y1i4jz"
Goal:
  Package the forward box comparison branch into a named predicate.

Add in PressureState.lean:

  def SourcePressureForwardBoxComparisonState
      {n : OddNat} {k r : ℕ}
      (L : List (SourcePressureLocalIslandWitness n k r))
      (W W' : SourcePressureLocalIslandWitness n k r) : Prop :=
    SourcePressureOrientedNeighborBoxState L W W' ∧
      W.val < W'.val ∧
        ¬ SourcePressureOrientedNeighborBoxState L W' W

Add projection lemmas if useful:

  SourcePressureForwardBoxComparisonState.box
  SourcePressureForwardBoxComparisonState.val_lt
  SourcePressureForwardBoxComparisonState.not_reverse_box

Add constructor:

  theorem SourcePressureOrientedNeighborBoxState.to_forwardComparisonState_of_sorted
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (hbox : SourcePressureOrientedNeighborBoxState L W W')
      (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
      SourcePressureForwardBoxComparisonState L W W'

Then add named split wrappers:

  sourcePressureFailureResolutionState_to_forwardBoxComparisonState_or_pairOverlap
  sourcePressureSortedFailureState_to_forwardBoxComparisonState_or_pairOverlap
  sourcePressureBeamSeedState_to_forwardBoxComparisonState_or_pairOverlap

Use existing:
  sourcePressureFailureResolutionState_to_forwardBoxComparison_or_pairOverlap
  sourcePressureSortedFailureState_to_forwardBoxComparison_or_pairOverlap
  sourcePressureBeamSeedState_to_forwardBoxComparison_or_pairOverlap

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

次で状態名が揃う。

```text id="cw3fjf"
S/R/B + sorted(L)
  -> ForwardBoxComparisonState ∨ PairOverlapObstruction
```

その後は `ForwardBoxComparisonState` を pair-comparison 層の入力にして、`PO` 側は obstruction branch として分離処理する。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 0f7d29fd..5289fd3c 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -1117,4 +1117,92 @@ theorem sourcePressureBeamSeedState_to_orientedNeighborBox_or_pairOverlap
   sourcePressureFailureResolutionState_to_orientedNeighborBox_or_pairOverlap
     (sourcePressureBeamSeedState_to_failureResolutionState h)
 
+/--
+Failure resolution reaches a comparison-ready split under sortedness.
+
+The boxed branch is strengthened from a raw two-endpoint box to a forward
+comparison package:
+
+```text
+Box(W,W') + sorted(L)
+  -> W.val < W'.val
+  -> not Box(W',W)
+```
+
+The pair-overlap obstruction branch is left unchanged.  This theorem is a
+local routing surface for the next comparison layer; it does not repair
+overlap, choose a canonical pair, or assert global coverage.
+-/
+theorem sourcePressureFailureResolutionState_to_forwardBoxComparison_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (h : SourcePressureFailureResolutionState L) :
+    (∃ W W',
+      SourcePressureOrientedNeighborBoxState L W W' ∧
+        W.val < W'.val ∧
+          ¬ SourcePressureOrientedNeighborBoxState L W' W) ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B := by
+  rcases
+    sourcePressureFailureResolutionState_to_orientedNeighborBox_or_pairOverlap h
+      with hbox | hoverlap
+  · rcases hbox with ⟨W, W', hbox⟩
+    exact Or.inl
+      ⟨W, W', hbox, hbox.val_lt_of_sorted hsorted,
+        hbox.not_reverse_box_of_sorted hsorted⟩
+  · exact Or.inr hoverlap
+
+/--
+Sorted failure reaches the comparison-ready boxed/overlap split.
+
+This is the sorted-failure entry point for the same forward-comparison surface
+provided by
+`sourcePressureFailureResolutionState_to_forwardBoxComparison_or_pairOverlap`.
+-/
+theorem sourcePressureSortedFailureState_to_forwardBoxComparison_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (h : SourcePressureSortedFailureState L) :
+    (∃ W W',
+      SourcePressureOrientedNeighborBoxState L W W' ∧
+        W.val < W'.val ∧
+          ¬ SourcePressureOrientedNeighborBoxState L W' W) ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
+  sourcePressureFailureResolutionState_to_forwardBoxComparison_or_pairOverlap
+    hsorted (sourcePressureSortedFailureState_to_failureResolutionState h)
+
+/--
+Beam seed reaches the comparison-ready boxed/overlap split.
+
+This is the Beam-facing entry point:
+
+```text
+BeamSeed + sorted(L)
+  -> ForwardBoxComparison
+   ∨ PairOverlapObstruction
+```
+
+The sortedness hypothesis is explicit because the forward value comparison is
+not a consequence of the seed state alone.
+-/
+theorem sourcePressureBeamSeedState_to_forwardBoxComparison_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (h : SourcePressureBeamSeedState L) :
+    (∃ W W',
+      SourcePressureOrientedNeighborBoxState L W W' ∧
+        W.val < W'.val ∧
+          ¬ SourcePressureOrientedNeighborBoxState L W' W) ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
+  sourcePressureFailureResolutionState_to_forwardBoxComparison_or_pairOverlap
+    hsorted (sourcePressureBeamSeedState_to_failureResolutionState h)
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-260.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-260.md
new file mode 100644
index 00000000..df7f9dd6
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-260.md
@@ -0,0 +1,103 @@
+# Report: petal-260
+
+## Goal
+
+Lift the existing boxed diagnostic / pair-overlap obstruction split into a
+comparison-ready split under sortedness.
+
+Target shape:
+
+```text
+FailureResolution + sorted(L)
+  -> ForwardBoxComparison or PairOverlapObstruction
+```
+
+with wrappers for `SortedFailureState` and `BeamSeedState` if they close
+cleanly.
+
+## Implemented
+
+Added in `DkMath.Collatz.PetalBridge.PressureState`:
+
+```lean
+theorem sourcePressureFailureResolutionState_to_forwardBoxComparison_or_pairOverlap
+theorem sourcePressureSortedFailureState_to_forwardBoxComparison_or_pairOverlap
+theorem sourcePressureBeamSeedState_to_forwardBoxComparison_or_pairOverlap
+```
+
+The boxed branch now carries:
+
+```lean
+SourcePressureOrientedNeighborBoxState L W W'
+W.val < W'.val
+not SourcePressureOrientedNeighborBoxState L W' W
+```
+
+The obstruction branch remains unchanged:
+
+```lean
+exists A B,
+  SourcePressureLocalIslandWitnessAdjacentPairInList L A B
+    and SourcePressureLocalIslandWitnessPairOverlapObstruction A B
+```
+
+## Meaning
+
+The state ladder now has comparison-ready public surfaces:
+
+```text
+FailureResolution + sorted(L)
+  -> ForwardBoxComparison or PairOverlapObstruction
+
+SortedFailure + sorted(L)
+  -> ForwardBoxComparison or PairOverlapObstruction
+
+BeamSeed + sorted(L)
+  -> ForwardBoxComparison or PairOverlapObstruction
+```
+
+This separates the two downstream cases cleanly:
+
+* `Box` side: forward value order is fixed and reverse box orientation is
+  impossible.
+* `PairOverlap` side: the local obstruction is preserved as an explicit
+  adjacent-pair obstruction.
+
+## Guardrails
+
+The sortedness hypothesis is explicit because the forward value comparison is
+not a consequence of failure resolution, sorted failure, or Beam seed alone.
+
+These theorems do not repair overlaps, do not choose a canonical adjacent pair,
+do not prove list coverage, and do not propagate the local comparison beyond
+the two witnesses.
+
+## Verification
+
+Commands run from `lean/dk_math`:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureState
+lake build DkMath.Collatz.PetalBridge
+```
+
+Both builds completed successfully.
+
+`git diff --check` is run as the final whitespace gate.
+
+## Next Branch Prediction
+
+The comparison-ready split is now ready to be consumed by the pair-comparison
+layer.
+
+Natural next theorem shape:
+
+```text
+BeamSeed + sorted(L)
+  -> forward comparison data or explicit overlap obstruction
+  -> caller-specific pair comparison surface
+```
+
+If a caller only needs the forward branch, it should consume the boxed branch
+directly.  If it needs total case analysis, it should keep the pair-overlap
+obstruction separate instead of coercing it into a diagnostic branch.
````
`````
