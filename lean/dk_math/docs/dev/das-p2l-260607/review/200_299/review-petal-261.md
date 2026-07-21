# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: d3d29f5ebe78f1290f57195349310d9692ddc45e

## Report

実装完了です。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:841) に named state を追加しました。

追加:

- `def SourcePressureForwardBoxComparisonState`
- `SourcePressureForwardBoxComparisonState.box`
- `SourcePressureForwardBoxComparisonState.val_lt`
- `SourcePressureForwardBoxComparisonState.not_reverse_box`
- `SourcePressureOrientedNeighborBoxState.to_forwardComparisonState_of_sorted`

さらに named split wrapper も追加しました。

- `sourcePressureFailureResolutionState_to_forwardBoxComparisonState_or_pairOverlap`
- `sourcePressureSortedFailureState_to_forwardBoxComparisonState_or_pairOverlap`
- `sourcePressureBeamSeedState_to_forwardBoxComparisonState_or_pairOverlap`

これで表面はこうなりました。

```text
FailureResolution + sorted(L)
  -> ForwardBoxComparisonState ∨ PairOverlapObstruction

SortedFailure + sorted(L)
  -> ForwardBoxComparisonState ∨ PairOverlapObstruction

BeamSeed + sorted(L)
  -> ForwardBoxComparisonState ∨ PairOverlapObstruction
```

レポート:
[report-petal-261.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-261.md)

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureState` 成功
- `lake build DkMath.Collatz.PetalBridge` 成功
- `git diff --check` 成功

差分は `PressureState.lean` と `report-petal-261.md` です。

## Review

## 判定

採用。
`ForwardBoxComparisonState` が名前付き状態として固定された。

追加：

```lean id="so1jgr"
def SourcePressureForwardBoxComparisonState
```

projection：

```lean id="mwbk6f"
SourcePressureForwardBoxComparisonState.box
SourcePressureForwardBoxComparisonState.val_lt
SourcePressureForwardBoxComparisonState.not_reverse_box
```

constructor：

```lean id="k0vxgj"
SourcePressureOrientedNeighborBoxState.to_forwardComparisonState_of_sorted
```

named split：

```lean id="w5kxx9"
sourcePressureFailureResolutionState_to_forwardBoxComparisonState_or_pairOverlap
sourcePressureSortedFailureState_to_forwardBoxComparisonState_or_pairOverlap
sourcePressureBeamSeedState_to_forwardBoxComparisonState_or_pairOverlap
```

これで表面が、

```text id="b0skm5"
S/R/B + sorted(L)
  -> ForwardBoxComparisonState ∨ PairOverlapObstruction
```

として読めるようになった。

## 増えた事実

これまで raw conjunction だった branch：

```lean id="tb6zw5"
SourcePressureOrientedNeighborBoxState L W W' ∧
  W.val < W'.val ∧
    ¬ SourcePressureOrientedNeighborBoxState L W' W
```

が、名前付き状態になった。

```lean id="iqhjad"
SourcePressureForwardBoxComparisonState L W W'
```

これは次段の theorem signature をかなり短くできる。

## 現在の状態表

```text id="j623f4"
SortedFailure + sorted(L)
  -> ForwardBoxComparisonState ∨ PairOverlapObstruction

FailureResolution + sorted(L)
  -> ForwardBoxComparisonState ∨ PairOverlapObstruction

BeamSeed + sorted(L)
  -> ForwardBoxComparisonState ∨ PairOverlapObstruction
```

`ForwardBoxComparisonState` 側は、

```text id="feb09f"
Box(W,W')
W.val < W'.val
¬ Box(W',W)
```

を持つ。
`PairOverlapObstruction` 側は、明示的な隣接 pair obstruction として残る。

## 次に攻める定理

次は `ForwardBoxComparisonState` の projection をもう少し caller-facing に広げる。

すでに `.box`, `.val_lt`, `.not_reverse_box` はある。
次に欲しいのは、box 経由でよく使うものを直接出す projection。

候補：

```lean id="g8ufz6"
SourcePressureForwardBoxComparisonState.left_box
SourcePressureForwardBoxComparisonState.right_box
SourcePressureForwardBoxComparisonState.adjacentPair
SourcePressureForwardBoxComparisonState.left_mem
SourcePressureForwardBoxComparisonState.right_mem
```

特に pair-comparison 層では `adjacentPair`, `left_mem`, `right_mem` が効く。

## Codex 指示

```text id="o8vchh"
Goal:
  Add convenience projections from SourcePressureForwardBoxComparisonState.

Add in PressureState.lean:

  theorem SourcePressureForwardBoxComparisonState.left_box
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardBoxComparisonState L W W') :
      SourcePressureBeamCenteredLocalPulseBox n k r L W

  theorem SourcePressureForwardBoxComparisonState.right_box
      ... :
      SourcePressureBeamCenteredLocalPulseBox n k r L W'

  theorem SourcePressureForwardBoxComparisonState.adjacentPair
      ... :
      SourcePressureLocalIslandWitnessAdjacentPairInList L W W'

  theorem SourcePressureForwardBoxComparisonState.left_mem
      ... :
      W ∈ L

  theorem SourcePressureForwardBoxComparisonState.right_mem
      ... :
      W' ∈ L

Use:
  h.box.left_box
  h.box.right_box
  h.box.adjacentPair
  h.box.left_mem
  h.box.right_mem

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

次で `ForwardBoxComparisonState` が、pair-comparison 層の入力として完成する。

```text id="j6j8ay"
FBC
  -> Box
  -> left/right pulse boxes
  -> AdjacentPairInList
  -> W ∈ L, W' ∈ L
  -> W.val < W'.val
  -> not reverse Box
```

その次に、`FBC ∨ PO` を入力にした本当の pair-comparison theorem へ進める。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 5289fd3c..9544e9fd 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -826,6 +826,70 @@ theorem SourcePressureOrientedNeighborBoxState.not_reverse_box_of_sorted
   exact hbox.not_val_ge_of_sorted hsorted
     (hrev.val_le_of_sorted hsorted)

+/--
+Named state for the forward comparison branch of a two-endpoint box.
+
+This packages the exact payload produced under sortedness:
+
+* the oriented neighbor box itself;
+* the forward native depth comparison `W.val < W'.val`;
+* exclusion of the reverse box orientation.
+
+It is a local pair-comparison state, not a canonical-pair selector and not a
+global coverage statement.
+-/
+def SourcePressureForwardBoxComparisonState
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (W W' : SourcePressureLocalIslandWitness n k r) : Prop :=
+  SourcePressureOrientedNeighborBoxState L W W' ∧
+    W.val < W'.val ∧
+      ¬ SourcePressureOrientedNeighborBoxState L W' W
+
+/-- Project the underlying oriented neighbor box from a forward comparison state. -/
+theorem SourcePressureForwardBoxComparisonState.box
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardBoxComparisonState L W W') :
+    SourcePressureOrientedNeighborBoxState L W W' :=
+  h.1
+
+/-- Project the forward value comparison from a forward comparison state. -/
+theorem SourcePressureForwardBoxComparisonState.val_lt
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardBoxComparisonState L W W') :
+    W.val < W'.val :=
+  h.2.1
+
+/-- Project reverse-box exclusion from a forward comparison state. -/
+theorem SourcePressureForwardBoxComparisonState.not_reverse_box
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardBoxComparisonState L W W') :
+    ¬ SourcePressureOrientedNeighborBoxState L W' W :=
+  h.2.2
+
+/--
+Constructor from a sorted oriented neighbor box to the named forward comparison
+state.
+
+The sortedness hypothesis is where the value comparison and reverse-orientation
+exclusion enter; the box alone intentionally remains weaker.
+-/
+theorem SourcePressureOrientedNeighborBoxState.to_forwardComparisonState_of_sorted
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hbox : SourcePressureOrientedNeighborBoxState L W W')
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    SourcePressureForwardBoxComparisonState L W W' :=
+  ⟨hbox, hbox.val_lt_of_sorted hsorted,
+    hbox.not_reverse_box_of_sorted hsorted⟩
+
 /--
 Package an oriented neighbor diagnostic into the two-endpoint box state.

@@ -1205,4 +1269,67 @@ theorem sourcePressureBeamSeedState_to_forwardBoxComparison_or_pairOverlap
   sourcePressureFailureResolutionState_to_forwardBoxComparison_or_pairOverlap
     hsorted (sourcePressureBeamSeedState_to_failureResolutionState h)

+/--
+Failure resolution reaches the named forward-comparison state or a concrete
+pair-overlap obstruction.
+
+This is the named-state wrapper over
+`sourcePressureFailureResolutionState_to_forwardBoxComparison_or_pairOverlap`.
+It removes tuple noise for callers that want to pass the forward branch into a
+pair-comparison theorem as one state object.
+-/
+theorem sourcePressureFailureResolutionState_to_forwardBoxComparisonState_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (h : SourcePressureFailureResolutionState L) :
+    (∃ W W',
+      SourcePressureForwardBoxComparisonState L W W') ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B := by
+  rcases
+    sourcePressureFailureResolutionState_to_forwardBoxComparison_or_pairOverlap
+      hsorted h with hforward | hoverlap
+  · rcases hforward with ⟨W, W', hbox, hlt, hnrev⟩
+    exact Or.inl ⟨W, W', hbox, hlt, hnrev⟩
+  · exact Or.inr hoverlap
+
+/--
+Sorted failure reaches the named forward-comparison state or a concrete
+pair-overlap obstruction.
+-/
+theorem sourcePressureSortedFailureState_to_forwardBoxComparisonState_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (h : SourcePressureSortedFailureState L) :
+    (∃ W W',
+      SourcePressureForwardBoxComparisonState L W W') ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
+  sourcePressureFailureResolutionState_to_forwardBoxComparisonState_or_pairOverlap
+    hsorted (sourcePressureSortedFailureState_to_failureResolutionState h)
+
+/--
+Beam seed reaches the named forward-comparison state or a concrete pair-overlap
+obstruction.
+
+This is the Beam-facing named split that later pair-comparison layers should
+prefer over the raw tuple form.
+-/
+theorem sourcePressureBeamSeedState_to_forwardBoxComparisonState_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (h : SourcePressureBeamSeedState L) :
+    (∃ W W',
+      SourcePressureForwardBoxComparisonState L W W') ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
+  sourcePressureFailureResolutionState_to_forwardBoxComparisonState_or_pairOverlap
+    hsorted (sourcePressureBeamSeedState_to_failureResolutionState h)
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-261.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-261.md
new file mode 100644
index 00000000..e58327cd
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-261.md
@@ -0,0 +1,118 @@
+# Report: petal-261
+
+## Goal
+
+Package the forward box comparison branch into a named predicate and expose
+named split wrappers.
+
+Desired surface:
+
+```text
+S/R/B + sorted(L)
+  -> ForwardBoxComparisonState or PairOverlapObstruction
+```
+
+## Implemented
+
+Added in `DkMath.Collatz.PetalBridge.PressureState`:
+
+```lean
+def SourcePressureForwardBoxComparisonState
+```
+
+The state packages:
+
+```lean
+SourcePressureOrientedNeighborBoxState L W W'
+W.val < W'.val
+not SourcePressureOrientedNeighborBoxState L W' W
+```
+
+Projection lemmas:
+
+```lean
+theorem SourcePressureForwardBoxComparisonState.box
+theorem SourcePressureForwardBoxComparisonState.val_lt
+theorem SourcePressureForwardBoxComparisonState.not_reverse_box
+```
+
+Constructor:
+
+```lean
+theorem SourcePressureOrientedNeighborBoxState.to_forwardComparisonState_of_sorted
+```
+
+Named split wrappers:
+
+```lean
+theorem sourcePressureFailureResolutionState_to_forwardBoxComparisonState_or_pairOverlap
+theorem sourcePressureSortedFailureState_to_forwardBoxComparisonState_or_pairOverlap
+theorem sourcePressureBeamSeedState_to_forwardBoxComparisonState_or_pairOverlap
+```
+
+## Meaning
+
+The forward comparison branch no longer has to be passed around as a raw nested
+conjunction.  It now has a stable state name:
+
+```lean
+SourcePressureForwardBoxComparisonState L W W'
+```
+
+This makes the next pair-comparison layer cleaner.  It can consume one named
+state for the forward branch and leave the pair-overlap branch as the explicit
+obstruction branch.
+
+## Guardrails
+
+The new state is only a packaging layer.  It does not add a new global
+mathematical claim.
+
+In particular, it does not:
+
+* select a canonical pair;
+* assert global coverage;
+* repair overlaps;
+* propagate local diagnostics;
+* prove convergence.
+
+The constructor from an oriented box still requires sortedness explicitly.
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
+The next layer can now define a pair-comparison theorem that consumes:
+
+```lean
+SourcePressureForwardBoxComparisonState L W W'
+```
+
+and keeps the obstruction side as:
+
+```lean
+SourcePressureLocalIslandWitnessPairOverlapObstruction A B
+```
+
+Candidate direction:
+
+```text
+ForwardBoxComparisonState
+  -> pair-comparison-facing local order facts
+
+PairOverlapObstruction
+  -> obstruction-facing branch
+```
+
+The named state should reduce theorem signatures in the next checkpoint.
````
`````
