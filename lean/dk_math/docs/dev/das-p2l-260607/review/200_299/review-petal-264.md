# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 1446bef83c1d9ff238edf03e42d3ce605078ebf0

## Report

実装完了です。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:1479) に、次の 3 本を追加しました。

- `sourcePressureFailureResolutionState_to_forwardPairComparisonState_or_pairOverlap`
- `sourcePressureSortedFailureState_to_forwardPairComparisonState_or_pairOverlap`
- `sourcePressureBeamSeedState_to_forwardPairComparisonState_or_pairOverlap`

これで `FailureResolution / SortedFailure / BeamSeed + sorted(L)` から、`ForwardPairComparisonState ∨ PairOverlapObstruction` へ直接入れる表面が揃いました。レポートは [report-petal-264.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-264.md:1) に追加しています。

検証済みです。

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

すべて通過しました。

## Review

## 判定

採用。
`ForwardPairComparisonState ∨ PairOverlapObstruction` まで、三入口すべてから直通になった。

追加：

```lean id="v3tx0v"
sourcePressureFailureResolutionState_to_forwardPairComparisonState_or_pairOverlap
sourcePressureSortedFailureState_to_forwardPairComparisonState_or_pairOverlap
sourcePressureBeamSeedState_to_forwardPairComparisonState_or_pairOverlap
```

これで表面はこう。

```text id="w0j79k"
FailureResolution + sorted(L) -> ForwardPairComparisonState ∨ PairOverlapObstruction
SortedFailure     + sorted(L) -> ForwardPairComparisonState ∨ PairOverlapObstruction
BeamSeed          + sorted(L) -> ForwardPairComparisonState ∨ PairOverlapObstruction
```

`ForwardBoxComparisonState` 側を `to_pairComparisonState` で持ち上げ、overlap 側はそのまま保持。狙い通りじゃ。

## 増えた事実

pair-comparison 層の入口が完成した。

これまで：

```text id="xpkygb"
S/R/B + sorted(L)
  -> FBC ∨ PO
```

今回：

```text id="a1yghb"
S/R/B + sorted(L)
  -> FPC ∨ PO
```

`FPC` 側には、すでに以下が入っている。

```text id="sc8a9u"
ForwardBoxComparisonState
AdjacentPairInList
left centered pulse box
right centered pulse box
W.val < W'.val
¬ reverse Box
```

つまり、正向き比較 branch と obstruction branch が分離されたまま、pair-comparison 入力として使える状態になった。

## 現在の状態表

```text id="u16ik7"
SortedFailure + sorted(L)
  -> ForwardPairComparisonState ∨ PairOverlapObstruction

FailureResolution + sorted(L)
  -> ForwardPairComparisonState ∨ PairOverlapObstruction

BeamSeed + sorted(L)
  -> ForwardPairComparisonState ∨ PairOverlapObstruction
```

これは綺麗。
`PressureState` はここで一つ大きな節目に到達している。

## 次に攻める定理

次は `ForwardPairComparisonState` から sign/box payload を直接投影する。

まず小さく：

```lean id="dazqdb"
SourcePressureForwardPairComparisonState.left_mem
SourcePressureForwardPairComparisonState.right_mem
```

次に signs：

```lean id="bhc81u"
SourcePressureForwardPairComparisonState.left_signs
SourcePressureForwardPairComparisonState.right_signs
```

`left_signs/right_signs` は、`left_box/right_box` から `SourcePressureBeamCenteredLocalPulseBox.signs` を使えるはず。

形：

```lean id="nc9j8m"
theorem SourcePressureForwardPairComparisonState.left_signs
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    W ∈ L ∧
      SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
        0 < SourcePressureMarginInt n k (r + W.val) ∧
          SourcePressureBeamAddressedDepthTarget L W.val ∧
            SourcePressureMarginInt n k (r + W.val + 1) ≤ 0
```

右も同型。

## Codex 指示

```text id="zgqmpm"
Goal:
  Add caller-facing projections from SourcePressureForwardPairComparisonState.

Add in PressureState.lean:

  theorem SourcePressureForwardPairComparisonState.left_mem
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W') :
      W ∈ L

  theorem SourcePressureForwardPairComparisonState.right_mem
      ... :
      W' ∈ L

  theorem SourcePressureForwardPairComparisonState.left_signs
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W') :
      W ∈ L ∧
        SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
          0 < SourcePressureMarginInt n k (r + W.val) ∧
            SourcePressureBeamAddressedDepthTarget L W.val ∧
              SourcePressureMarginInt n k (r + W.val + 1) ≤ 0

  theorem SourcePressureForwardPairComparisonState.right_signs
      ... :
      W' ∈ L ∧
        SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
          0 < SourcePressureMarginInt n k (r + W'.val) ∧
            SourcePressureBeamAddressedDepthTarget L W'.val ∧
              SourcePressureMarginInt n k (r + W'.val + 1) ≤ 0

Use:
  h.left_box
  h.right_box
  SourcePressureBeamCenteredLocalPulseBox.signs

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

次で `FPC` からこれが直に取れる。

```text id="0n0g9i"
FPC
  -> left signs
  -> right signs
  -> W.val < W'.val
  -> adjacent pair
```

そこまで整えたら、左右 pulse の「正の中心が並ぶ」比較補題へ入れる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 96e8f5d2..ac4bbc57 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -1468,4 +1468,68 @@ theorem sourcePressureBeamSeedState_to_forwardBoxComparisonState_or_pairOverlap
   sourcePressureFailureResolutionState_to_forwardBoxComparisonState_or_pairOverlap
     hsorted (sourcePressureBeamSeedState_to_failureResolutionState h)
 
+/--
+Failure resolution reaches the forward pair-comparison state or a concrete
+pair-overlap obstruction.
+
+This is the pair-comparison-facing lift of
+`sourcePressureFailureResolutionState_to_forwardBoxComparisonState_or_pairOverlap`.
+The forward branch is converted by
+`SourcePressureForwardBoxComparisonState.to_pairComparisonState`; the
+obstruction branch is unchanged.
+-/
+theorem sourcePressureFailureResolutionState_to_forwardPairComparisonState_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (h : SourcePressureFailureResolutionState L) :
+    (∃ W W',
+      SourcePressureForwardPairComparisonState L W W') ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B := by
+  rcases
+    sourcePressureFailureResolutionState_to_forwardBoxComparisonState_or_pairOverlap
+      hsorted h with hforward | hoverlap
+  · rcases hforward with ⟨W, W', hFBC⟩
+    exact Or.inl ⟨W, W', hFBC.to_pairComparisonState⟩
+  · exact Or.inr hoverlap
+
+/--
+Sorted failure reaches the forward pair-comparison state or a concrete
+pair-overlap obstruction.
+-/
+theorem sourcePressureSortedFailureState_to_forwardPairComparisonState_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (h : SourcePressureSortedFailureState L) :
+    (∃ W W',
+      SourcePressureForwardPairComparisonState L W W') ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
+  sourcePressureFailureResolutionState_to_forwardPairComparisonState_or_pairOverlap
+    hsorted (sourcePressureSortedFailureState_to_failureResolutionState h)
+
+/--
+Beam seed reaches the forward pair-comparison state or a concrete pair-overlap
+obstruction.
+
+This is the Beam-facing pair-comparison entry point produced by the current
+state ladder.
+-/
+theorem sourcePressureBeamSeedState_to_forwardPairComparisonState_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (h : SourcePressureBeamSeedState L) :
+    (∃ W W',
+      SourcePressureForwardPairComparisonState L W W') ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
+  sourcePressureFailureResolutionState_to_forwardPairComparisonState_or_pairOverlap
+    hsorted (sourcePressureBeamSeedState_to_failureResolutionState h)
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-264.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-264.md
new file mode 100644
index 00000000..208942e5
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-264.md
@@ -0,0 +1,108 @@
+# Report: petal-264
+
+## Goal
+
+Lift the named forward-box split to the forward-pair-comparison state.
+
+Target surface:
+
+```text
+FailureResolution + sorted(L)
+  -> ForwardPairComparisonState ∨ PairOverlapObstruction
+
+SortedFailure + sorted(L)
+  -> ForwardPairComparisonState ∨ PairOverlapObstruction
+
+BeamSeed + sorted(L)
+  -> ForwardPairComparisonState ∨ PairOverlapObstruction
+```
+
+## Implemented
+
+Added the following theorems in
+`DkMath.Collatz.PetalBridge.PressureState`:
+
+```lean
+sourcePressureFailureResolutionState_to_forwardPairComparisonState_or_pairOverlap
+sourcePressureSortedFailureState_to_forwardPairComparisonState_or_pairOverlap
+sourcePressureBeamSeedState_to_forwardPairComparisonState_or_pairOverlap
+```
+
+The implementation reuses the existing forward-box split:
+
+```lean
+sourcePressureFailureResolutionState_to_forwardBoxComparisonState_or_pairOverlap
+sourcePressureSortedFailureState_to_forwardBoxComparisonState_or_pairOverlap
+sourcePressureBeamSeedState_to_forwardBoxComparisonState_or_pairOverlap
+```
+
+and converts the forward branch by:
+
+```lean
+SourcePressureForwardBoxComparisonState.to_pairComparisonState
+```
+
+The overlap obstruction branch is passed through unchanged.
+
+## Meaning
+
+The pair-comparison layer now has a clean entry point.
+
+Instead of making callers unpack a `ForwardBoxComparisonState` and then convert
+it locally, the state ladder provides the pair-facing branch directly:
+
+```text
+state ladder
+  -> ForwardPairComparisonState
+     or concrete PairOverlapObstruction
+```
+
+This keeps the main branch and the obstruction branch separated.  The forward
+branch is now ready for comparison lemmas that consume:
+
+- adjacent-pair address data;
+- left and right centered pulse boxes;
+- forward value order;
+- reverse-box exclusion.
+
+## Guardrails
+
+This checkpoint is only a packaging and lift step.
+
+It does not assert:
+
+- global coverage;
+- canonical witness selection;
+- overlap repair;
+- propagation beyond the explicit adjacent pair;
+- Collatz convergence.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureState
+lake build DkMath.Collatz.PetalBridge
+```
+
+`git diff --check` is part of the final gate for this checkpoint.
+
+## Next Branch Prediction
+
+The next natural branch is to add convenience projections from
+`SourcePressureForwardPairComparisonState`, mirroring the already useful
+`ForwardBoxComparisonState` surface.
+
+Candidate projections:
+
+```lean
+SourcePressureForwardPairComparisonState.left_mem
+SourcePressureForwardPairComparisonState.right_mem
+SourcePressureForwardPairComparisonState.left_signs
+SourcePressureForwardPairComparisonState.right_signs
+```
+
+The strongest immediate target is probably to expose the sign/height/jump
+payload already stored in the two endpoint boxes, while keeping the pair-overlap
+obstruction branch separate.
````
`````
