# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 2e0f5600a56b7cf17fbf458e400e8be54b6d99d8

## Report

実装完了です。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:543) に `sourcePressureBeamSeedState_to_orientedNeighborDiagnostic_or_pairOverlap` を追加しました。`BeamSeedState -> FailureResolutionState -> OrientedNeighborDiagnostic ∨ PairOverlapObstruction` を直接使える薄い lift theorem です。

レポートは [report-petal-250.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-250.md:1) に追加しました。

確認済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

差分は `PressureState.lean` の変更と `report-petal-250.md` の新規追加です。

## Review

## 判定

採用。
`BeamSeedState` から refined exit まで直通になった。

追加：

```lean id="lz010b"
theorem sourcePressureBeamSeedState_to_orientedNeighborDiagnostic_or_pairOverlap
```

内容：

```text id="gmuy3x"
BeamSeedState L
  -> OrientedNeighborDiagnosticState L W W'
   ∨ PairOverlapObstruction A B
```

中身は、

```lean id="auygi2"
sourcePressureBeamSeedState_to_failureResolutionState
sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap
```

の合成。Beam-facing caller が `FailureResolutionState` を手で経由しなくてよくなった。

## 状態表の現状

これで主要入口が揃った。

```text id="ccn61j"
SortedFailure
  -> OrientedNeighborDiagnostic ∨ PairOverlapObstruction

FailureResolution
  -> OrientedNeighborDiagnostic ∨ PairOverlapObstruction

BeamSeed
  -> OrientedNeighborDiagnostic ∨ PairOverlapObstruction
```

状態名で読むと、

```text id="np43og"
S -> D ∨ PO
R -> D ∨ PO
B -> D ∨ PO
```

じゃ。

## 増えた事実

`BeamSeed` はもう単なる pulse box の入口ではなく、同時に

```text id="kq87wa"
diagnostic branch
or
overlap obstruction branch
```

へ分岐できる入口になった。

これは大きい。
Beam 側で「seed を持っている」なら、そのまま次の二択に進める。

## 次に攻める場所

次は **OrientedNeighborDiagnosticState の中身を sign-level へ落とす**。

いま `D` は mass-balance centered diagnostic を持っている。

```text id="99xd0p"
W entry comparison
W addressed target
W exit comparison

W' entry comparison
W' addressed target
W' exit comparison
```

次に欲しいのは、cp235 と同じ sign pattern を `W` と `W'` の両方へ出すこと。

狙い：

```lean id="xu7xp2"
theorem sourcePressureOrientedNeighborDiagnosticState_to_pair_center_margin_signs
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureOrientedNeighborDiagnosticState L W W') :
    -- signs for W and signs for W'
```

より実用的には、まず片側ずつ。

```lean id="3q7tsw"
sourcePressureOrientedNeighborDiagnosticState_left_center_margin_signs
sourcePressureOrientedNeighborDiagnosticState_right_center_margin_signs
```

形は、

```text id="x2a0g1"
SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0
0 < SourcePressureMarginInt n k (r + W.val)
SourcePressureBeamAddressedDepthTarget L W.val
SourcePressureMarginInt n k (r + W.val + 1) ≤ 0
```

これは `sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right_edge` と `sourcePressureMargin_next_nonpos_of_massBalanceRight_le_left` で作れるはず。

ただし `prev nonpos` は centered diagnostic だけでは出ないかもしれない。
その場合は `W.property` を使う。`W` は `SourcePressureLocalIslandWitness` なので local island property を持っているはず。

## Codex 指示

```text id="f6yo4e"
Goal:
  Project sign patterns from SourcePressureOrientedNeighborDiagnosticState.

Add in PressureState.lean:

  theorem sourcePressureOrientedNeighborDiagnosticState_left_center_margin_signs
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureOrientedNeighborDiagnosticState L W W') :
      SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
        0 < SourcePressureMarginInt n k (r + W.val) ∧
          SourcePressureBeamAddressedDepthTarget L W.val ∧
            SourcePressureMarginInt n k (r + W.val + 1) ≤ 0

  theorem sourcePressureOrientedNeighborDiagnosticState_right_center_margin_signs
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureOrientedNeighborDiagnosticState L W W') :
      SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
        0 < SourcePressureMarginInt n k (r + W'.val) ∧
          SourcePressureBeamAddressedDepthTarget L W'.val ∧
            SourcePressureMarginInt n k (r + W'.val + 1) ≤ 0

Use:
  SourcePressureOrientedNeighborDiagnosticState fields
  sourcePressureLocalIsland_iff_margin
  sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right_edge
  sourcePressureMargin_next_nonpos_of_massBalanceRight_le_left
  omega if needed for r + (val - 1) + 1 = r + val

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

これで `D` が sign-level でも読める。

```text id="rysnuw"
OrientedNeighborDiagnostic
  -> signs for W
  -> signs for W'
```

その次は `D` に height/jump box を足して、

```text id="2fhx8w"
OrientedNeighborDiagnostic
  -> two endpoint local pulse boxes or partial boxes
```

へ進める。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index c2b3b4de..bf445899 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -525,4 +525,31 @@ theorem sourcePressureSortedFailureState_to_orientedNeighborDiagnostic_or_pairOv
   sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap
     (sourcePressureSortedFailureState_to_failureResolutionState h)

+/--
+Beam seed reaches the same refined diagnostic/obstruction split.
+
+This theorem exposes the Beam-seed entry point as a direct caller-facing split:
+
+```text
+BeamSeed
+  -> OrientedNeighborDiagnostic
+   ∨ PairOverlapObstruction
+```
+
+It is only the already-proved `BeamSeed -> FailureResolution` transition
+followed by the pair-refined failure-resolution split.  No stronger accounting,
+repair, propagation, or convergence statement is introduced here.
+-/
+theorem sourcePressureBeamSeedState_to_orientedNeighborDiagnostic_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureBeamSeedState L) :
+    (∃ W W',
+      SourcePressureOrientedNeighborDiagnosticState L W W') ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
+  sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap
+    (sourcePressureBeamSeedState_to_failureResolutionState h)
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-250.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-250.md
new file mode 100644
index 00000000..9cb8fc5f
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-250.md
@@ -0,0 +1,71 @@
+# Report: petal-250
+
+## Goal
+
+Lift the refined diagnostic/obstruction split to `SourcePressureBeamSeedState`.
+
+## Implemented
+
+Added in `DkMath.Collatz.PetalBridge.PressureState`:
+
+```lean
+theorem sourcePressureBeamSeedState_to_orientedNeighborDiagnostic_or_pairOverlap
+```
+
+This theorem composes:
+
+```lean
+sourcePressureBeamSeedState_to_failureResolutionState
+sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap
+```
+
+and exposes the Beam-seed entry point directly as:
+
+```text
+BeamSeedState L
+  -> OrientedNeighborDiagnosticState L W W'
+   OR
+     AdjacentPairInList L A B
+     + PairOverlapObstruction A B
+```
+
+## Automaton Reading
+
+The Beam-seed branch now reaches the same pair-refined diagnostic surface as
+sorted failure:
+
+```text
+B -> R -> D ∨ PO
+```
+
+where:
+
+- `B` is Beam seed,
+- `R` is failure resolution,
+- `D` is an oriented neighbor diagnostic,
+- `PO` is a concrete pair-level overlap obstruction.
+
+This lets Beam-facing callers use a single theorem without manually stepping
+through the failure-resolution state.
+
+## Guardrails
+
+This is only a state-lift theorem.  It does not add:
+
+- overlap repair,
+- canonical obstructing-pair selection,
+- global coverage,
+- aggregation over all adjacent pairs,
+- transport or propagation,
+- convergence or Collatz termination.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureState
+lake build DkMath.Collatz.PetalBridge
+git diff --check
+```
+
````
`````
