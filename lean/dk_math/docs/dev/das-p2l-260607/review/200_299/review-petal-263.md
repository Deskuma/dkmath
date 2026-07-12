# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 3f06fbd094756cbc93b75ebd0a8cf061c5e92a08

## Report

実装完了です。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:935) に pair-comparison-facing state を追加しました。

追加:

- `def SourcePressureForwardPairComparisonState`
- `SourcePressureForwardPairComparisonState.forward`
- `SourcePressureForwardPairComparisonState.adjacentPair`
- `SourcePressureForwardPairComparisonState.left_box`
- `SourcePressureForwardPairComparisonState.right_box`
- `SourcePressureForwardPairComparisonState.val_lt`
- `SourcePressureForwardPairComparisonState.not_reverse_box`
- `SourcePressureForwardBoxComparisonState.to_pairComparisonState`

これで、

```text
ForwardBoxComparisonState
  -> ForwardPairComparisonState
```

が取れます。`FPC` 側には、forward state、adjacent pair、左右 pulse box、`val_lt`、reverse box 排除が揃っています。

レポート:
[report-petal-263.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-263.md)

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureState` 成功
- `lake build DkMath.Collatz.PetalBridge` 成功
- `git diff --check` 成功

差分は `PressureState.lean` と `report-petal-263.md` です。

## Review

## 判定

採用。
`ForwardBoxComparisonState` から、pair-comparison-facing な `ForwardPairComparisonState` へ進める面ができた。

追加：

```lean id="novn4y"
def SourcePressureForwardPairComparisonState
```

projection：

```lean id="xzz67c"
SourcePressureForwardPairComparisonState.forward
SourcePressureForwardPairComparisonState.adjacentPair
SourcePressureForwardPairComparisonState.left_box
SourcePressureForwardPairComparisonState.right_box
SourcePressureForwardPairComparisonState.val_lt
SourcePressureForwardPairComparisonState.not_reverse_box
```

constructor：

```lean id="p1g1cf"
SourcePressureForwardBoxComparisonState.to_pairComparisonState
```

これで、

```text id="r98mqr"
FBC -> ForwardPairComparisonState
```

が取れる。`FPC` 側には forward state、ordered adjacent pair、左右 pulse box、`val_lt`、reverse box 排除が揃った。

## 増えた事実

`SourcePressureForwardPairComparisonState L W W'` は、次段 pair-comparison theorem の入力としてかなり良い。

中身はこれ。

```text id="h0ghvf"
ForwardBoxComparisonState L W W'
AdjacentPairInList L W W'
CenteredLocalPulseBox W
CenteredLocalPulseBox W'
```

そして projection で、

```text id="vubkqy"
W.val < W'.val
¬ Box(W',W)
```

も取れる。

## 現在の状態表

```text id="cguznh"
S/R/B + sorted(L)
  -> FBC ∨ PO

FBC
  -> FPC
```

なので、次は当然これ。

```text id="qw98om"
S/R/B + sorted(L)
  -> FPC ∨ PO
```

## 次に攻める定理

次は既存の named split から `FBC` 側だけ `FPC` に持ち上げる。

狙い：

```lean id="zdg3eu"
sourcePressureFailureResolutionState_to_forwardPairComparisonState_or_pairOverlap
sourcePressureSortedFailureState_to_forwardPairComparisonState_or_pairOverlap
sourcePressureBeamSeedState_to_forwardPairComparisonState_or_pairOverlap
```

中身は単純。

```text id="nc4o1v"
FBC ∨ PO
  -> FPC ∨ PO
```

`FBC` branch では、

```lean id="u36zlr"
hforward.to_pairComparisonState
```

を使う。

## Codex 指示

```text id="yp2m55"
Goal:
  Lift the named forward-box split to the forward-pair-comparison state.

Add in PressureState.lean:

  theorem sourcePressureFailureResolutionState_to_forwardPairComparisonState_or_pairOverlap
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
      (h : SourcePressureFailureResolutionState L) :
      (∃ W W',
        SourcePressureForwardPairComparisonState L W W') ∨
        ∃ A B,
          SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
            SourcePressureLocalIslandWitnessPairOverlapObstruction A B

  theorem sourcePressureSortedFailureState_to_forwardPairComparisonState_or_pairOverlap
      ...

  theorem sourcePressureBeamSeedState_to_forwardPairComparisonState_or_pairOverlap
      ...

Use:
  sourcePressureFailureResolutionState_to_forwardBoxComparisonState_or_pairOverlap
  sourcePressureSortedFailureState_to_forwardBoxComparisonState_or_pairOverlap
  sourcePressureBeamSeedState_to_forwardBoxComparisonState_or_pairOverlap
  SourcePressureForwardBoxComparisonState.to_pairComparisonState

Proof shape:
  split FBC / PO.
  FBC -> left with to_pairComparisonState.
  PO  -> right unchanged.

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

次で表面はこうなる。

```text id="e2bzqr"
SortedFailure + sorted(L)
  -> ForwardPairComparisonState ∨ PairOverlapObstruction

FailureResolution + sorted(L)
  -> ForwardPairComparisonState ∨ PairOverlapObstruction

BeamSeed + sorted(L)
  -> ForwardPairComparisonState ∨ PairOverlapObstruction
```

これができれば、pair-comparison 層の入口は完成。次は `FPC` 側で左右 pulse box の sign/height/jump を使った比較補題へ進める。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 2da2e67a..96e8f5d2 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -918,6 +918,97 @@ theorem SourcePressureForwardBoxComparisonState.right_mem
     W' ∈ L :=
   h.box.right_mem
 
+/--
+Pair-comparison-facing packaging of the forward box branch.
+
+This state keeps the forward comparison state and repeats the local pair data
+that the next layer naturally consumes:
+
+* the ordered adjacent-pair address;
+* the left endpoint's centered pulse box;
+* the right endpoint's centered pulse box.
+
+The duplicated projections are intentional.  They keep later pair-comparison
+theorems from depending on the internal shape of
+`SourcePressureForwardBoxComparisonState`.
+-/
+def SourcePressureForwardPairComparisonState
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (W W' : SourcePressureLocalIslandWitness n k r) : Prop :=
+  SourcePressureForwardBoxComparisonState L W W' ∧
+    SourcePressureLocalIslandWitnessAdjacentPairInList L W W' ∧
+      SourcePressureBeamCenteredLocalPulseBox n k r L W ∧
+        SourcePressureBeamCenteredLocalPulseBox n k r L W'
+
+/-- Project the underlying forward box comparison state. -/
+theorem SourcePressureForwardPairComparisonState.forward
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    SourcePressureForwardBoxComparisonState L W W' :=
+  h.1
+
+/-- Project the ordered adjacent-pair address from a forward pair comparison state. -/
+theorem SourcePressureForwardPairComparisonState.adjacentPair
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    SourcePressureLocalIslandWitnessAdjacentPairInList L W W' :=
+  h.2.1
+
+/-- Project the left endpoint pulse box from a forward pair comparison state. -/
+theorem SourcePressureForwardPairComparisonState.left_box
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    SourcePressureBeamCenteredLocalPulseBox n k r L W :=
+  h.2.2.1
+
+/-- Project the right endpoint pulse box from a forward pair comparison state. -/
+theorem SourcePressureForwardPairComparisonState.right_box
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    SourcePressureBeamCenteredLocalPulseBox n k r L W' :=
+  h.2.2.2
+
+/-- Project the forward value comparison from a forward pair comparison state. -/
+theorem SourcePressureForwardPairComparisonState.val_lt
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    W.val < W'.val :=
+  h.forward.val_lt
+
+/-- Project reverse-box exclusion from a forward pair comparison state. -/
+theorem SourcePressureForwardPairComparisonState.not_reverse_box
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    ¬ SourcePressureOrientedNeighborBoxState L W' W :=
+  h.forward.not_reverse_box
+
+/--
+Constructor from the forward box comparison state to the pair-comparison-facing
+state.
+
+All additional fields are projections already stored in the forward state.
+-/
+theorem SourcePressureForwardBoxComparisonState.to_pairComparisonState
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardBoxComparisonState L W W') :
+    SourcePressureForwardPairComparisonState L W W' :=
+  ⟨h, h.adjacentPair, h.left_box, h.right_box⟩
+
 /--
 Constructor from a sorted oriented neighbor box to the named forward comparison
 state.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-263.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-263.md
new file mode 100644
index 00000000..b91baaca
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-263.md
@@ -0,0 +1,103 @@
+# Report: petal-263
+
+## Goal
+
+Create the first pair-comparison-facing surface from:
+
+```lean
+SourcePressureForwardBoxComparisonState
+```
+
+The new surface should package the forward branch together with the adjacent
+pair and both endpoint pulse boxes.
+
+## Implemented
+
+Added in `DkMath.Collatz.PetalBridge.PressureState`:
+
+```lean
+def SourcePressureForwardPairComparisonState
+```
+
+The state stores:
+
+```lean
+SourcePressureForwardBoxComparisonState L W W'
+SourcePressureLocalIslandWitnessAdjacentPairInList L W W'
+SourcePressureBeamCenteredLocalPulseBox n k r L W
+SourcePressureBeamCenteredLocalPulseBox n k r L W'
+```
+
+Projection lemmas:
+
+```lean
+theorem SourcePressureForwardPairComparisonState.forward
+theorem SourcePressureForwardPairComparisonState.adjacentPair
+theorem SourcePressureForwardPairComparisonState.left_box
+theorem SourcePressureForwardPairComparisonState.right_box
+theorem SourcePressureForwardPairComparisonState.val_lt
+theorem SourcePressureForwardPairComparisonState.not_reverse_box
+```
+
+Constructor:
+
+```lean
+theorem SourcePressureForwardBoxComparisonState.to_pairComparisonState
+```
+
+## Meaning
+
+The forward branch now has a dedicated pair-comparison-facing state:
+
+```text
+FBC -> ForwardPairComparisonState
+```
+
+This is still a local witness-pair object.  It does not decide the overlap
+branch and does not merge diagnostics with obstructions.
+
+## Guardrails
+
+The state duplicates data available from `FBC` intentionally.  The purpose is
+API stability: later pair-comparison theorems can consume
+`SourcePressureForwardPairComparisonState` without depending on how
+`SourcePressureForwardBoxComparisonState` is represented internally.
+
+No new global claim is introduced.  There is no coverage, canonical selection,
+propagation, overlap repair, or convergence statement.
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
+The immediate next lift is:
+
+```text
+S/R/B + sorted(L)
+  -> ForwardPairComparisonState or PairOverlapObstruction
+```
+
+This should reuse the existing named split:
+
+```lean
+sourcePressure..._to_forwardBoxComparisonState_or_pairOverlap
+```
+
+and apply:
+
+```lean
+SourcePressureForwardBoxComparisonState.to_pairComparisonState
+```
+
+on the forward branch.
````
`````
