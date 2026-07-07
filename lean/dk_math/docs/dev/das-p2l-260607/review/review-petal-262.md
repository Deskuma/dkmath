# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 5bdc35039b72ecfafe123677023411445fb1917e

## Report

実装完了です。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:877) に `SourcePressureForwardBoxComparisonState` の convenience projection を追加しました。

追加 theorem:

- `SourcePressureForwardBoxComparisonState.left_box`
- `SourcePressureForwardBoxComparisonState.right_box`
- `SourcePressureForwardBoxComparisonState.adjacentPair`
- `SourcePressureForwardBoxComparisonState.left_mem`
- `SourcePressureForwardBoxComparisonState.right_mem`

これで `FBC` から以下が直接取れます。

```text
Box
left/right pulse boxes
AdjacentPairInList
W ∈ L, W' ∈ L
W.val < W'.val
not reverse Box
```

レポート:
[report-petal-262.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-262.md)

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureState` 成功
- `lake build DkMath.Collatz.PetalBridge` 成功
- `git diff --check` 成功

差分は `PressureState.lean` と `report-petal-262.md` です。

## Review

## 判定

採用。
`SourcePressureForwardBoxComparisonState` が pair-comparison 層の入力としてかなり整った。

追加：

```lean id="k0dx0v"
SourcePressureForwardBoxComparisonState.left_box
SourcePressureForwardBoxComparisonState.right_box
SourcePressureForwardBoxComparisonState.adjacentPair
SourcePressureForwardBoxComparisonState.left_mem
SourcePressureForwardBoxComparisonState.right_mem
```

既存の projection と合わせて、`FBC` から必要な局所データが直接取れる。

## 増えた事実

`SourcePressureForwardBoxComparisonState L W W'` から、現在はこれが揃う。

```text id="6c8r42"
FBC
  -> Box
  -> left_box
  -> right_box
  -> AdjacentPairInList
  -> W ∈ L
  -> W' ∈ L
  -> W.val < W'.val
  -> ¬ Box(W',W)
```

これで、次段 theorem はもう `h.1.2.1...` のような conjunction unpacking をしなくてよい。
`FBC` を一つ渡せば、pair comparison に必要な基本材料を呼び出せる。

## 現在の状態表

```text id="7jjpa4"
SortedFailure + sorted(L)
  -> FBC ∨ PO

FailureResolution + sorted(L)
  -> FBC ∨ PO

BeamSeed + sorted(L)
  -> FBC ∨ PO

FBC
  -> ordered adjacent pair
  -> left/right pulse boxes
  -> forward value order
  -> reverse box exclusion
```

かなり綺麗に閉じた。

## 次に攻める定理

次は `FBC` から **pair-comparison-facing state** を作る段階。

今の `FBC` は box と順序を持つ。
次に、pair comparison 層が欲しがる情報をまとめた state を切る。

候補：

```lean id="0vf7ll"
def SourcePressureForwardPairComparisonState
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (W W' : SourcePressureLocalIslandWitness n k r) : Prop :=
  SourcePressureForwardBoxComparisonState L W W' ∧
    SourcePressureLocalIslandWitnessAdjacentPairInList L W W' ∧
      SourcePressureBeamCenteredLocalPulseBox n k r L W ∧
        SourcePressureBeamCenteredLocalPulseBox n k r L W'
```

ただしこれは `FBC` から全部 projection できるので、冗長とも言える。

なので、まずは theorem でよい。

```lean id="bth6yu"
theorem SourcePressureForwardBoxComparisonState.to_pairComparisonFacts
```

中身は tuple でもよいが、名前を作るなら state 化。

## Codex 指示

```text id="k55pwv"
Goal:
  Create the first pair-comparison-facing surface from
  SourcePressureForwardBoxComparisonState.

Prefer a named state if signatures stay cleaner.

Add in PressureState.lean:

  def SourcePressureForwardPairComparisonState
      {n : OddNat} {k r : ℕ}
      (L : List (SourcePressureLocalIslandWitness n k r))
      (W W' : SourcePressureLocalIslandWitness n k r) : Prop :=
    SourcePressureForwardBoxComparisonState L W W' ∧
      SourcePressureLocalIslandWitnessAdjacentPairInList L W W' ∧
        SourcePressureBeamCenteredLocalPulseBox n k r L W ∧
          SourcePressureBeamCenteredLocalPulseBox n k r L W'

Add projections:
  SourcePressureForwardPairComparisonState.forward
  SourcePressureForwardPairComparisonState.adjacentPair
  SourcePressureForwardPairComparisonState.left_box
  SourcePressureForwardPairComparisonState.right_box
  SourcePressureForwardPairComparisonState.val_lt
  SourcePressureForwardPairComparisonState.not_reverse_box

Add constructor:
  theorem SourcePressureForwardBoxComparisonState.to_pairComparisonState
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardBoxComparisonState L W W') :
      SourcePressureForwardPairComparisonState L W W'

Use:
  h.adjacentPair
  h.left_box
  h.right_box
  h.val_lt
  h.not_reverse_box

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

次でこうなる。

```text id="sds4p8"
FBC
  -> ForwardPairComparisonState
```

その後に、

```text id="0givjt"
S/R/B + sorted(L)
  -> ForwardPairComparisonState ∨ PairOverlapObstruction
```

まで lift する。
これで pair-comparison 層の入口が完成する。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 9544e9fd..2da2e67a 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -873,6 +873,51 @@ theorem SourcePressureForwardBoxComparisonState.not_reverse_box
     ¬ SourcePressureOrientedNeighborBoxState L W' W :=
   h.2.2
 
+/-- Project the left centered pulse box from a forward comparison state. -/
+theorem SourcePressureForwardBoxComparisonState.left_box
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardBoxComparisonState L W W') :
+    SourcePressureBeamCenteredLocalPulseBox n k r L W :=
+  h.box.left_box
+
+/-- Project the right centered pulse box from a forward comparison state. -/
+theorem SourcePressureForwardBoxComparisonState.right_box
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardBoxComparisonState L W W') :
+    SourcePressureBeamCenteredLocalPulseBox n k r L W' :=
+  h.box.right_box
+
+/-- Project the ordered adjacent-pair address from a forward comparison state. -/
+theorem SourcePressureForwardBoxComparisonState.adjacentPair
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardBoxComparisonState L W W') :
+    SourcePressureLocalIslandWitnessAdjacentPairInList L W W' :=
+  h.box.adjacentPair
+
+/-- The left endpoint of a forward comparison state is a member of the list. -/
+theorem SourcePressureForwardBoxComparisonState.left_mem
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardBoxComparisonState L W W') :
+    W ∈ L :=
+  h.box.left_mem
+
+/-- The right endpoint of a forward comparison state is a member of the list. -/
+theorem SourcePressureForwardBoxComparisonState.right_mem
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardBoxComparisonState L W W') :
+    W' ∈ L :=
+  h.box.right_mem
+
 /--
 Constructor from a sorted oriented neighbor box to the named forward comparison
 state.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-262.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-262.md
new file mode 100644
index 00000000..4b92e75f
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-262.md
@@ -0,0 +1,90 @@
+# Report: petal-262
+
+## Goal
+
+Add convenience projections from:
+
+```lean
+SourcePressureForwardBoxComparisonState
+```
+
+so the named state is ready to serve as a pair-comparison-layer input.
+
+## Implemented
+
+Added in `DkMath.Collatz.PetalBridge.PressureState`:
+
+```lean
+theorem SourcePressureForwardBoxComparisonState.left_box
+theorem SourcePressureForwardBoxComparisonState.right_box
+theorem SourcePressureForwardBoxComparisonState.adjacentPair
+theorem SourcePressureForwardBoxComparisonState.left_mem
+theorem SourcePressureForwardBoxComparisonState.right_mem
+```
+
+These complement the existing projections:
+
+```lean
+theorem SourcePressureForwardBoxComparisonState.box
+theorem SourcePressureForwardBoxComparisonState.val_lt
+theorem SourcePressureForwardBoxComparisonState.not_reverse_box
+```
+
+## Meaning
+
+`SourcePressureForwardBoxComparisonState` now exposes all local data expected by
+the next pair-comparison layer:
+
+```text
+FBC
+  -> Box
+  -> left/right pulse boxes
+  -> AdjacentPairInList
+  -> W in L, W' in L
+  -> W.val < W'.val
+  -> not reverse Box
+```
+
+Callers can stay at the named-state level and project exactly the local fact
+they need without unpacking the conjunction manually.
+
+## Guardrails
+
+These are pure projection lemmas.  They add no new mathematical strength beyond
+the already stored `SourcePressureForwardBoxComparisonState`.
+
+They do not assert global coverage, canonical pair selection, propagation,
+overlap repair, or convergence.
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
+The named forward branch is now complete enough to feed a real pair-comparison
+surface.
+
+Candidate next step:
+
+```text
+ForwardBoxComparisonState L W W'
+  -> pair-comparison-facing facts for W and W'
+```
+
+The total state split should continue to keep the obstruction branch separate:
+
+```text
+ForwardBoxComparisonState or PairOverlapObstruction
+```
+
+rather than coercing overlap into a diagnostic branch.
````
`````
