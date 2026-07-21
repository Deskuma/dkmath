# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 1f93d7625d6f413f8b4c0fa51447f07726079700

## Report

実装・調査完了です。

結論として、`SourcePressureOrientedNeighborBoxState` から直接取り出せる最強の順序関係は `SourcePressureLocalIslandWitnessAdjacentPairInList L W W'` でした。これは「`L` の中で `W, W'` がこの順で隣接している」という list-address relation で、`SourcePressureLocalIslandWitnessBefore W W'` や `W.val < W'.val` は含んでいません。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:550) にその注意書きをコードコメントとして残し、以下を追加しました。

```lean
SourcePressureOrientedNeighborBoxState.orderedAdjacentPairInList
SourcePressureOrientedNeighborBoxState.left_mem
SourcePressureOrientedNeighborBoxState.right_mem
```

実装位置:
[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:579)

レポートは [report-petal-255.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-255.md:1) に追加しました。

確認済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

## Review

## 判定

採用。
`Box` から取れる順序関係の限界が確認された。

追加：

```lean id="soedfl"
SourcePressureOrientedNeighborBoxState.orderedAdjacentPairInList
SourcePressureOrientedNeighborBoxState.left_mem
SourcePressureOrientedNeighborBoxState.right_mem
```

結論は明確。

```text id="0zxekr"
Box(W,W')
  -> AdjacentPairInList L W W'
```

までは取れる。

しかし、

```text id="zbnrrz"
SourcePressureLocalIslandWitnessBefore W W'
W.val < W'.val
```

はまだ取れない。`AdjacentPairInList` は list-address relation であり、数値 depth order ではない。ここが今回の重要な観測。

## 増えた事実

`Box(W,W')` から直接使えるもの：

```text id="6smj0b"
ordered adjacent pair in L
W ∈ L
W' ∈ L
```

これは比較層の入口になる。

今の最強関係はこれ。

```lean id="272fjk"
SourcePressureLocalIslandWitnessAdjacentPairInList L W W'
```

つまり、`W` と `W'` は list `L` の中でこの順に隣接している。

## 重要な Gap

次の比較には、追加 invariant が必要。

候補は二つ。

```text id="tlk214"
AdjacentPairInList L W W'
+
L is sorted by witness address
-> SourcePressureLocalIslandWitnessBefore W W'
```

または、

```text id="me9s19"
AdjacentPairInList L W W'
+
L is sorted by W.val
-> W.val < W'.val
```

ここを入れないと、list 上の隣接を数値順序に変換できない。

## 次に攻める定理

次は sortedness/address-order invariant を探す。

まず既存にあるか確認：

```text id="vft2wr"
SortedBeforeFailure
sorted
Before
WitnessBefore
val order
address order
AdjacentPairInList
```

もし既存で `SortedBeforeFailure` が list order を含むなら、そこから引ける可能性がある。

狙いはこれ。

```lean id="rvs7rd"
theorem sourcePressureAdjacentPairInList_before_of_sorted
    ...
    (hsorted : <sortedness predicate on L>)
    (hin : SourcePressureLocalIslandWitnessAdjacentPairInList L W W') :
    SourcePressureLocalIslandWitnessBefore W W'
```

または数値版：

```lean id="2jl73q"
theorem sourcePressureAdjacentPairInList_val_lt_of_sortedByVal
    ...
    (hsorted : <sorted-by-val predicate on L>)
    (hin : SourcePressureLocalIslandWitnessAdjacentPairInList L W W') :
    W.val < W'.val
```

## Codex 指示

```text id="y3t0o6"
Goal:
  Find or define the sortedness/address-order bridge needed to turn
  AdjacentPairInList into witness order or value order.

Inspect:
  SourcePressureLocalIslandWitnessAdjacentPairInList
  SourcePressureLocalIslandWitnessBefore
  SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
  any sortedness / List.Pairwise / val-order definitions around pressure files

Search:
  Sorted
  sorted
  Before
  before
  val <
  Pairwise
  AdjacentPairInList

Try:
  theorem sourcePressureAdjacentPairInList_before_of_sorted
      ...
      (hsorted : <existing sortedness predicate>)
      (hin : SourcePressureLocalIslandWitnessAdjacentPairInList L W W') :
      SourcePressureLocalIslandWitnessBefore W W'

If Before is not the right target, try:
  theorem sourcePressureAdjacentPairInList_val_lt_of_sorted
      ...
      (hsorted : <existing sortedness predicate>)
      (hin : SourcePressureLocalIslandWitnessAdjacentPairInList L W W') :
      W.val < W'.val

If no sortedness predicate exists:
  Report exact missing invariant and propose the smallest definition.

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

ここからは比較層。

```text id="8837t2"
Box(W,W')
  -> AdjacentPairInList L W W'
  + sortedness/address invariant
  -> W before W' or W.val < W'.val
```

この invariant が見つかるか、無ければ定義する。
次の球はそこじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 9981cedd..21fb2ed5 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -546,6 +546,64 @@ theorem SourcePressureOrientedNeighborBoxState.adjacentPair
     SourcePressureLocalIslandWitnessAdjacentPairInList L W W' :=
   h.diagnostic.adjacentPair

+/-
+Order-projection note for the next comparison layer.
+
+`SourcePressureLocalIslandWitnessAdjacentPairInList L W W'` is the strongest
+order relation currently stored in `SourcePressureOrientedNeighborBoxState`.
+It says that `W` and `W'` occur as an ordered neighboring pair in the explicit
+list `L`.
+
+It does *not* contain either of the following stronger facts:
+
+```text
+SourcePressureLocalIslandWitnessBefore W W'
+W.val < W'.val
+```
+
+Those facts concern interval-pulse address order / numeric depth order.  They
+are not derivable from list adjacency alone without an additional invariant
+saying that the witness list is sorted by address/depth.  The comparison layer
+should therefore consume the ordered adjacent-pair address first, then add the
+required sortedness/address-order hypothesis explicitly.
+-/
+
+/--
+Project the strongest currently available ordered pair relation from a
+two-endpoint box: `W` and `W'` are adjacent in this order in the enclosing list.
+
+This is intentionally an alias of `.adjacentPair` with a more comparison-facing
+name.  It is not a witness-level `Before` theorem and not a numeric value-order
+theorem.
+-/
+theorem SourcePressureOrientedNeighborBoxState.orderedAdjacentPairInList
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureOrientedNeighborBoxState L W W') :
+    SourcePressureLocalIslandWitnessAdjacentPairInList L W W' :=
+  h.adjacentPair
+
+/-- The left endpoint of a two-endpoint box is a member of the enclosing list. -/
+theorem SourcePressureOrientedNeighborBoxState.left_mem
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureOrientedNeighborBoxState L W W') :
+    W ∈ L :=
+  sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem
+    h.orderedAdjacentPairInList
+
+/-- The right endpoint of a two-endpoint box is a member of the enclosing list. -/
+theorem SourcePressureOrientedNeighborBoxState.right_mem
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureOrientedNeighborBoxState L W W') :
+    W' ∈ L :=
+  sourcePressureLocalIslandWitnessAdjacentPairInList_right_mem
+    h.orderedAdjacentPairInList
+
 /--
 Package an oriented neighbor diagnostic into the two-endpoint box state.

diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-255.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-255.md
new file mode 100644
index 00000000..5fde706f
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-255.md
@@ -0,0 +1,100 @@
+# Report: petal-255
+
+## Goal
+
+Extract the ordered before/value relation from
+`SourcePressureOrientedNeighborBoxState`.
+
+## Investigation Result
+
+The available stored relation is:
+
+```lean
+SourcePressureLocalIslandWitnessAdjacentPairInList L W W'
+```
+
+This relation means that `W` and `W'` occur as an ordered neighboring pair in
+the explicit witness list `L`.
+
+It does not imply either of the stronger relations:
+
+```lean
+SourcePressureLocalIslandWitnessBefore W W'
+W.val < W'.val
+```
+
+The reason is structural: `AdjacentPairInList` is a list-address relation only.
+It records ordered neighboring positions in `L`, but it does not say that `L`
+is sorted by pulse-address order or by numeric depth.
+
+## Implemented
+
+Added in `DkMath.Collatz.PetalBridge.PressureState`:
+
+```lean
+theorem SourcePressureOrientedNeighborBoxState.orderedAdjacentPairInList
+theorem SourcePressureOrientedNeighborBoxState.left_mem
+theorem SourcePressureOrientedNeighborBoxState.right_mem
+```
+
+The new comparison-facing projection is intentionally an alias of the existing
+box adjacent-pair projection:
+
+```text
+Box(W,W') -> AdjacentPairInList L W W'
+```
+
+The membership projections expose:
+
+```text
+Box(W,W') -> W  in L
+Box(W,W') -> W' in L
+```
+
+## Code Comment
+
+Added a source-level note explaining why `Before` and `W.val < W'.val` are not
+derived here.  Future comparison theorems should add an explicit sortedness or
+address-order hypothesis before attempting to prove those stronger relations.
+
+## Next Direction
+
+The next comparison layer should likely introduce one of:
+
+```text
+AdjacentPairInList L W W'
++ list sorted by witness address
+-> SourcePressureLocalIslandWitnessBefore W W'
+```
+
+or:
+
+```text
+AdjacentPairInList L W W'
++ list sorted by W.val
+-> W.val < W'.val
+```
+
+This keeps list adjacency separate from mathematical address/depth order.
+
+## Guardrails
+
+This checkpoint does not add:
+
+- witness-level `Before`,
+- numeric depth comparison,
+- sortedness assumptions,
+- transport or propagation,
+- coverage or aggregation,
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
