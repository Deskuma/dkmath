# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: ff29804a88022699e51275f1a4a939482bb64b70

## Report

実装完了です。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:622) に、sortedness/address-order bridge を追加しました。

追加 theorem:

- `sourcePressureAdjacentPairInList_before_of_sorted`
- `SourcePressureOrientedNeighborBoxState.before_of_sorted`

これで、

```text
AdjacentPairInList L W W'
+ SourcePressureLocalIslandWitnessListSortedBefore L
-> SourcePressureLocalIslandWitnessBefore W W'
```

が取れます。`W.val < W'.val` までは主張せず、既存の witness/address-level `Before` に接続する形で固定しました。

レポートも追加しました:
[report-petal-256.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-256.md)

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureState` 成功
- `lake build DkMath.Collatz.PetalBridge` 成功
- `git diff --check` 成功

現在の差分は `PressureState.lean` の変更と `report-petal-256.md` の新規追加です。

## Review

## 判定

採用。
`Box + sortedness -> Before` が通った。

追加：

```lean id="cpk6ow"
sourcePressureAdjacentPairInList_before_of_sorted
SourcePressureOrientedNeighborBoxState.before_of_sorted
```

これで、

```text id="lv8hk2"
AdjacentPairInList L W W'
+ SourcePressureLocalIslandWitnessListSortedBefore L
-> SourcePressureLocalIslandWitnessBefore W W'
```

さらに box-facing では、

```text id="cxu1cb"
Box(W,W')
+ sorted(L)
-> W before W'
```

が取れる。

## 増えた事実

重要なのは、既存 invariant が見つかったこと。

```lean id="j2l53g"
SourcePressureLocalIslandWitnessListSortedBefore L
```

これは witness list を interval-pulse address に変換した後の sortedness。
今回、それと `AdjacentPairInList` を組み合わせて、

```lean id="clog5o"
SourcePressureLocalIslandWitnessBefore W W'
```

へ接続した。

これで比較層の入口ができた。

```text id="oqxlp0"
Box
  -> ordered adjacent pair
  + sorted witness list
  -> witness-level Before
```

## 現在の状態表

```text id="igq9yp"
SortedFailure
  -> Box ∨ PO

FailureResolution
  -> Box ∨ PO

BeamSeed
  -> Box ∨ PO

Box
  -> ordered adjacent pair
  -> left/right pulse boxes
  -> Before, if list sorted
```

ここまで来ると、`Box` は単なる局所診断ではなく、**順序付き二点比較の入口**になった。

## 次に攻める定理

次は `Before` が何を意味するかを引き出す。

候補は二つ。

```text id="qnn7um"
Before
  -> address end <= next start
```

または、

```text id="dx875d"
Before
  -> no overlap / separated interval
```

`SourcePressureLocalIslandWitnessBefore W W'` の定義が interval-pulse address の before なら、次に欲しいのは address projection。

狙い：

```lean id="0q3kxc"
theorem SourcePressureLocalIslandWitnessBefore_to_addressBefore
```

既に定義同値なら alias でよい。

Box-facing にするなら：

```lean id="g8t9ls"
theorem SourcePressureOrientedNeighborBoxState.addressBefore_of_sorted
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (hbox : SourcePressureOrientedNeighborBoxState L W W')
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
    SourcePressureIntervalPulseAddressBefore
      (sourcePressureIntervalPulseAddress_of_localIslandWitness W)
      (sourcePressureIntervalPulseAddress_of_localIslandWitness W')
```

これは `before_of_sorted` がほぼそのまま使える可能性が高い。

## Codex 指示

```text id="twiyyg"
Goal:
  Extract address-level comparison facts from SourcePressureLocalIslandWitnessBefore.

Inspect:
  SourcePressureLocalIslandWitnessBefore
  SourcePressureIntervalPulseAddressBefore
  sourcePressureIntervalPulseAddress_of_localIslandWitness
  fields/projections of interval pulse address:
    start
    len
    right edge

Try to add:

  theorem SourcePressureOrientedNeighborBoxState.addressBefore_of_sorted
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (hbox : SourcePressureOrientedNeighborBoxState L W W')
      (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
      SourcePressureIntervalPulseAddressBefore
        (sourcePressureIntervalPulseAddress_of_localIslandWitness W)
        (sourcePressureIntervalPulseAddress_of_localIslandWitness W')

Then inspect whether address-before yields numeric facts such as:

  rightEdge(W) <= start(W')
  W.val <= W'.val
  W.val < W'.val

Add the strongest direct theorem that Lean gives with existing definitions.
Do not force W.val < W'.val if the address relation only gives non-overlap.

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

今の球筋はこれ。

```text id="sj682u"
Box(W,W')
+ sorted(L)
-> W before W'
-> address comparison
-> numeric/depth comparison if available
```

次は `Before` の中身を開く。
ここから pair comparison が本格的に始まる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 21fb2ed5..0b001a6e 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -604,6 +604,79 @@ theorem SourcePressureOrientedNeighborBoxState.right_mem
   sourcePressureLocalIslandWitnessAdjacentPairInList_right_mem
     h.orderedAdjacentPairInList

+/--
+An addressed adjacent pair in a sorted witness list inherits witness-level
+`Before`.
+
+This is the missing comparison bridge found at cp256.  The sortedness
+predicate already exists as `SourcePressureLocalIslandWitnessListSortedBefore`;
+it is adjacent sortedness after converting witnesses to interval-pulse
+addresses.  Since `SourcePressureLocalIslandWitnessAdjacentPairInList` has the
+same head-or-tail recursive shape, the bridge is a structural induction over
+the enclosing list.
+
+This theorem does not prove any numeric value order such as `W.val < W'.val`.
+It only turns list adjacency plus address-sortedness into witness-level
+ordered non-overlap.
+-/
+theorem sourcePressureAdjacentPairInList_before_of_sorted
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (hin : SourcePressureLocalIslandWitnessAdjacentPairInList L W W') :
+    SourcePressureLocalIslandWitnessBefore W W' := by
+  induction L generalizing W W' with
+  | nil =>
+      exact False.elim hin
+  | cons A rest ih =>
+      cases rest with
+      | nil =>
+          exact False.elim hin
+      | cons B rest =>
+          rcases hin with hhead | htail
+          · rcases hhead with ⟨hW, hW'⟩
+            subst W
+            subst W'
+            change
+              SourcePressureIntervalPulseAddressBefore
+                (sourcePressureIntervalPulseAddress_of_localIslandWitness A)
+                (sourcePressureIntervalPulseAddress_of_localIslandWitness B)
+            change
+              SourcePressureIntervalPulseAddressFamilySortedBefore
+                (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList
+                  (A :: B :: rest)) at hsorted
+            exact hsorted.1
+          · have htailSorted :
+                SourcePressureLocalIslandWitnessListSortedBefore (B :: rest) := by
+              change
+                SourcePressureIntervalPulseAddressFamilySortedBefore
+                  (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList
+                    (A :: B :: rest)) at hsorted
+              change
+                SourcePressureIntervalPulseAddressFamilySortedBefore
+                  (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList
+                    (B :: rest))
+              exact hsorted.2
+            exact ih htailSorted htail
+
+/--
+Box-facing version of
+`sourcePressureAdjacentPairInList_before_of_sorted`.
+
+A two-endpoint box supplies the ordered adjacent-pair address; sortedness of
+the enclosing witness list supplies the mathematical address order.
+-/
+theorem SourcePressureOrientedNeighborBoxState.before_of_sorted
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hbox : SourcePressureOrientedNeighborBoxState L W W')
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    SourcePressureLocalIslandWitnessBefore W W' :=
+  sourcePressureAdjacentPairInList_before_of_sorted hsorted
+    hbox.orderedAdjacentPairInList
+
 /--
 Package an oriented neighbor diagnostic into the two-endpoint box state.

diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-256.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-256.md
new file mode 100644
index 00000000..a5f73c19
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-256.md
@@ -0,0 +1,120 @@
+# Report: petal-256
+
+## Goal
+
+Find or define the sortedness/address-order bridge needed to turn
+`SourcePressureLocalIslandWitnessAdjacentPairInList` into witness order or value
+order.
+
+## Investigation
+
+The required sortedness invariant already exists:
+
+```lean
+SourcePressureLocalIslandWitnessListSortedBefore L
+```
+
+This is the witness-list version of address-family sortedness.  It sorts the
+local island witnesses after converting them to interval-pulse addresses.
+
+The right target for this checkpoint is also already present:
+
+```lean
+SourcePressureLocalIslandWitnessBefore W W'
+```
+
+This is stronger and more structural than a raw `W.val < W'.val` target for the
+current layer, because it records the address-level ordered non-overlap relation
+used by the pressure accounting files.
+
+No existing invariant was found that directly gives `W.val < W'.val` from
+adjacency.  This report therefore keeps the new bridge at witness/address order.
+
+## Implemented
+
+Added in `DkMath.Collatz.PetalBridge.PressureState`:
+
+```lean
+theorem sourcePressureAdjacentPairInList_before_of_sorted
+```
+
+This proves:
+
+```text
+SourcePressureLocalIslandWitnessListSortedBefore L
+  + SourcePressureLocalIslandWitnessAdjacentPairInList L W W'
+  -> SourcePressureLocalIslandWitnessBefore W W'
+```
+
+Also added the box-facing projection:
+
+```lean
+theorem SourcePressureOrientedNeighborBoxState.before_of_sorted
+```
+
+This packages the common caller path:
+
+```text
+Box(W,W')
+  -> ordered adjacent pair in L
+  -> sortedness of L
+  -> W before W'
+```
+
+## Meaning
+
+The two-endpoint box now has a clean entrance into the comparison layer.
+
+Before this checkpoint, `Box(W,W')` could project its oriented diagnostic and
+adjacent-pair data, but it did not have a local theorem that combines that
+adjacency with the enclosing list sortedness invariant.
+
+After this checkpoint, downstream pair-comparison work can stay at the
+box-facing API:
+
+```lean
+hbox.before_of_sorted hsorted
+```
+
+## Guardrails
+
+The new theorem does not prove numeric depth comparison:
+
+```lean
+W.val < W'.val
+```
+
+It also does not add coverage, transport, propagation, convergence, or any
+global Collatz claim.  It only connects an explicit adjacent pair in a sorted
+witness list to the already-defined witness-level `Before` relation.
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
+`git diff --check` is run as the final whitespace gate for this checkpoint.
+
+## Next Branch Prediction
+
+The next natural branch is pair comparison under the `Before` relation.
+
+Candidate direction:
+
+```text
+SourcePressureOrientedNeighborBoxState L W W'
+  + SourcePressureLocalIslandWitnessListSortedBefore L
+  -> SourcePressureLocalIslandWitnessBefore W W'
+  -> pair comparison facts usable by the pressure-beam layer
+```
+
+If a numeric theorem is needed, the next investigation should inspect whether
+`SourcePressureLocalIslandWitnessBefore W W'` already implies a useful value or
+address inequality.  If it does not, the smallest bridge should be added at the
+`SourcePressureLocalIslandWitnessBefore` layer, not at the box layer.
````
`````
