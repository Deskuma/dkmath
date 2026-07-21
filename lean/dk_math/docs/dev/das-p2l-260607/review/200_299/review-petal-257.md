# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 8a221612ccda89f64173e1af75b0450c352ab012

## Report

実装完了です。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:689) に、`Before` から address-level / value-level 比較を取り出す projection 群を追加しました。

追加 theorem:

- `SourcePressureOrientedNeighborBoxState.addressBefore_of_sorted`
- `SourcePressureOrientedNeighborBoxState.rightEdge_lt_start_of_sorted`
- `SourcePressureOrientedNeighborBoxState.rightEdge_le_start_of_sorted`
- `SourcePressureOrientedNeighborBoxState.val_lt_of_sorted`
- `SourcePressureOrientedNeighborBoxState.val_le_of_sorted`

結論として、今の構造ではここまで取れます。

```text
Box(W,W') + sorted(L)
  -> addressBefore(W,W')
  -> rightEdge(W) < start(W')
  -> W.val < W'.val
```

local-island witness が singleton interval-pulse address へ変換されるため、`W.val < W'.val` まで自然に閉じました。

レポート:
[report-petal-257.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-257.md)

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureState` 成功
- `lake build DkMath.Collatz.PetalBridge` 成功
- `git diff --check` 成功

現在の差分は `PressureState.lean` と `report-petal-257.md` です。

## Review

## 判定

採用。
ついに `Box + sorted(L)` から数値順序まで落ちた。

追加：

```lean
SourcePressureOrientedNeighborBoxState.addressBefore_of_sorted
SourcePressureOrientedNeighborBoxState.rightEdge_lt_start_of_sorted
SourcePressureOrientedNeighborBoxState.rightEdge_le_start_of_sorted
SourcePressureOrientedNeighborBoxState.val_lt_of_sorted
SourcePressureOrientedNeighborBoxState.val_le_of_sorted
```

到達した結論：

```text
Box(W,W') + sorted(L)
  -> addressBefore(W,W')
  -> rightEdge(W) < start(W')
  -> W.val < W'.val
```

local-island witness が singleton interval-pulse address へ変換されるため、`W.val < W'.val` まで自然に閉じた。これは大きい。

## 増えた事実

前回まで：

```text
Box(W,W') + sorted(L)
  -> W before W'
```

今回：

```text
Box(W,W') + sorted(L)
  -> W.val < W'.val
```

つまり、比較層が **address-level** から **native depth/value-level** に降りた。

特にこの流れが綺麗。

```text
SourcePressureLocalIslandWitnessBefore W W'
  = address-before between singleton addresses

address-before:
  A.start + A.len <= B.start

singleton address:
  rightEdge(W) = W.val
  start(W') = W'.val

therefore:
  W.val < W'.val
```

## 現在の状態表

```text
SortedFailure
  -> Box ∨ PO

FailureResolution
  -> Box ∨ PO

BeamSeed
  -> Box ∨ PO

Box + sorted(L)
  -> W before W'
  -> W.val < W'.val
```

ここまでで、`Box` は単なる二点診断ではなく、**順序付き深さ比較を持つ二点診断**になった。

## 次に攻める定理

次は `val_lt_of_sorted` から使いやすい否定・非衝突系を薄く出す。

まずこれ。

```lean
theorem SourcePressureOrientedNeighborBoxState.val_ne_of_sorted
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (hbox : SourcePressureOrientedNeighborBoxState L W W')
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
    W.val ≠ W'.val
```

証明は `ne_of_lt (hbox.val_lt_of_sorted hsorted)`。

次に reverse 排除。

```lean
theorem SourcePressureOrientedNeighborBoxState.not_val_ge_of_sorted
    ...
    ¬ W'.val ≤ W.val
```

またはより Lean で使いやすく、

```lean
theorem SourcePressureOrientedNeighborBoxState.not_val_eq_of_sorted
```

だけ先に置くのがよい。

## Codex 指示

```text
Goal:
  Add small caller-facing consequences of val_lt_of_sorted.

Add in PressureState.lean:

  theorem SourcePressureOrientedNeighborBoxState.val_ne_of_sorted
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (hbox : SourcePressureOrientedNeighborBoxState L W W')
      (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
      W.val ≠ W'.val

Optionally add:

  theorem SourcePressureOrientedNeighborBoxState.not_val_ge_of_sorted
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (hbox : SourcePressureOrientedNeighborBoxState L W W')
      (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
      ¬ W'.val ≤ W.val

Use:
  hbox.val_lt_of_sorted hsorted
  ne_of_lt
  omega or exact not_le_of_gt ...

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

ここからは非衝突・逆向き排除。

```text
Box(W,W') + sorted(L)
  -> W.val < W'.val
  -> W.val ≠ W'.val
  -> not reverse order
```

この小補題群を置いたら、次は pair comparison 本体へ進める。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 0b001a6e..1ce48b95 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -677,6 +677,105 @@ theorem SourcePressureOrientedNeighborBoxState.before_of_sorted
   sourcePressureAdjacentPairInList_before_of_sorted hsorted
     hbox.orderedAdjacentPairInList

+/--
+Address-level projection of `before_of_sorted`.
+
+`SourcePressureLocalIslandWitnessBefore` is definitionally the address-level
+`SourcePressureIntervalPulseAddressBefore` relation after converting both
+witnesses to singleton interval-pulse addresses.  This theorem keeps that
+definition available under a box-facing name so later comparison proofs can
+work directly with address coordinates.
+-/
+theorem SourcePressureOrientedNeighborBoxState.addressBefore_of_sorted
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hbox : SourcePressureOrientedNeighborBoxState L W W')
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    SourcePressureIntervalPulseAddressBefore
+      (sourcePressureIntervalPulseAddress_of_localIslandWitness W)
+      (sourcePressureIntervalPulseAddress_of_localIslandWitness W') :=
+  hbox.before_of_sorted hsorted
+
+/--
+Address-coordinate form of the ordered box comparison.
+
+The address-level before relation is `A.start + A.len ≤ B.start`.  Since
+interval-pulse addresses have positive length, this gives a strict separation
+between the left endpoint's right edge `A.start + A.len - 1` and the right
+endpoint's start.
+
+This is still only an address comparison.  It does not claim coverage,
+transport, or global monotonicity of all pressure depths.
+-/
+theorem SourcePressureOrientedNeighborBoxState.rightEdge_lt_start_of_sorted
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hbox : SourcePressureOrientedNeighborBoxState L W W')
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    (sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
+        (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1 <
+      (sourcePressureIntervalPulseAddress_of_localIslandWitness W').start := by
+  have hbefore := hbox.addressBefore_of_sorted hsorted
+  have hlen :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len :=
+    SourcePressureIntervalPulseAddress.len_pos
+      (sourcePressureIntervalPulseAddress_of_localIslandWitness W)
+  unfold SourcePressureIntervalPulseAddressBefore at hbefore
+  omega
+
+/--
+Non-strict version of `rightEdge_lt_start_of_sorted`.
+
+This wrapper is useful for callers that consume non-overlap as a weak
+inequality while the strict version remains available for depth comparison.
+-/
+theorem SourcePressureOrientedNeighborBoxState.rightEdge_le_start_of_sorted
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hbox : SourcePressureOrientedNeighborBoxState L W W')
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    (sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
+        (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1 ≤
+      (sourcePressureIntervalPulseAddress_of_localIslandWitness W').start :=
+  le_of_lt (hbox.rightEdge_lt_start_of_sorted hsorted)
+
+/--
+Value-level comparison extracted from a sorted oriented neighbor box.
+
+For local-island witnesses, the generated interval-pulse address is a
+singleton: its start and right edge are both `W.val`.  Therefore the
+address-level strict separation becomes the native depth comparison
+`W.val < W'.val`.
+
+This theorem is the strongest direct numeric comparison available from the
+current definitions: it depends on the explicit adjacent pair inside the box
+and on the sortedness invariant for the enclosing witness list.
+-/
+theorem SourcePressureOrientedNeighborBoxState.val_lt_of_sorted
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hbox : SourcePressureOrientedNeighborBoxState L W W')
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    W.val < W'.val := by
+  have hsep := hbox.rightEdge_lt_start_of_sorted hsorted
+  rw [sourcePressureIntervalPulseAddress_of_localIslandWitness_rightEdge_eq,
+    sourcePressureIntervalPulseAddress_of_localIslandWitness_start_eq] at hsep
+  exact hsep
+
+/-- Non-strict value-level wrapper for callers that only need `≤`. -/
+theorem SourcePressureOrientedNeighborBoxState.val_le_of_sorted
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hbox : SourcePressureOrientedNeighborBoxState L W W')
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    W.val ≤ W'.val :=
+  le_of_lt (hbox.val_lt_of_sorted hsorted)
+
 /--
 Package an oriented neighbor diagnostic into the two-endpoint box state.

diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-257.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-257.md
new file mode 100644
index 00000000..32dea017
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-257.md
@@ -0,0 +1,126 @@
+# Report: petal-257
+
+## Goal
+
+Extract address-level comparison facts from
+`SourcePressureLocalIslandWitnessBefore`, then expose the strongest direct
+numeric comparison available for a sorted oriented neighbor box.
+
+## Investigation
+
+The witness-level order is definitionally the address-level order:
+
+```lean
+SourcePressureLocalIslandWitnessBefore W W'
+```
+
+unfolds to:
+
+```lean
+SourcePressureIntervalPulseAddressBefore
+  (sourcePressureIntervalPulseAddress_of_localIslandWitness W)
+  (sourcePressureIntervalPulseAddress_of_localIslandWitness W')
+```
+
+The address-level order itself is:
+
+```lean
+A.start + A.len <= B.start
+```
+
+For local-island witnesses, the converted interval-pulse address is a singleton.
+Existing coordinate lemmas give:
+
+```lean
+(sourcePressureIntervalPulseAddress_of_localIslandWitness W).start = W.val
+(sourcePressureIntervalPulseAddress_of_localIslandWitness W).start
+  + (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1
+  = W.val
+```
+
+Therefore the sorted box comparison can be pushed all the way to:
+
+```lean
+W.val < W'.val
+```
+
+## Implemented
+
+Added in `DkMath.Collatz.PetalBridge.PressureState`:
+
+```lean
+theorem SourcePressureOrientedNeighborBoxState.addressBefore_of_sorted
+theorem SourcePressureOrientedNeighborBoxState.rightEdge_lt_start_of_sorted
+theorem SourcePressureOrientedNeighborBoxState.rightEdge_le_start_of_sorted
+theorem SourcePressureOrientedNeighborBoxState.val_lt_of_sorted
+theorem SourcePressureOrientedNeighborBoxState.val_le_of_sorted
+```
+
+## Meaning
+
+The comparison chain is now available as a box-facing API:
+
+```text
+Box(W,W')
+  + SourcePressureLocalIslandWitnessListSortedBefore L
+  -> SourcePressureLocalIslandWitnessBefore W W'
+  -> address-before between singleton interval-pulse addresses
+  -> right-edge(W) < start(W')
+  -> W.val < W'.val
+```
+
+This is the first explicit numeric/depth comparison extracted from the
+two-endpoint box state.
+
+## Guardrails
+
+The new `val_lt_of_sorted` theorem is still local:
+
+* it depends on the explicit oriented neighbor box;
+* it depends on sortedness of the enclosing witness list;
+* it does not sort arbitrary lists;
+* it does not assert global coverage of local islands;
+* it does not propagate the comparison beyond the two endpoints;
+* it does not prove convergence.
+
+The proof succeeds because local-island witnesses generate singleton
+interval-pulse addresses.  For a future non-singleton address carrier, the
+strong direct comparison would remain the address-level
+`rightEdge < start`, not necessarily a native `val` comparison.
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
+The natural next branch is to use `val_lt_of_sorted` in pair-comparison or
+neighbor-exclusion statements.
+
+Candidate directions:
+
+```text
+Box(W,W') + sorted(L)
+  -> W.val < W'.val
+  -> W.val != W'.val
+```
+
+and, if useful for downstream automation:
+
+```text
+Box(W,W') + sorted(L)
+  -> not reverse address-before
+  -> not reverse box ordering
+```
+
+The second direction should be added only if a caller needs a negative
+orientation fact.  The clean positive fact is now `val_lt_of_sorted`.
````
`````
