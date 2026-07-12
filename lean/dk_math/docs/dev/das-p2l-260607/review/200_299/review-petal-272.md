# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 960b758b11d7bdeb7564fda9aa63f8c62c43a9d9

## Report

通りました。これで分かることは、`FPC` の左右の正中心は「異なる」だけでなく「隣接すらできない」ということです。

具体的には [PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:1223) に追加しました。

- `SourcePressureForwardPairComparisonState.not_right_val_eq_left_succ`
- `SourcePressureForwardPairComparisonState.left_succ_lt_right_val`

意味はこうです。

```text
FPC
  -> W.val < W'.val
  -> W'.val ≠ W.val + 1
  -> W.val + 1 < W'.val
```

つまり、左の正中心の直後に右の正中心は置けません。理由は、もし `W'.val = W.val + 1` なら、右 pulse の previous boundary が左 pulse の positive center と同じ index になり、同じ margin が

```text
0 < margin
margin <= 0
```

を同時に満たして矛盾するためです。これは最初の実質的な interference theorem です。

レポートは [report-petal-272.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-272.md:1) に追加済みです。

検証:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

すべて通過しました。

## Review

## 判定

採用。
これは大きい。`FPC` で初めて **boundary sign が実際に干渉して、隣接中心を排除する theorem** が通った。

追加：

```lean id="r6dhsm"
SourcePressureForwardPairComparisonState.not_right_val_eq_left_succ
SourcePressureForwardPairComparisonState.left_succ_lt_right_val
```

これで、

```text id="z3k7nq"
FPC
  -> W.val < W'.val
  -> W'.val ≠ W.val + 1
  -> W.val + 1 < W'.val
```

が取れる。つまり、左右の正中心は「異なる」だけでなく、**隣接すらできない**。

## 増えた事実

今回の核心はここ。

```text id="t57ygf"
もし W'.val = W.val + 1 なら、
right previous boundary index = left center index
```

すると、同じ margin に対して、

```text id="bgvw0j"
left center:
  0 < margin

right previous:
  margin <= 0
```

が同時に出て矛盾する。

これは単なる projection ではなく、左右 pulse window の符号が衝突して生まれた **最初の実質的 interference theorem** じゃ。

## 現在の状態表

```text id="ktyh0d"
SortedFailure + sorted(L)
  -> FPC ∨ PO

FailureResolution + sorted(L)
  -> FPC ∨ PO

BeamSeed + sorted(L)
  -> FPC ∨ PO

FPC
  -> boundary signs
  -> center index order
  -> center index separation
  -> W.val + 1 < W'.val
```

これで `FPC` は、

```text id="8bx34s"
正中心
非正 boundary
少なくとも 1 slot の gap
非正 boundary
正中心
```

という形を強制する。

## 数学的意味

これは `FPC` branch における **局所 pulse 間の最小距離** だと読める。

以前：

```text id="am4x86"
W.val < W'.val
```

今回：

```text id="sq6xvg"
W.val + 1 < W'.val
```

この差は大きい。
前者は「順序」。後者は「干渉による隣接禁止」。

つまり、正中心は連続して並べない。
間に少なくとも一つの値 slot が必要になる。

## 次に攻める定理

次は report の予測通り、index-level 版。

```lean id="dxz2rz"
theorem SourcePressureForwardPairComparisonState.left_next_index_lt_right_center_index
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    r + W.val + 1 < r + W'.val
```

または、既存 index 表記に合わせるなら：

```lean id="ljzwum"
theorem SourcePressureForwardPairComparisonState.left_next_boundary_lt_right_center_index
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    r + (W.val + 1) < r + W'.val
```

`h.left_succ_lt_right_val` と `omega` で閉じるはず。

## Codex 指示

```text id="fk4k4e"
Goal:
  Add the index-level form of the first interference theorem.

Add in PressureState.lean:

  theorem SourcePressureForwardPairComparisonState.left_next_index_lt_right_center_index
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W') :
      r + W.val + 1 < r + W'.val

Optionally also add the syntactic variant:

  theorem SourcePressureForwardPairComparisonState.left_next_boundary_lt_right_center_index
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W') :
      r + (W.val + 1) < r + W'.val

Use:
  h.left_succ_lt_right_val
  omega

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

次で margin-index 側でも、

```text id="y4xvfi"
left next boundary < right center
```

が言える。
その後は、左 pulse window と右 pulse window が中心隣接では重ならない、という **window separation surface** へ進める。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 9caa0104..f80a22c7 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -1213,6 +1213,44 @@ theorem SourcePressureForwardPairComparisonState.indexed_boundary_separation_sur
   exact ⟨hprevL, hcenterL, hnextL, hprevR, hcenterR, hnextR, hlt,
     h.center_index_ne⟩
 
+/--
+First interference theorem for a forward pair comparison state.
+
+The right positive center cannot be exactly the successor of the left positive
+center.  If it were, the right endpoint's previous nonpositive boundary would
+coincide with the left endpoint's positive center.
+-/
+theorem SourcePressureForwardPairComparisonState.not_right_val_eq_left_succ
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    W'.val ≠ W.val + 1 := by
+  intro hsucc
+  rcases h.boundary_sign_pair_surface with
+    ⟨_, hcenterL, _, hprevR, _, _, _⟩
+  have hidx : r + (W'.val - 1) = r + W.val := by
+    omega
+  have hle : SourcePressureMarginInt n k (r + W.val) ≤ 0 := by
+    simpa [hidx] using hprevR
+  exact (not_le_of_gt hcenterL) hle
+
+/--
+The right positive center is separated from the left positive center by more
+than one value step.
+
+This is the value-level form of the first interference theorem.
+-/
+theorem SourcePressureForwardPairComparisonState.left_succ_lt_right_val
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    W.val + 1 < W'.val := by
+  have hlt : W.val < W'.val := h.val_lt
+  have hne : W'.val ≠ W.val + 1 := h.not_right_val_eq_left_succ
+  omega
+
 /--
 Constructor from the forward box comparison state to the pair-comparison-facing
 state.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-272.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-272.md
new file mode 100644
index 00000000..b2741965
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-272.md
@@ -0,0 +1,112 @@
+# Report: petal-272
+
+## Goal
+
+Prove the first interference theorem:
+
+```text
+in a forward pair comparison state,
+the right positive center cannot be exactly the successor of the left center
+```
+
+## Implemented
+
+Added the following theorems in
+`DkMath.Collatz.PetalBridge.PressureState`:
+
+```lean
+SourcePressureForwardPairComparisonState.not_right_val_eq_left_succ
+SourcePressureForwardPairComparisonState.left_succ_lt_right_val
+```
+
+The first theorem uses the local pulse boundary signs:
+
+```text
+left center > 0
+right previous <= 0
+```
+
+If `W'.val = W.val + 1`, then the right previous index coincides with the left
+center index.  This would force the same margin value to be both positive and
+nonpositive.
+
+The second theorem combines:
+
+```lean
+h.val_lt
+h.not_right_val_eq_left_succ
+```
+
+with `omega`.
+
+## What This Shows
+
+This is stronger than distinctness.
+
+Before this checkpoint, the forward pair gave:
+
+```text
+W.val < W'.val
+```
+
+Now it gives:
+
+```text
+W.val + 1 < W'.val
+```
+
+So two positive centers in an `FPC` branch cannot be adjacent.  There must be at
+least one value slot between them.
+
+In local-pulse language:
+
+```text
+positive center
+nonpositive next / previous boundary
+positive center
+```
+
+cannot collapse into adjacent centers.  The boundary sign pattern enforces a
+real gap.
+
+## Guardrails
+
+This checkpoint proves a local interference fact for the explicit forward pair.
+
+It does not assert:
+
+- global spacing for all centers;
+- uniqueness of centers;
+- non-overlap of all pulse windows;
+- absence of other witnesses between unrelated pairs;
+- global coverage;
+- Collatz convergence.
+
+The pair-overlap obstruction branch remains separate.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureState
+```
+
+The final gate for this checkpoint also runs:
+
+```text
+lake build DkMath.Collatz.PetalBridge
+git diff --check
+```
+
+## Next Branch Prediction
+
+The next useful theorem is the index-level form:
+
+```text
+r + W.val + 1 < r + W'.val
+```
+
+or, equivalently, the right center is strictly beyond the left center's next
+boundary.  That would make the pulse-window separation usable directly in
+margin-index proofs.
````
`````
