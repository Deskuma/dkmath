# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 5d294e0505abcb93c7b84c176aa8b0b5ac9428e5

## Report

実装完了です。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:1182) に compact separation surface を追加しました。

- `SourcePressureForwardPairComparisonState.indexed_center_separation_surface`
- `SourcePressureForwardPairComparisonState.indexed_boundary_separation_surface`

これで `FPC` から、中心 index の strict order と noncoincidence をまとめて取れます。optional 側では、左右の boundary sign window も一緒に保持します。

レポートは [report-petal-271.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-271.md:1) に追加済みです。

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
`FPC` から center index の strict order と noncoincidence をまとめて取れる compact surface が追加された。

追加：

```lean id="yb94fe"
SourcePressureForwardPairComparisonState.indexed_center_separation_surface
SourcePressureForwardPairComparisonState.indexed_boundary_separation_surface
```

`indexed_center_separation_surface` は、

```text id="d0w4k8"
r + W.val < r + W'.val
r + W.val ≠ r + W'.val
```

を束ねる。
`indexed_boundary_separation_surface` は、左右 boundary sign window に加えて、この separation も同時に持つ。`center_index_lt / center_index_ne / indexed_boundary_pair_surface` の薄い包装として良い。

## 増えた事実

`FPC` はここまで来た。

```text id="igrtpy"
FPC
  -> left/right boundary signs
  -> r + W.val < r + W'.val
  -> r + W.val ≠ r + W'.val
```

つまり、二つの正中心が margin index 上で一致しないことは、もう直接呼べる。

## 現在の状態表

```text id="hcaxvr"
SortedFailure + sorted(L)
  -> FPC ∨ PO

FailureResolution + sorted(L)
  -> FPC ∨ PO

BeamSeed + sorted(L)
  -> FPC ∨ PO

FPC
  -> indexed_boundary_pair_surface
  -> indexed_center_separation_surface
  -> indexed_boundary_separation_surface
```

この checkpoint で、index-level separation surface は完成。

## 次に攻める定理

次は、いよいよ最初の干渉補題に入れる。

重要なのはこれ。

```text id="yfur4t"
もし W'.val = W.val + 1 なら、
right previous index = left center index
```

すると、

```text id="vshshc"
left center > 0
right previous <= 0
```

が同じ index に重なって矛盾する。

したがって、`FPC` では中心が隣接できない。

```lean id="vmszhm"
theorem SourcePressureForwardPairComparisonState.not_right_val_eq_left_succ
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    W'.val ≠ W.val + 1
```

さらに進めるなら、

```lean id="i5idnz"
theorem SourcePressureForwardPairComparisonState.left_succ_lt_right_val
    ... :
    W.val + 1 < W'.val
```

まで狙える。`h.val_lt` と `not_right_val_eq_left_succ` から、Nat の順序で閉じるはず。

## Codex 指示

```text id="gdffgy"
Goal:
  Prove the first interference theorem:
  in a forward pair comparison state, the right center cannot be exactly the
  successor of the left center.

Add in PressureState.lean:

  theorem SourcePressureForwardPairComparisonState.not_right_val_eq_left_succ
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W') :
      W'.val ≠ W.val + 1

Proof idea:
  Use h.boundary_sign_pair_surface.
  left center gives:
    0 < SourcePressureMarginInt n k (r + W.val)
  right previous gives:
    SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0
  If W'.val = W.val + 1, then:
    r + (W'.val - 1) = r + W.val
  Contradiction by not_le_of_gt.

Likely proof shape:
  intro hsucc
  rcases h.boundary_sign_pair_surface with
    ⟨_, hcenterL, _, hprevR, _, _, _⟩
  have hidx : r + (W'.val - 1) = r + W.val := by omega
  have hle : SourcePressureMarginInt n k (r + W.val) ≤ 0 := by
    simpa [hidx] using hprevR
  exact (not_le_of_gt hcenterL) hle

If this closes, optionally add:

  theorem SourcePressureForwardPairComparisonState.left_succ_lt_right_val
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W') :
      W.val + 1 < W'.val

Use:
  h.val_lt
  h.not_right_val_eq_left_succ
  omega

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

次が通ると強い。

```text id="d7q4ho"
FPC
  -> W.val + 1 < W'.val
```

つまり、二つの正中心は単に一致しないだけでなく、**隣接もできない**。
これは初めて boundary sign が実際に干渉して生む比較定理になる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index da4add25..9caa0104 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -1173,6 +1173,46 @@ theorem SourcePressureForwardPairComparisonState.indexed_boundary_pair_surface
   exact ⟨hprevL, hcenterL, hnextL, hprevR, hcenterR, hnextR,
     h.center_index_lt⟩
 
+/--
+Compact separation surface for the two center indices of a forward pair.
+
+The strict order is the main payload; the non-equality projection is repeated
+because many later obstruction and interference lemmas consume `≠` directly.
+-/
+theorem SourcePressureForwardPairComparisonState.indexed_center_separation_surface
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    r + W.val < r + W'.val ∧
+      r + W.val ≠ r + W'.val :=
+  ⟨h.center_index_lt, h.center_index_ne⟩
+
+/--
+Boundary-sign pair surface with explicit center-index separation.
+
+This is the caller-facing form for local pulse comparison: both endpoints carry
+their nonpositive-positive-nonpositive sign windows, and the center indices are
+strictly ordered and distinct.
+-/
+theorem SourcePressureForwardPairComparisonState.indexed_boundary_separation_surface
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
+      0 < SourcePressureMarginInt n k (r + W.val) ∧
+        SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
+          SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
+            0 < SourcePressureMarginInt n k (r + W'.val) ∧
+              SourcePressureMarginInt n k (r + W'.val + 1) ≤ 0 ∧
+                r + W.val < r + W'.val ∧
+                  r + W.val ≠ r + W'.val := by
+  rcases h.indexed_boundary_pair_surface with
+    ⟨hprevL, hcenterL, hnextL, hprevR, hcenterR, hnextR, hlt⟩
+  exact ⟨hprevL, hcenterL, hnextL, hprevR, hcenterR, hnextR, hlt,
+    h.center_index_ne⟩
+
 /--
 Constructor from the forward box comparison state to the pair-comparison-facing
 state.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-271.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-271.md
new file mode 100644
index 00000000..67c4130d
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-271.md
@@ -0,0 +1,109 @@
+# Report: petal-271
+
+## Goal
+
+Add compact index-level center separation surfaces from
+`SourcePressureForwardPairComparisonState`.
+
+Target surfaces:
+
+```text
+FPC
+  -> r + W.val < r + W'.val
+  -> r + W.val != r + W'.val
+```
+
+and, where useful:
+
+```text
+FPC
+  -> left/right boundary signs
+  -> r + W.val < r + W'.val
+  -> r + W.val != r + W'.val
+```
+
+## Implemented
+
+Added the following theorems in
+`DkMath.Collatz.PetalBridge.PressureState`:
+
+```lean
+SourcePressureForwardPairComparisonState.indexed_center_separation_surface
+SourcePressureForwardPairComparisonState.indexed_boundary_separation_surface
+```
+
+The first theorem bundles:
+
+```lean
+h.center_index_lt
+h.center_index_ne
+```
+
+The second theorem extends:
+
+```lean
+h.indexed_boundary_pair_surface
+```
+
+with:
+
+```lean
+h.center_index_ne
+```
+
+## Meaning
+
+The forward pair-comparison branch now has a compact separation surface at the
+same index level used by `SourcePressureMarginInt`.
+
+This matters for the next interference/overlap readings.  Those callers usually
+need both:
+
+- strict center-index order;
+- center-index noncoincidence.
+
+The optional boundary version keeps the local pulse windows and the separation
+facts together, avoiding repeated unpacking in later pair-comparison lemmas.
+
+## Guardrails
+
+This checkpoint only repackages already proved local facts.
+
+It does not assert:
+
+- a gap of at least two;
+- non-overlap of the full pulse windows;
+- uniqueness of positive centers;
+- absence of other centers;
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
+The next useful branch is probably a first negative/interference theorem:
+
+```text
+indexed_boundary_separation_surface
+  -> the two center indices do not coincide
+```
+
+That is already available directly through the new surface.  If callers need a
+single named obstruction-facing statement, add a theorem that projects the
+noncoincidence while retaining the boundary context.
````
`````
