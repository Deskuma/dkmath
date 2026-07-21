# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: b120b73b847d7cf7cff10483eb544e70f558dc80

## Report

実装完了です。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:1159) に `SourcePressureForwardPairComparisonState.indexed_boundary_pair_surface` を追加しました。

これで `FPC` から、左右の局所 pulse 境界符号と center index の順序を同時に取れます。

```text
left previous <= 0
left center > 0
left next <= 0
right previous <= 0
right center > 0
right next <= 0
r + W.val < r + W'.val
```

レポートは [report-petal-270.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-270.md:1) に追加済みです。

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
`FPC` の boundary sign surface が、`SourcePressureMarginInt` の実 index 言語へ揃った。

追加：

```lean id="l0t6w3"
theorem SourcePressureForwardPairComparisonState.indexed_boundary_pair_surface
```

内容は狙い通り。

```text id="ozrf4b"
left previous <= 0
left center   > 0
left next     <= 0

right previous <= 0
right center   > 0
right next     <= 0

r + W.val < r + W'.val
```

`boundary_sign_pair_surface` と `center_index_lt` を束ねる薄い theorem として、よく閉じている。

## 増えた事実

これで `FPC` の比較 surface は、value 側ではなく margin index 側で読める。

```text id="eieb5a"
FPC
  -> left/right boundary signs
  -> center index order
```

特に、これまでは最後が

```lean id="i5t1tb"
W.val < W'.val
```

だったが、今回から

```lean id="bsa69x"
r + W.val < r + W'.val
```

として直接使える。

これは次の干渉・分離・隣接比較で効く。

## 現在の状態表

```text id="v7h2u7"
SortedFailure + sorted(L)
  -> FPC ∨ PO

FailureResolution + sorted(L)
  -> FPC ∨ PO

BeamSeed + sorted(L)
  -> FPC ∨ PO

FPC
  -> center_pair_surface
  -> boundary_sign_pair_surface
  -> center_index_lt
  -> center_index_ne
  -> indexed_boundary_pair_surface
```

ここまでで `FPC` は、二つの局所 pulse window が index 順序付きで並ぶ状態になった。

## 次に攻める定理

次は、index-level の noncoincidence surface を束ねる。

```lean id="l6278a"
theorem SourcePressureForwardPairComparisonState.indexed_center_separation_surface
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    r + W.val < r + W'.val ∧
      r + W.val ≠ r + W'.val
```

これは `center_index_lt` と `center_index_ne` の束ね。

さらに boundary 付きにするなら：

```lean id="i0cwtj"
theorem SourcePressureForwardPairComparisonState.indexed_boundary_separation_surface
```

で、`indexed_boundary_pair_surface` の payload に `center_index_ne` も加える。

## Codex 指示

```text id="mwktp3"
Goal:
  Add compact index-level center separation surfaces from
  SourcePressureForwardPairComparisonState.

Add in PressureState.lean:

  theorem SourcePressureForwardPairComparisonState.indexed_center_separation_surface
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W') :
      r + W.val < r + W'.val ∧
        r + W.val ≠ r + W'.val

Optional if useful:

  theorem SourcePressureForwardPairComparisonState.indexed_boundary_separation_surface
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W') :
      SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
        0 < SourcePressureMarginInt n k (r + W.val) ∧
          SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
            SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
              0 < SourcePressureMarginInt n k (r + W'.val) ∧
                SourcePressureMarginInt n k (r + W'.val + 1) ≤ 0 ∧
                  r + W.val < r + W'.val ∧
                    r + W.val ≠ r + W'.val

Use:
  h.center_index_lt
  h.center_index_ne
  h.indexed_boundary_pair_surface

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

次で `FPC` はこうなる。

```text id="dmkx0a"
FPC
  -> left/right boundary signs
  -> ordered center indices
  -> distinct center indices
```

その次に、中心間距離が `1` か `2以上` かへ分けられる。
ここから隣接 pulse の干渉面、つまり「隣り合う正中心がどの boundary を共有するか」に入れる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 9bdbae8e..da4add25 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -1149,6 +1149,30 @@ theorem SourcePressureForwardPairComparisonState.center_index_ne
     r + W.val ≠ r + W'.val :=
   ne_of_lt h.center_index_lt

+/--
+Boundary-sign pair surface with the order stated at the actual center indices.
+
+This is the same two-pulse boundary surface as
+`boundary_sign_pair_surface`, but the final comparison is expressed in the
+index language used by `SourcePressureMarginInt`.
+-/
+theorem SourcePressureForwardPairComparisonState.indexed_boundary_pair_surface
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
+                r + W.val < r + W'.val := by
+  rcases h.boundary_sign_pair_surface with
+    ⟨hprevL, hcenterL, hnextL, hprevR, hcenterR, hnextR, _hlt⟩
+  exact ⟨hprevL, hcenterL, hnextL, hprevR, hcenterR, hnextR,
+    h.center_index_lt⟩
+
 /--
 Constructor from the forward box comparison state to the pair-comparison-facing
 state.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-270.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-270.md
new file mode 100644
index 00000000..f8296d59
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-270.md
@@ -0,0 +1,93 @@
+# Report: petal-270
+
+## Goal
+
+Bundle boundary signs with index-level center order.
+
+Target surface:
+
+```text
+FPC
+  -> left local pulse signs
+  -> right local pulse signs
+  -> r + W.val < r + W'.val
+```
+
+## Implemented
+
+Added the following theorem in
+`DkMath.Collatz.PetalBridge.PressureState`:
+
+```lean
+SourcePressureForwardPairComparisonState.indexed_boundary_pair_surface
+```
+
+The proof combines:
+
+```lean
+h.boundary_sign_pair_surface
+h.center_index_lt
+```
+
+## Meaning
+
+The forward pair-comparison branch now has a boundary-sign surface stated in
+the same index language as `SourcePressureMarginInt`.
+
+The theorem exposes:
+
+```text
+left previous <= 0
+left center > 0
+left next <= 0
+right previous <= 0
+right center > 0
+right next <= 0
+r + W.val < r + W'.val
+```
+
+This is the comparison-ready version of the two local pulse windows.  It avoids
+forcing downstream callers to translate `W.val < W'.val` into center-index
+order each time.
+
+## Guardrails
+
+This checkpoint only rebundles already proved local facts.
+
+It does not assert:
+
+- a minimum distance between the two center indices beyond strict order;
+- non-overlap of the whole pulse windows;
+- uniqueness of positive centers;
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
+The next natural branch is to derive a compact noncoincidence theorem for the
+two positive center indices together with their boundary signs:
+
+```text
+indexed_boundary_pair_surface
+center_index_ne
+```
+
+If more useful for callers, this can be phrased as a named two-center
+separation surface before moving into interference/overlap comparisons.
````
`````
