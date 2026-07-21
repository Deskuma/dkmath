# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 6320d9a8949dfffd805b95c27914fc1dceca5c72

## Report

実装完了です。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:1134) に index-level の順序補題を追加しました。

- `SourcePressureForwardPairComparisonState.center_index_lt`
- `SourcePressureForwardPairComparisonState.center_index_ne`

これで `FPC` から `W.val < W'.val` だけでなく、実際に margin が参照する center index 側でも

```text
r + W.val < r + W'.val
r + W.val ≠ r + W'.val
```

が直接取れます。

レポートは [report-petal-269.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-269.md:1) に追加済みです。

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
`FPC` の value order が、実際に `SourcePressureMarginInt` が参照する center index order へ持ち上がった。

追加：

```lean id="f8x0cw"
SourcePressureForwardPairComparisonState.center_index_lt
SourcePressureForwardPairComparisonState.center_index_ne
```

これで `FPC` から、

```text id="jph7kx"
W.val < W'.val
r + W.val < r + W'.val
r + W.val ≠ r + W'.val
```

が直接取れる。`center_index_lt` は `h.val_lt` と `omega`、`center_index_ne` は `ne_of_lt` で閉じており、狙い通りの薄い index bridge じゃ。

## 増えた事実

これまでの比較は witness value 側だった。

```text id="e287f3"
W.val < W'.val
```

今回から、margin index 側でも比較できる。

```text id="6m5z1m"
r + W.val < r + W'.val
```

これは重要。
`boundary_sign_pair_surface` の各項は、

```text id="9h6k5h"
r + (W.val - 1)
r + W.val
r + W.val + 1
```

の形で出るので、今後の干渉・隣接・分離補題が index 上で書ける。

## 現在の状態表

```text id="uam8k0"
SortedFailure + sorted(L)
  -> FPC ∨ PO

FailureResolution + sorted(L)
  -> FPC ∨ PO

BeamSeed + sorted(L)
  -> FPC ∨ PO

FPC
  -> boundary_sign_pair_surface
  -> center_pair_surface
  -> center_index_lt
  -> center_index_ne
```

かなり良い。
`FPC` は「二つの局所 pulse 中心が、margin index 上でも順序付きで分離している」と読めるようになった。

## 次に攻める定理

次は `center_index_lt` と boundary sign を束ねて、**index-level pulse pair surface** を作る。

```lean id="q5vtl8"
theorem SourcePressureForwardPairComparisonState.indexed_boundary_pair_surface
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
                r + W.val < r + W'.val
```

既存 `boundary_sign_pair_surface` の最後だけ、`W.val < W'.val` から `r + W.val < r + W'.val` に差し替える theorem じゃ。

## Codex 指示

```text id="jba1zd"
Goal:
  Bundle boundary signs with index-level center order.

Add in PressureState.lean:

  theorem SourcePressureForwardPairComparisonState.indexed_boundary_pair_surface
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
                  r + W.val < r + W'.val

Use:
  h.boundary_sign_pair_surface
  h.center_index_lt

Proof shape:
  rcases h.boundary_sign_pair_surface with
    ⟨hprevL, hcenterL, hnextL, hprevR, hcenterR, hnextR, _hlt⟩
  exact ⟨hprevL, hcenterL, hnextL, hprevR, hcenterR, hnextR,
    h.center_index_lt⟩

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

次で `FPC` はこうなる。

```text id="c54rmo"
FPC
  -> left boundary signs
  -> right boundary signs
  -> center index order
```

その次に、中心間距離が `1` の場合と `2以上` の場合へ分けるとよい。
ここから、隣接 pulse の干渉・非干渉を読む段階に入れる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 4ee70e8f..9bdbae8e 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -1127,6 +1127,28 @@ theorem SourcePressureForwardPairComparisonState.boundary_sign_pair_surface
   rcases h.right_signs with ⟨_, hprevR, hcenterR, _, hnextR⟩
   exact ⟨hprevL, hcenterL, hnextL, hprevR, hcenterR, hnextR, h.val_lt⟩

+/--
+Lift the forward value order to the actual center indices used by the margin
+function.
+-/
+theorem SourcePressureForwardPairComparisonState.center_index_lt
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    r + W.val < r + W'.val := by
+  have hlt : W.val < W'.val := h.val_lt
+  omega
+
+/-- The two center indices of a forward pair comparison state are distinct. -/
+theorem SourcePressureForwardPairComparisonState.center_index_ne
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    r + W.val ≠ r + W'.val :=
+  ne_of_lt h.center_index_lt
+
 /--
 Constructor from the forward box comparison state to the pair-comparison-facing
 state.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-269.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-269.md
new file mode 100644
index 00000000..246fe0b9
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-269.md
@@ -0,0 +1,88 @@
+# Report: petal-269
+
+## Goal
+
+Add index-level center order consequences from
+`SourcePressureForwardPairComparisonState`.
+
+Target surface:
+
+```text
+FPC
+  -> W.val < W'.val
+  -> r + W.val < r + W'.val
+  -> center indices are distinct
+```
+
+## Implemented
+
+Added the following theorems in
+`DkMath.Collatz.PetalBridge.PressureState`:
+
+```lean
+SourcePressureForwardPairComparisonState.center_index_lt
+SourcePressureForwardPairComparisonState.center_index_ne
+```
+
+The first theorem uses `h.val_lt` and `omega`.  The second theorem is a direct
+`ne_of_lt` projection from the strict index order.
+
+## Meaning
+
+The forward pair-comparison branch now descends from witness-value order to the
+actual center indices used by `SourcePressureMarginInt`.
+
+This is useful because boundary and center facts are stated at indices such as:
+
+```text
+r + (W.val - 1)
+r + W.val
+r + W.val + 1
+```
+
+The new theorems make the center-index separation explicit before later
+comparison lemmas combine it with boundary-sign surfaces.
+
+## Guardrails
+
+This checkpoint only transports an already proved local value order through
+addition by `r`.
+
+It does not assert:
+
+- a minimum gap larger than one;
+- non-overlap of the full pulse windows;
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
+The next natural branch is to combine index separation with the boundary-sign
+surface:
+
+```text
+boundary_sign_pair_surface
+center_index_lt
+center_index_ne
+```
+
+This should support the first interference/adjacency reading theorem for two
+positive pulse centers.
````
`````
