# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 08b050a657b9ab24776c609e31f3ffbd6d60e7c1

## Report

Implemented and verified.

Added in [PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:1313):

- `SourcePressureForwardPairComparisonState.left_next_boundary_before_right_center`
- `SourcePressureForwardPairComparisonState.left_next_boundary_nonpos_and_before_right_center`

Added report:

- [report-petal-275.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-275.md)

Verification passed:

- `lake build DkMath.Collatz.PetalBridge.PressureState`
- `lake build DkMath.Collatz.PetalBridge`
- `git diff --check`

What is now established as fact: from any `SourcePressureForwardPairComparisonState L W W'`, Lean can directly project that the left next boundary is nonpositive and strictly before the right positive center:

```lean
SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
  r + W.val + 1 < r + W'.val
```

So the forward pair has a local index-level gap: the right center cannot sit at the left center’s successor, and the left successor boundary is already nonpositive before the right center appears. This is still local to the explicit pair state, not a global Collatz result.

現在、事実として確立されているのは、任意の `SourcePressureForwardPairComparisonState L W W'` に対して、Lean が「左側の次の境界が非正であり、かつ右側の正の中心よりも厳密に手前にある」ことを直接導き出せるという点です：

```lean
SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
r + W.val + 1 < r + W'.val
```

つまり、この前方ペア（forward pair）には局所的なインデックス・レベルのギャップが存在します。すなわち、右側の中心は左側の中心の直後（後続位置）には配置され得ず、右側の中心が現れるよりも前の段階で、左側の後続境界はすでに非正となっているのです。これはあくまで明示的なペアの状態に関する局所的な事実に過ぎず、コラッツ予想に関する大域的な結果ではありません。

## Review

## 判定

採用。
`indexed_boundary_gap_surface` から、次段でよく使う局所干渉 projection が切り出された。

追加：

```lean id="q95z1v"
SourcePressureForwardPairComparisonState.left_next_boundary_before_right_center
SourcePressureForwardPairComparisonState.left_next_boundary_nonpos_and_before_right_center
```

これで `FPC` から直接、

```lean id="khbmfs"
r + W.val + 1 < r + W'.val
```

および、

```lean id="h2sp67"
SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
  r + W.val + 1 < r + W'.val
```

が取れる。`indexed_boundary_gap_surface` の薄い projection として適切じゃ。

## 増えた事実

今回で、左 pulse の「次境界」が独立した caller-facing fact になった。

```text id="cvz8ds"
FPC
  -> left next boundary <= 0
  -> left next boundary < right center
```

これはかなり使いやすい。
今後、右中心との干渉を見るときに、長い boundary surface を毎回 destructuring しなくてよくなる。

## 現在の状態表

```text id="z5up1a"
SortedFailure + sorted(L)
  -> FPC ∨ PO

FailureResolution + sorted(L)
  -> FPC ∨ PO

BeamSeed + sorted(L)
  -> FPC ∨ PO

FPC
  -> indexed_boundary_gap_surface
  -> left_next_boundary_before_right_center
  -> left_next_boundary_nonpos_and_before_right_center
```

これで局所干渉の第一核はかなり締まった。

## 数学的意味

今回の theorem は、次の局所像を短く表す。

```text id="7bu1t8"
left center:
  positive

left next boundary:
  nonpositive
  strictly before right center

right center:
  positive
```

つまり、正中心がそのまま隣へ連続するのではなく、左中心の直後で一度 `<= 0` に落ち、その後に右中心が現れる。
これは `FPC` branch の **正中心間に非正境界が挟まる** という構造を、後段から呼びやすくしたものじゃ。

## 次に攻める定理

次は report の予測通り、もう少し豊かな interference surface を作るとよい。

```lean id="qnahry"
theorem SourcePressureForwardPairComparisonState.left_next_interference_surface
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    0 < SourcePressureMarginInt n k (r + W.val) ∧
      SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
        0 < SourcePressureMarginInt n k (r + W'.val) ∧
          r + W.val + 1 < r + W'.val
```

これで、

```text id="x7q09n"
left center > 0
left next <= 0
right center > 0
left next < right center
```

が一発で取れる。

## Codex 指示

```text id="vv5o1z"
Goal:
  Add a compact left-next interference surface for the next local
  window-comparison layer.

Add in PressureState.lean:

  theorem SourcePressureForwardPairComparisonState.left_next_interference_surface
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W') :
      0 < SourcePressureMarginInt n k (r + W.val) ∧
        SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
          0 < SourcePressureMarginInt n k (r + W'.val) ∧
            r + W.val + 1 < r + W'.val

Use:
  h.indexed_boundary_gap_surface
  or
  h.left_next_boundary_nonpos_and_before_right_center

Proof shape:
  rcases h.indexed_boundary_gap_surface with
    ⟨_, hcenterL, hnextL, _, hcenterR, _, _, _, hgap⟩
  exact ⟨hcenterL, hnextL, hcenterR, hgap⟩

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

次で `FPC` は局所干渉としてこう読める。

```text id="cyg3yr"
positive center
nonpositive next boundary
gap
positive center
```

その次は右側も対称的に、`right previous boundary` と左中心側の関係を projection 化すると、window separation の左右両面が揃う。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 02c0eaac..8bdb83b3 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -1306,6 +1306,36 @@ theorem SourcePressureForwardPairComparisonState.indexed_boundary_gap_surface
   exact ⟨hprevL, hcenterL, hnextL, hprevR, hcenterR, hnextR,
     hlt, hne, h.left_next_index_lt_right_center_index⟩

+/--
+Projection from `indexed_boundary_gap_surface`: the left next boundary index is
+strictly before the right positive center.
+-/
+theorem SourcePressureForwardPairComparisonState.left_next_boundary_before_right_center
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    r + W.val + 1 < r + W'.val := by
+  rcases h.indexed_boundary_gap_surface with
+    ⟨_, _, _, _, _, _, _, _, hgap⟩
+  exact hgap
+
+/--
+Compact caller-facing projection for the next interference layer: the left next
+boundary is nonpositive and still lies strictly before the right positive
+center.
+-/
+theorem SourcePressureForwardPairComparisonState.left_next_boundary_nonpos_and_before_right_center
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
+      r + W.val + 1 < r + W'.val := by
+  rcases h.indexed_boundary_gap_surface with
+    ⟨_, _, hnextL, _, _, _, _, _, hgap⟩
+  exact ⟨hnextL, hgap⟩
+
 /--
 Constructor from the forward box comparison state to the pair-comparison-facing
 state.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-275.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-275.md
new file mode 100644
index 00000000..de57b215
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-275.md
@@ -0,0 +1,89 @@
+# Report: petal-275
+
+## Goal
+
+Add compact projections from `indexed_boundary_gap_surface` for the next
+window-interference layer.
+
+## Implemented
+
+Added two projection theorems:
+
+- `SourcePressureForwardPairComparisonState.left_next_boundary_before_right_center`
+- `SourcePressureForwardPairComparisonState.left_next_boundary_nonpos_and_before_right_center`
+
+Both project from:
+
+- `SourcePressureForwardPairComparisonState.indexed_boundary_gap_surface`
+
+## Established Fact
+
+For any concrete forward pair comparison state
+
+```lean
+h : SourcePressureForwardPairComparisonState L W W'
+```
+
+Lean now exposes the following facts directly:
+
+```lean
+r + W.val + 1 < r + W'.val
+```
+
+and:
+
+```lean
+SourcePressureMarginInt n k (r + W.val + 1) <= 0
+  ∧ r + W.val + 1 < r + W'.val
+```
+
+The second theorem is the more useful caller-facing projection: it says the
+left next boundary is already nonpositive and still strictly before the right
+positive center.
+
+## What Can Be Concluded
+
+The forward pair comparison state now gives a compact local obstruction against
+immediate center contact:
+
+- the left center is positive;
+- its next boundary is nonpositive;
+- that next boundary is strictly before the right positive center.
+
+So the local pulse cannot move directly from the left positive center to the
+right positive center at the immediate successor index.  There is an index-level
+gap between the left next boundary and the right center.
+
+## Guardrails
+
+This remains a local statement about a chosen forward pair comparison state.
+It does not claim global coverage, uniqueness of all centers, full window
+disjointness for arbitrary witnesses, or Collatz convergence.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureState
+lake build DkMath.Collatz.PetalBridge
+```
+
+The final whitespace gate is:
+
+```text
+git diff --check
+```
+
+## Next Branch Prediction
+
+The next natural step is to name a slightly richer interference state, perhaps
+one that combines:
+
+- left center positivity;
+- left next boundary nonpositivity;
+- right center positivity;
+- `left next boundary < right center`.
+
+That would give the next layer a single input theorem for local window
+interference without destructuring the full boundary surface.
````
`````
