# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 1f3842fc631a9b8e62d76c98f453dd06f9a59911

## Report

Implemented and verified.

Added in [PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:1366):

- `SourcePressureForwardPairComparisonState.left_next_boundary_le_right_previous_boundary`
- `SourcePressureForwardPairComparisonState.boundary_corridor_surface`

Added report:

- [report-petal-277.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-277.md)

Verification passed:

- `lake build DkMath.Collatz.PetalBridge.PressureState`
- `lake build DkMath.Collatz.PetalBridge`
- `git diff --check`

What is now established as fact: in any `SourcePressureForwardPairComparisonState L W W'`, Lean proves the index corridor

```lean
r + W.val + 1 ≤ r + (W'.val - 1)
```

and also the bundled sign corridor

```lean
SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
  SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
    r + W.val + 1 ≤ r + (W'.val - 1)
```

So the local forward pair has nonpositive boundary endpoints bracketing the gap between the two positive centers. This does not yet say every interior index in that corridor is nonpositive; it only fixes both corridor endpoints and their order.

現在、以下のことが事実として確立されています。任意の `SourcePressureForwardPairComparisonState L W W'` において、Lean は「インデックス・コリドー（index corridor）」

```lean
r + W.val + 1 ≤ r + (W'.val - 1)
```

および「バンドルされた符号コリドー（bundled sign corridor）」

```lean
SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
r + W.val + 1 ≤ r + (W'.val - 1)
```

を証明します。つまり、この局所的な前方ペア（local forward pair）は、2つの正の中心（positive centers）の間のギャップを挟み込む形で、非正（nonpositive）の境界端点を持っていることになります。ただし、これはコリドー内のすべての内部インデックスが非正であることを直ちに意味するわけではありません。あくまで、コリドーの両端点とその順序が確定したということに過ぎません。

## Review

## 判定

採用。
`FPC` の二つの正中心の間に、**非正 boundary corridor** が立った。

追加：

```lean id="q7qyix"
SourcePressureForwardPairComparisonState.left_next_boundary_le_right_previous_boundary
SourcePressureForwardPairComparisonState.boundary_corridor_surface
```

これで `FPC` から、

```lean id="y0z2fq"
r + W.val + 1 ≤ r + (W'.val - 1)
```

および、

```lean id="o4j3qy"
SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
  SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
    r + W.val + 1 ≤ r + (W'.val - 1)
```

が直接取れる。これは「左 next boundary」と「右 previous boundary」が、両方とも非正で、しかも順序付きで corridor の両端になる、という定理じゃ。

## 増えた事実

これまで：

```text id="hmx7yz"
left center > 0
left next <= 0
left next < right center
right center > 0
```

今回：

```text id="ql2k9b"
left center > 0
left next <= 0
left next <= right previous
right previous <= 0
right center > 0
```

ここで初めて、二つの正中心の間に **非正端点で挟まれた corridor** が明示された。

## 数学的意味

これは `FPC` branch の局所形をかなり強くしている。

```text id="t9h5wy"
positive center
  ↓
nonpositive boundary
  ↓ corridor
nonpositive boundary
  ↓
positive center
```

ただし report の注意通り、これはまだ「corridor 内の全 index が非正」までは言っていない。
確定したのは、

```text id="yq49i9"
corridor の左端が非正
corridor の右端が非正
左端 <= 右端
```

までじゃ。

この慎重さは良い。

## 現在の状態表

```text id="vp8xgk"
SortedFailure + sorted(L)
  -> FPC ∨ PO

FailureResolution + sorted(L)
  -> FPC ∨ PO

BeamSeed + sorted(L)
  -> FPC ∨ PO

FPC
  -> left_next_interference_surface
  -> boundary_corridor_surface
```

`FPC` は、二つの正 pulse が非正 corridor を挟んで並ぶ構造として読める段階に入った。

## 次に攻める定理

次は corridor が **接触型** か **真の gap 型** かを分けるとよい。

```lean id="y066ak"
theorem SourcePressureForwardPairComparisonState.boundary_corridor_eq_or_lt
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    r + W.val + 1 = r + (W'.val - 1) ∨
      r + W.val + 1 < r + (W'.val - 1)
```

意味はこう。

```text id="l7f2ka"
contact case:
  left next boundary = right previous boundary

gap case:
  left next boundary < right previous boundary
```

値側でも置くなら：

```lean id="n0nt07"
theorem SourcePressureForwardPairComparisonState.right_val_eq_left_add_two_or_left_add_two_lt_right_val
    ... :
    W'.val = W.val + 2 ∨ W.val + 2 < W'.val
```

これは `h.left_succ_lt_right_val` から `omega` で行けるはず。

## Codex 指示

```text id="btfyaz"
Goal:
  Split the boundary corridor into contact-or-gap cases.

Add in PressureState.lean:

  theorem SourcePressureForwardPairComparisonState.boundary_corridor_eq_or_lt
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W') :
      r + W.val + 1 = r + (W'.val - 1) ∨
        r + W.val + 1 < r + (W'.val - 1)

Use:
  h.left_next_boundary_le_right_previous_boundary
  omega

Optional value-level version:

  theorem SourcePressureForwardPairComparisonState.right_val_eq_left_add_two_or_left_add_two_lt_right_val
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W') :
      W'.val = W.val + 2 ∨ W.val + 2 < W'.val

Use:
  h.left_succ_lt_right_val
  omega

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

次で、二正中心の間はこう分類できる。

```text id="a8k81b"
contact:
  非正 boundary を共有している

gap:
  非正 boundary 端点の間に余白 corridor がある
```

これは window separation 層の入口としてかなり良い。次から「接触していても正中心は隣接できない」「gap があれば corridor をさらに解析する」という分岐が作れる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 4d7044d0..90c9d983 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -1356,6 +1356,40 @@ theorem SourcePressureForwardPairComparisonState.left_next_interference_surface
     ⟨_, hcenterL, hnextL, _, hcenterR, _, _, _, hgap⟩
   exact ⟨hcenterL, hnextL, hcenterR, hgap⟩
 
+/--
+Index corridor between the left next boundary and the right previous boundary.
+
+The first interference theorem gives `W.val + 1 < W'.val`; at the addressed
+index level this means the left next boundary is no later than the right
+previous boundary.
+-/
+theorem SourcePressureForwardPairComparisonState.left_next_boundary_le_right_previous_boundary
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    r + W.val + 1 ≤ r + (W'.val - 1) := by
+  have hgap : W.val + 1 < W'.val := h.left_succ_lt_right_val
+  omega
+
+/--
+Boundary corridor surface for a forward pair comparison state.
+
+Both corridor endpoints are nonpositive boundary indices, and the left next
+boundary lies no later than the right previous boundary.
+-/
+theorem SourcePressureForwardPairComparisonState.boundary_corridor_surface
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
+      SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
+        r + W.val + 1 ≤ r + (W'.val - 1) := by
+  rcases h.indexed_boundary_gap_surface with
+    ⟨_, _, hnextL, hprevR, _, _, _, _, _⟩
+  exact ⟨hnextL, hprevR, h.left_next_boundary_le_right_previous_boundary⟩
+
 /--
 Constructor from the forward box comparison state to the pair-comparison-facing
 state.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-277.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-277.md
new file mode 100644
index 00000000..942747e2
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-277.md
@@ -0,0 +1,87 @@
+# Report: petal-277
+
+## Goal
+
+Relate the left next boundary to the right previous boundary in a forward pair
+comparison state.
+
+## Implemented
+
+Added:
+
+- `SourcePressureForwardPairComparisonState.left_next_boundary_le_right_previous_boundary`
+- `SourcePressureForwardPairComparisonState.boundary_corridor_surface`
+
+The first theorem is derived from:
+
+- `SourcePressureForwardPairComparisonState.left_succ_lt_right_val`
+
+The second theorem bundles signs from:
+
+- `SourcePressureForwardPairComparisonState.indexed_boundary_gap_surface`
+
+and the new corridor inequality.
+
+## Established Fact
+
+For any concrete forward pair comparison state
+
+```lean
+h : SourcePressureForwardPairComparisonState L W W'
+```
+
+Lean now proves the index corridor:
+
+```lean
+r + W.val + 1 <= r + (W'.val - 1)
+```
+
+and the sign-bundled version:
+
+```lean
+SourcePressureMarginInt n k (r + W.val + 1) <= 0
+  ∧ SourcePressureMarginInt n k (r + (W'.val - 1)) <= 0
+  ∧ r + W.val + 1 <= r + (W'.val - 1)
+```
+
+## What Can Be Concluded
+
+The local forward pair has a nonpositive boundary corridor between the two
+positive centers:
+
+- the left next boundary is nonpositive;
+- the right previous boundary is nonpositive;
+- the left next boundary is no later than the right previous boundary.
+
+This upgrades the earlier strict center separation into a boundary-to-boundary
+corridor statement.  It is the first compact form saying that the region between
+the two positive centers is bracketed by nonpositive boundary endpoints.
+
+## Guardrails
+
+This is local to an explicit forward pair comparison state.  It does not assert
+that every index inside the corridor is nonpositive, nor does it prove global
+coverage, global uniqueness, arbitrary window disjointness, or Collatz
+termination.
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
+Final whitespace gate:
+
+```text
+git diff --check
+```
+
+## Next Branch Prediction
+
+The next useful branch is likely an explicit named corridor predicate, but only
+if downstream proofs repeatedly need the three bundled facts.  For now,
+`boundary_corridor_surface` is a sufficient compact theorem for local
+window-comparison callers.
````
`````
