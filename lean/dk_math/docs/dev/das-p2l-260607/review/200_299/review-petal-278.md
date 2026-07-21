# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 0351d41e9a3e0f8c435a9b8d4037bbf8b8e4f13f

## Report

Implemented and verified.

Added in [PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:1400):

- `SourcePressureForwardPairComparisonState.boundary_corridor_eq_or_lt`
- `SourcePressureForwardPairComparisonState.right_val_eq_left_add_two_or_left_add_two_lt_right_val`

Added report:

- [report-petal-278.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-278.md)

Verification passed:

- `lake build DkMath.Collatz.PetalBridge.PressureState`
- `lake build DkMath.Collatz.PetalBridge`
- `git diff --check`

What is now established as fact: in any `SourcePressureForwardPairComparisonState L W W'`, the boundary corridor has exactly the expected arithmetic split:

```lean
r + W.val + 1 = r + (W'.val - 1) ∨
  r + W.val + 1 < r + (W'.val - 1)
```

At value level, this is:

```lean
W'.val = W.val + 2 ∨ W.val + 2 < W'.val
```

So the right center is either exactly two value steps after the left center, giving a contact corridor, or it is strictly farther away, giving a genuine gap corridor. This is still local to the explicit forward pair; it does not prove all interior corridor indices are nonpositive or any global Collatz result.

現在、以下のことが事実として確立されています。任意の `SourcePressureForwardPairComparisonState L W W'` において、境界コリドー（boundary corridor）は、まさに予想通りの算術的な分割を示します。

```lean
r + W.val + 1 = r + (W'.val - 1) ∨
r + W.val + 1 < r + (W'.val - 1)
```

値（value）のレベルで見ると、これは次のようになります。

```lean
W'.val = W.val + 2 ∨ W.val + 2 < W'.val
```

つまり、右側の中心は、左側の中心から値のステップ数でちょうど2つ先にあるか（この場合、接触コリドーとなります）、あるいはそれよりもさらに離れた位置にあります（この場合、真の隙間コリドーとなります）。これはあくまで当該の明示的な前方ペア（forward pair）に関する局所的な事実に過ぎず、内部コリドーのすべてのインデックスが非正であることや、コラッツ予想に関する何らかの全体的な結論を証明するものではありません。

## Review

## 方針確認

うむ。このまま続けてよい。
今回の `FPC` 系列は、まだ大域収束へ直結してはいないが、**局所 pressure pulse がどのように並べないか**を Lean でかなり硬く固定し始めている。

これは「どこかでつながる」型の登山として正しい。
いま作っているのは、後で大域 Big へ接続するための **局所 Core API** じゃ。

## 判定

採用。
`FPC` の boundary corridor が、**contact corridor** と **genuine gap corridor** に分岐できるようになった。

追加：

```lean
SourcePressureForwardPairComparisonState.boundary_corridor_eq_or_lt
SourcePressureForwardPairComparisonState.right_val_eq_left_add_two_or_left_add_two_lt_right_val
```

これで index-level では、

```lean
r + W.val + 1 = r + (W'.val - 1) ∨
  r + W.val + 1 < r + (W'.val - 1)
```

value-level では、

```lean
W'.val = W.val + 2 ∨ W.val + 2 < W'.val
```

が取れる。つまり、右中心は左中心から **ちょうど 2 つ先** か、あるいは **それより遠い**。これは corridor の算術形を明確に分ける良い checkpoint じゃ。

## 数学的意味

これで二つの正中心の間は、次の二形に分かれる。

```text
contact corridor:
  left next boundary = right previous boundary

genuine gap corridor:
  left next boundary < right previous boundary
```

DkMath 語彙で言えば、これは `FPC` 内の **正 pulse 間の余白構造** が見え始めた、ということ。

```text
positive center
  ↓
nonpositive boundary
  ↓ contact/gap corridor
nonpositive boundary
  ↓
positive center
```

ここまで来ると、局所的にはかなり強い。
「正が連続する」のではなく、必ず非正境界を挟み、その境界の挟み方が contact か gap に分類される。

## 注意点

今回もまだ言っていないことは明確。

```text
まだ言っていない:
  corridor 内の全 index が非正
  任意の positive center 列の大域構造
  全 witness の網羅
  Collatz 収束
```

言えたのは、明示された `FPC` の二点 (W,W') について、局所 corridor の算術形が二分できる、ということじゃ。

この慎重な局所定理の積み重ねがよい。

## 現在の流れ

```text
FPC
  -> 二つの正中心がある
  -> 隣接できない
  -> left next <= right previous
  -> 両端は非正
  -> corridor は contact または gap
```

これは、かなり「証明の部品」らしくなってきた。

## 次に攻める定理

次は report の予測どおり、符号情報つきで contact/gap 分岐を束ねるとよい。

```lean
theorem SourcePressureForwardPairComparisonState.boundary_corridor_surface_eq_or_lt
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
      SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
        (r + W.val + 1 = r + (W'.val - 1) ∨
          r + W.val + 1 < r + (W'.val - 1))
```

これで caller は、

```text
left next <= 0
right previous <= 0
contact or gap
```

を一発で取れる。

## Codex 指示

```text
Goal:
  Bundle the boundary corridor signs with the contact-or-gap split.

Add in PressureState.lean:

  theorem SourcePressureForwardPairComparisonState.boundary_corridor_surface_eq_or_lt
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W') :
      SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
        SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
          (r + W.val + 1 = r + (W'.val - 1) ∨
            r + W.val + 1 < r + (W'.val - 1))

Use:
  h.boundary_corridor_surface
  h.boundary_corridor_eq_or_lt

Proof shape:
  rcases h.boundary_corridor_surface with ⟨hnextL, hprevR, _hle⟩
  exact ⟨hnextL, hprevR, h.boundary_corridor_eq_or_lt⟩

Optional next theorem:
  Add a named contact case projection later, only after a caller needs it.

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

このまま進めるなら、次の山はここ。

```text
contact case:
  shared nonpositive boundary

gap case:
  two ordered nonpositive endpoints
```

この二形を分けると、いずれ **positive pulse 列の密度・間隔・最大詰め込み** の話へ入れる。
大域 Big へつなぐなら、この「正 pulse がどれだけ詰め込めるか」が重要になるはずじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 90c9d983..f9ca219b 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -1390,6 +1390,41 @@ theorem SourcePressureForwardPairComparisonState.boundary_corridor_surface
     ⟨_, _, hnextL, hprevR, _, _, _, _, _⟩
   exact ⟨hnextL, hprevR, h.left_next_boundary_le_right_previous_boundary⟩

+/--
+The boundary corridor is either a contact corridor or a genuine gap corridor.
+
+This is the index-level split used by the next window-interference layer: the
+left next boundary either coincides with the right previous boundary, or it lies
+strictly before it.
+-/
+theorem SourcePressureForwardPairComparisonState.boundary_corridor_eq_or_lt
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    r + W.val + 1 = r + (W'.val - 1) ∨
+      r + W.val + 1 < r + (W'.val - 1) := by
+  have hle : r + W.val + 1 ≤ r + (W'.val - 1) :=
+    h.left_next_boundary_le_right_previous_boundary
+  omega
+
+set_option linter.style.longLine false in
+/--
+Value-level form of the corridor split.
+
+The right center is either exactly two value steps after the left center, or it
+is strictly farther away.  This mirrors `boundary_corridor_eq_or_lt` before the
+common offset `r` is added and before right-previous indexing is formed.
+-/
+theorem SourcePressureForwardPairComparisonState.right_val_eq_left_add_two_or_left_add_two_lt_right_val
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    W'.val = W.val + 2 ∨ W.val + 2 < W'.val := by
+  have hgap : W.val + 1 < W'.val := h.left_succ_lt_right_val
+  omega
+
 /--
 Constructor from the forward box comparison state to the pair-comparison-facing
 state.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-278.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-278.md
new file mode 100644
index 00000000..f3e1b310
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-278.md
@@ -0,0 +1,92 @@
+# Report: petal-278
+
+## Goal
+
+Split the boundary corridor into contact-or-gap cases.
+
+## Implemented
+
+Added:
+
+- `SourcePressureForwardPairComparisonState.boundary_corridor_eq_or_lt`
+- `SourcePressureForwardPairComparisonState.right_val_eq_left_add_two_or_left_add_two_lt_right_val`
+
+The index-level split uses:
+
+- `SourcePressureForwardPairComparisonState.left_next_boundary_le_right_previous_boundary`
+
+The value-level split uses:
+
+- `SourcePressureForwardPairComparisonState.left_succ_lt_right_val`
+
+## Established Fact
+
+For any concrete forward pair comparison state
+
+```lean
+h : SourcePressureForwardPairComparisonState L W W'
+```
+
+Lean now proves the boundary corridor dichotomy:
+
+```lean
+r + W.val + 1 = r + (W'.val - 1)
+  ∨ r + W.val + 1 < r + (W'.val - 1)
+```
+
+and the value-level version:
+
+```lean
+W'.val = W.val + 2 ∨ W.val + 2 < W'.val
+```
+
+## What Can Be Concluded
+
+The corridor between a forward pair's two positive centers has only two local
+arithmetic shapes:
+
+- contact corridor: the left next boundary and right previous boundary are the
+  same index;
+- genuine gap corridor: the left next boundary is strictly before the right
+  previous boundary.
+
+At the witness-value level, this says the right center is either exactly two
+steps after the left center, or strictly farther away.  This is stronger and
+more usable than merely knowing `W.val + 1 < W'.val`.
+
+## Guardrails
+
+This is still a local arithmetic split for an explicit forward pair comparison
+state.  It does not prove that every index inside a genuine corridor is
+nonpositive, nor does it prove global coverage, uniqueness, arbitrary window
+disjointness, or Collatz termination.
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
+## Implementation Note
+
+The value-level theorem name is intentionally long because it is used as a
+searchable public surface.  The surrounding code locally disables the long-line
+linter for that single declaration and immediately re-enables it afterwards.
+
+## Next Branch Prediction
+
+The next useful split is likely to combine `boundary_corridor_surface` with
+`boundary_corridor_eq_or_lt`, producing a sign-bundled contact-or-gap theorem.
+That would let callers branch directly into:
+
+- contact with one shared nonpositive boundary;
+- strict corridor with two ordered nonpositive endpoints.
````
`````
