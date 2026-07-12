# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 20c1c95c9336e71bfc2c35f155276fc2c98baf75

## Report

実装完了です。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:1493) に `SourcePressureForwardPairComparisonState.right_value_corridor_surface` を追加しました。これは既存の `boundary_corridor_surface_eq_or_lt` を消費して、value-level に

```lean
W'.val = W.val + 2 ∨ W.val + 2 < W'.val
```

を出す downstream caller surface です。endpoint の非正性も一緒に運びますが、strict corridor の内部全点については主張していません。

[report-petal-281.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-281.md:1) も追加しました。

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

結論として、ForwardPairComparisonState では「右 center は左 center のちょうど 2 value step 後、またはそれより遠い」ことが Lean で固定されました。これは局所 pair 比較の事実であり、global uniqueness や Collatz termination ではありません。

## Review

## 判定

採用。
`PressureState` の corridor API をそのまま増やし続けるのではなく、既存 corridor split を消費する **downstream caller surface** に進めたのが良い。

追加：

```lean id="si0m3v"
SourcePressureForwardPairComparisonState.right_value_corridor_surface
```

これで `FPC` から、

```lean id="tqzd6u"
SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
  SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
    (W'.val = W.val + 2 ∨ W.val + 2 < W'.val)
```

が直接取れる。つまり、非正 corridor endpoint を保持したまま、value-level で「右中心は左中心の 2 step 後、またはそれより遠い」と読めるようになった。

## 実装レビュー

実装は安全。

```lean id="foabvw"
rcases h.boundary_corridor_surface_eq_or_lt with ⟨hnextL, hprevR, hsplit⟩
```

で endpoint signs と index-level split を取り出し、`omega` で value-level split に落としている。
`right_val_eq_left_add_two_or_left_add_two_lt_right_val` は既にあったが、今回の theorem は endpoint signs も一緒に運ぶので、単なる重複ではなく caller-facing surface として意味がある。

## 数学的意味

これで corridor split は、index 言語から value 言語へ降りた。

```text id="b7z46q"
index-level:
  left next boundary = right previous boundary
  or
  left next boundary < right previous boundary

value-level:
  W'.val = W.val + 2
  or
  W.val + 2 < W'.val
```

つまり、

```text id="x1o2c6"
contact corridor:
  value gap exactly 2

strict gap corridor:
  value gap greater than 2
```

と読める。

これは `FPC` の正中心列を解析するときに、かなり扱いやすい形じゃ。

## 注意点

主張は適切に絞られている。

まだ言っていない：

```text id="mx89tj"
strict corridor 内部の全 index が非正
positive center の大域一意性
全 window の disjointness
Collatz termination
```

今回も endpoint-only の局所 pair theorem に留まっている。よい。

## 現在の到達点

```text id="l6u78f"
FPC
  -> nonpositive corridor endpoints
  -> contact/gap index split
  -> value gap is exactly 2 or greater than 2
```

これは局所 Core API としてかなり良い形。
次に大域 Big へつなぐなら、「正中心の最小 spacing」が value-level で扱えるようになった意味が大きい。

## 次に攻めるなら

次は report の通り、branch-specific projection は caller が必要になってからでよい。
ただ、もし進めるならこの二つ。

```lean id="o47qcw"
theorem SourcePressureForwardPairComparisonState.contact_value_corridor_surface
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W')
    (hcontact : W'.val = W.val + 2) :
    SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
      SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
        W'.val = W.val + 2
```

```lean id="qp7a3i"
theorem SourcePressureForwardPairComparisonState.strict_value_gap_corridor_surface
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W')
    (hgap : W.val + 2 < W'.val) :
    SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
      SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
        W.val + 2 < W'.val
```

## Codex 指示

```text id="fs13i7"
Goal:
  Prefer using SourcePressureForwardPairComparisonState.right_value_corridor_surface
  as the public value-level corridor surface.

Do not add more projection theorems unless a concrete downstream caller needs
branch-specific contact/gap data.

If branch-specific value projections are needed, add only thin endpoint-only
theorems:

  contact:
    endpoint signs + W'.val = W.val + 2

  strict gap:
    endpoint signs + W.val + 2 < W'.val

Guardrails:
  Do not claim all interior indices of a strict corridor are nonpositive.
  Do not claim global uniqueness of positive centers.
  Do not claim arbitrary window disjointness.
  Do not claim Collatz termination.

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

`PressureState` の局所 corridor surface は、いったん十分。
次はこれを使って、正中心列の spacing、詰め込み密度、pulse 列の伝播へ橋をかける段階じゃ。局所 Core から Beam へ進む準備が整ってきた。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 6117b7d8..20f32943 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -1481,6 +1481,33 @@ theorem SourcePressureForwardPairComparisonState.right_val_eq_left_add_two_or_le
   have hgap : W.val + 1 < W'.val := h.left_succ_lt_right_val
   omega
 
+/--
+Downstream value-level reading of the boundary corridor split.
+
+This consumes the index-level contact-or-gap corridor and exports the result in
+terms of witness values: the right center is either exactly two value steps
+after the left center, or strictly farther away.  The theorem carries only the
+two endpoint signs already present in the corridor surface; it does not assert
+anything about interior indices of a strict corridor.
+-/
+theorem SourcePressureForwardPairComparisonState.right_value_corridor_surface
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
+      SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
+        (W'.val = W.val + 2 ∨ W.val + 2 < W'.val) := by
+  rcases h.boundary_corridor_surface_eq_or_lt with ⟨hnextL, hprevR, hsplit⟩
+  have hgap : W.val + 1 < W'.val := h.left_succ_lt_right_val
+  have hvalue : W'.val = W.val + 2 ∨ W.val + 2 < W'.val := by
+    rcases hsplit with hcontact | hstrict
+    · left
+      omega
+    · right
+      omega
+  exact ⟨hnextL, hprevR, hvalue⟩
+
 /--
 Constructor from the forward box comparison state to the pair-comparison-facing
 state.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-281.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-281.md
new file mode 100644
index 00000000..6c25c65d
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-281.md
@@ -0,0 +1,74 @@
+# Report: petal-281
+
+## Goal
+
+Stop expanding the corridor API itself and start a downstream caller theorem
+that consumes the existing boundary corridor split.
+
+## Implemented
+
+Added:
+
+- `SourcePressureForwardPairComparisonState.right_value_corridor_surface`
+
+This theorem consumes
+`SourcePressureForwardPairComparisonState.boundary_corridor_surface_eq_or_lt`
+and exports the result at the witness-value level.
+
+## Established Fact
+
+For any
+`h : SourcePressureForwardPairComparisonState L W W'`, Lean proves:
+
+```lean
+SourcePressureMarginInt n k (r + W.val + 1) <= 0
+  ∧ SourcePressureMarginInt n k (r + (W'.val - 1)) <= 0
+  ∧ (W'.val = W.val + 2 ∨ W.val + 2 < W'.val)
+```
+
+So a forward pair comparison has two nonpositive corridor endpoints, and the
+right center is either exactly two value steps after the left center or is
+strictly farther away.
+
+## What Can Be Concluded
+
+This is the first downstream caller-facing use of the corridor split.  The
+index-level contact/gap branch now has a direct value-level reading:
+
+- contact corresponds to the adjacent centers having value gap `2`;
+- strict gap corresponds to the right center being more than two value steps
+  after the left center.
+
+## Guardrails
+
+The theorem still only carries endpoint signs.  It does not prove:
+
+- every interior index of a strict corridor is nonpositive;
+- global positive-center uniqueness;
+- arbitrary window disjointness;
+- Collatz termination.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureState
+```
+
+Final gate:
+
+```text
+lake build DkMath.Collatz.PetalBridge
+git diff --check
+```
+
+## Next Branch Prediction
+
+The next useful branch is to expose branch-specific value projections only if a
+caller needs them:
+
+- contact: `W'.val = W.val + 2` plus endpoint signs;
+- strict gap: `W.val + 2 < W'.val` plus endpoint signs.
+
+Until then, `right_value_corridor_surface` is the cleaner public surface.
````
`````
