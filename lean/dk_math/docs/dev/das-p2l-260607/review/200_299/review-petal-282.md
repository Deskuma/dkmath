# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 1567afa470433a16ee8ed227da999f000ae3b366

## Report

実装完了です。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:1519) に branch-specific な薄い caller theorem を追加しました。

- `SourcePressureForwardPairComparisonState.contact_value_corridor_surface`
- `SourcePressureForwardPairComparisonState.strict_gap_value_corridor_surface`

これで contact branch では endpoint signs と `W'.val = W.val + 2`、strict-gap branch では endpoint signs と `W.val + 2 < W'.val` が直接取れます。どちらも endpoint-only で、strict corridor 内部全点の非正性は主張していません。

[report-petal-282.md](/lean_dk_math/docs/dev/das-p2l-260607/review/report-petal-282.md:1) も追加しました。

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

事実として固定できたのは、ForwardPairComparisonState の corridor split が value-level で「ちょうど 2 step」または「2 step より遠い」に分岐することです。global uniqueness、arbitrary disjointness、Collatz termination は含みません。

## Review

## 判定

採用。
`right_value_corridor_surface` を public default としつつ、branch-specific な薄い caller theorem が追加された。

追加：

```lean id="ktk7v3"
SourcePressureForwardPairComparisonState.contact_value_corridor_surface
SourcePressureForwardPairComparisonState.strict_gap_value_corridor_surface
```

contact branch では、

```lean id="x0k6zr"
SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
  SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
    W'.val = W.val + 2
```

strict-gap branch では、

```lean id="w7h0zw"
SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
  SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
    W.val + 2 < W'.val
```

が直接取れる。endpoint-only に留めており、strict corridor 内部全点の非正性や大域主張を混ぜていない点もよい。

## 実装レビュー

実装は素直で安全。

contact 側は、

```lean id="n16ueu"
h.contact_corridor_shared_nonpos hcontact
h.left_succ_lt_right_val
omega
```

strict-gap 側は、

```lean id="keghnb"
h.strict_gap_corridor_endpoints_nonpos hstrict
omega
```

で閉じている。既存の corridor branch data を消費するだけなので、依存関係も自然じゃ。

一点だけ軽い確認として、report 内のリンクが `/lean_dk_math/...` になっているように見える。実体パスが通常の `/lean/dk_math/...` なら、docs 側だけ後で直しておくとよい。Lean 本体には影響しない。

## 数学的意味

これで corridor split は、index-level から value-level へ完全に降りた。

```text id="xwwlkc"
contact branch:
  right center = left center + 2

strict-gap branch:
  right center > left center + 2
```

つまり、`FPC` の二つの正中心は、

```text id="z3m45v"
隣接不可
最小 value gap は 2
gap = 2 なら contact corridor
gap > 2 なら strict corridor
```

として読める。

これは正中心列の spacing 解析へ進むための局所部品としてかなり使いやすい。

## 注意点

今回も主張は適切に限定されている。

まだ言っていない：

```text id="bmxh3w"
strict corridor 内部の全 index が非正
positive center の大域一意性
arbitrary window disjointness
global coverage
Collatz termination
```

言えたのは、明示された `ForwardPairComparisonState` の二中心に対して、branch ごとの endpoint signs と value gap が固定できる、という局所事実じゃ。

## 現在の到達点

```text id="uzk9q8"
FPC
  -> right_value_corridor_surface
  -> contact_value_corridor_surface
  -> strict_gap_value_corridor_surface
```

ここで corridor layer はかなり十分。
これ以上 projection を足すより、次は本当に consumer 側へ移るのがよい。

## 次に攻めるなら

次は `PressureState` 内で surface を増やすより、正中心列の spacing を読む consumer theorem が自然。

たとえば、まずは名前だけでも次のような方向。

```lean id="sordpi"
-- candidate consumer direction
-- From a forward pair, the value gap is at least 2.
theorem SourcePressureForwardPairComparisonState.two_le_value_gap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    W.val + 2 ≤ W'.val
```

これは `right_value_corridor_surface` から `omega` で閉じるはず。
この theorem は「正中心の最小 spacing」を短く呼ぶための consumer-facing fact になる。

## Codex 指示

```text id="e4vq1f"
Goal:
  Stop expanding the corridor branch API, and add a first consumer-facing
  spacing theorem if useful.

Suggested theorem in PressureState.lean:

  theorem SourcePressureForwardPairComparisonState.two_le_value_gap
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W') :
      W.val + 2 ≤ W'.val

Use:
  h.right_value_corridor_surface

Proof shape:
  rcases h.right_value_corridor_surface with ⟨_, _, hsplit⟩
  rcases hsplit with hcontact | hstrict
  · omega
  · omega

Guardrails:
  Do not add more contact/gap projections unless a concrete caller needs them.
  Do not claim every interior index of a strict corridor is nonpositive.
  Do not claim global positive-center uniqueness.
  Do not claim arbitrary window disjointness.
  Do not claim Collatz termination.

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

ここからは「corridor がある」ではなく、**正中心は最低 2 step 離れる**という spacing 定理へ寄せる。
これが揃うと、次に positive pulse の詰め込み密度や局所 Big の上界へ接続しやすくなる。

---

### Revised Edition

```text
Goal:
  Continue the Collatz/PetalBridge proof route. Do not stop at another tiny
  projection theorem. Use the existing FPC corridor surfaces to move toward
  a local Big / positive-pulse packing bound.

Main direction:
  FPC corridor
    -> a nonpositive separator exists between the two positive centers
    -> value/index spacing is available as a compact consumer theorem
    -> lift this separator/spacing result back to the upstream split
       states such as BeamSeed / SortedFailure / FailureResolution when possible.

Existing facts to consume:
  - SourcePressureForwardPairComparisonState.right_value_corridor_surface
  - SourcePressureForwardPairComparisonState.contact_value_corridor_surface
  - SourcePressureForwardPairComparisonState.strict_gap_value_corridor_surface
  - SourcePressureForwardPairComparisonState.left_next_boundary_nonpos_and_before_right_center
  - SourcePressureForwardPairComparisonState.left_next_boundary_before_right_center
  - SourcePressureForwardPairComparisonState.left_succ_lt_right_val
  - sourcePressureBeamSeedState_to_forwardPairComparisonState_or_pairOverlap
  - sourcePressureSortedFailureState_to_forwardPairComparisonState_or_pairOverlap
  - sourcePressureFailureResolutionState_to_forwardPairComparisonState_or_pairOverlap

Phase A:
  Add a consumer theorem showing that every FPC pair has a nonpositive separator
  strictly between its two positive center indices.

Suggested theorem:

  theorem SourcePressureForwardPairComparisonState.exists_nonpos_index_between_centers
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W') :
      ∃ m : ℕ,
        r + W.val < m ∧
          m < r + W'.val ∧
            SourcePressureMarginInt n k m ≤ 0

Proof idea:
  choose m = r + W.val + 1
  use:
    h.left_next_boundary_nonpos_and_before_right_center
  and omega.

Phase B:
  Add compact spacing theorems from the same FPC state.

Suggested theorems:

  theorem SourcePressureForwardPairComparisonState.two_le_value_gap
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W') :
      W.val + 2 ≤ W'.val

  theorem SourcePressureForwardPairComparisonState.two_le_index_gap
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W') :
      r + W.val + 2 ≤ r + W'.val

Use:
  h.right_value_corridor_surface
  or h.left_succ_lt_right_val
  and omega.

Phase C:
  Lift the separator theorem back to upstream split states, so callers do not
  need to manually unpack FPC.

Suggested high-value theorem shape:

  theorem sourcePressureBeamSeedState_to_nonposSeparator_or_pairOverlap
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (hseed : SourcePressureBeamSeedState L)
      (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
      (∃ W W' m,
        SourcePressureForwardPairComparisonState L W W' ∧
          r + W.val < m ∧
            m < r + W'.val ∧
              SourcePressureMarginInt n k m ≤ 0) ∨
        SourcePressurePairOverlapObstruction L

If the exact pair-overlap obstruction name differs, inspect existing theorem
statements and use the already existing type from:
  sourcePressureBeamSeedState_to_forwardPairComparisonState_or_pairOverlap

Also add analogous lifted theorems for SortedFailure and FailureResolution if
they close cheaply:

  sourcePressureSortedFailureState_to_nonposSeparator_or_pairOverlap
  sourcePressureFailureResolutionState_to_nonposSeparator_or_pairOverlap

Phase D:
  If Phase C closes, write a short report section explaining the new proof route:

    Upstream failure/seed state
      -> FPC or PairOverlap
      -> if FPC, there is a nonpositive separator between two positive centers
      -> therefore positive centers cannot be packed consecutively
      -> this is the first local packing obstruction toward local Big.

Important:
  The purpose is to advance the Collatz proof route, not to stop at API cleanup.
  Keep theorem statements local and honest, but always connect the new theorem
  to the local Big / packing-bound route in the report.

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 20f32943..a4946a78 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -1508,6 +1508,52 @@ theorem SourcePressureForwardPairComparisonState.right_value_corridor_surface
       omega
   exact ⟨hnextL, hprevR, hvalue⟩

+/--
+Contact branch of the value-level corridor surface.
+
+This is a thin branch-specific caller theorem: the contact equality between
+boundary indices forces the right center to be exactly two witness-value steps
+after the left center, and it carries only the two endpoint signs.  No interior
+corridor assertion is introduced here.
+-/
+theorem SourcePressureForwardPairComparisonState.contact_value_corridor_surface
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W')
+    (hcontact : r + W.val + 1 = r + (W'.val - 1)) :
+    SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
+      SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
+        W'.val = W.val + 2 := by
+  rcases h.contact_corridor_shared_nonpos hcontact with ⟨hnextL, hprevR⟩
+  have hgap : W.val + 1 < W'.val := h.left_succ_lt_right_val
+  have hvalue : W'.val = W.val + 2 := by
+    omega
+  exact ⟨hnextL, hprevR, hvalue⟩
+
+/--
+Strict-gap branch of the value-level corridor surface.
+
+This is a thin branch-specific caller theorem: when the left next boundary is
+strictly before the right previous boundary, the right center is strictly more
+than two witness-value steps after the left center.  The theorem remains
+endpoint-only.
+-/
+theorem SourcePressureForwardPairComparisonState.strict_gap_value_corridor_surface
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W')
+    (hstrict : r + W.val + 1 < r + (W'.val - 1)) :
+    SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
+      SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
+        W.val + 2 < W'.val := by
+  rcases h.strict_gap_corridor_endpoints_nonpos hstrict with
+    ⟨hnextL, hprevR, hgap⟩
+  have hvalue : W.val + 2 < W'.val := by
+    omega
+  exact ⟨hnextL, hprevR, hvalue⟩
+
 /--
 Constructor from the forward box comparison state to the pair-comparison-facing
 state.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-282.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-282.md
new file mode 100644
index 00000000..8691691f
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-282.md
@@ -0,0 +1,89 @@
+# Report: petal-282
+
+## Goal
+
+Keep `SourcePressureForwardPairComparisonState.right_value_corridor_surface`
+as the preferred public value-level corridor surface, and add only thin
+branch-specific projections if needed by downstream callers.
+
+## Implemented
+
+Added two endpoint-only branch projections:
+
+- `SourcePressureForwardPairComparisonState.contact_value_corridor_surface`
+- `SourcePressureForwardPairComparisonState.strict_gap_value_corridor_surface`
+
+Both theorems consume existing corridor branch data and avoid adding any new
+global or interior-corridor claim.
+
+## Established Facts
+
+In the contact branch
+
+```lean
+r + W.val + 1 = r + (W'.val - 1)
+```
+
+Lean proves:
+
+```lean
+SourcePressureMarginInt n k (r + W.val + 1) <= 0
+  ∧ SourcePressureMarginInt n k (r + (W'.val - 1)) <= 0
+  ∧ W'.val = W.val + 2
+```
+
+In the strict-gap branch
+
+```lean
+r + W.val + 1 < r + (W'.val - 1)
+```
+
+Lean proves:
+
+```lean
+SourcePressureMarginInt n k (r + W.val + 1) <= 0
+  ∧ SourcePressureMarginInt n k (r + (W'.val - 1)) <= 0
+  ∧ W.val + 2 < W'.val
+```
+
+## What Can Be Concluded
+
+The public theorem `right_value_corridor_surface` remains the compact default:
+
+```lean
+endpoint signs
+  ∧ (W'.val = W.val + 2 ∨ W.val + 2 < W'.val)
+```
+
+When a caller has already selected a branch, the new theorems provide the
+corresponding value-level consequence directly.
+
+## Guardrails
+
+These are local forward-pair comparison facts only.  They do not prove:
+
+- all interior indices of a strict corridor are nonpositive;
+- global uniqueness of positive centers;
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
+The corridor layer is now sufficiently surfaced for both compact and
+branch-specific callers.  The next useful work should start from a concrete
+consumer of these value gaps, rather than extending the corridor API further.
````
`````
