# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 1bced525d97b1644189c77f8d4b152e8467bff68

## Report

実装完了です。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:1689) に `SourcePressureLocalPackingSeparatorState.center_separator_surface` を追加しました。これで named state から直接、

```lean
0 < SourcePressureMarginInt n k (r + W.val)
∧ SourcePressureMarginInt n k m ≤ 0
∧ 0 < SourcePressureMarginInt n k (r + W'.val)
∧ r + W.val < m
∧ m < r + W'.val
∧ W.val + 2 ≤ W'.val
```

が取れます。つまり、局所的に

```text
positive center -> nonpositive separator -> positive center
```

という符号配置が theorem として固定されました。

上流 lift も追加済みです。

- `sourcePressureFailureResolutionState_to_centerSeparatorSurface_or_pairOverlap`
- `sourcePressureSortedFailureState_to_centerSeparatorSurface_or_pairOverlap`
- `sourcePressureBeamSeedState_to_centerSeparatorSurface_or_pairOverlap`

これで `BeamSeed / SortedFailure / FailureResolution + sorted(L)` から、center/separator/center surface か concrete pair-overlap obstruction へ到達できます。

[report-petal-285.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-285.md:1) も追加しました。

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

今回の事実は、有限窓 packing bound に向かうための局所構造です。大域 coverage や大域終了性はまだ主張していません。

## Review

## 判定

採用。
今回は `LocalPackingSeparatorState` から、実際の符号配置

```text id="ilb3mw"
positive center -> nonpositive separator -> positive center
```

を一発で読める surface まで進んだ。

追加：

```lean id="yr1rte"
SourcePressureLocalPackingSeparatorState.center_separator_surface
```

さらに上流 lift：

```lean id="l6ebka"
sourcePressureFailureResolutionState_to_centerSeparatorSurface_or_pairOverlap
sourcePressureSortedFailureState_to_centerSeparatorSurface_or_pairOverlap
sourcePressureBeamSeedState_to_centerSeparatorSurface_or_pairOverlap
```

これで `BeamSeed / SortedFailure / FailureResolution + sorted(L)` から、center/separator/center surface か concrete pair-overlap obstruction へ到達できるようになった。

## 実装レビュー

かなり良い。

`center_separator_surface` は、まさに欲しかった局所像をそのまま定理にしている。

```lean id="f1k80k"
0 < SourcePressureMarginInt n k (r + W.val) ∧
  SourcePressureMarginInt n k m ≤ 0 ∧
    0 < SourcePressureMarginInt n k (r + W'.val) ∧
      r + W.val < m ∧
        m < r + W'.val ∧
          W.val + 2 ≤ W'.val
```

証明も既存 API の合成で閉じている。

```lean id="k0juh6"
h.forward.center_pair_surface
h.separator_nonpos
h.left_lt_separator
h.separator_lt_right
h.two_le_value_gap
```

これは projection ではあるが、単なる小補題ではない。
**局所 packing bound へ入るための surface** になっている。

## 進展評価

改善された指示の方向は、今回も効いている。

ここまでの進行はこう。

```text id="rb1tbc"
FPC corridor
  -> nonpositive separator
  -> LocalPackingSeparatorState
  -> center/separator/center surface
  -> upstream seed/failure split
```

前より明らかに、単発依頼から脱している。
特に report に

```text id="n4om6a"
observed local structure
  -> reusable local theorem
  -> finite-window packing bound
  -> local Big
```

と書けているのは良い。
これは「小補題を作った」ではなく、「次の山へ向かう途中の checkpoint」として認識できている。

## 数学的意味

今回の theorem により、局所現象はこう固定された。

```text id="u8hiql"
左の正中心
  < 非正 separator
  < 右の正中心
```

しかも、value gap は最低 2。

```text id="jk5ofa"
W.val + 2 ≤ W'.val
```

これは、正中心が有限窓の中で無制限に詰まることを防ぐ最初の形じゃ。

ここから自然に、

```text id="pwkq4o"
有限 window 内に positive center を何個置けるか
```

という packing bound へ進む。

## 注意点

今回の report は、前よりかなり前向きになっている。
ただし、まだ次の文は少しだけ防御的じゃ。

```text id="bqxzal"
This checkpoint is local to the explicit witness list L.
```

これは正しいが、次からは必ず後ろに目的を書くとよい。

```text id="i1idkh"
This checkpoint is local to the explicit witness list L,
and it is designed to become the finite-window carrier for packing bounds.
```

否定だけで終わらせない。
常に「何へ昇格するか」まで書く。

## 次の本命

次は report の予測通り、**finite-window carrier** を作る段階じゃ。

目的は、

```text id="h21ev9"
window bounds
left positive center in window
nonpositive separator in window
right positive center in window
```

を一つの state として持つこと。

いきなり counting / density theorem へ行くより、まず carrier を作るのが正しい。

## 次の Codex 指示

```text id="c2foz0"
Goal:
  Continue from the center/separator/center surface toward a finite-window
  packing bound.  Do not stop at another projection-only theorem.

  Build the first finite-window carrier that records a local packing separator
  inside an explicit index window.

Phase A:
  Add a named finite-window local packing state.

Suggested definition:

  def SourcePressureFiniteWindowPackingSeparatorState
      {n : OddNat} {k r : ℕ}
      (L : List (SourcePressureLocalIslandWitness n k r))
      (lo hi : ℕ)
      (W W' : SourcePressureLocalIslandWitness n k r)
      (m : ℕ) : Prop :=
    SourcePressureLocalPackingSeparatorState L W W' m ∧
      lo ≤ r + W.val ∧
        r + W'.val ≤ hi

Meaning:
  The local packing separator lies between two positive centers, and both
  positive centers are inside the finite window [lo, hi].  The separator is then
  also inside the window by the inequalities already stored in
  SourcePressureLocalPackingSeparatorState.

Phase B:
  Add projections:
    - .localPacking
    - .left_center_in_window
    - .right_center_in_window
    - .separator_in_window
    - .center_separator_surface
    - .two_le_value_gap
    - .two_le_index_gap

Suggested useful theorem:

  theorem SourcePressureFiniteWindowPackingSeparatorState.separator_in_window
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {lo hi : ℕ}
      {W W' : SourcePressureLocalIslandWitness n k r}
      {m : ℕ}
      (h : SourcePressureFiniteWindowPackingSeparatorState L lo hi W W' m) :
      lo ≤ m ∧ m ≤ hi

Proof idea:
  use:
    h.localPacking.left_lt_separator
    h.localPacking.separator_lt_right
    h.left_center_in_window
    h.right_center_in_window
  and omega.

Phase C:
  Add constructor from SourcePressureLocalPackingSeparatorState with explicit
  window bounds.

  theorem SourcePressureLocalPackingSeparatorState.to_finiteWindowPackingSeparatorState
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {lo hi : ℕ}
      {W W' : SourcePressureLocalIslandWitness n k r}
      {m : ℕ}
      (h : SourcePressureLocalPackingSeparatorState L W W' m)
      (hlo : lo ≤ r + W.val)
      (hhi : r + W'.val ≤ hi) :
      SourcePressureFiniteWindowPackingSeparatorState L lo hi W W' m

Phase D:
  If cheap, lift the upstream center/separator surface into the finite-window
  state under explicit window-bound assumptions.

Suggested shape:

  theorem sourcePressureBeamSeedState_to_finiteWindowPackingSeparatorState_or_pairOverlap
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {lo hi : ℕ}
      (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
      (h : SourcePressureBeamSeedState L)
      (hlo_all : ∀ W, W ∈ L → lo ≤ r + W.val)
      (hhi_all : ∀ W, W ∈ L → r + W.val ≤ hi) :
      (∃ W W' m,
        SourcePressureFiniteWindowPackingSeparatorState L lo hi W W' m)
        ∨ PairOverlapObstruction-shape-already-used-here

Use the actual pair-overlap obstruction shape from the existing upstream
theorems.

If membership projections are needed:
  use SourcePressureForwardPairComparisonState.left_mem / right_mem through
  SourcePressureLocalPackingSeparatorState.forward.

Phase E:
  Report the route explicitly:

    LocalPackingSeparatorState
      -> center/separator/center surface
      -> finite-window carrier
      -> separator is inside the same finite window
      -> this prepares positive-center packing bounds
      -> local Big.

Do not frame this as merely avoiding global claims.
Frame it as the finite-window packaging step needed before counting/packing
density theorems.

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

次は、

```text id="fm7tq3"
center/separator/center surface
  -> finite-window carrier
  -> separator also lies inside window
```

まで行く。

その次に初めて、

```text id="r0qt0u"
finite-window positive center packing bound
```

へ入る。
ここから local Big が見えてくる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 6dc8096e..1d65aff4 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -1679,6 +1679,30 @@ theorem SourcePressureLocalPackingSeparatorState.two_le_index_gap
     r + W.val + 2 ≤ r + W'.val :=
   h.forward.two_le_index_gap

+/--
+Center/separator/center surface of the local packing state.
+
+This is the first finite-window-packing-facing reading of the named state:
+the left center is positive, the separator is nonpositive, and the right center
+is positive, with strict index placement and two-step value spacing.
+-/
+theorem SourcePressureLocalPackingSeparatorState.center_separator_surface
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r} {m : ℕ}
+    (h : SourcePressureLocalPackingSeparatorState L W W' m) :
+    0 < SourcePressureMarginInt n k (r + W.val) ∧
+      SourcePressureMarginInt n k m ≤ 0 ∧
+        0 < SourcePressureMarginInt n k (r + W'.val) ∧
+          r + W.val < m ∧
+            m < r + W'.val ∧
+              W.val + 2 ≤ W'.val := by
+  rcases h.forward.center_pair_surface with
+    ⟨hcenterL, hcenterR, _htargetL, _htargetR, _hlt⟩
+  exact
+    ⟨hcenterL, h.separator_nonpos, hcenterR, h.left_lt_separator,
+      h.separator_lt_right, h.two_le_value_gap⟩
+
 /--
 Constructor from a forward pair-comparison state to the named local packing
 separator state.
@@ -2378,4 +2402,91 @@ theorem sourcePressureBeamSeedState_to_localPackingSeparatorState_or_pairOverlap
   sourcePressureFailureResolutionState_to_localPackingSeparatorState_or_pairOverlap
     hsorted (sourcePressureBeamSeedState_to_failureResolutionState h)

+/--
+Failure resolution reaches a center/separator/center local-packing surface or
+a concrete adjacent-pair overlap obstruction.
+
+The forward branch exposes the actual observed sign pattern:
+
+```text
+positive center -> nonpositive separator -> positive center
+```
+-/
+theorem sourcePressureFailureResolutionState_to_centerSeparatorSurface_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (h : SourcePressureFailureResolutionState L) :
+    (∃ W W' m,
+      SourcePressureLocalPackingSeparatorState L W W' m ∧
+        0 < SourcePressureMarginInt n k (r + W.val) ∧
+          SourcePressureMarginInt n k m ≤ 0 ∧
+            0 < SourcePressureMarginInt n k (r + W'.val) ∧
+              r + W.val < m ∧
+                m < r + W'.val ∧
+                  W.val + 2 ≤ W'.val) ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B := by
+  rcases
+    sourcePressureFailureResolutionState_to_localPackingSeparatorState_or_pairOverlap
+      hsorted h with hsep | hoverlap
+  · rcases hsep with ⟨W, W', m, hpack⟩
+    rcases hpack.center_separator_surface with
+      ⟨hcenterL, hnonpos, hcenterR, hleft, hright, hgap⟩
+    exact
+      Or.inl
+        ⟨W, W', m, hpack, hcenterL, hnonpos, hcenterR, hleft, hright,
+          hgap⟩
+  · exact Or.inr hoverlap
+
+/--
+Sorted failure reaches a center/separator/center local-packing surface or a
+concrete adjacent-pair overlap obstruction.
+-/
+theorem sourcePressureSortedFailureState_to_centerSeparatorSurface_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (h : SourcePressureSortedFailureState L) :
+    (∃ W W' m,
+      SourcePressureLocalPackingSeparatorState L W W' m ∧
+        0 < SourcePressureMarginInt n k (r + W.val) ∧
+          SourcePressureMarginInt n k m ≤ 0 ∧
+            0 < SourcePressureMarginInt n k (r + W'.val) ∧
+              r + W.val < m ∧
+                m < r + W'.val ∧
+                  W.val + 2 ≤ W'.val) ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
+  sourcePressureFailureResolutionState_to_centerSeparatorSurface_or_pairOverlap
+    hsorted (sourcePressureSortedFailureState_to_failureResolutionState h)
+
+/--
+Beam seed reaches a center/separator/center local-packing surface or a concrete
+adjacent-pair overlap obstruction.
+
+This is the Beam-facing finite-window packing surface currently available from
+the state ladder.
+-/
+theorem sourcePressureBeamSeedState_to_centerSeparatorSurface_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (h : SourcePressureBeamSeedState L) :
+    (∃ W W' m,
+      SourcePressureLocalPackingSeparatorState L W W' m ∧
+        0 < SourcePressureMarginInt n k (r + W.val) ∧
+          SourcePressureMarginInt n k m ≤ 0 ∧
+            0 < SourcePressureMarginInt n k (r + W'.val) ∧
+              r + W.val < m ∧
+                m < r + W'.val ∧
+                  W.val + 2 ≤ W'.val) ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
+  sourcePressureFailureResolutionState_to_centerSeparatorSurface_or_pairOverlap
+    hsorted (sourcePressureBeamSeedState_to_failureResolutionState h)
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-285.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-285.md
new file mode 100644
index 00000000..6b426942
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-285.md
@@ -0,0 +1,114 @@
+# Report: petal-285
+
+## Goal
+
+Expose the local sign pattern carried by
+`SourcePressureLocalPackingSeparatorState`:
+
+```text
+positive center -> nonpositive separator -> positive center
+```
+
+This checkpoint moves the named packing separator state toward finite-window
+packing bounds and local Big.
+
+## Implemented
+
+Added:
+
+- `SourcePressureLocalPackingSeparatorState.center_separator_surface`
+
+Added upstream lifted surface theorems:
+
+- `sourcePressureFailureResolutionState_to_centerSeparatorSurface_or_pairOverlap`
+- `sourcePressureSortedFailureState_to_centerSeparatorSurface_or_pairOverlap`
+- `sourcePressureBeamSeedState_to_centerSeparatorSurface_or_pairOverlap`
+
+## Established Facts
+
+From a local packing separator state, Lean now projects:
+
+```lean
+0 < SourcePressureMarginInt n k (r + W.val)
+  ∧ SourcePressureMarginInt n k m <= 0
+  ∧ 0 < SourcePressureMarginInt n k (r + W'.val)
+  ∧ r + W.val < m
+  ∧ m < r + W'.val
+  ∧ W.val + 2 <= W'.val
+```
+
+So the named state directly exposes:
+
+```text
+left positive center
+  < nonpositive separator
+  < right positive center
+```
+
+with a certified value gap of at least two.
+
+## Upstream Route
+
+The state ladder now reaches this center/separator/center surface:
+
+```text
+FailureResolution + sorted(L)
+  -> center/separator/center surface
+   ∨ concrete adjacent-pair overlap obstruction
+
+SortedFailure + sorted(L)
+  -> center/separator/center surface
+   ∨ concrete adjacent-pair overlap obstruction
+
+BeamSeed + sorted(L)
+  -> center/separator/center surface
+   ∨ concrete adjacent-pair overlap obstruction
+```
+
+## What Can Be Concluded
+
+This is the next step in the route:
+
+```text
+observed local structure
+  -> reusable local theorem
+  -> finite-window packing bound
+  -> local Big
+```
+
+The explicit local phenomenon is now theoremized: a forward pair of positive
+centers carries a nonpositive separator strictly between them.  Upstream seed
+and failure states either expose that pattern or return a concrete overlap
+obstruction.
+
+## Guardrails
+
+This checkpoint is local to the explicit witness list `L`.  It does not claim:
+
+- global coverage;
+- global uniqueness of positive centers;
+- arbitrary window disjointness;
+- global termination.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureState
+lake build DkMath.Collatz.PetalBridge
+git diff --check
+```
+
+## Next Branch Prediction
+
+The next useful step is a finite-window carrier that stores:
+
+```text
+window bounds
+left positive center in window
+nonpositive separator in window
+right positive center in window
+```
+
+Only after that should counting or packing-density theorems be attempted.
````
`````
