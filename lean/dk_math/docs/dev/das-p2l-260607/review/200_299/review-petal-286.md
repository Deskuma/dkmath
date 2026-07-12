# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: f8b0dadd288f3d806d807431bc0dc6963ec3ddd6

## Report

実装完了です。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:971) に `SourcePressureFiniteWindowPackingSeparatorState` を追加しました。これは finite window `[lo, hi]` 内に左右の正 center を持つ `LocalPackingSeparatorState` を保持する carrier です。

追加した主な projection / constructor:

- `SourcePressureFiniteWindowPackingSeparatorState.localPacking`
- `SourcePressureFiniteWindowPackingSeparatorState.left_center_in_window`
- `SourcePressureFiniteWindowPackingSeparatorState.right_center_in_window`
- `SourcePressureFiniteWindowPackingSeparatorState.separator_in_window`
- `SourcePressureFiniteWindowPackingSeparatorState.center_separator_surface`
- `SourcePressureFiniteWindowPackingSeparatorState.two_le_value_gap`
- `SourcePressureFiniteWindowPackingSeparatorState.two_le_index_gap`
- `SourcePressureLocalPackingSeparatorState.to_finiteWindowPackingSeparatorState`

重要な新事実は、左右の正 center が `[lo, hi]` に入っていれば、その間の非正 separator も同じ window に入ることです。

```lean
lo ≤ m ∧ m ≤ hi
```

上流 lift も追加しました。

- `sourcePressureFailureResolutionState_to_finiteWindowPackingSeparatorState_or_pairOverlap`
- `sourcePressureSortedFailureState_to_finiteWindowPackingSeparatorState_or_pairOverlap`
- `sourcePressureBeamSeedState_to_finiteWindowPackingSeparatorState_or_pairOverlap`

これで、`L` 内の全 witness center が `[lo, hi]` に入るという仮定のもと、

```text
BeamSeed / SortedFailure / FailureResolution
  -> FiniteWindowPackingSeparatorState
   ∨ concrete adjacent-pair overlap obstruction
```

まで進みました。

[report-petal-286.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-286.md:1) も追加済みです。

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

次はこの finite-window carrier から、window 内の `positive -> nonpositive -> positive` surface を直接引き出す theorem を置くのが自然です。その後で counting / packing-density 側へ進めます。

## Review

## 判定

採用。
今回は `center/separator/center surface` から、さらに **finite-window carrier** へ進んでいる。

追加された中心定義：

```lean id="d9s7qk"
SourcePressureFiniteWindowPackingSeparatorState
```

これは、

```lean id="xxiwn6"
SourcePressureLocalPackingSeparatorState L W W' m ∧
  lo ≤ r + W.val ∧
    r + W'.val ≤ hi
```

を持つ state じゃ。つまり、左右の正中心が有限窓 `[lo, hi]` に入っていることを保持し、その間にある非正 separator も同じ窓に入ることを導く carrier になった。

## 実装レビュー

良い進展。
今回の核はこれ。

```lean id="ewbyyw"
SourcePressureFiniteWindowPackingSeparatorState.separator_in_window
```

内容は、

```lean id="zyss1i"
lo ≤ m ∧ m ≤ hi
```

であり、証明は次の構造をそのまま使っている。

```text id="h14ham"
lo ≤ left center < separator < right center ≤ hi
```

これは有限窓 packing bound に入る前の、かなり重要な橋じゃ。

さらに上流 lift も揃っている。

```lean id="gkle3c"
sourcePressureFailureResolutionState_to_finiteWindowPackingSeparatorState_or_pairOverlap
sourcePressureSortedFailureState_to_finiteWindowPackingSeparatorState_or_pairOverlap
sourcePressureBeamSeedState_to_finiteWindowPackingSeparatorState_or_pairOverlap
```

これで、list 全体の witness center が `[lo, hi]` に入るという仮定のもと、

```text id="a9y3hr"
BeamSeed / SortedFailure / FailureResolution
  -> FiniteWindowPackingSeparatorState
   ∨ PairOverlap
```

まで進んだ。

## 進展評価

改善された指示は、さらに効いている。

流れがこう進んだ。

```text id="mkw7qx"
nonpositive separator
  -> LocalPackingSeparatorState
  -> center/separator/center surface
  -> FiniteWindowPackingSeparatorState
  -> separator is inside the same finite window
```

これはもう単発 projection ではない。
**有限窓内の詰め込み上界**へ進むための carrier を作れている。

特に report のこの流れは良い。

```text id="qthhq8"
LocalPackingSeparatorState
  -> center/separator/center surface
  -> finite-window carrier
  -> separator is inside the same finite window
  -> prepares positive-center packing bounds
  -> local Big
```

これなら Codex も「次は counting / packing 側へ進む」と読める。

## 数学的意味

今回で、局所構造は有限窓に入った。

```text id="fasgq9"
window [lo, hi]
  contains left positive center
  contains right positive center
  therefore also contains the nonpositive separator between them
```

つまり、正中心を有限窓に二つ置くなら、その間の非正 separator も同じ窓の中に置かざるを得ない。

これは次の packing bound の核になる。

```text id="nrmfiv"
positive center を置くには、
separator 用の場所も必要になる。
```

これが詰め込み制限の始まりじゃ。

## 注意点

今回の report は、前よりかなり良い。
ただ、次からは `Guardrails` を単独で強く置くより、こう書く方がよい。

```text id="ngh0q6"
This checkpoint does not count centers yet.
It creates the finite-window carrier needed for the next counting and packing-bound layer.
```

否定ではなく、**次に何を可能にしたか** を主語にする。

## 次に攻める定理

次は report の予測通り、finite-window surface を作るのが自然。

欲しいのはこれ。

```text id="l2884e"
left center positive and in window
separator nonpositive and in window
right center positive and in window
two-step spacing
```

Lean では例えば：

```lean id="rgx541"
theorem SourcePressureFiniteWindowPackingSeparatorState.window_center_separator_surface
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {lo hi : ℕ}
    {W W' : SourcePressureLocalIslandWitness n k r}
    {m : ℕ}
    (h : SourcePressureFiniteWindowPackingSeparatorState L lo hi W W' m) :
    lo ≤ r + W.val ∧
      0 < SourcePressureMarginInt n k (r + W.val) ∧
        lo ≤ m ∧
          m ≤ hi ∧
            SourcePressureMarginInt n k m ≤ 0 ∧
              r + W'.val ≤ hi ∧
                0 < SourcePressureMarginInt n k (r + W'.val) ∧
                  W.val + 2 ≤ W'.val
```

これで、有限窓内の `positive -> nonpositive -> positive` が一発で取れる。

## Codex 指示

今回はまだ宇宙式反転射影の全容は渡さず、現行の PressureState / finite-window packing route として進めるのがよい。

```text id="p3m50f"
Goal:
  Continue from SourcePressureFiniteWindowPackingSeparatorState toward a
  finite-window packing bound.  Do not stop at carrier creation.  Add the first
  finite-window surface that exposes the actual in-window sign pattern:

    positive center in window
      -> nonpositive separator in window
      -> positive center in window

Phase A:
  Add a compact finite-window surface theorem.

  theorem SourcePressureFiniteWindowPackingSeparatorState.window_center_separator_surface
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {lo hi : ℕ}
      {W W' : SourcePressureLocalIslandWitness n k r}
      {m : ℕ}
      (h : SourcePressureFiniteWindowPackingSeparatorState L lo hi W W' m) :
      lo ≤ r + W.val ∧
        0 < SourcePressureMarginInt n k (r + W.val) ∧
          lo ≤ m ∧
            m ≤ hi ∧
              SourcePressureMarginInt n k m ≤ 0 ∧
                r + W'.val ≤ hi ∧
                  0 < SourcePressureMarginInt n k (r + W'.val) ∧
                    W.val + 2 ≤ W'.val

Use:
  h.left_center_in_window
  h.right_center_in_window
  h.separator_in_window
  h.center_separator_surface

Proof shape:
  rcases h.center_separator_surface with
    ⟨hcenterL, hnonpos, hcenterR, _hleft, _hright, hgap⟩
  rcases h.separator_in_window with ⟨hmlo, hmhi⟩
  exact ⟨h.left_center_in_window, hcenterL, hmlo, hmhi,
    hnonpos, h.right_center_in_window, hcenterR, hgap⟩

Phase B:
  Add upstream lifted versions only if they close cheaply:

    sourcePressureFailureResolutionState_to_windowCenterSeparatorSurface_or_pairOverlap
    sourcePressureSortedFailureState_to_windowCenterSeparatorSurface_or_pairOverlap
    sourcePressureBeamSeedState_to_windowCenterSeparatorSurface_or_pairOverlap

Use:
  sourcePressureFailureResolutionState_to_finiteWindowPackingSeparatorState_or_pairOverlap
  sourcePressureSortedFailureState_to_finiteWindowPackingSeparatorState_or_pairOverlap
  sourcePressureBeamSeedState_to_finiteWindowPackingSeparatorState_or_pairOverlap

Phase C:
  Report the route as:

    FiniteWindowPackingSeparatorState
      -> in-window center/separator/center surface
      -> every selected pair of positive centers forces an in-window
         nonpositive separator
      -> this prepares the first finite-window positive-center packing bound
      -> local Big.

Do not frame the report as merely avoiding global claims.
Frame it as the finite-window surface needed before counting.

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

次で、

```text id="yowend"
FiniteWindowPackingSeparatorState
  -> window_center_separator_surface
```

が取れる。
その次から、いよいよ counting / packing-density 側へ入れる。

方向はかなり良い。
局所構造が、有限窓の中に固定され始めている。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 1d65aff4..aa05e911 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -960,6 +960,24 @@ def SourcePressureLocalPackingSeparatorState
       m < r + W'.val ∧
         SourcePressureMarginInt n k m ≤ 0
 
+/--
+Finite-window local packing separator state.
+
+This is the first finite-window carrier for the local packing obstruction.  It
+stores a local packing separator and records that both positive center indices
+are inside the explicit window `[lo, hi]`.  The separator itself is then forced
+inside the same window by the strict inequalities in the local packing state.
+-/
+def SourcePressureFiniteWindowPackingSeparatorState
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (lo hi : ℕ)
+    (W W' : SourcePressureLocalIslandWitness n k r)
+    (m : ℕ) : Prop :=
+  SourcePressureLocalPackingSeparatorState L W W' m ∧
+    lo ≤ r + W.val ∧
+      r + W'.val ≤ hi
+
 /-- Project the underlying forward box comparison state. -/
 theorem SourcePressureForwardPairComparisonState.forward
     {n : OddNat} {k r : ℕ}
@@ -1703,6 +1721,97 @@ theorem SourcePressureLocalPackingSeparatorState.center_separator_surface
     ⟨hcenterL, h.separator_nonpos, hcenterR, h.left_lt_separator,
       h.separator_lt_right, h.two_le_value_gap⟩
 
+/-- Project the underlying local packing separator state. -/
+theorem SourcePressureFiniteWindowPackingSeparatorState.localPacking
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ} {W W' : SourcePressureLocalIslandWitness n k r} {m : ℕ}
+    (h : SourcePressureFiniteWindowPackingSeparatorState L lo hi W W' m) :
+    SourcePressureLocalPackingSeparatorState L W W' m :=
+  h.1
+
+/-- The left positive center lies inside the finite window lower bound. -/
+theorem SourcePressureFiniteWindowPackingSeparatorState.left_center_in_window
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ} {W W' : SourcePressureLocalIslandWitness n k r} {m : ℕ}
+    (h : SourcePressureFiniteWindowPackingSeparatorState L lo hi W W' m) :
+    lo ≤ r + W.val :=
+  h.2.1
+
+/-- The right positive center lies inside the finite window upper bound. -/
+theorem SourcePressureFiniteWindowPackingSeparatorState.right_center_in_window
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ} {W W' : SourcePressureLocalIslandWitness n k r} {m : ℕ}
+    (h : SourcePressureFiniteWindowPackingSeparatorState L lo hi W W' m) :
+    r + W'.val ≤ hi :=
+  h.2.2
+
+/--
+The separator lies inside the same finite window as the two centers.
+
+This is the key finite-window consequence: once both positive centers are in
+the window and the separator is strictly between them, the separator is also in
+the window.
+-/
+theorem SourcePressureFiniteWindowPackingSeparatorState.separator_in_window
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ} {W W' : SourcePressureLocalIslandWitness n k r} {m : ℕ}
+    (h : SourcePressureFiniteWindowPackingSeparatorState L lo hi W W' m) :
+    lo ≤ m ∧ m ≤ hi := by
+  have hlo : lo ≤ r + W.val := h.left_center_in_window
+  have hleft : r + W.val < m := h.localPacking.left_lt_separator
+  have hright : m < r + W'.val := h.localPacking.separator_lt_right
+  have hhi : r + W'.val ≤ hi := h.right_center_in_window
+  omega
+
+/-- Finite-window state exposes the center/separator/center surface. -/
+theorem SourcePressureFiniteWindowPackingSeparatorState.center_separator_surface
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ} {W W' : SourcePressureLocalIslandWitness n k r} {m : ℕ}
+    (h : SourcePressureFiniteWindowPackingSeparatorState L lo hi W W' m) :
+    0 < SourcePressureMarginInt n k (r + W.val) ∧
+      SourcePressureMarginInt n k m ≤ 0 ∧
+        0 < SourcePressureMarginInt n k (r + W'.val) ∧
+          r + W.val < m ∧
+            m < r + W'.val ∧
+              W.val + 2 ≤ W'.val :=
+  h.localPacking.center_separator_surface
+
+/-- Value-level two-step spacing inherited by the finite-window state. -/
+theorem SourcePressureFiniteWindowPackingSeparatorState.two_le_value_gap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ} {W W' : SourcePressureLocalIslandWitness n k r} {m : ℕ}
+    (h : SourcePressureFiniteWindowPackingSeparatorState L lo hi W W' m) :
+    W.val + 2 ≤ W'.val :=
+  h.localPacking.two_le_value_gap
+
+/-- Index-level two-step spacing inherited by the finite-window state. -/
+theorem SourcePressureFiniteWindowPackingSeparatorState.two_le_index_gap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ} {W W' : SourcePressureLocalIslandWitness n k r} {m : ℕ}
+    (h : SourcePressureFiniteWindowPackingSeparatorState L lo hi W W' m) :
+    r + W.val + 2 ≤ r + W'.val :=
+  h.localPacking.two_le_index_gap
+
+/--
+Constructor from a local packing separator to the finite-window carrier under
+explicit bounds on the two positive centers.
+-/
+theorem SourcePressureLocalPackingSeparatorState.to_finiteWindowPackingSeparatorState
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ} {W W' : SourcePressureLocalIslandWitness n k r} {m : ℕ}
+    (h : SourcePressureLocalPackingSeparatorState L W W' m)
+    (hlo : lo ≤ r + W.val) (hhi : r + W'.val ≤ hi) :
+    SourcePressureFiniteWindowPackingSeparatorState L lo hi W W' m :=
+  ⟨h, hlo, hhi⟩
+
 /--
 Constructor from a forward pair-comparison state to the named local packing
 separator state.
@@ -2489,4 +2598,83 @@ theorem sourcePressureBeamSeedState_to_centerSeparatorSurface_or_pairOverlap
   sourcePressureFailureResolutionState_to_centerSeparatorSurface_or_pairOverlap
     hsorted (sourcePressureBeamSeedState_to_failureResolutionState h)
 
+/--
+Failure resolution reaches a finite-window packing separator state or a
+concrete adjacent-pair overlap obstruction.
+
+The window hypotheses are deliberately explicit: every witness center in `L`
+is assumed to lie in `[lo, hi]`, so the selected forward pair and its separator
+are packaged into the finite-window carrier.
+-/
+theorem sourcePressureFailureResolutionState_to_finiteWindowPackingSeparatorState_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (h : SourcePressureFailureResolutionState L)
+    (hlo_all : ∀ W, W ∈ L → lo ≤ r + W.val)
+    (hhi_all : ∀ W, W ∈ L → r + W.val ≤ hi) :
+    (∃ W W' m,
+      SourcePressureFiniteWindowPackingSeparatorState L lo hi W W' m) ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B := by
+  rcases
+    sourcePressureFailureResolutionState_to_localPackingSeparatorState_or_pairOverlap
+      hsorted h with hsep | hoverlap
+  · rcases hsep with ⟨W, W', m, hpack⟩
+    have hlo : lo ≤ r + W.val := hlo_all W hpack.forward.left_mem
+    have hhi : r + W'.val ≤ hi := hhi_all W' hpack.forward.right_mem
+    exact
+      Or.inl
+        ⟨W, W', m,
+          hpack.to_finiteWindowPackingSeparatorState hlo hhi⟩
+  · exact Or.inr hoverlap
+
+/--
+Sorted failure reaches a finite-window packing separator state or a concrete
+adjacent-pair overlap obstruction.
+-/
+theorem sourcePressureSortedFailureState_to_finiteWindowPackingSeparatorState_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (h : SourcePressureSortedFailureState L)
+    (hlo_all : ∀ W, W ∈ L → lo ≤ r + W.val)
+    (hhi_all : ∀ W, W ∈ L → r + W.val ≤ hi) :
+    (∃ W W' m,
+      SourcePressureFiniteWindowPackingSeparatorState L lo hi W W' m) ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
+  sourcePressureFailureResolutionState_to_finiteWindowPackingSeparatorState_or_pairOverlap
+    hsorted (sourcePressureSortedFailureState_to_failureResolutionState h)
+    hlo_all hhi_all
+
+/--
+Beam seed reaches a finite-window packing separator state or a concrete
+adjacent-pair overlap obstruction.
+
+This is the first Beam-facing finite-window packaging theorem.  It does not
+count centers yet; it prepares the exact carrier needed before counting or
+packing-density arguments.
+-/
+theorem sourcePressureBeamSeedState_to_finiteWindowPackingSeparatorState_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (h : SourcePressureBeamSeedState L)
+    (hlo_all : ∀ W, W ∈ L → lo ≤ r + W.val)
+    (hhi_all : ∀ W, W ∈ L → r + W.val ≤ hi) :
+    (∃ W W' m,
+      SourcePressureFiniteWindowPackingSeparatorState L lo hi W W' m) ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
+  sourcePressureFailureResolutionState_to_finiteWindowPackingSeparatorState_or_pairOverlap
+    hsorted (sourcePressureBeamSeedState_to_failureResolutionState h)
+    hlo_all hhi_all
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-286.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-286.md
new file mode 100644
index 00000000..c7ace881
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-286.md
@@ -0,0 +1,130 @@
+# Report: petal-286
+
+## Goal
+
+Continue from the center/separator/center surface toward finite-window packing
+bounds by creating the first finite-window carrier.
+
+## Implemented
+
+Added:
+
+- `SourcePressureFiniteWindowPackingSeparatorState`
+
+Added projections and constructor:
+
+- `SourcePressureFiniteWindowPackingSeparatorState.localPacking`
+- `SourcePressureFiniteWindowPackingSeparatorState.left_center_in_window`
+- `SourcePressureFiniteWindowPackingSeparatorState.right_center_in_window`
+- `SourcePressureFiniteWindowPackingSeparatorState.separator_in_window`
+- `SourcePressureFiniteWindowPackingSeparatorState.center_separator_surface`
+- `SourcePressureFiniteWindowPackingSeparatorState.two_le_value_gap`
+- `SourcePressureFiniteWindowPackingSeparatorState.two_le_index_gap`
+- `SourcePressureLocalPackingSeparatorState.to_finiteWindowPackingSeparatorState`
+
+Added upstream finite-window lifted split theorems:
+
+- `sourcePressureFailureResolutionState_to_finiteWindowPackingSeparatorState_or_pairOverlap`
+- `sourcePressureSortedFailureState_to_finiteWindowPackingSeparatorState_or_pairOverlap`
+- `sourcePressureBeamSeedState_to_finiteWindowPackingSeparatorState_or_pairOverlap`
+
+## Established Facts
+
+The finite-window state stores a local packing separator and records that both
+positive center indices lie in `[lo, hi]`:
+
+```lean
+SourcePressureLocalPackingSeparatorState L W W' m
+  ∧ lo <= r + W.val
+  ∧ r + W'.val <= hi
+```
+
+Lean proves the separator is also inside the same window:
+
+```lean
+lo <= m ∧ m <= hi
+```
+
+This follows from:
+
+```text
+lo <= left center < separator < right center <= hi
+```
+
+## Upstream Route
+
+With explicit list-wide window bounds
+
+```lean
+hlo_all : ∀ W, W ∈ L → lo <= r + W.val
+hhi_all : ∀ W, W ∈ L → r + W.val <= hi
+```
+
+the state ladder now reaches the finite-window carrier:
+
+```text
+FailureResolution + sorted(L)
+  -> FiniteWindowPackingSeparatorState
+   ∨ concrete adjacent-pair overlap obstruction
+
+SortedFailure + sorted(L)
+  -> FiniteWindowPackingSeparatorState
+   ∨ concrete adjacent-pair overlap obstruction
+
+BeamSeed + sorted(L)
+  -> FiniteWindowPackingSeparatorState
+   ∨ concrete adjacent-pair overlap obstruction
+```
+
+## What Can Be Concluded
+
+The route has advanced from a raw local sign pattern to a finite-window carrier:
+
+```text
+LocalPackingSeparatorState
+  -> center/separator/center surface
+  -> finite-window carrier
+  -> separator is inside the same finite window
+  -> prepares positive-center packing bounds
+  -> local Big
+```
+
+The key new fact is that once both positive centers are inside an explicit
+window, the certified nonpositive separator is also inside that window.
+
+## Guardrails
+
+This checkpoint does not count centers yet.  It also does not claim:
+
+- global coverage;
+- arbitrary disjointness of windows;
+- maximality of the window;
+- global termination.
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
+The next layer should define a finite-window surface bundling:
+
+```text
+left center positive and in window
+separator nonpositive and in window
+right center positive and in window
+two-step spacing
+```
+
+This should be added before attempting any actual counting theorem.
````
`````
