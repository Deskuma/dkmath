# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: f12747639ec0fe7a6315eef72ee3aada62d92f54

## Report

cp-287 を完了しました。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean#L1792) に以下を追加しました。

- 有限窓内の `positive → nonpositive → positive` surface
- FailureResolution / SortedFailure / BeamSeed からの lift
- 厳密な順序鎖：
  `lo ≤ left center < separator < right center ≤ hi`
- 窓幅の必要条件：
  `lo + 2 ≤ hi`

Lean により、有限窓 carrier が存在すれば、二つの正中心間に同じ窓内の非正 separator が必ず存在し、三点は相異なる順序位置を占めることが確定しました。

次の counting 段階で必要なのは、複数 pair 間で separator がどう再利用されるかという不変量です。候補は注入性、区間非重複、または bounded multiplicity です。

結果は [report-petal-287.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-287.md) に記録しました。

検証済み：

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

## Review

## 判定

採用。
そして今回は、かなり良い進展じゃ。`SourcePressureFiniteWindowPackingSeparatorState` が単なる carrier ではなく、**counting 直前の有限窓 surface** まで育った。

追加された主な成果は、次の三系統。

```lean id="y805kx"
SourcePressureFiniteWindowPackingSeparatorState.window_center_separator_surface
SourcePressureFiniteWindowPackingSeparatorState.window_order_chain
SourcePressureFiniteWindowPackingSeparatorState.two_le_window_width
```

さらに、`FailureResolution / SortedFailure / BeamSeed` からの lift も追加されている。これで有限窓 carrier が存在するとき、

```text id="y3lxzf"
lo ≤ left center < separator < right center ≤ hi
```

という厳密な順序鎖と、窓幅の必要条件

```lean id="b2v45v"
lo + 2 ≤ hi
```

まで Lean で固定された。これは counting / packing-density へ入る直前の非常に良い足場じゃ。

## 実装レビュー

`window_center_separator_surface` は、前回こちらが求めた形にかなり忠実。

有限窓内で、

```text id="ntbzg8"
positive center in window
  -> nonpositive separator in window
  -> positive center in window
```

を surface として取り出せる。

さらに `window_order_chain` がよい。これは単に符号を読むだけでなく、三点が有限窓内で消費する順序位置を明示する。

```lean id="sn6dhc"
lo ≤ r + W.val ∧
  r + W.val < m ∧
    m < r + W'.val ∧
      r + W'.val ≤ hi
```

そして `two_le_window_width` は、ここから自然に出る最初の packing 予兆じゃ。

```lean id="ptqzf7"
lo + 2 ≤ hi
```

これはまだ「個数上界」ではないが、**二つの正中心と一つの separator を置くには、有限窓に少なくとも三位置分の幅が必要** という第一消費法則になっている。

## 改善された指示の進展評価

かなり改善されている。
前回までの流れを並べると、こうじゃ。

```text id="wh9zwd"
LocalPackingSeparatorState
  -> center/separator/center surface
  -> FiniteWindowPackingSeparatorState
  -> separator in same window
  -> window center/separator surface
  -> ordered chain
  -> minimum window width
```

これはもう単発補題ではない。
**有限窓 packing bound に向かって、必要な carrier と surface と幅制約を順に積んでいる**。

特に `two_le_window_width` は良い。
これで初めて、「正中心を二つ選ぶと窓の幅を消費する」という counting 方向の言葉が Lean theorem になった。

## 数学的意味

今回の定理は、局所観測を有限窓の幾何へ落としている。

```text id="c3znbx"
左正中心
  < 非正 separator
  < 右正中心
```

この三点は同じ `[lo, hi]` に入る。
したがって、この局所構造が一つ存在するだけで、窓には最低限の幅が要求される。

```text id="bvxvly"
one local packing separator
  -> three ordered occupied indices
  -> window width at least 2
```

これは、次の段階で複数の正中心列を扱うときの基本単位になる。

## 注意点

まだ言えていないことは明確じゃ。

```text id="ixgmj4"
複数 pair の separator が互いに異なる
separator を何回まで再利用できるか
pair 区間が非重複である
有限窓内の positive center 個数上界
packing density
local Big 上界
```

つまり、今回で「一つの pair が窓をどう消費するか」は見えた。
しかし、「複数 pair が同じ窓内でどう干渉するか」は次の問題じゃ。

ここが次の山になる。

## 次に攻める本命

次は report の言う通り、**separator reuse invariant** じゃ。

数え上げに入るには、以下のどれかが必要になる。

```text id="l1iyku"
1. separator injection
   pair ごとに separator が異なる

2. interval disjointness
   pair が作る consumed interval が互いに重ならない

3. bounded multiplicity
   一つの separator が使われる回数に上界がある
```

この三つのうち、いきなり injection や disjointness を狙うと強すぎる可能性がある。
次はまず **bounded multiplicity の最小形** を探すのがよい。

ただし、Lean 実装としては最初に「reuse の観測 state」を置くのが安全じゃ。

## 次の Codex 指示

```text id="qi17fl"
Goal:
  Continue from the finite-window ordered chain toward the first reusable
  counting invariant.  Do not stop at another surface theorem.

  The next target is to understand how separators can be reused by multiple
  positive-center pairs inside the same finite window.

Current established local unit:
  SourcePressureFiniteWindowPackingSeparatorState gives

    lo ≤ left center < separator < right center ≤ hi

  and therefore

    lo + 2 ≤ hi

  for one selected pair.

Main problem for counting:
  To count positive centers in a finite window, we must understand whether
  different selected pairs can share the same separator, overlap their consumed
  intervals, or have bounded multiplicity.

Phase A:
  Add a minimal pair-of-packings comparison state.

Suggested definition:

  def SourcePressureFiniteWindowPackingPairComparisonState
      {n : OddNat} {k r : ℕ}
      (L : List (SourcePressureLocalIslandWitness n k r))
      (lo hi : ℕ)
      (W₁ W₁' : SourcePressureLocalIslandWitness n k r)
      (m₁ : ℕ)
      (W₂ W₂' : SourcePressureLocalIslandWitness n k r)
      (m₂ : ℕ) : Prop :=
    SourcePressureFiniteWindowPackingSeparatorState L lo hi W₁ W₁' m₁ ∧
      SourcePressureFiniteWindowPackingSeparatorState L lo hi W₂ W₂' m₂

Phase B:
  Add basic projections for the two finite-window packing states:
    - .left
    - .right
    - .left_order_chain
    - .right_order_chain
    - .left_window_width
    - .right_window_width

Phase C:
  Add the first separator comparison split:

  theorem SourcePressureFiniteWindowPackingPairComparisonState.separator_eq_or_ne
      ... :
      m₁ = m₂ ∨ m₁ ≠ m₂

  This is mathematically trivial, but it creates the branch point for the next
  checkpoint.

Phase D:
  In the same checkpoint, if cheap, add branch-specific surfaces:

  separator_eq_surface:
    m₁ = m₂ plus both ordered chains

  separator_ne_surface:
    m₁ ≠ m₂ plus both ordered chains

Do not try to prove injection or disjointness yet unless it follows immediately
from existing hypotheses.  The goal is to expose the reuse branch explicitly.

Phase E:
  Report the route as:

    finite-window ordered chain
      -> one pair consumes three ordered positions
      -> pair-of-packings comparison
      -> separator reuse split
      -> prepares bounded multiplicity / packing count
      -> local Big.

Important:
  Do not frame this as merely avoiding overclaims.
  The purpose is to prepare the actual counting invariant needed for finite
  window packing bounds.

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

次の山はこれじゃ。

```text id="dpjng0"
one local packing unit
  -> pair of local packing units
  -> separator shared or distinct
  -> reuse invariant
  -> bounded multiplicity
  -> finite-window packing bound
```

Codex GPT-5.6 Sol になったなら、このあたりの「単発 projection ではなく、次の構造分岐まで作る」依頼はちょうどよさそうじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index aa05e911..9b922793 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -1781,6 +1781,63 @@ theorem SourcePressureFiniteWindowPackingSeparatorState.center_separator_surface
               W.val + 2 ≤ W'.val :=
   h.localPacking.center_separator_surface

+/--
+Finite-window center/separator/center surface used immediately before counting.
+
+Both positive centers and the forced nonpositive separator are exposed inside
+the same explicit window.  Thus every selected forward pair contributes the
+ordered in-window sign pattern `positive -> nonpositive -> positive`, together
+with the two-step spacing needed by a finite-window packing argument.
+-/
+theorem SourcePressureFiniteWindowPackingSeparatorState.window_center_separator_surface
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ} {W W' : SourcePressureLocalIslandWitness n k r} {m : ℕ}
+    (h : SourcePressureFiniteWindowPackingSeparatorState L lo hi W W' m) :
+    lo ≤ r + W.val ∧
+      0 < SourcePressureMarginInt n k (r + W.val) ∧
+        lo ≤ m ∧
+          m ≤ hi ∧
+            SourcePressureMarginInt n k m ≤ 0 ∧
+              r + W'.val ≤ hi ∧
+                0 < SourcePressureMarginInt n k (r + W'.val) ∧
+                  W.val + 2 ≤ W'.val := by
+  rcases h.center_separator_surface with
+    ⟨hcenterL, hnonpos, hcenterR, _hleft, _hright, hgap⟩
+  rcases h.separator_in_window with ⟨hmlo, hmhi⟩
+  exact
+    ⟨h.left_center_in_window, hcenterL, hmlo, hmhi, hnonpos,
+      h.right_center_in_window, hcenterR, hgap⟩
+
+/--
+Ordered index chain underlying the finite-window packing surface.
+
+This caller-facing form records the exact finite interval consumed by one
+selected pair: left center, separator, and right center occur strictly in that
+order inside `[lo, hi]`.
+-/
+theorem SourcePressureFiniteWindowPackingSeparatorState.window_order_chain
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ} {W W' : SourcePressureLocalIslandWitness n k r} {m : ℕ}
+    (h : SourcePressureFiniteWindowPackingSeparatorState L lo hi W W' m) :
+    lo ≤ r + W.val ∧
+      r + W.val < m ∧
+        m < r + W'.val ∧
+          r + W'.val ≤ hi :=
+  ⟨h.left_center_in_window, h.localPacking.left_lt_separator,
+    h.localPacking.separator_lt_right, h.right_center_in_window⟩
+
+/-- The finite window contains at least the three ordered occupied indices. -/
+theorem SourcePressureFiniteWindowPackingSeparatorState.two_le_window_width
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ} {W W' : SourcePressureLocalIslandWitness n k r} {m : ℕ}
+    (h : SourcePressureFiniteWindowPackingSeparatorState L lo hi W W' m) :
+    lo + 2 ≤ hi := by
+  rcases h.window_order_chain with ⟨hlo, hleft, hright, hhi⟩
+  omega
+
 /-- Value-level two-step spacing inherited by the finite-window state. -/
 theorem SourcePressureFiniteWindowPackingSeparatorState.two_le_value_gap
     {n : OddNat} {k r : ℕ}
@@ -2677,4 +2734,92 @@ theorem sourcePressureBeamSeedState_to_finiteWindowPackingSeparatorState_or_pair
     hsorted (sourcePressureBeamSeedState_to_failureResolutionState h)
     hlo_all hhi_all

+/--
+Failure resolution exposes an in-window positive/separator/positive surface or
+a concrete adjacent-pair overlap obstruction.
+
+This is the finite-window surface immediately preceding counting: every
+selected forward pair supplies a nonpositive separator in the same window as
+its two positive centers.
+-/
+theorem sourcePressureFailureResolutionState_to_windowCenterSeparatorSurface_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (h : SourcePressureFailureResolutionState L)
+    (hlo_all : ∀ W, W ∈ L → lo ≤ r + W.val)
+    (hhi_all : ∀ W, W ∈ L → r + W.val ≤ hi) :
+    (∃ W W' m,
+      SourcePressureFiniteWindowPackingSeparatorState L lo hi W W' m ∧
+        lo ≤ r + W.val ∧
+          0 < SourcePressureMarginInt n k (r + W.val) ∧
+            lo ≤ m ∧
+              m ≤ hi ∧
+                SourcePressureMarginInt n k m ≤ 0 ∧
+                  r + W'.val ≤ hi ∧
+                    0 < SourcePressureMarginInt n k (r + W'.val) ∧
+                      W.val + 2 ≤ W'.val) ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B := by
+  rcases
+    sourcePressureFailureResolutionState_to_finiteWindowPackingSeparatorState_or_pairOverlap
+      hsorted h hlo_all hhi_all with hwindow | hoverlap
+  · rcases hwindow with ⟨W, W', m, hpack⟩
+    exact Or.inl ⟨W, W', m, hpack, hpack.window_center_separator_surface⟩
+  · exact Or.inr hoverlap
+
+/-- Sorted failure inherits the finite-window sign surface or overlap split. -/
+theorem sourcePressureSortedFailureState_to_windowCenterSeparatorSurface_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (h : SourcePressureSortedFailureState L)
+    (hlo_all : ∀ W, W ∈ L → lo ≤ r + W.val)
+    (hhi_all : ∀ W, W ∈ L → r + W.val ≤ hi) :
+    (∃ W W' m,
+      SourcePressureFiniteWindowPackingSeparatorState L lo hi W W' m ∧
+        lo ≤ r + W.val ∧
+          0 < SourcePressureMarginInt n k (r + W.val) ∧
+            lo ≤ m ∧
+              m ≤ hi ∧
+                SourcePressureMarginInt n k m ≤ 0 ∧
+                  r + W'.val ≤ hi ∧
+                    0 < SourcePressureMarginInt n k (r + W'.val) ∧
+                      W.val + 2 ≤ W'.val) ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
+  sourcePressureFailureResolutionState_to_windowCenterSeparatorSurface_or_pairOverlap
+    hsorted (sourcePressureSortedFailureState_to_failureResolutionState h)
+    hlo_all hhi_all
+
+/-- Beam seed inherits the finite-window sign surface or overlap split. -/
+theorem sourcePressureBeamSeedState_to_windowCenterSeparatorSurface_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (h : SourcePressureBeamSeedState L)
+    (hlo_all : ∀ W, W ∈ L → lo ≤ r + W.val)
+    (hhi_all : ∀ W, W ∈ L → r + W.val ≤ hi) :
+    (∃ W W' m,
+      SourcePressureFiniteWindowPackingSeparatorState L lo hi W W' m ∧
+        lo ≤ r + W.val ∧
+          0 < SourcePressureMarginInt n k (r + W.val) ∧
+            lo ≤ m ∧
+              m ≤ hi ∧
+                SourcePressureMarginInt n k m ≤ 0 ∧
+                  r + W'.val ≤ hi ∧
+                    0 < SourcePressureMarginInt n k (r + W'.val) ∧
+                      W.val + 2 ≤ W'.val) ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
+  sourcePressureFailureResolutionState_to_windowCenterSeparatorSurface_or_pairOverlap
+    hsorted (sourcePressureBeamSeedState_to_failureResolutionState h)
+    hlo_all hhi_all
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-287.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-287.md
new file mode 100644
index 00000000..bbdb9e72
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-287.md
@@ -0,0 +1,118 @@
+# Report: petal-287
+
+## Goal
+
+Expose the finite-window sign pattern carried by
+`SourcePressureFiniteWindowPackingSeparatorState`, then lift that surface
+through the failure-resolution state ladder.
+
+## Implemented
+
+Added the requested finite-window surface:
+
+- `SourcePressureFiniteWindowPackingSeparatorState.window_center_separator_surface`
+
+It exposes, in one theorem:
+
+```text
+positive left center in the window
+  -> nonpositive separator in the window
+  -> positive right center in the window
+  -> two-step center spacing
+```
+
+Added the three upstream lifted splits:
+
+- `sourcePressureFailureResolutionState_to_windowCenterSeparatorSurface_or_pairOverlap`
+- `sourcePressureSortedFailureState_to_windowCenterSeparatorSurface_or_pairOverlap`
+- `sourcePressureBeamSeedState_to_windowCenterSeparatorSurface_or_pairOverlap`
+
+Each state now reaches either the explicit finite-window sign surface or a
+concrete adjacent-pair overlap obstruction.
+
+## Additional Results
+
+Added two counting-facing consequences:
+
+- `SourcePressureFiniteWindowPackingSeparatorState.window_order_chain`
+- `SourcePressureFiniteWindowPackingSeparatorState.two_le_window_width`
+
+The order-chain theorem fixes the exact index geometry:
+
+```text
+lo <= left center < separator < right center <= hi
+```
+
+Consequently Lean proves:
+
+```lean
+lo + 2 <= hi
+```
+
+Thus any finite window carrying this state contains at least three distinct
+ordered indices and has width at least two.
+
+## Established Facts
+
+For every selected forward pair represented by the finite-window carrier:
+
+1. Both centers have positive pressure margin.
+2. An explicit separator between them has nonpositive pressure margin.
+3. All three indices lie in the same explicit finite window.
+4. The centers are separated by at least two value steps.
+5. The window itself must have width at least two.
+
+These are theorem-level facts checked by Lean.  They are the local packing
+contract needed before finite-family counting begins.
+
+## State Route
+
+```text
+FiniteWindowPackingSeparatorState
+  -> in-window positive / nonpositive / positive surface
+  -> strict in-window order chain
+  -> each selected positive-center pair consumes a separator position
+  -> finite-window positive-center packing input
+  -> local Big
+```
+
+The upstream route is now:
+
+```text
+FailureResolution / SortedFailure / BeamSeed + sorted(L) + window bounds
+  -> window center/separator/center surface
+   | concrete adjacent-pair overlap obstruction
+```
+
+## Counting Boundary
+
+The next genuine counting theorem requires a finite family of selected pairs.
+To turn the local result into a cardinality inequality, the implementation must
+control reuse of separator indices across that family.  The smallest useful
+next invariant is therefore one of:
+
+- injectivity of the chosen separator as a function of an ordered pair;
+- disjointness of the open center intervals of selected pairs; or
+- a bounded-multiplicity theorem for separator reuse.
+
+Once one of these is available, the present order-chain theorem can feed a
+finite cardinality bound directly.
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
+No `sorry` was introduced in the Wall/pressure state work.
+
+## Next Branch Prediction
+
+Introduce a finite selected-pair family and determine the weakest provable
+separator-reuse invariant.  Prefer bounded multiplicity if injectivity is too
+strong; the local theorem already supplies every pair with an in-window
+nonpositive separator.
````
`````
