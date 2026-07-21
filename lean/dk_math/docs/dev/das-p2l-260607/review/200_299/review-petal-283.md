# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 9818076a27441179a89067623b99735574b29a93

## Report

進めました。今回は小さな projection ではなく、FPC corridor から局所 packing obstruction まで一段進めています。

[PressureState.lean](/lean_dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:1565) に FPC 単体の定理を追加しました。

- `SourcePressureForwardPairComparisonState.exists_nonpos_index_between_centers`
- `SourcePressureForwardPairComparisonState.two_le_value_gap`
- `SourcePressureForwardPairComparisonState.two_le_index_gap`

さらに upstream state へ lift しました。

- `sourcePressureFailureResolutionState_to_nonposSeparator_or_pairOverlap`
- `sourcePressureSortedFailureState_to_nonposSeparator_or_pairOverlap`
- `sourcePressureBeamSeedState_to_nonposSeparator_or_pairOverlap`

これで事実として、ForwardPairComparisonState では二つの正 center の間に非正 separator が存在します。具体的には `m = r + W.val + 1` が

```lean
r + W.val < m ∧ m < r + W'.val ∧ SourcePressureMarginInt n k m ≤ 0
```

を満たします。また value/index の両方で 2-step spacing も固定されました。

上流からは、

```text
BeamSeed / SortedFailure / FailureResolution + sorted(L)
  -> nonpositive separator between two positive centers
   ∨ concrete adjacent-pair overlap obstruction
```

まで読めます。これは局所 witness/list 内の現象であり、コラッツ予想や大域終了性とは切り離しています。

[report-petal-283.md](/lean_dk_math/docs/dev/das-p2l-260607/review/report-petal-283.md:1) も追加済みです。

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

## Review

## 判定

採用。
そして、**改善された長距離指示は効いた** と評価してよい。

今回は、前回までのような corridor projection の追加ではなく、ちゃんと次の段に進んでいる。

追加された FPC 単体の定理：

```lean id="jnm6wk"
SourcePressureForwardPairComparisonState.exists_nonpos_index_between_centers
SourcePressureForwardPairComparisonState.two_le_value_gap
SourcePressureForwardPairComparisonState.two_le_index_gap
```

さらに upstream lift：

```lean id="m3x3ou"
sourcePressureFailureResolutionState_to_nonposSeparator_or_pairOverlap
sourcePressureSortedFailureState_to_nonposSeparator_or_pairOverlap
sourcePressureBeamSeedState_to_nonposSeparator_or_pairOverlap
```

これで、`BeamSeed / SortedFailure / FailureResolution + sorted(L)` から、**非正 separator を挟む二つの正中心**、または **pair-overlap obstruction** まで上がった。これは前回の「局所 Core から packing obstruction へ進め」という修正指示に沿っている。

## 改善された指示の進展評価

かなり改善された。

前回まで：

```text id="ws4trq"
FPC corridor
  -> projection
  -> projection
  -> projection
```

今回：

```text id="j1p3l5"
FPC corridor
  -> nonpositive separator exists
  -> two-step spacing
  -> upstream state ladder へ lift
```

つまり、**API 掃除から consumer theorem へ移った**。

特に重要なのはこれ。

```lean id="v1jxbs"
∃ m : ℕ,
  r + W.val < m ∧
    m < r + W'.val ∧
      SourcePressureMarginInt n k m ≤ 0
```

これは、二つの正中心の間に、具体的な非正 separator が存在するという形。
単なる「隣接できない」より強い。

## 数学的意味

今回の成果は、局所 packing obstruction じゃ。

```text id="hoc6lo"
positive center
  ↓
nonpositive separator
  ↓
positive center
```

この形が `FPC` から出る。
さらに上流で、

```text id="qd5xuw"
BeamSeed + sorted(L)
  -> separator branch
   ∨ pair-overlap obstruction
```

まで持ち上がった。

これは **local Big への入口** になっている。
なぜなら、正 center が連続して詰め込めないなら、有限 window 内に置ける正 center の数へ上界を出す方向に進めるからじゃ。

## まだ残る問題

ただし、report 側の言い回しには少しブレーキが残っている。

```text id="si560h"
It does not attempt to prove or discuss the global Collatz conjecture.
```

これは「今回の theorem は大域終了性を主張しない」という意味なら正しい。
しかし Codex に対しては、また **大域方向を考えるな** と読まれる危険がある。

今後はこう書かせるべきじゃ。

```text id="zgjsxi"
This checkpoint does not claim global Collatz termination.
Its role is to build a local packing obstruction that will be used as a stepping stone toward the local Big and later global route.
```

つまり、否定だけで終わらせず、**何へ接続するかを必ず書く**。

## 次の本命

次は `SourcePressureLocalPackingSeparatorState` を作ってよい。
report では「repeated callers が必要なら」と弱く書いているが、ここはもう必要。上流 lift までできたので、separator package を名前付き state にする段階じゃ。

次の構造：

```lean id="d0xzuk"
def SourcePressureLocalPackingSeparatorState
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (W W' : SourcePressureLocalIslandWitness n k r)
    (m : ℕ) : Prop :=
  SourcePressureForwardPairComparisonState L W W' ∧
    r + W.val < m ∧
      m < r + W'.val ∧
        SourcePressureMarginInt n k m ≤ 0
```

そして上流 theorem をこれに置き換える。

```text id="tequzx"
BeamSeed + sorted(L)
  -> ∃ W W' m, SourcePressureLocalPackingSeparatorState L W W' m
   ∨ PairOverlap
```

これで以後、長い existential payload を毎回持たずに済む。

## 次の Codex 指示

今回は単発にしない。
次の山は **packing separator state を定義し、上流 ladder を state 形式へ再公開し、local Big / packing bound へ進む準備を作る** こと。

```text id="hnlx4h"
Goal:
  Continue the Collatz/PetalBridge local Big route.
  Do not stop at one projection theorem.
  Package the newly proved nonpositive separator into a named local packing state,
  then lift the upstream BeamSeed / SortedFailure / FailureResolution routes to
  that state.

Phase A:
  Add a named local packing separator state.

  def SourcePressureLocalPackingSeparatorState
      {n : OddNat} {k r : ℕ}
      (L : List (SourcePressureLocalIslandWitness n k r))
      (W W' : SourcePressureLocalIslandWitness n k r)
      (m : ℕ) : Prop :=
    SourcePressureForwardPairComparisonState L W W' ∧
      r + W.val < m ∧
        m < r + W'.val ∧
          SourcePressureMarginInt n k m ≤ 0

Phase B:
  Add projections:
    - .forward
    - .left_lt_separator
    - .separator_lt_right
    - .separator_nonpos
    - .two_le_value_gap
    - .two_le_index_gap

Phase C:
  Add constructor from FPC:

  theorem SourcePressureForwardPairComparisonState.to_localPackingSeparatorState
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W') :
      ∃ m,
        SourcePressureLocalPackingSeparatorState L W W' m

  Use:
    h.exists_nonpos_index_between_centers

Phase D:
  Re-express the upstream routes using the named state:

  theorem sourcePressureFailureResolutionState_to_localPackingSeparatorState_or_pairOverlap
  theorem sourcePressureSortedFailureState_to_localPackingSeparatorState_or_pairOverlap
  theorem sourcePressureBeamSeedState_to_localPackingSeparatorState_or_pairOverlap

  Shape:
    (∃ W W' m, SourcePressureLocalPackingSeparatorState L W W' m)
      ∨ pair-overlap obstruction

  Use the existing:
    sourcePressureFailureResolutionState_to_nonposSeparator_or_pairOverlap
    sourcePressureSortedFailureState_to_nonposSeparator_or_pairOverlap
    sourcePressureBeamSeedState_to_nonposSeparator_or_pairOverlap

Phase E:
  In the report, explicitly state the route:
    FPC corridor
      -> nonpositive separator
      -> LocalPackingSeparatorState
      -> upstream seed/failure split
      -> first reusable local packing obstruction toward local Big.

  Do not phrase this as avoiding the Collatz proof route.
  Phrase it as:
    "This checkpoint does not claim global termination, but it is explicitly
     designed as a local packing obstruction toward the local Big route."

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## まとめ

今回の `review-petal-283` は、前回の反省が反映されている。
**単発 projection から、局所 packing obstruction へ進んだ。**

次は名前付き state 化して、上流 theorem をすべてその state に接続する。
そこまで行けば、次の段で「有限 window 内の positive center packing bound」へ入れる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index a4946a78..d8306154 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -1554,6 +1554,58 @@ theorem SourcePressureForwardPairComparisonState.strict_gap_value_corridor_surfa
     omega
   exact ⟨hnextL, hprevR, hvalue⟩

+/--
+There is a nonpositive separator strictly between the two positive centers.
+
+The separator is the left next boundary `r + W.val + 1`.  This is the first
+packing-facing consequence of the forward pair-comparison state: two positive
+centers are not consecutive at the index level, because a nonpositive boundary
+lies strictly between them.
+-/
+theorem SourcePressureForwardPairComparisonState.exists_nonpos_index_between_centers
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    ∃ m : ℕ,
+      r + W.val < m ∧
+        m < r + W'.val ∧
+          SourcePressureMarginInt n k m ≤ 0 := by
+  rcases h.left_next_boundary_nonpos_and_before_right_center with ⟨hnext, hlt⟩
+  refine ⟨r + W.val + 1, ?_, hlt, hnext⟩
+  omega
+
+/--
+Value-level two-step spacing between the two positive centers.
+
+This is a compact consumer form of `right_value_corridor_surface`: the right
+witness value is at least two steps after the left witness value.
+-/
+theorem SourcePressureForwardPairComparisonState.two_le_value_gap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    W.val + 2 ≤ W'.val := by
+  rcases h.right_value_corridor_surface with ⟨_, _, heq | hlt⟩
+  · omega
+  · omega
+
+/--
+Index-level two-step spacing between the two positive centers.
+
+The common offset `r` preserves the value-level spacing, making the separation
+usable by index-based local Big / packing arguments.
+-/
+theorem SourcePressureForwardPairComparisonState.two_le_index_gap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    r + W.val + 2 ≤ r + W'.val := by
+  have hgap : W.val + 2 ≤ W'.val := h.two_le_value_gap
+  omega
+
 /--
 Constructor from the forward box comparison state to the pair-comparison-facing
 state.
@@ -2091,4 +2143,83 @@ theorem sourcePressureBeamSeedState_to_forwardPairComparisonState_or_pairOverlap
   sourcePressureFailureResolutionState_to_forwardPairComparisonState_or_pairOverlap
     hsorted (sourcePressureBeamSeedState_to_failureResolutionState h)

+/--
+Failure resolution produces either a local nonpositive separator between two
+positive centers, or a concrete adjacent-pair overlap obstruction.
+
+This theorem is the first packing-facing lift from the state ladder.  The
+forward branch no longer exposes only an FPC witness; it also packages the
+separator index that lies strictly between the two centers.
+-/
+theorem sourcePressureFailureResolutionState_to_nonposSeparator_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (h : SourcePressureFailureResolutionState L) :
+    (∃ W W' m,
+      SourcePressureForwardPairComparisonState L W W' ∧
+        r + W.val < m ∧
+          m < r + W'.val ∧
+            SourcePressureMarginInt n k m ≤ 0) ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B := by
+  rcases sourcePressureFailureResolutionState_to_forwardPairComparisonState_or_pairOverlap
+      hsorted h with hforward | hoverlap
+  · rcases hforward with ⟨W, W', hFPC⟩
+    rcases hFPC.exists_nonpos_index_between_centers with
+      ⟨m, hleft, hright, hnonpos⟩
+    exact Or.inl ⟨W, W', m, hFPC, hleft, hright, hnonpos⟩
+  · exact Or.inr hoverlap
+
+/--
+Sorted failure produces either a local nonpositive separator between two
+positive centers, or a concrete adjacent-pair overlap obstruction.
+-/
+theorem sourcePressureSortedFailureState_to_nonposSeparator_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (h : SourcePressureSortedFailureState L) :
+    (∃ W W' m,
+      SourcePressureForwardPairComparisonState L W W' ∧
+        r + W.val < m ∧
+          m < r + W'.val ∧
+            SourcePressureMarginInt n k m ≤ 0) ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
+  sourcePressureFailureResolutionState_to_nonposSeparator_or_pairOverlap
+    hsorted (sourcePressureSortedFailureState_to_failureResolutionState h)
+
+/--
+Beam seed produces either a local nonpositive separator between two positive
+centers, or a concrete adjacent-pair overlap obstruction.
+
+This is the Beam-facing packing obstruction surface:
+
+```text
+BeamSeed + sorted(L)
+  -> positive centers with a nonpositive separator
+   ∨ pair-overlap obstruction
+```
+
+The statement is intentionally local to the explicit witness list `L`.
+-/
+theorem sourcePressureBeamSeedState_to_nonposSeparator_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (h : SourcePressureBeamSeedState L) :
+    (∃ W W' m,
+      SourcePressureForwardPairComparisonState L W W' ∧
+        r + W.val < m ∧
+          m < r + W'.val ∧
+            SourcePressureMarginInt n k m ≤ 0) ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
+  sourcePressureFailureResolutionState_to_nonposSeparator_or_pairOverlap
+    hsorted (sourcePressureBeamSeedState_to_failureResolutionState h)
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-283.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-283.md
new file mode 100644
index 00000000..83394edc
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-283.md
@@ -0,0 +1,119 @@
+# Report: petal-283
+
+## Goal
+
+Move beyond corridor API cleanup and use the existing FPC corridor surfaces to
+build a local positive-pulse packing obstruction.
+
+The work deliberately treats this as a local phenomenon.  It does not attempt
+to prove or discuss the global Collatz conjecture.
+
+## Implemented
+
+Added FPC-level consumer theorems:
+
+- `SourcePressureForwardPairComparisonState.exists_nonpos_index_between_centers`
+- `SourcePressureForwardPairComparisonState.two_le_value_gap`
+- `SourcePressureForwardPairComparisonState.two_le_index_gap`
+
+Added upstream lifted split theorems:
+
+- `sourcePressureFailureResolutionState_to_nonposSeparator_or_pairOverlap`
+- `sourcePressureSortedFailureState_to_nonposSeparator_or_pairOverlap`
+- `sourcePressureBeamSeedState_to_nonposSeparator_or_pairOverlap`
+
+## Established Facts
+
+For any
+`h : SourcePressureForwardPairComparisonState L W W'`, Lean now proves that
+there exists an index `m` strictly between the two positive center indices:
+
+```lean
+∃ m : ℕ,
+  r + W.val < m ∧
+    m < r + W'.val ∧
+      SourcePressureMarginInt n k m <= 0
+```
+
+The witness is the left next boundary:
+
+```lean
+m = r + W.val + 1
+```
+
+Lean also proves the compact spacing facts:
+
+```lean
+W.val + 2 <= W'.val
+r + W.val + 2 <= r + W'.val
+```
+
+## Upstream Route
+
+The state ladder now exposes the local packing obstruction directly:
+
+```text
+FailureResolution + sorted(L)
+  -> nonpositive separator between two positive centers
+   ∨ concrete adjacent-pair overlap obstruction
+
+SortedFailure + sorted(L)
+  -> nonpositive separator between two positive centers
+   ∨ concrete adjacent-pair overlap obstruction
+
+BeamSeed + sorted(L)
+  -> nonpositive separator between two positive centers
+   ∨ concrete adjacent-pair overlap obstruction
+```
+
+This is the first local Big / packing-bound style surface in the current
+PressureState branch: forward positive centers cannot be packed consecutively
+without a nonpositive separator between them.
+
+## What Can Be Concluded
+
+Within a sorted explicit witness list, the BeamSeed/FailureResolution route has
+two possible local outcomes:
+
+1. the forward pair branch yields two positive centers with a certified
+   nonpositive separator strictly between them;
+2. the obstruction branch yields a concrete adjacent-pair overlap obstruction.
+
+This is a local structural fact about explicit witnesses and margins.
+
+## Guardrails
+
+This checkpoint does not prove:
+
+- global positive-center uniqueness;
+- arbitrary window disjointness;
+- all interior corridor indices are nonpositive;
+- global coverage of all possible centers;
+- any global Collatz termination statement.
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
+The next natural local phenomenon to isolate is a named packing state:
+
+```text
+SourcePressureLocalPackingSeparatorState L W W' m
+```
+
+This should be added only if repeated callers need to carry the separator
+package.  Otherwise, the current upstream split theorems are already a usable
+surface for local packing-bound experiments.
````
`````
