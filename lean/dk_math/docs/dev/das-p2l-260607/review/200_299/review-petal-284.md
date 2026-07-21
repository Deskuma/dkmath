# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 69beb2fb17563ff6352df9104bcfa8d6a227d5f2

## Report

実装完了です。今回は、局所現象としての「正中心の packing は非正 separator を要求する」を名前付き状態へ押し上げました。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:953) に `SourcePressureLocalPackingSeparatorState` を追加しました。これは

```lean
SourcePressureForwardPairComparisonState L W W'
∧ r + W.val < m
∧ m < r + W'.val
∧ SourcePressureMarginInt n k m ≤ 0
```

を保持する local packing obstruction carrier です。

あわせて projection と constructor を追加しました。

- `SourcePressureLocalPackingSeparatorState.forward`
- `SourcePressureLocalPackingSeparatorState.left_lt_separator`
- `SourcePressureLocalPackingSeparatorState.separator_lt_right`
- `SourcePressureLocalPackingSeparatorState.separator_nonpos`
- `SourcePressureLocalPackingSeparatorState.two_le_value_gap`
- `SourcePressureLocalPackingSeparatorState.two_le_index_gap`
- `SourcePressureForwardPairComparisonState.to_localPackingSeparatorState`

上流 split も名前付き state へ lift 済みです。

- `sourcePressureFailureResolutionState_to_localPackingSeparatorState_or_pairOverlap`
- `sourcePressureSortedFailureState_to_localPackingSeparatorState_or_pairOverlap`
- `sourcePressureBeamSeedState_to_localPackingSeparatorState_or_pairOverlap`

これで観測された事実は次の形になりました。

```text
FPC corridor
  -> nonpositive separator
  -> LocalPackingSeparatorState
  -> BeamSeed / SortedFailure / FailureResolution split
  -> reusable local packing obstruction toward local Big
```

[report-petal-284.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-284.md:1) も追加済みです。

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

この checkpoint は大域終了性を主張しません。ただし、局所 witness list 上で「二つの正中心の間には非正 separator が存在せざるを得ない」という再利用可能な obstruction を Lean 定理として固定しました。

## Review

## 判定

採用。
今回は前回の `nonposSeparator` を、きちんと **名前付き状態** へ押し上げている。

追加された中心定義：

```lean id="rwz7xy"
SourcePressureLocalPackingSeparatorState
```

これは次を保持する local packing obstruction carrier じゃ。

```lean id="ztj3v2"
SourcePressureForwardPairComparisonState L W W' ∧
  r + W.val < m ∧
    m < r + W'.val ∧
      SourcePressureMarginInt n k m ≤ 0
```

さらに projection、FPC からの constructor、上流 split まで実装されている。`BeamSeed / SortedFailure / FailureResolution` から `LocalPackingSeparatorState ∨ PairOverlapObstruction` へ届くようになったのは大きい。

## 実装レビュー

かなり良い進展。

前回までの構造は、

```text id="bq0g8f"
FPC
  -> ∃ m, nonpositive separator
```

だった。
今回で、

```text id="xm0g1y"
FPC
  -> LocalPackingSeparatorState

BeamSeed / SortedFailure / FailureResolution
  -> LocalPackingSeparatorState ∨ PairOverlap
```

になった。

これは「一回限りの存在定理」ではなく、後段が持ち運べる state になっている。
特に、次の projection が揃っているのがよい。

```lean id="zjrsfg"
SourcePressureLocalPackingSeparatorState.forward
SourcePressureLocalPackingSeparatorState.left_lt_separator
SourcePressureLocalPackingSeparatorState.separator_lt_right
SourcePressureLocalPackingSeparatorState.separator_nonpos
SourcePressureLocalPackingSeparatorState.two_le_value_gap
SourcePressureLocalPackingSeparatorState.two_le_index_gap
```

局所 packing obstruction として再利用可能になった。

## 改善された指示の進展評価

前回の指示修正は効いている。

以前の流れ：

```text id="aowhji"
corridor projection
  -> corridor projection
  -> corridor projection
```

今回の流れ：

```text id="z9jnhn"
separator theorem
  -> named local packing state
  -> upstream ladder lift
  -> reusable local Big / packing-bound carrier
```

これは、明らかに **小補題小出し** から **構造化** へ進んでいる。

report の文章も改善されている。特に、

```text id="wmvwep"
This checkpoint turns the previous raw separator theorem into a reusable local
packing obstruction.
```

と書けているのはよい。単なる安全宣言ではなく、「何へ進むための部品か」を説明できている。

ただし、まだ少しだけ弱い。
次からは「toward local Big」だけでなく、もう一歩具体的に、

```text id="jdot7n"
finite-window packing bound
```

まで report / Codex 指示に入れるとよい。

## 数学的意味

今回の定義により、観測された局所現象はこう定式化された。

```text id="h4j697"
left positive center
  ↓
nonpositive separator
  ↓
right positive center
```

つまり、二つの正中心は、単に離れているだけではない。
その間に **非正 separator** が存在する。

これは、正中心が無制限に詰め込まれることを妨げる局所構造じゃ。
したがって次の目標は自然に、

```text id="lqv8xo"
有限 window 内で positive centers が最大いくつ置けるか
```

へ向かう。

## 現在の到達点

```text id="rcu0df"
FPC corridor
  -> nonpositive separator
  -> LocalPackingSeparatorState
  -> upstream seed/failure split
  -> reusable local packing obstruction
```

ここまでで、局所 Core はかなり形になった。
次は、この state を使って **center surface** と **finite-window packing bound** へ進む段階じゃ。

## 次に攻める定理

まずは `LocalPackingSeparatorState` から、正中心・非正 separator・正中心を一発で読む surface を作るのがよい。

```lean id="cwa2f2"
theorem SourcePressureLocalPackingSeparatorState.center_separator_surface
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    {m : ℕ}
    (h : SourcePressureLocalPackingSeparatorState L W W' m) :
    0 < SourcePressureMarginInt n k (r + W.val) ∧
      SourcePressureMarginInt n k m ≤ 0 ∧
        0 < SourcePressureMarginInt n k (r + W'.val) ∧
          r + W.val < m ∧
            m < r + W'.val ∧
              W.val + 2 ≤ W'.val
```

これは `h.forward.center_pair_surface`、`h.separator_nonpos`、`h.left_lt_separator`、`h.separator_lt_right`、`h.two_le_value_gap` で閉じるはず。

その次に、上流からこの surface まで持ち上げる。

```text id="veymux"
BeamSeed + sorted(L)
  -> center-separator surface
   ∨ PairOverlap
```

ここまで行くと、次の有限 window packing bound の caller がかなり書きやすい。

## Codex 指示

```text id="g69b5i"
Goal:
  Continue from the named local packing separator state toward a finite-window
  packing bound.  Do not stop at packaging only.  Build the first surface that
  exposes the actual local pattern:

    positive center
      -> nonpositive separator
      -> positive center

Phase A:
  Add a compact surface theorem from SourcePressureLocalPackingSeparatorState.

  theorem SourcePressureLocalPackingSeparatorState.center_separator_surface
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      {m : ℕ}
      (h : SourcePressureLocalPackingSeparatorState L W W' m) :
      0 < SourcePressureMarginInt n k (r + W.val) ∧
        SourcePressureMarginInt n k m ≤ 0 ∧
          0 < SourcePressureMarginInt n k (r + W'.val) ∧
            r + W.val < m ∧
              m < r + W'.val ∧
                W.val + 2 ≤ W'.val

  Use:
    h.forward.center_pair_surface
    h.separator_nonpos
    h.left_lt_separator
    h.separator_lt_right
    h.two_le_value_gap

Phase B:
  Add upstream lifted versions if they close cheaply:

    sourcePressureFailureResolutionState_to_centerSeparatorSurface_or_pairOverlap
    sourcePressureSortedFailureState_to_centerSeparatorSurface_or_pairOverlap
    sourcePressureBeamSeedState_to_centerSeparatorSurface_or_pairOverlap

  Shape:
    (∃ W W' m,
      SourcePressureLocalPackingSeparatorState L W W' m ∧
        0 < SourcePressureMarginInt n k (r + W.val) ∧
          SourcePressureMarginInt n k m ≤ 0 ∧
            0 < SourcePressureMarginInt n k (r + W'.val) ∧
              r + W.val < m ∧
                m < r + W'.val ∧
                  W.val + 2 ≤ W'.val)
      ∨ PairOverlapObstruction

  Prefer reusing:
    sourcePressureFailureResolutionState_to_localPackingSeparatorState_or_pairOverlap
    sourcePressureSortedFailureState_to_localPackingSeparatorState_or_pairOverlap
    sourcePressureBeamSeedState_to_localPackingSeparatorState_or_pairOverlap

Phase C:
  In the report, describe this as the next step toward finite-window packing:

    LocalPackingSeparatorState
      -> center/separator/center surface
      -> positive centers require a certified nonpositive separator
      -> this prepares finite-window packing bounds and local Big.

  Avoid making this merely an API cleanup report.  The point is the route:
    observed local structure
      -> reusable local theorem
      -> finite-window packing bound
      -> local Big.

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

次は明確にここ。

```text id="qojqg4"
LocalPackingSeparatorState
  -> center-separator-center surface
  -> finite-window positive-center packing bound
```

ここまで来れば、「正中心が詰め込めない」という直感が、有限 window の上界定理へ変わり始める。
その上界が local Big の入口になる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index d8306154..6dc8096e 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -941,6 +941,25 @@ def SourcePressureForwardPairComparisonState
       SourcePressureBeamCenteredLocalPulseBox n k r L W ∧
         SourcePressureBeamCenteredLocalPulseBox n k r L W'

+/--
+Named local packing separator state.
+
+This packages the first local packing obstruction obtained from a forward pair:
+two positive centers are separated by an explicit nonpositive margin index.
+The state is local to the explicit witness list `L`; it is a reusable carrier
+for local Big / packing-bound arguments and does not make a global coverage
+claim.
+-/
+def SourcePressureLocalPackingSeparatorState
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (W W' : SourcePressureLocalIslandWitness n k r)
+    (m : ℕ) : Prop :=
+  SourcePressureForwardPairComparisonState L W W' ∧
+    r + W.val < m ∧
+      m < r + W'.val ∧
+        SourcePressureMarginInt n k m ≤ 0
+
 /-- Project the underlying forward box comparison state. -/
 theorem SourcePressureForwardPairComparisonState.forward
     {n : OddNat} {k r : ℕ}
@@ -1606,6 +1625,78 @@ theorem SourcePressureForwardPairComparisonState.two_le_index_gap
   have hgap : W.val + 2 ≤ W'.val := h.two_le_value_gap
   omega

+/-- Project the forward pair-comparison state from a local packing separator. -/
+theorem SourcePressureLocalPackingSeparatorState.forward
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r} {m : ℕ}
+    (h : SourcePressureLocalPackingSeparatorState L W W' m) :
+    SourcePressureForwardPairComparisonState L W W' :=
+  h.1
+
+/-- The left center index is strictly before the separator. -/
+theorem SourcePressureLocalPackingSeparatorState.left_lt_separator
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r} {m : ℕ}
+    (h : SourcePressureLocalPackingSeparatorState L W W' m) :
+    r + W.val < m :=
+  h.2.1
+
+/-- The separator is strictly before the right center index. -/
+theorem SourcePressureLocalPackingSeparatorState.separator_lt_right
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r} {m : ℕ}
+    (h : SourcePressureLocalPackingSeparatorState L W W' m) :
+    m < r + W'.val :=
+  h.2.2.1
+
+/-- The separator margin is nonpositive. -/
+theorem SourcePressureLocalPackingSeparatorState.separator_nonpos
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r} {m : ℕ}
+    (h : SourcePressureLocalPackingSeparatorState L W W' m) :
+    SourcePressureMarginInt n k m ≤ 0 :=
+  h.2.2.2
+
+/-- Value-level two-step spacing inherited from the forward pair state. -/
+theorem SourcePressureLocalPackingSeparatorState.two_le_value_gap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r} {m : ℕ}
+    (h : SourcePressureLocalPackingSeparatorState L W W' m) :
+    W.val + 2 ≤ W'.val :=
+  h.forward.two_le_value_gap
+
+/-- Index-level two-step spacing inherited from the forward pair state. -/
+theorem SourcePressureLocalPackingSeparatorState.two_le_index_gap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r} {m : ℕ}
+    (h : SourcePressureLocalPackingSeparatorState L W W' m) :
+    r + W.val + 2 ≤ r + W'.val :=
+  h.forward.two_le_index_gap
+
+/--
+Constructor from a forward pair-comparison state to the named local packing
+separator state.
+
+The chosen separator is supplied by
+`exists_nonpos_index_between_centers`, currently the left next boundary.
+-/
+theorem SourcePressureForwardPairComparisonState.to_localPackingSeparatorState
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    ∃ m,
+      SourcePressureLocalPackingSeparatorState L W W' m := by
+  rcases h.exists_nonpos_index_between_centers with
+    ⟨m, hleft, hright, hnonpos⟩
+  exact ⟨m, h, hleft, hright, hnonpos⟩
+
 /--
 Constructor from the forward box comparison state to the pair-comparison-facing
 state.
@@ -2222,4 +2313,69 @@ theorem sourcePressureBeamSeedState_to_nonposSeparator_or_pairOverlap
   sourcePressureFailureResolutionState_to_nonposSeparator_or_pairOverlap
     hsorted (sourcePressureBeamSeedState_to_failureResolutionState h)

+/--
+Failure resolution reaches the named local packing separator state or a
+concrete adjacent-pair overlap obstruction.
+
+This is the named-state form of
+`sourcePressureFailureResolutionState_to_nonposSeparator_or_pairOverlap`.
+-/
+theorem sourcePressureFailureResolutionState_to_localPackingSeparatorState_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (h : SourcePressureFailureResolutionState L) :
+    (∃ W W' m,
+      SourcePressureLocalPackingSeparatorState L W W' m) ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B := by
+  rcases sourcePressureFailureResolutionState_to_nonposSeparator_or_pairOverlap
+      hsorted h with hsep | hoverlap
+  · rcases hsep with ⟨W, W', m, hFPC, hleft, hright, hnonpos⟩
+    exact Or.inl ⟨W, W', m, hFPC, hleft, hright, hnonpos⟩
+  · exact Or.inr hoverlap
+
+/--
+Sorted failure reaches the named local packing separator state or a concrete
+adjacent-pair overlap obstruction.
+-/
+theorem sourcePressureSortedFailureState_to_localPackingSeparatorState_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (h : SourcePressureSortedFailureState L) :
+    (∃ W W' m,
+      SourcePressureLocalPackingSeparatorState L W W' m) ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
+  sourcePressureFailureResolutionState_to_localPackingSeparatorState_or_pairOverlap
+    hsorted (sourcePressureSortedFailureState_to_failureResolutionState h)
+
+/--
+Beam seed reaches the named local packing separator state or a concrete
+adjacent-pair overlap obstruction.
+
+This is the Beam-facing named local-packing split:
+
+```text
+BeamSeed + sorted(L)
+  -> LocalPackingSeparatorState
+   ∨ PairOverlapObstruction
+```
+-/
+theorem sourcePressureBeamSeedState_to_localPackingSeparatorState_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (h : SourcePressureBeamSeedState L) :
+    (∃ W W' m,
+      SourcePressureLocalPackingSeparatorState L W W' m) ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
+  sourcePressureFailureResolutionState_to_localPackingSeparatorState_or_pairOverlap
+    hsorted (sourcePressureBeamSeedState_to_failureResolutionState h)
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-284.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-284.md
new file mode 100644
index 00000000..e082b782
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-284.md
@@ -0,0 +1,133 @@
+# Report: petal-284
+
+## Goal
+
+Package the local nonpositive separator into a named local packing state and
+lift the upstream BeamSeed / SortedFailure / FailureResolution routes to that
+state.
+
+The focus is the observed local phenomenon itself: positive centers carried by
+the forward pair state cannot be packed without a certified nonpositive
+separator between them.
+
+## Implemented
+
+Added the named state:
+
+- `SourcePressureLocalPackingSeparatorState`
+
+Added projections:
+
+- `SourcePressureLocalPackingSeparatorState.forward`
+- `SourcePressureLocalPackingSeparatorState.left_lt_separator`
+- `SourcePressureLocalPackingSeparatorState.separator_lt_right`
+- `SourcePressureLocalPackingSeparatorState.separator_nonpos`
+- `SourcePressureLocalPackingSeparatorState.two_le_value_gap`
+- `SourcePressureLocalPackingSeparatorState.two_le_index_gap`
+
+Added constructor:
+
+- `SourcePressureForwardPairComparisonState.to_localPackingSeparatorState`
+
+Added upstream named-state split theorems:
+
+- `sourcePressureFailureResolutionState_to_localPackingSeparatorState_or_pairOverlap`
+- `sourcePressureSortedFailureState_to_localPackingSeparatorState_or_pairOverlap`
+- `sourcePressureBeamSeedState_to_localPackingSeparatorState_or_pairOverlap`
+
+## Established Facts
+
+The named state records:
+
+```lean
+SourcePressureForwardPairComparisonState L W W'
+  ∧ r + W.val < m
+  ∧ m < r + W'.val
+  ∧ SourcePressureMarginInt n k m <= 0
+```
+
+From this state, Lean can project both local spacing facts:
+
+```lean
+W.val + 2 <= W'.val
+r + W.val + 2 <= r + W'.val
+```
+
+Every `SourcePressureForwardPairComparisonState L W W'` produces such a named
+separator state:
+
+```lean
+∃ m, SourcePressureLocalPackingSeparatorState L W W' m
+```
+
+## Upstream Route
+
+The state ladder now reaches the named local packing state:
+
+```text
+FailureResolution + sorted(L)
+  -> LocalPackingSeparatorState
+   ∨ concrete adjacent-pair overlap obstruction
+
+SortedFailure + sorted(L)
+  -> LocalPackingSeparatorState
+   ∨ concrete adjacent-pair overlap obstruction
+
+BeamSeed + sorted(L)
+  -> LocalPackingSeparatorState
+   ∨ concrete adjacent-pair overlap obstruction
+```
+
+## What Can Be Concluded
+
+This checkpoint turns the previous raw separator theorem into a reusable local
+packing obstruction.
+
+The observed structure is now:
+
+```text
+FPC corridor
+  -> nonpositive separator
+  -> LocalPackingSeparatorState
+  -> upstream seed/failure split
+  -> reusable local packing obstruction toward local Big
+```
+
+This is a local theorem about explicit witness lists and margin signs.  It does
+not need to refer to any external named conjecture.
+
+## Guardrails
+
+This checkpoint does not claim global termination.  It also does not claim:
+
+- global positive-center uniqueness;
+- arbitrary window disjointness;
+- global coverage of all possible centers;
+- nonpositivity of every interior point of a strict corridor.
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
+The next reusable layer is likely one of:
+
+- a compact `LocalPackingSeparatorState.center_surface` projection containing
+  left positive center, nonpositive separator, right positive center;
+- a finite-list aggregation step that counts or indexes repeated local packing
+  separators without claiming global coverage.
+
+The first is cheaper and should be preferred unless a real aggregation caller is
+ready.
````
`````
