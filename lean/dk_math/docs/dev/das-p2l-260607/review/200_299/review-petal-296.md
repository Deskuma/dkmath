# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking

gch: f5cad67a6575916d59ca9b0e61e5c1a26677a59e

## Report

cp-296 を実装しました。

今回、pair payload の意味をさらに縮約しました。

```text
OrientedNeighborBoxState
  ↔ OrientedNeighborDiagnosticState
  ↔ AdjacentDiagnosis
```

さらに sortedness、ordered adjacency、window bounds の下で、

```text
CanonicalFiniteWindowPackingState
  ↔ OrientedNeighborBoxState
  ↔ AdjacentDiagnosis
```

が成立します。

その結果、unresolved internal pair は正確に、

```text
internal adjacent pair
かつ
AdjacentDiagnosis が存在しない pair
```

として特徴付けられました。

`sourcePressureUndiagnosedInternalPairFamily` という意味的 alias も追加し、local-Big を診断語彙で再公開しています。

現在の残課題は、任意の internal adjacent pair に対して

```text
AdjacentDiagnosis
```

を構成する per-pair producer です。既存の BeamSeed / FailureResolution は existential な選択 pair については証明しますが、全 internal pair を一様には覆いません。

結果は [report-petal-296.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-296.md) に記録しました。

確認済み:

- `lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking`
- `lake build DkMath.Collatz.PetalBridge.PressureState`
- `lake build DkMath.Collatz.PetalBridge`
- `git diff --check`
- 新規 `sorry` / `axiom` なし

## Review

## 判定

**条件付き採用。実装自体は正しいが、ここで本線を停止して非空性監査が必要じゃ。**

cp-296 は state の意味を正確に縮約した。

```text
OrientedNeighborBoxState
  ↔ OrientedNeighborDiagnosticState
  ↔ AdjacentDiagnosis
```

さらに sortedness、adjacency、window bounds の下で、

```text
CanonicalFiniteWindowPackingState
  ↔ AdjacentDiagnosis
```

まで Lean で固定された。ビルド、集約 import、`git diff --check`、no-sorry も問題ない。

しかし、この縮約によって **重大な極性の不一致**が露出した。

## 発見された構造的不整合

`AdjacentDiagnosis` は、もともと **sorted-before failure を解決するための carrier** じゃ。

その recovered branch は、pair `W,W'` に対して逆向きの順序、

```text
SourcePressureLocalIslandWitnessBefore W' W
```

を保持する。実際、既存 recovered state から diagnosis を作る際にも、この reverse-before witness を使っている。

一方、有限窓 packing 側では、

```text
SourcePressureLocalIslandWitnessListSortedBefore L
SourcePressureLocalIslandWitnessAdjacentPairInList L W W'
```

から、正方向の順序、

```text
SourcePressureLocalIslandWitnessBefore W W'
```

が得られる。

つまり recovered branch では、

```text
W before W'
W' before W
```

を同時に要求する。

各 interval-pulse address の長さは正なので、これは成立しない。

もう一方の overlap branch も、もともと sorted-before failure の解決分岐として導入されたものじゃ。既存 automaton は明確に、

```text
sorted-before failure
  -> recovered adjacent pair
     or adjacent overlap obstruction
```

という向きで設計されている。

したがって、sorted list 上の adjacent pair では、こちらも成立しないはずじゃ。

Lean で次が閉じる可能性が非常に高い。

$$
\text{SortedAdjacent}(L,W,W')\Longrightarrow\neg\text{AdjacentDiagnosis}(L,W,W')
$$

## cp-296 の意味が反転する

cp-296 は、

```lean
SourcePressureCanonicalFiniteWindowPackingState L lo hi W W'
  ↔ SourcePressureLocalIslandWitnessAdjacentDiagnosis L W W'
```

を証明した。

したがって、上の非両立性が Lean で確定すると、

$$
\text{SortedAdjacent}(L,W,W')\Longrightarrow\neg\text{CanonicalFiniteWindowPackingState}(L,W,W')
$$

になる。

すると sortedness の下では、

```text
canonical packing pair family = empty
```

になる。

さらに、

```text
undiagnosed internal pair family = all internal adjacent pairs
```

となる可能性が高い。

この場合、cp-290 以降の packing theorem は論理的には正しい。しかし canonical family が空なので、**非空な packing 現象を数えていない**。

たとえば、

```text
canonicalPairFamily.card ≤ half-window capacity
```

は、左辺が常に `0` なら当然成立する。

つまり、

- 証明が誤っているわけではない
- counting lemma も正しい
- しかし carrier の選択が failure 側に寄りすぎた
- sorted packing への適用が空虚になっている

という状況じゃ。

## これはどこで混線したか

本来、二つの層は分けるべきだった。

```text
Failure diagnosis layer:
  sorted-before が壊れたとき
  reverse-before recovered または overlap obstruction

Sorted packing layer:
  sorted adjacent local-island witnesses
  中心間の非正 separator
  two-spacing
  finite-window density
```

ところが `OrientedNeighborBoxState` が `AdjacentDiagnosis` を内部に含んでいたため、failure diagnosis が sorted packing carrier に混入した。

これは、わっちの前段の指示でも見落としていた設計ミスじゃ。
cp-296 が意味を最後まで縮約したことで、ようやくはっきり見えた。

## 正しい packing の Core

実は packing に `AdjacentDiagnosis` は不要じゃ。

各 `SourcePressureLocalIslandWitness` 自体が、中心付近の符号構造を持つ。

概念的には、

```text
margin(center) > 0
margin(center + 1) ≤ 0
```

である。

sorted adjacent pair `W,W'` について、もし、

```text
W'.val = W.val + 1
```

なら、

```text
W の next margin ≤ 0
W' の center margin > 0
```

が同じ位置で衝突する。

したがって、

$$
W.val+2\le W'.val
$$

が直接出るはずじゃ。

つまり sorted local-island witness の中心値そのものが、既に two-separated である。

これなら positive witness を直接数えられる。

$$
\text{positiveWitnesses.card}\le\frac{hi-lo}{2}+1
$$

これは現在の `+2` より一つ鋭い。

## 非正位置との対応

各 positive witness `W` に対して、

```text
r + W.val + 1
```

は非正位置になる。

最後の in-window witness を除けば、この separator は同じ窓内にある。

したがって、

```text
全 positive witness
  -> 非正 separator
     + 最大一点の右境界
```

という injection が作れる。

これにより、診断 coverage を仮定せず無条件で、

$$
\text{positiveWitnesses.card}\le\text{nonposPositions.card}+1
$$

が狙える。

つまり本来欲しかった local Big は、

$$
\text{positiveWitnesses.card}\le\frac{hi-lo}{2}+1
$$

$$
\text{positiveWitnesses.card}\le\text{nonposPositions.card}+1
$$

として、`AdjacentDiagnosis` なしで閉じられる可能性が高い。

## cp-296 の扱い

cp-296 の theorem 群は削除しなくてよい。

むしろ、

```text
failure-oriented canonical state
```

が sorted packing には使えないことを証明する audit API として残せる。

ただし、次の report 記述、

```text
internal adjacent pair -> AdjacentDiagnosis
```

を「残る producer」とする解釈は撤回すべきじゃ。

この producer は不足しているのではなく、**sortedness と両立しないため構成不能**である可能性が高い。

## 次の Codex 指示

````text
Goal:
  Stop the attempted universal AdjacentDiagnosis producer.

  cp-296 has exposed a likely polarity mismatch:

    AdjacentDiagnosis is a failure-resolution carrier,
    while FiniteWindowPacking assumes a sorted witness list.

  First prove or refute this incompatibility in Lean.  If it closes as expected,
  audit the existing canonical packing family for vacuity and rebuild the
  packing layer on diagnosis-free sorted local-island data.

Phase A — prove sortedness excludes AdjacentDiagnosis:

Prove:

```lean
theorem sourcePressureAdjacentDiagnosis_not_of_sorted_adjacent
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
    (hpair :
      SourcePressureLocalIslandWitnessAdjacentPairInList L W W') :
    ¬ SourcePressureLocalIslandWitnessAdjacentDiagnosis L W W'
```

Split the diagnosis.

Recovered branch:
- obtain `SourcePressureLocalIslandWitnessBefore W' W`;
- obtain `SourcePressureLocalIslandWitnessBefore W W'` from
  `sourcePressureAdjacentPairInList_before_of_sorted hsorted hpair`;
- unfold the address-level `Before` relations;
- use positive address lengths and `omega` to contradict the two directions.

Overlap branch:
- use
  `SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
    .hasSortedBeforeFailure`;
- prove the reusable incompatibility theorem:

```lean
theorem sourcePressureSortedBefore_not_failure
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
    ¬ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L
```

This should be a direct structural induction over the adjacent list
predicates.

Phase B — audit canonical packing vacuity:

Using cp-296, prove:

```lean
theorem sourcePressureCanonicalFiniteWindowPackingState_false_of_sorted
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
    (hpair :
      SourcePressureLocalIslandWitnessAdjacentPairInList L W W')
    (hlo : lo ≤ r + W.val)
    (hhi : r + W'.val ≤ hi) :
    ¬ SourcePressureCanonicalFiniteWindowPackingState L lo hi W W'
```

Then prove:

```lean
theorem sourcePressureCanonicalPackingPairFamily_eq_empty_of_sorted
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
    sourcePressureCanonicalPackingPairFamily L lo hi = ∅
```

Also characterize the current semantic alias under sortedness:

```text
sourcePressureUndiagnosedInternalPairFamily
  = every internal adjacent pair in the window
```

Do not continue the old coverage route if these theorems close.

Phase C — introduce a diagnosis-free sorted pair carrier:

Define:

```lean
def SourcePressureSortedAdjacentPulsePairState
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (W W' : SourcePressureLocalIslandWitness n k r) : Prop :=
  SourcePressureLocalIslandWitnessAdjacentPairInList L W W' ∧
    SourcePressureBeamCenteredLocalPulseBox n k r L W ∧
      SourcePressureBeamCenteredLocalPulseBox n k r L W'
```

This state must not contain:
- `AdjacentDiagnosis`;
- recovered reverse-before data;
- overlap obstruction data;
- any sorted-before failure carrier.

Add a general constructor:

```lean
theorem sourcePressureBeamCenteredLocalPulseBox_of_mem
    (hW : W ∈ L) :
    SourcePressureBeamCenteredLocalPulseBox n k r L W
```

Use:
- `sourcePressureBeamPulse_witness_singleton_full_diagnostic_at_center`;
- local-island witness membership;
- `sourcePressureMarginInt_bounds_window`;
- `sourcePressureNetDropInt_bounds_window`.

Then construct the pair state from adjacency.

Phase D — prove direct two-spacing of sorted local-island centers:

Prove:

```lean
theorem sourcePressureAdjacentPair_value_gap_two_of_sorted
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
    (hpair :
      SourcePressureLocalIslandWitnessAdjacentPairInList L W W') :
    W.val + 2 ≤ W'.val
```

Suggested proof:
- sorted adjacency gives `W.val < W'.val`;
- suppose `W'.val = W.val + 1`;
- `W.property` gives nonpositive margin at `r + W.val + 1`;
- `W'.property` gives positive margin at `r + W'.val`;
- rewrite the coordinates and contradict with `omega`.

Do not route this through AdjacentDiagnosis or the old canonical state.

Phase E — direct positive-center half-window bound:

Define the Finset of actual center coordinates:

```lean
noncomputable def sourcePressurePositiveCenterPositionsInWindow
    ...
    : Finset ℕ :=
  (sourcePressurePositiveWitnessesInWindow L lo hi).image
    (fun W => r + W.val)
```

Under sortedness:
- prove the coordinate map is injective on the witness Finset;
- prove distinct coordinates are two-separated;
- prove every coordinate lies in `[lo, hi]`.

Apply:

```lean
finset_card_le_half_window_add_one_of_twoSeparated
```

to prove the stronger unconditional theorem:

```lean
theorem sourcePressurePositiveWitnesses_card_le_half_window_add_one_direct
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
    (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
      (hi - lo) / 2 + 1
```

This theorem must not contain:
- canonical packing family;
- unresolved pair family;
- AdjacentDiagnosis;
- internal coverage.

Phase F — direct sign-capacity injection:

For every in-window positive witness except the unique maximal in-window
witness, map:

```text
W ↦ r + W.val + 1
```

Prove:
- the image lies in `sourcePressureNonposPositionsInWindow`;
- the map is injective;
- the omitted maximal in-window witness contributes at most one.

Obtain:

```lean
theorem sourcePressurePositiveWitnesses_card_le_nonposPositions_add_one_direct
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
    (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
      (sourcePressureNonposPositionsInWindow n k lo hi).card + 1
```

Reuse the existing boundary-witness subsingleton theorem where useful.

Phase G — package the nonvacuous local Big:

Add:

```lean
theorem sourcePressurePositiveWitnesses_directLocalBig
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
    (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
        (hi - lo) / 2 + 1 ∧
      (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
        (sourcePressureNonposPositionsInWindow n k lo hi).card + 1
```

Interpretation:

```text
sorted local-island centers
  -> direct two-spacing
  -> half-window density

all nonterminal positive centers
  -> distinct nonpositive successor coordinates
  -> sign capacity plus one maximal boundary witness
```

Phase H — compatibility and documentation:

Keep the cp-290–cp-296 API for compatibility, but document it as the
failure-diagnostic packing route.

Add comments stating:
- `AdjacentDiagnosis` belongs to sorted-before failure resolution;
- it is not the correct carrier for sorted-list packing;
- under sortedness the old canonical family is empty, if Phase B confirms it.

Do not delete old theorems unless dependency cleanup is mechanical.

Update the report with:
- whether sortedness excludes AdjacentDiagnosis;
- whether the old canonical family is empty;
- whether direct two-spacing closed;
- the stronger direct half-window theorem;
- the direct nonpositive-position theorem.

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
````

## 総合評価

cp-296 は一見すると wrapper 整理じゃが、実際にはもっと大きな成果になった。

```text
CanonicalPacking
  ↔ AdjacentDiagnosis
```

まで縮約したことで、

```text
sorted packing
failure diagnosis
```

という、本来別の二つの世界が混ざっていたことが露出した。

したがって次は `AdjacentDiagnosis` producer を探すのではない。

**old canonical family が sortedness 下で空であることを Lean に確認し、local-island witness 自体の two-spacing から packing bound を直接作り直す。**

ここが通れば、現在の、

$$
\text{positiveWitnesses.card}\le\frac{hi-lo}{2}+2+\text{undiagnosedPairs.card}
$$

より強い、

$$
\text{positiveWitnesses.card}\le\frac{hi-lo}{2}+1
$$

へ進める。

これは差し戻しではなく、Lean が設計上の混線を見つけてくれた瞬間じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean
index ff4acbfa..39af924c 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean
@@ -1145,7 +1145,79 @@ theorem mem_sourcePressureUnresolvedInternalPairFamily_iff_not_orientedNeighborB
     apply mem_sourcePressureUnresolvedInternalPairFamily.2
     refine ⟨hzip, hlo, hhi, ?_⟩
     intro hcanon
-    exact hnotbox ((sourcePressureCanonicalFiniteWindowPackingState_iff_orientedNeighborBox_of_sorted
-      hsorted hlo hhi).1 hcanon)
+    have hiff := sourcePressureCanonicalFiniteWindowPackingState_iff_orientedNeighborBox_of_sorted
+      hsorted hlo hhi
+    exact hnotbox (hiff.1 hcanon)
+
+/-- Oriented box data adds no information beyond its full diagnostic. -/
+theorem sourcePressureOrientedNeighborBoxState_iff_diagnostic
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r} :
+    SourcePressureOrientedNeighborBoxState L W W' ↔
+      SourcePressureOrientedNeighborDiagnosticState L W W' := by
+  constructor
+  · exact SourcePressureOrientedNeighborBoxState.diagnostic
+  · exact sourcePressureOrientedNeighborDiagnosticState_to_boxState
+
+/-- Project the adjacent diagnosis carried by an oriented diagnostic state. -/
+theorem SourcePressureOrientedNeighborDiagnosticState.adjacentDiagnosis
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureOrientedNeighborDiagnosticState L W W') :
+    SourcePressureLocalIslandWitnessAdjacentDiagnosis L W W' := by
+  rcases h with ⟨_hin, hdiag, _hentry, _haddr, _hexit,
+    _hentry', _haddr', _hexit'⟩
+  exact hdiag
+
+theorem sourcePressureOrientedNeighborDiagnosticState_iff_adjacentDiagnosis
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hpair : SourcePressureLocalIslandWitnessAdjacentPairInList L W W') :
+    SourcePressureOrientedNeighborDiagnosticState L W W' ↔
+      SourcePressureLocalIslandWitnessAdjacentDiagnosis L W W' := by
+  constructor
+  · exact SourcePressureOrientedNeighborDiagnosticState.adjacentDiagnosis
+  · exact sourcePressureOrientedNeighborDiagnosticState_of_forward hpair
+
+theorem sourcePressureCanonicalFiniteWindowPackingState_iff_adjacentDiagnosis
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (hpair : SourcePressureLocalIslandWitnessAdjacentPairInList L W W')
+    (hlo : lo ≤ r + W.val) (hhi : r + W'.val ≤ hi) :
+    SourcePressureCanonicalFiniteWindowPackingState L lo hi W W' ↔
+      SourcePressureLocalIslandWitnessAdjacentDiagnosis L W W' := by
+  rw [sourcePressureCanonicalFiniteWindowPackingState_iff_orientedNeighborBox_of_sorted
+    hsorted hlo hhi, sourcePressureOrientedNeighborBoxState_iff_diagnostic]
+  exact sourcePressureOrientedNeighborDiagnosticState_iff_adjacentDiagnosis hpair
+
+/-- Semantic alias: unresolved internal pairs are undiagnosed internal pairs. -/
+noncomputable def sourcePressureUndiagnosedInternalPairFamily
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (lo hi : ℕ) :=
+  sourcePressureUnresolvedInternalPairFamily L lo hi
+
+theorem sourcePressurePositiveWitnesses_card_le_half_window_add_two_add_undiagnosedInternal
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
+      (hi - lo) / 2 + 2 +
+        (sourcePressureUndiagnosedInternalPairFamily L lo hi).card :=
+  sourcePressurePositiveWitnesses_card_le_half_window_add_two_add_unresolvedInternal hsorted
+
+theorem sourcePressurePositiveWitnesses_card_le_nonposPositions_add_one_add_undiagnosedInternal
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
+      (sourcePressureNonposPositionsInWindow n k lo hi).card + 1 +
+        (sourcePressureUndiagnosedInternalPairFamily L lo hi).card :=
+  sourcePressurePositiveWitnesses_card_le_nonposPositions_add_one_add_unresolvedInternal hsorted

 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-296.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-296.md
new file mode 100644
index 00000000..e75e5718
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-296.md
@@ -0,0 +1,100 @@
+# Petal implementation report cp-296
+
+## Semantic collapse of the pair state
+
+The apparent three-layer pair payload has been reduced to the actual
+diagnostic payload.
+
+```text
+OrientedNeighborBoxState
+  <-> OrientedNeighborDiagnosticState
+  <-> AdjacentDiagnosis       (under ordered adjacency)
+```
+
+The first equivalence is unconditional: the oriented diagnostic already
+constructs both endpoint pulse boxes.  The second uses the existing forward
+diagnostic producer and an explicit adjacent-pair hypothesis.
+
+## Canonical state characterization
+
+Under sortedness, ordered adjacency, and explicit internal window bounds:
+
+```text
+CanonicalFiniteWindowPackingState
+  <-> OrientedNeighborBoxState
+  <-> AdjacentDiagnosis
+```
+
+Thus the canonical separator is not an additional independent phenomenon. It
+is the finite-window packaging of the adjacent diagnosis.
+
+## Unresolved pair meaning
+
+The unresolved internal family now has a direct sorted membership theorem:
+
+```text
+pair is unresolved
+  <-> pair is in zip(L, L.tail)
+   and both centers are in the window
+   and the pair lacks AdjacentDiagnosis
+```
+
+The semantic alias `sourcePressureUndiagnosedInternalPairFamily` exposes this
+meaning without changing the existing carrier or counting results.
+
+The previous box-obstruction predicate remains for compatibility, but its
+three apparent branches are not independent: a full oriented diagnostic
+constructs both pulse boxes.  The true missing payload is
+`¬ SourcePressureLocalIslandWitnessAdjacentDiagnosis`.
+
+## Producer audit result
+
+Existing BeamSeed / SortedFailure / FailureResolution constructors produce a
+diagnosed existential pair and therefore eliminate the obstruction for that
+selected pair. They do not yet provide a universal theorem for every internal
+adjacent pair in an arbitrary list.
+
+The exact missing producer statement is therefore:
+
+```text
+internal adjacent pair -> AdjacentDiagnosis
+```
+
+or a positive disjunction separating recovered diagnosis from an existing
+positive overlap/budget obstruction. No genuine recovered/overlap split was
+asserted without such positive data.
+
+## Local-Big surface
+
+The strongest decomposition remains:
+
+```text
+positiveWitnesses.card
+  <= half-window capacity + 2 + undiagnosedInternalPairFamily.card
+
+positiveWitnesses.card
+  <= nonpositive-position capacity + 1
+       + undiagnosedInternalPairFamily.card
+```
+
+Under internal coverage, the undiagnosed family is empty and the endpoint-
+corrected bounds from cp-294 apply.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking
+lake build DkMath.Collatz.PetalBridge.PressureState
+lake build DkMath.Collatz.PetalBridge
+git diff --check
+```
+
+No new `sorry` or `axiom` was introduced.
+
+## Next target
+
+Construct a positive per-pair producer for `AdjacentDiagnosis`, or formalize
+the smallest positive obstruction data distinguishing recovered, overlap, and
+budget-missing branches.
````
`````
