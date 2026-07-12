# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking

gch: 92c13cdcbc0974481eb79cb40d7afb4447dcd05f

## Report

cp-294 を完了しました。

boundary の cardinality が閉じました。

```text
boundaryWitnesses.card ≤ 1
```

追加した主な補題:

- sorted witness list の successor existence
- boundary witness の subsingleton 性
- residue の補正上界
- unresolved internal pair を含む local-Big
- internal coverage 下の endpoint-corrected local-Big

最終的に、sorted list に対して次が成立します。

```text
positiveWitnesses.card
  ≤ (hi - lo) / 2 + 2
    + unresolvedInternalPairFamily.card

positiveWitnesses.card
  ≤ nonposPositions.card + 1
    + unresolvedInternalPairFamily.card
```

さらに internal coverage がある場合、unresolved family が空になるため、

```text
positiveWitnesses.card ≤ (hi - lo) / 2 + 2
positiveWitnesses.card ≤ nonposPositions.card + 1
```

が得られます。

実装箇所は [FiniteWindowPacking.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean:862)、結果報告は [report-petal-294.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-294.md) です。

確認済み:

- `lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking`
- `lake build DkMath.Collatz.PetalBridge.PressureState`
- `lake build DkMath.Collatz.PetalBridge`
- `git diff --check`
- 新規 `sorry` / `axiom` なし

## Review

## 判定

**採用。cp-294 で有限窓 local Big の境界項が閉じた。**

今回の決定的な成果は、

```lean
sourcePressureFiniteWindowBoundaryWitnesses_card_le_one
```

じゃ。

これにより、cp-293 まで残っていた有限窓の右端誤差が、厳密に **高々一点**へ圧縮された。

そして無条件に、

$$
\#Positive \le \frac{hi-lo}{2} + 2 + \#UnresolvedInternalPair
$$

$$
\#Positive \le \#Nonpos + 1 + \#UnresolvedInternalPair
$$

が確定した。

さらに internal pair coverage を仮定すると unresolved family が空になるため、

$$
\#Positive \le \frac{hi-lo}{2}+2
$$

$$
\#Positive \le \#Nonpos+1
$$

まで Lean で閉じた。build、公開 import、`git diff --check` が通り、新規 `sorry` / `axiom` もない。

## 今回閉じた核心

追加された list-order 補題は、

```lean
sourcePressureAdjacent_successor_exists_le_of_mem_of_val_lt
```

じゃ。

内容は、

```text
同じ sorted list に W より右の V が存在する
  -> W には immediate successor W' が存在する
  -> W'.val ≤ V.val
```

というもの。

これは単なる list 補題ではなく、有限窓境界を制御する鍵だった。

二つの boundary witness `W₁`,`W₂` があり、仮に、

$$
W_1.val<W_2.val
$$

なら、`W₁` の successor `W'` が存在して、

$$
W'.val\le W_2.val
$$

となる。

`W₂` は窓内なので、

$$
r+W'.val\le r+W_2.val\le hi
$$

じゃ。

すると `W₁` は窓内 successor を持つことになり、boundary の定義と矛盾する。

逆向きも同様。したがって、

```lean
sourcePressureFiniteWindowBoundaryWitnesses_subsingleton
```

が成立し、boundary は高々一つになった。

## boundary の正体

ここで閉じた boundary は、必ずしも list 全体の最終要素ではない。

正確には、

> **有限窓 `[lo,hi]` に入っている witness のうち、最も右側にある witness**

じゃ。

その右隣が、

- そもそも存在しない、または
- 存在するが `hi` の外側へ出ている

という二つを一つに包んでいる。

今回の subsingleton theorem は、この解釈を完全に形式化したものじゃ。

## residue が完全に分解された

cp-291 では、

```text
Positive ≤ CanonicalCore + Residue
```

だった。

cp-292–293 で residue が、

```text
UnresolvedInternalLeft ∪ Boundary
```

に分類された。

今回、

$$
\#Boundary\le1
$$

が閉じたため、

```lean
sourcePressurePositiveCoverageResidue_card_le_unresolvedPair_add_one
```

によって、

$$
\#Residue\le\#UnresolvedInternalPair+1
$$

が確定した。

したがって現在の finite-window 会計は、

$$
\#Positive \le \#CanonicalPacking + \#UnresolvedInternalPair + 1
$$

じゃ。

canonical packing には半窓上界があるため、

$$
\#Positive \le \frac{hi-lo}{2}+1 + \#UnresolvedInternalPair + 1
$$

すなわち、

$$
\#Positive \le \frac{hi-lo}{2}+2 + \#UnresolvedInternalPair
$$

となる。

これは `Big = Core + Gap` の形がかなり明瞭になった。

```text
Core:
  half-window canonical packing capacity

Gap:
  unresolved internal pair count

Boundary correction:
  1
```

## local Big の到達点

今回追加された、

```lean
sourcePressurePositiveWitnesses_localBig_with_unresolvedInternal
```

は、現在の無条件 local Big の本体と言ってよい。

二つの容量を同時に持つ。

```text
幾何容量:
  Positive ≤ half-window + 2 + unresolved

符号容量:
  Positive ≤ Nonpos + 1 + unresolved
```

つまり positive center は、

1. 二間隔 packing が許す位置容量
2. 非正 separator が提供する符号容量
3. 未解決 internal pair
4. 一点の窓境界

によって支配される。

これは単なる存在・分類 theorem ではなく、明確な **有限量上界**じゃ。

## internal coverage 下では local Big が完成

```lean
sourcePressurePositiveWitnesses_endpointCorrectedLocalBig_of_internalCoverage
```

により、

```text
全 internal adjacent pair が canonical packing state を持つ
```

なら unresolved family は空になる。

したがって、

$$
\#Positive\le\frac{hi-lo}{2}+2
$$

$$
\#Positive\le\#Nonpos+1
$$

が成立する。

ここまで来ると、counting 側の不足はもうない。

残っている問いはただ一つ。

> **なぜ各 internal adjacent pair は canonical state を持つのか。**

あるいは、持たないなら、

> **何がその pair を阻害しているのか。**

じゃ。

## 実装レビュー

実装はよい。

特に、

```lean
sourcePressureFiniteWindowBoundaryWitnesses_subsingleton
```

を先に証明し、その後 `Finset.card_le_one` に落とした構造はきれいじゃ。

また、不要だった sortedness 引数を、

```lean
sourcePressureUnresolvedInternalLeftWitnesses_card_le_pairFamily
```

から削除した点も正しい。

軽微な整理候補は二つ。

### 1. theorem 名

```lean
sourcePressureAdjacent_successor_exists_le_of_mem_of_val_lt
```

は `_` の位置が少し不揃いなので、将来的には、

```lean
sourcePressureAdjacentSuccessor_exists_le_of_mem_of_val_lt
```

または、

```lean
sourcePressure_exists_adjacentSuccessor_le_of_mem_of_val_lt
```

の alias を置くと読みやすい。

今すぐ rename する必要はない。

### 2. 未使用変数

successor theorem 内の、

```lean
have hAB : A.val < B.val := ...
```

は現在の証明では使われていない。

また endpoint theorem 内の、

```lean
have hzero := congrArg Finset.card hempty
```

も使われていない。

どちらも削除可能な小さな清掃箇所じゃ。証明内容には影響しない。

## 次の本当の obstruction

既存定義を照合すると、

```lean
SourcePressureForwardPairComparisonState L W W'
```

は単なる adjacency ではない。

次を要求する。

```text
ForwardBoxComparisonState
ordered adjacent pair
left centered pulse box
right centered pulse box
```

さらに `ForwardBoxComparisonState` は、

```text
oriented neighbor box
W.val < W'.val
reverse orientation の排除
```

を要求する。

そして oriented neighbor box は、

```text
oriented diagnostic
left centered pulse box
right centered pulse box
```

からできている。

したがって、sorted internal adjacent pair が canonical state にならない本当の原因は、概ね次のどれかじゃ。

```text
1. pair の oriented diagnostic が不足している

2. left endpoint の centered pulse box が不足している

3. right endpoint の centered pulse box が不足している
```

sortedness と adjacency があれば、

```text
W.val < W'.val
reverse orientation は不可能
```

は閉じる可能性が高い。

つまり次の未解決量は、list order ではなく、**pair diagnostic / pulse-box producer** へ絞られた。

## 次に攻める定理

まず、現在の重複した state を必要十分条件へ整理するのがよい。

概念的には、

```lean
SourcePressureForwardPairComparisonState L W W'
  ↔
SourcePressureForwardBoxComparisonState L W W'
```

が成立するはずじゃ。

なぜなら `ForwardBoxComparisonState` の内部にある oriented box から、

- adjacency
- left pulse box
- right pulse box

は既に projection できる。

逆向きは定義の第一成分そのもの。

これが閉じれば、internal coverage の主語を大幅に簡略化できる。

さらに sorted adjacency の下で、

```lean
SourcePressureForwardBoxComparisonState L W W'
  ↔
SourcePressureOrientedNeighborBoxState L W W'
```

まで落とせる可能性がある。

その理由は、

- `val_lt` は sorted adjacency から出る
- reverse box は reverse adjacency を含むので sortedness と矛盾する

からじゃ。

最終的には、

```text
canonical internal coverage
  ↔
every internal adjacent pair has an oriented neighbor box
```

まで還元できる。

## 次の Codex 指示

```text
Goal:
  Reduce the remaining unresolved-internal count to its exact producer-side
  obstruction.

  The finite-window counting and boundary layers are now closed.  Do not add
  more counting wrappers first.  Simplify the pair-state hierarchy and classify
  every unresolved internal pair by the missing diagnostic/box evidence.

Phase A — simplify ForwardPairComparisonState:
  Prove:

    theorem sourcePressureForwardPairComparisonState_iff_forwardBoxComparisonState
        {n : OddNat} {k r : ℕ}
        {L : List (SourcePressureLocalIslandWitness n k r)}
        {W W' : SourcePressureLocalIslandWitness n k r} :
      SourcePressureForwardPairComparisonState L W W' ↔
        SourcePressureForwardBoxComparisonState L W W'

  Forward direction:
    use `.forwardBox` or the first projection.

  Reverse direction:
    construct the duplicated fields using:
      h.adjacentPair
      h.left_box
      h.right_box

  Use actual existing projection names.

Phase B — remove order bureaucracy under sorted adjacency:
  Prove:

    theorem sourcePressureForwardBoxComparisonState_iff_orientedNeighborBox_of_sorted
        (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
        (hpair :
          SourcePressureLocalIslandWitnessAdjacentPairInList L W W') :
      SourcePressureForwardBoxComparisonState L W W' ↔
        SourcePressureOrientedNeighborBoxState L W W'

  Reverse direction requires:
    - W.val < W'.val from sorted adjacency;
    - reverse oriented box is impossible because it projects
      AdjacentPairInList L W' W.

  Add the smallest reusable theorem excluding reverse adjacency in a sorted
  list if needed.

Phase C — canonical-state characterization:
  Under explicit internal-window bounds and sorted adjacency, prove:

    SourcePressureCanonicalFiniteWindowPackingState L lo hi W W'
      ↔ SourcePressureOrientedNeighborBoxState L W W'

  or the strongest equivalent shape Lean permits.

  Use:
    FPC -> canonical finite-window constructor
    canonical state -> finiteWindow -> localPacking -> forward
    Phases A and B.

  This theorem should make clear that, after order and window conditions are
  supplied, the only remaining mathematical payload is the oriented neighbor
  box.

Phase D — characterize unresolved internal pairs:
  Prove a membership equivalence:

    P ∈ sourcePressureUnresolvedInternalPairFamily L lo hi
      ↔
    P ∈ L.zip L.tail
      ∧ lo ≤ r + P.1.val
      ∧ r + P.2.val ≤ hi
      ∧ ¬ SourcePressureOrientedNeighborBoxState L P.1 P.2

  Require sortedness for this theorem if needed.

Phase E — exact obstruction state:
  Define:

    def SourcePressureInternalPairBoxObstruction
        (L ...) (W W' ...) : Prop :=
      ¬ SourcePressureOrientedNeighborDiagnosticState L W W'
        ∨ ¬ SourcePressureBeamCenteredLocalPulseBox n k r L W
        ∨ ¬ SourcePressureBeamCenteredLocalPulseBox n k r L W'

  Prove:

    ¬ SourcePressureOrientedNeighborBoxState L W W'
      ↔ SourcePressureInternalPairBoxObstruction L W W'

  Then prove every unresolved internal pair carries this obstruction.

Phase F — split the unresolved family:
  Define three filtered pair families if useful:

    unresolvedDiagnosticPairs
    unresolvedLeftPulseBoxPairs
    unresolvedRightPulseBoxPairs

  Prove:

    unresolvedInternalPairFamily
      ⊆ unresolvedDiagnosticPairs
         ∪ unresolvedLeftPulseBoxPairs
         ∪ unresolvedRightPulseBoxPairs

  Derive the cardinality bound:

    unresolvedInternalPairFamily.card
      ≤ diagnosticMissing.card
        + leftBoxMissing.card
        + rightBoxMissing.card

  Feed this into:
    sourcePressurePositiveWitnesses_localBig_with_unresolvedInternal

  to expose the local Big as:

    canonical capacity
      + diagnostic Gap
      + endpoint-box Gap
      + one boundary witness.

Phase G — producer audit:
  Search existing theorems that construct:
    SourcePressureBeamCenteredLocalPulseBox
    SourcePressureOrientedNeighborDiagnosticState
    SourcePressureOrientedNeighborBoxState

  For each component, record whether it is:
    - implied by SourcePressureLocalIslandWitness.property;
    - implied by sorted adjacency;
    - produced only for an existential pair by BeamSeed /
      SortedFailure / FailureResolution;
    - or genuinely absent.

  Attempt the strongest per-pair theorem available.

  Preferred target:

    internal adjacent pair
      -> OrientedNeighborBoxState
       ∨ exact diagnostic/box obstruction.

  Do not return to global BeamSeed coverage until this per-pair theorem is
  explicit.

Phase H — cleanup:
  Remove the unused `hAB` and `hzero` local facts.
  Optionally add a consistently named alias for
    sourcePressureAdjacent_successor_exists_le_of_mem_of_val_lt.

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check

Report:
  - the simplified state equivalences;
  - the exact unresolved-pair obstruction;
  - which obstruction components current producers can already eliminate;
  - the strongest updated local-Big decomposition.
```

## 総合評価

cp-294 で、有限窓の accounting 層は事実上完成した。

```text
canonical packing Core
  + unresolved internal Gap
  + boundary 1
```

まで定量化されている。

しかも internal coverage があれば、

```text
Positive ≤ half-window + 2
Positive ≤ Nonpos + 1
```

が確定する。

ここから先は、数え方を改善する段階ではない。

**各 internal pair がなぜ canonical になるのか、または何が不足して canonical にならないのかを、局所 producer の中身まで分解する段階**じゃ。

境界は閉じた。
残った Gap は、純粋に内部診断の問題へ絞られた。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean
index 7c7046da..c2c528c3 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean
@@ -797,7 +797,7 @@ theorem sourcePressureCanonicalPackingUnitFamily_card
 theorem sourcePressureUnresolvedInternalLeftWitnesses_card_le_pairFamily
     {n : OddNat} {k r lo hi : ℕ}
     {L : List (SourcePressureLocalIslandWitness n k r)}
-    (_hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    :
     (sourcePressureUnresolvedInternalLeftWitnesses L lo hi).card ≤
       (sourcePressureUnresolvedInternalPairFamily L lo hi).card := by
   classical
@@ -854,4 +854,180 @@ theorem sourcePressurePositiveCoverageResidue_subset_unresolvedLeft_union_bounda
   · apply Finset.mem_union_right
     exact mem_sourcePressureFiniteWindowBoundaryWitnesses.2 ⟨hpos, hboundary⟩
 
+/--
+In a sorted witness list, a non-maximal witness has an adjacent successor no
+larger than any later witness.  This is the list-order bridge needed by the
+finite-window boundary argument.
+-/
+theorem sourcePressureAdjacent_successor_exists_le_of_mem_of_val_lt
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W V : SourcePressureLocalIslandWitness n k r}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (hW : W ∈ L) (hV : V ∈ L) (hval : W.val < V.val) :
+    ∃ W', SourcePressureLocalIslandWitnessAdjacentPairInList L W W' ∧
+      W'.val ≤ V.val := by
+  induction L generalizing W V with
+  | nil => simp at hW
+  | cons A rest ih =>
+      cases rest with
+      | nil =>
+          simp only [List.mem_singleton] at hW hV
+          subst W
+          subst V
+          omega
+      | cons B rest =>
+          have htailSorted :
+              SourcePressureLocalIslandWitnessListSortedBefore (B :: rest) := by
+            change SourcePressureIntervalPulseAddressFamilySortedBefore
+              (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList
+                (A :: B :: rest)) at hsorted
+            change SourcePressureIntervalPulseAddressFamilySortedBefore
+              (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList
+                (B :: rest))
+            exact hsorted.2
+          rcases List.mem_cons.1 hW with hWA | hWtail
+          · subst W
+            rcases List.mem_cons.1 hV with hVA | hVtail
+            · subst V
+              omega
+            have hAB : A.val < B.val :=
+              sourcePressureLocalIslandWitnessBefore_val_lt
+                (sourcePressureAdjacentPairInList_before_of_sorted hsorted
+                  SourcePressureLocalIslandWitnessAdjacentPairInList.head)
+            have hB_le : B.val ≤ V.val :=
+              sourcePressureSortedWitnessList_head_val_le_of_mem htailSorted
+                hVtail
+            exact ⟨B, SourcePressureLocalIslandWitnessAdjacentPairInList.head,
+              hB_le⟩
+          · have hVtail : V ∈ B :: rest := by
+              rcases List.mem_cons.1 hV with hVA | hVtail
+              · have hA_le_W : A.val ≤ W.val :=
+                  sourcePressureSortedWitnessList_head_val_le_of_mem hsorted
+                    (by exact List.mem_cons_of_mem A hWtail)
+                subst V
+                omega
+              · exact hVtail
+            rcases ih htailSorted hWtail hVtail hval with ⟨W', hpair, hle⟩
+            exact ⟨W', SourcePressureLocalIslandWitnessAdjacentPairInList.tail hpair,
+              hle⟩
+
+/-- The finite-window boundary carrier is subsingleton under sortedness. -/
+theorem sourcePressureFiniteWindowBoundaryWitnesses_subsingleton
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    ∀ W₁ ∈ sourcePressureFiniteWindowBoundaryWitnesses L lo hi,
+      ∀ W₂ ∈ sourcePressureFiniteWindowBoundaryWitnesses L lo hi, W₁ = W₂ := by
+  intro W₁ h₁ W₂ h₂
+  rcases mem_sourcePressureFiniteWindowBoundaryWitnesses.1 h₁ with
+    ⟨hW₁, hboundary₁⟩
+  rcases mem_sourcePressureFiniteWindowBoundaryWitnesses.1 h₂ with
+    ⟨hW₂, hboundary₂⟩
+  by_cases heq : W₁.val = W₂.val
+  · exact Subtype.ext heq
+  · rcases Nat.lt_or_gt_of_ne heq with hlt | hgt
+    · have hsucc := sourcePressureAdjacent_successor_exists_le_of_mem_of_val_lt
+        hsorted
+        (mem_sourcePressurePositiveWitnessesInWindow.1 hW₁).1
+        (mem_sourcePressurePositiveWitnessesInWindow.1 hW₂).1 hlt
+      rcases hsucc with ⟨W', hpair, hle⟩
+      exact False.elim (hboundary₁ ⟨W', hpair, le_trans (Nat.add_le_add_left hle r)
+        (mem_sourcePressurePositiveWitnessesInWindow.1 hW₂).2.2⟩)
+    · have hsucc := sourcePressureAdjacent_successor_exists_le_of_mem_of_val_lt
+        hsorted
+        (mem_sourcePressurePositiveWitnessesInWindow.1 hW₂).1
+        (mem_sourcePressurePositiveWitnessesInWindow.1 hW₁).1 hgt
+      rcases hsucc with ⟨W', hpair, hle⟩
+      exact False.elim (hboundary₂ ⟨W', hpair, le_trans (Nat.add_le_add_left hle r)
+        (mem_sourcePressurePositiveWitnessesInWindow.1 hW₁).2.2⟩)
+
+theorem sourcePressureFiniteWindowBoundaryWitnesses_card_le_one
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    (sourcePressureFiniteWindowBoundaryWitnesses L lo hi).card ≤ 1 := by
+  apply Finset.card_le_one.2
+  intro W hW V hV
+  exact sourcePressureFiniteWindowBoundaryWitnesses_subsingleton hsorted W hW V hV
+
+theorem sourcePressurePositiveCoverageResidue_card_le_unresolvedPair_add_one
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    (sourcePressurePositiveCoverageResidue L lo hi).card ≤
+      (sourcePressureUnresolvedInternalPairFamily L lo hi).card + 1 := by
+  calc
+    _ ≤ (sourcePressureUnresolvedInternalLeftWitnesses L lo hi ∪
+          sourcePressureFiniteWindowBoundaryWitnesses L lo hi).card :=
+      Finset.card_le_card
+        (sourcePressurePositiveCoverageResidue_subset_unresolvedLeft_union_boundary)
+    _ ≤ (sourcePressureUnresolvedInternalLeftWitnesses L lo hi).card +
+          (sourcePressureFiniteWindowBoundaryWitnesses L lo hi).card :=
+      Finset.card_union_le _ _
+    _ ≤ (sourcePressureUnresolvedInternalPairFamily L lo hi).card + 1 := by
+      apply Nat.add_le_add
+      · exact sourcePressureUnresolvedInternalLeftWitnesses_card_le_pairFamily
+      · exact sourcePressureFiniteWindowBoundaryWitnesses_card_le_one hsorted
+
+theorem sourcePressurePositiveWitnesses_card_le_half_window_add_two_add_unresolvedInternal
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
+      (hi - lo) / 2 + 2 +
+        (sourcePressureUnresolvedInternalPairFamily L lo hi).card := by
+  have hbase := sourcePressurePositiveWitnesses_card_le_half_window_add_one_add_residue
+    (L := L) (lo := lo) (hi := hi) hsorted
+  have hres := sourcePressurePositiveCoverageResidue_card_le_unresolvedPair_add_one
+    (L := L) (lo := lo) (hi := hi) hsorted
+  omega
+
+theorem sourcePressurePositiveWitnesses_card_le_nonposPositions_add_one_add_unresolvedInternal
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
+      (sourcePressureNonposPositionsInWindow n k lo hi).card + 1 +
+        (sourcePressureUnresolvedInternalPairFamily L lo hi).card := by
+  have hbase := sourcePressurePositiveWitnesses_card_le_nonposPositions_add_residue
+    (L := L) (lo := lo) (hi := hi) hsorted
+  have hres := sourcePressurePositiveCoverageResidue_card_le_unresolvedPair_add_one
+    (L := L) (lo := lo) (hi := hi) hsorted
+  omega
+
+theorem sourcePressurePositiveWitnesses_localBig_with_unresolvedInternal
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
+        (hi - lo) / 2 + 2 +
+          (sourcePressureUnresolvedInternalPairFamily L lo hi).card ∧
+      (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
+        (sourcePressureNonposPositionsInWindow n k lo hi).card + 1 +
+          (sourcePressureUnresolvedInternalPairFamily L lo hi).card :=
+  ⟨sourcePressurePositiveWitnesses_card_le_half_window_add_two_add_unresolvedInternal
+      hsorted,
+    sourcePressurePositiveWitnesses_card_le_nonposPositions_add_one_add_unresolvedInternal
+      hsorted⟩
+
+theorem sourcePressurePositiveWitnesses_endpointCorrectedLocalBig_of_internalCoverage
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (hcoverage : SourcePressureCanonicalInternalPairCoverageInWindow L lo hi) :
+    (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤ (hi - lo) / 2 + 2 ∧
+      (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
+        (sourcePressureNonposPositionsInWindow n k lo hi).card + 1 := by
+  have hempty :=
+    sourcePressureUnresolvedInternalPairFamily_eq_empty_of_internalCoverage hcoverage
+  have hzero := congrArg Finset.card hempty
+  constructor
+  · simpa [hempty] using
+      sourcePressurePositiveWitnesses_card_le_half_window_add_two_add_unresolvedInternal
+        (L := L) (lo := lo) (hi := hi) hsorted
+  · simpa [hempty] using
+      sourcePressurePositiveWitnesses_card_le_nonposPositions_add_one_add_unresolvedInternal
+        (L := L) (lo := lo) (hi := hi) hsorted
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-294.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-294.md
new file mode 100644
index 00000000..663c03a9
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-294.md
@@ -0,0 +1,77 @@
+# Petal implementation report cp-294
+
+## Closed in this checkpoint
+
+The finite-window boundary term is now closed under sorted-before.
+
+- Added the sorted-list successor lemma:
+  a witness with a later larger witness has an adjacent successor whose value
+  is no larger than that later witness.
+- Proved the unified finite-window boundary carrier is subsingleton.
+- Proved:
+
+```text
+boundaryWitnesses.card <= 1
+```
+
+- Removed the unnecessary sortedness argument from the unresolved-left image
+  bound.
+- Combined the residue classification with the unresolved-pair and boundary
+  bounds.
+
+## Final unconditional inequalities
+
+For a sorted witness list:
+
+```text
+positiveWitnesses.card
+  <= (hi - lo) / 2 + 2 + unresolvedInternalPairFamily.card
+
+positiveWitnesses.card
+  <= nonposPositions.card + 1 + unresolvedInternalPairFamily.card
+```
+
+These are bundled as
+`sourcePressurePositiveWitnesses_localBig_with_unresolvedInternal`.
+
+## Internal coverage specialization
+
+Under `SourcePressureCanonicalInternalPairCoverageInWindow`, the unresolved
+internal family is empty.  The endpoint-corrected local-Big theorem is now:
+
+```text
+positiveWitnesses.card <= (hi - lo) / 2 + 2
+positiveWitnesses.card <= nonposPositions.card + 1
+```
+
+Bundled as
+`sourcePressurePositiveWitnesses_endpointCorrectedLocalBig_of_internalCoverage`.
+
+## Interpretation
+
+The finite-window accounting chain is now explicit:
+
+```text
+two-spaced canonical separators
+  -> canonical pair density
+  -> positive-center residue
+  -> unresolved internal pairs + one maximal boundary witness
+  -> endpoint-corrected local Big
+```
+
+The remaining mathematical question is producer-side: prove internal coverage
+for every internal adjacent pair, or classify the exact local obstruction when
+that coverage fails. No global convergence claim is made here.
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
````
`````
