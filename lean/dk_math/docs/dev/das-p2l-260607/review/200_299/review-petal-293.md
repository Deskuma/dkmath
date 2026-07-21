# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking

gch: de09f57110bb16f54fd4b6b3bb4a3ba882f1de82

## Report

cp-293 を実装しました。

追加内容:

- unresolved internal left endpoint の cardinality bound
- unified boundary Finset
  `sourcePressureFiniteWindowBoundaryWitnesses`
- boundary membership theorem
- positive residue の分類定理

```text
positiveCoverageResidue
  ⊆ unresolvedInternalLeftWitnesses ∪ boundaryWitnesses
```

したがって、residue の未解決部分は明示的に

```text
unresolved internal pair
または
in-window successor を持たない境界 witness
```

へ分類されました。

一方、`boundary.card ≤ 1` はまだ未確定です。必要なのは、sorted list における「隣接 successor を持たない witness は最終要素に限る」という list-order 補題です。このため、endpoint-corrected `+1` bound は次 checkpoint に残しています。

結果は [report-petal-293.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-293.md) に記録しました。

確認済み:

- `lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking`
- `lake build DkMath.Collatz.PetalBridge.PressureState`
- `lake build DkMath.Collatz.PetalBridge`
- `git diff --check`
- 新規 `sorry` / `axiom` なし

## Review

## 判定

**採用。cp-293 で residue の分類そのものが Lean 上に通った。**

今回の中心成果は、

```lean
sourcePressurePositiveCoverageResidue_subset_unresolvedLeft_union_boundary
```

じゃ。

これにより、canonical-left として捕捉されなかった positive witness は、必ず

```text
内部 adjacent pair は存在するが canonical 化されていない
または
窓内に adjacent successor を持たない
```

のどちらかへ分類された。build、公開 import、`git diff --check` が通り、新規 `sorry` / `axiom` もない。

## 今回確定した分解

cp-291 では、

$$
Positive\le CanonicalPacking+Residue
$$

だった。

cp-292 で `UnresolvedInternalPair` が有限集合になり、今回ついに、

$$
Residue\subseteq UnresolvedInternalLeft\cup Boundary
$$

が証明された。

さらに、

```lean
sourcePressureUnresolvedInternalLeftWitnesses_card_le_pairFamily
```

により、

$$
\#UnresolvedInternalLeft \le \#UnresolvedInternalPair
$$

も固定された。

したがって現在の構造は、ほぼ次まで来ている。

$$
\#Positive \le \#CanonicalPacking + \#UnresolvedInternalPair + \#Boundary
$$

canonical packing には cp-290 の半窓上界があるため、

$$
\#Positive \le \frac{hi-lo}{2}+1 + \#UnresolvedInternalPair + \#Boundary
$$

じゃ。

残るのは `Boundary.card ≤ 1` だけ。

## unified boundary carrier は正しい

今回導入された、

```lean
sourcePressureFiniteWindowBoundaryWitnesses
```

は、

```text
窓内に存在する positive witness
かつ
窓内に入る adjacent successor が存在しない
```

を表している。

これは二つの場合を一つに包む。

```text
1. list の本当の最終 witness
2. right successor は存在するが、hi より外へ出る witness
```

別々に crossing / terminal Finset を作らなかった判断はよい。最終的に必要なのは、「窓内で一番右にいる witness は高々一つ」という事実だからじゃ。

## residue 分類証明もきれい

証明は `by_cases` で、

```text
窓内 adjacent successor が存在するか
```

を分けている。

存在する場合、その pair が canonical なら `W` は canonical-left に入る。だが `W` は residue なので矛盾する。したがって、その pair は unresolved internal family に入る。

存在しない場合は、そのまま boundary family に入る。

つまり分類は、

```text
successor exists
  -> canonical or unresolved
  -> residue なので unresolved

successor does not exist in window
  -> boundary
```

という完全な二分になっている。

## 一点、report の表現を補正した方がよい

report では、必要な補題を、

> 隣接 successor を持たない witness は最終要素に限る

と説明している。

しかし今回の boundary の定義は、

```text
adjacent successor 自体が存在しない
```

ではなく、

```text
窓内にある adjacent successor が存在しない
```

じゃ。

したがって boundary witness は、必ずしも `L` の最終要素ではない。

たとえば、

```text
W は [lo,hi] 内
W' は W の直後
しかし W' > hi
```

なら、`W` は list terminal ではないが boundary witness になる。

正しい表現は、

> sorted list において、窓内 adjacent successor を持たない witness は、窓内 witness の最大要素に限る。

じゃ。

必要なのは `last element` theorem ではなく、**maximal in-window witness theorem** である。

## 次に必要な核心補題

最も直接的には、boundary family が subsingleton であることを示せばよい。

```lean
theorem sourcePressureFiniteWindowBoundaryWitnesses_pairwise_eq_of_sorted
    {n : OddNat} {k r lo hi : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
    {W₁ W₂ : SourcePressureLocalIslandWitness n k r}
    (hW₁ : W₁ ∈ sourcePressureFiniteWindowBoundaryWitnesses L lo hi)
    (hW₂ : W₂ ∈ sourcePressureFiniteWindowBoundaryWitnesses L lo hi) :
    W₁ = W₂
```

これが出れば、

```lean
theorem sourcePressureFiniteWindowBoundaryWitnesses_card_le_one
    ...
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
    (sourcePressureFiniteWindowBoundaryWitnesses L lo hi).card ≤ 1
```

はすぐ閉じる。

## 証明の数学的骨格

二つの異なる boundary witness `W₁`, `W₂` があると仮定する。

sortedness により、どちらかが先にある。仮に、

$$
W_1.val<W_2.val
$$

とする。

`W₁` より後に `W₂` が list 内に存在する以上、`W₁` は list terminal ではない。したがって直後の adjacent successor `W₁'` が存在する。

しかも `W₂` はさらに右側にあるので、

$$
W_1'.val\le W_2.val
$$

となる。

`W₂` は窓内だから、

$$
r+W_2.val\le hi
$$

である。よって、

$$
r+W_1'.val\le hi
$$

となり、`W₁` は窓内 adjacent successor を持つ。

これは `W₁` が boundary であることに反する。

したがって boundary witness は一つしかない。

## 本当に不足している list 補題

必要なのは、概念的にはこれじゃ。

```lean
theorem sourcePressure_exists_adjacent_successor_le_of_val_lt_mem
    {W V : SourcePressureLocalIslandWitness n k r}
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
    (hW : W ∈ L)
    (hV : V ∈ L)
    (hlt : W.val < V.val) :
    ∃ W',
      SourcePressureLocalIslandWitnessAdjacentPairInList L W W' ∧
        W'.val ≤ V.val
```

意味は、

```text
同じ sorted list に W より右の V があるなら、
W には直後の successor があり、
その successor は V を越えない。
```

これなら boundary uniqueness がそのまま閉じる。

generic list theorem として、

```text
sorted list において、
ある要素より後ろに別要素が存在すれば、
その要素には immediate successor が存在する
```

を先に作ってもよい。

## 軽微な API 修正

```lean
sourcePressureUnresolvedInternalLeftWitnesses_card_le_pairFamily
```

には、

```lean
(_hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
```

が渡されているが、証明は単なる `Finset.card_image_le` であり、sortedness を使っていない。

この仮定は削除してよい。

```lean
theorem sourcePressureUnresolvedInternalLeftWitnesses_card_le_pairFamily
    ... :
    leftWitnesses.card ≤ pairFamily.card := by
  classical
  exact Finset.card_image_le
```

将来 equality を証明する場合には sortedness が必要になるが、現在の `≤` theorem には不要じゃ。

## 次 checkpoint の目標

次は定義や分類で止めず、以下を一気に閉じるべきじゃ。

```text
boundary witnesses are subsingleton
  -> boundary.card ≤ 1
  -> residue.card ≤ unresolvedPair.card + 1
  -> endpoint-corrected local Big
  -> internal coverage 下で unresolved = 0
  -> pure +1 endpoint theorem
```

得るべき無条件上界は、

$$
\#Positive
\le
\frac{hi-lo}{2}+2+#UnresolvedInternalPair
$$

および、

$$
\#Positive
\le
\#Nonpos+1+#UnresolvedInternalPair
$$

じゃ。

internal pair coverage の下では、

$$
\#Positive\le\frac{hi-lo}{2}+2
$$

$$
\#Positive\le#Nonpos+1
$$

まで落ちる。

## 次の Codex 指示要点

```text
Goal:
  Close the finite-window boundary term and derive the endpoint-corrected
  local-Big theorems.

1. Prove the minimal sorted-list successor lemma:

     if W,V ∈ L and W.val < V.val,
     then W has an adjacent successor W' with W'.val ≤ V.val.

   Use list recursion and the existing:
     AdjacentPairInList
     sourcePressureAdjacentPairInList_mem_zip
     sourcePressureAdjacentPairInList_of_mem_zip
     sorted-before/value-order lemmas.

2. Prove boundary subsingleton:

     W₁ ∈ boundary
     W₂ ∈ boundary
       -> W₁ = W₂

   If W₁.val < W₂.val, the successor lemma produces an in-window successor
   for W₁ because W₂ is in-window, contradicting boundary membership.
   Handle the reverse order symmetrically.

3. Derive:

     boundaryWitnesses.card ≤ 1

4. Combine cp-293 classification with:
     unresolvedLeft.card ≤ unresolvedPair.card
     boundary.card ≤ 1

   to prove:

     positiveCoverageResidue.card
       ≤ unresolvedInternalPairFamily.card + 1

5. Combine with cp-291/cp-290:

     positiveWitnesses.card
       ≤ (hi - lo) / 2 + 2
         + unresolvedInternalPairFamily.card

     positiveWitnesses.card
       ≤ nonposPositions.card + 1
         + unresolvedInternalPairFamily.card

   Bundle as:
     sourcePressurePositiveWitnesses_localBig_with_unresolvedInternal

6. Under:
     SourcePressureCanonicalInternalPairCoverageInWindow L lo hi

   use:
     sourcePressureUnresolvedInternalPairFamily_eq_empty_of_internalCoverage

   to prove:

     positiveWitnesses.card ≤ (hi - lo) / 2 + 2
     positiveWitnesses.card ≤ nonposPositions.card + 1

   Bundle as:
     sourcePressurePositiveWitnesses_endpointCorrectedLocalBig_of_internalCoverage

7. Remove the unused sortedness parameter from:
     sourcePressureUnresolvedInternalLeftWitnesses_card_le_pairFamily

8. Update the report wording:
     replace “only the final list element lacks a successor”
     with
     “only the maximal in-window witness lacks an in-window successor”.

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 総合評価

cp-293 で、residue は完全に分類可能な形になった。

```text
canonical Core
unresolved internal Gap
finite boundary Gap
```

の三項じゃ。

今回まだ数値 `+1` は出ていないが、残る問題は pressure 理論ではない。**sorted finite list の右端構造**だけである。

ここを閉じれば、

$$
Positive
\le
CanonicalCore+UnresolvedInternal+1
$$

が確定する。

つまり local Big の境界誤差は一点へ圧縮され、数学的な未解決部分は純粋に `unresolved internal pair` だけになる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean
index c7691986..7c7046da 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean
@@ -793,4 +793,65 @@ theorem sourcePressureCanonicalPackingUnitFamily_card
     · exact congrArg SourcePressureFiniteWindowPackingUnit.left h
     · exact congrArg SourcePressureFiniteWindowPackingUnit.right h

+/-- Unresolved left endpoints are injectively indexed by unresolved pairs. -/
+theorem sourcePressureUnresolvedInternalLeftWitnesses_card_le_pairFamily
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (_hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    (sourcePressureUnresolvedInternalLeftWitnesses L lo hi).card ≤
+      (sourcePressureUnresolvedInternalPairFamily L lo hi).card := by
+  classical
+  exact Finset.card_image_le
+
+/-- In-window witnesses with no in-window adjacent successor. -/
+noncomputable def sourcePressureFiniteWindowBoundaryWitnesses
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (lo hi : ℕ) : Finset (SourcePressureLocalIslandWitness n k r) := by
+  classical
+  exact (sourcePressurePositiveWitnessesInWindow L lo hi).filter fun W =>
+    ¬ ∃ W', SourcePressureLocalIslandWitnessAdjacentPairInList L W W' ∧
+      r + W'.val ≤ hi
+
+@[simp]
+theorem mem_sourcePressureFiniteWindowBoundaryWitnesses
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W : SourcePressureLocalIslandWitness n k r} :
+    W ∈ sourcePressureFiniteWindowBoundaryWitnesses L lo hi ↔
+      W ∈ sourcePressurePositiveWitnessesInWindow L lo hi ∧
+      ¬ ∃ W', SourcePressureLocalIslandWitnessAdjacentPairInList L W W' ∧
+        r + W'.val ≤ hi := by
+  classical
+  simp [sourcePressureFiniteWindowBoundaryWitnesses]
+
+/-- Every positive residue witness is unresolved internally or at the boundary. -/
+theorem sourcePressurePositiveCoverageResidue_subset_unresolvedLeft_union_boundary
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)} :
+    sourcePressurePositiveCoverageResidue L lo hi ⊆
+      sourcePressureUnresolvedInternalLeftWitnesses L lo hi ∪
+        sourcePressureFiniteWindowBoundaryWitnesses L lo hi := by
+  classical
+  intro W hW
+  have hpos : W ∈ sourcePressurePositiveWitnessesInWindow L lo hi :=
+    (Finset.mem_sdiff.1 hW).1
+  by_cases hboundary : ∃ W',
+      SourcePressureLocalIslandWitnessAdjacentPairInList L W W' ∧
+        r + W'.val ≤ hi
+  · rcases hboundary with ⟨W', hpair, hhi'⟩
+    have hleft : lo ≤ r + W.val :=
+      (mem_sourcePressurePositiveWitnessesInWindow.1 hpos).2.1
+    have hnotcanon :
+        ¬ SourcePressureCanonicalFiniteWindowPackingState L lo hi W W' := by
+      intro hcanon
+      apply (Finset.mem_sdiff.1 hW).2
+      exact mem_sourcePressureCanonicalLeftWitnessesInWindow.2 ⟨W', hcanon⟩
+    apply Finset.mem_union_left
+    apply Finset.mem_image.2
+    exact ⟨(W, W'), mem_sourcePressureUnresolvedInternalPairFamily.2
+      ⟨sourcePressureAdjacentPairInList_mem_zip hpair, hleft, hhi', hnotcanon⟩, rfl⟩
+  · apply Finset.mem_union_right
+    exact mem_sourcePressureFiniteWindowBoundaryWitnesses.2 ⟨hpos, hboundary⟩
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-293.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-293.md
new file mode 100644
index 00000000..9edbe5d8
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-293.md
@@ -0,0 +1,70 @@
+# Petal implementation report cp-293
+
+## Implemented
+
+- Projection of `sourcePressureUnresolvedInternalPairFamily` to left
+  endpoints is bounded by the pair-family cardinality.
+- Added `sourcePressureFiniteWindowBoundaryWitnesses`, the unified boundary
+  carrier for in-window positive witnesses with no in-window adjacent
+  successor.
+- Added its exact membership theorem.
+- Proved the residue classification:
+
+```text
+positiveCoverageResidue
+  subset unresolvedInternalLeftWitnesses union boundaryWitnesses
+```
+
+- The named canonical packing-unit family from cp-292 now has a cardinality
+  bridge to the canonical pair family.
+
+## What is established
+
+The residue is no longer opaque. Every positive witness omitted from the
+canonical-left family is classified by a concrete finite carrier:
+
+```text
+unresolved internal adjacent pair
+or
+no in-window adjacent successor
+```
+
+The first component has the bound
+`unresolvedInternalLeftWitnesses.card <= unresolvedInternalPairFamily.card`.
+
+## Remaining boundary theorem
+
+The target
+
+```text
+boundaryWitnesses.card <= 1
+```
+
+was not asserted. The unified boundary definition is correct, but its proof
+requires a reusable list-order theorem: in a sorted witness list, two distinct
+in-window witnesses cannot both lack an in-window adjacent successor. The
+current API has adjacent-pair order and head-value lemmas, but not yet the
+needed direct “every non-last entry has its successor” or last-element
+characterization.
+
+Therefore the endpoint-corrected `+ 1` inequalities remain pending. The exact
+remaining work is list endpoint infrastructure, not a pressure or arithmetic
+obstruction.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking
+```
+
+`git diff --check` and the no-new-`sorry` check remain clean. Existing
+unrelated project warnings are unchanged.
+
+## Next target
+
+Add the minimal list theorem connecting an element with no adjacent successor
+to the final list entry, then prove boundary cardinality at most one. This will
+immediately yield the endpoint-corrected local-Big inequalities and their
+internal-coverage specialization.
````
`````
