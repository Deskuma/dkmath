# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking

gch: f82c37dd31b0f8966fc6d34290924f4f496d80e2

## Report

cp-291 を実装しました。

[FiniteWindowPacking.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean#L353) に以下を追加しています。

- finite window 内の positive witness Finset
- canonical pair の左端 Finset
- sorted list における隣接右端の一意性
- canonical-left と canonical-pair の同数性
- coverage 仮定下の半窓上界と非正位置上界
- coverage 不要の residue 分解
- residue 補正付き local-Big 上界

確定した無条件の結果は次です。

```text
positiveWitnesses.card
  ≤ (hi - lo) / 2 + 1 + residue.card

positiveWitnesses.card
  ≤ nonposPositions.card + residue.card
```

`residue.card ≤ 1` は現行 state API からは証明できません。既存 state は一組の pair を existential に生成するだけで、全非終端 pair を認証しないためです。必要な universal contract を `SourcePressureCanonicalNonterminalPairCoverageInWindow` としてコード上に固定しました。

結果は [report-petal-291.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-291.md) に記録済みです。

検証済み:

- `lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking`
- `lake build DkMath.Collatz.PetalBridge.PressureState`
- `lake build DkMath.Collatz.PetalBridge`
- `git diff --check`
- 新規 `sorry` / `axiom` なし

## Review

## 判定

**採用。cp-291 は、local Big の未確定部分を `residue` として正確に分離した重要 checkpoint じゃ。**

今回、全 positive center を無理に canonical pair へ押し込まず、

```text
positive centers
  = canonical-left として認証された部分
    + 未認証 residue
```

という形へ進んだ。

無条件で確定したのは、

$$
\#Positive\le \frac{hi-lo}{2}+1+\#Residue
$$

および、

$$
\#Positive\le\#Nonpos+\#Residue
$$

じゃ。

これは単なる「証明できなかった分を残した」のではない。DkMath の語彙では、まさに

```text
Core:
  canonical packing で制御できた半窓容量

Gap:
  canonical pair にまだ接続されていない residue

Big:
  Core + Gap
```

という、明示的な local Big 分解になった。

## 今回増えた事実

### 1. positive witness を有限集合として固定

```lean
sourcePressurePositiveWitnessesInWindow
```

が、`L` に属し、中心座標が `[lo,hi]` に入る local-island witness を抽出する。

名前には `Positive` とあるが、filter 自体に符号条件がないのは問題ない。型

```lean
SourcePressureLocalIslandWitness n k r
```

そのものが local island の証明を持つため、各要素の中心 margin は既に正じゃ。

その事実も、

```lean
sourcePressurePositiveWitnessesInWindow_center_margin_pos
```

として明示された。

### 2. canonical pair の左端集合

```lean
sourcePressureCanonicalLeftWitnessesInWindow
```

が導入された。

これは、

```text
canonical pair family
  -- Prod.fst -->
canonical left witnesses
```

という像じゃ。

さらに、

```lean
mem_sourcePressureCanonicalLeftWitnessesInWindow
```

によって、

```text
W が canonical-left 集合に属する
  ↔
ある W' が存在し、(W,W') が canonical packing state
```

という caller-facing な特徴づけまで得られた。

### 3. 同じ左端の右隣は一意

```lean
sourcePressureAdjacentPairInList_right_unique_of_sorted
```

により、sorted list では、

```text
(W,W₁') が隣接
(W,W₂') が隣接
  -> W₁' = W₂'
```

が証明された。

これにより `Prod.fst` は canonical pair family 上で単射となり、

```lean
sourcePressureCanonicalLeftWitnesses_card_eq_pairFamily_card
```

が得られた。

つまり、canonical pair の個数と、その左正中心の個数は完全に一致する。

これは cp-290 の pair counting を positive-center counting へ渡すための正しい橋じゃ。

## coverage 仮定下では全 positive local Big が閉じた

```lean
SourcePressureCanonicalLeftCoverageInWindow
```

を仮定すれば、

```lean
sourcePressurePositiveWitnesses_localBig_of_coverage
```

により、

$$
\#Positive\le\frac{hi-lo}{2}+1
$$

かつ、

$$
\#Positive\le\#Nonpos
$$

が得られる。

すなわち full coverage があれば、

```text
全 positive center
  -> canonical left center
  -> canonical separator
  -> two-spacing
  -> half-window bound
```

が完全に閉じる。

数学本体の counting 部分は、もう不足していない。
残っているのは **coverage producer** だけじゃ。

## residue 分解の意味

今回の中心定義は、

```lean
sourcePressurePositiveCoverageResidue
```

じゃ。

これは正確に、

```text
positive witnesses \ canonical left witnesses
```

を表す。

したがって residue は、単なる抽象的な「何か分からないもの」ではない。

```text
L 内に実在する positive center だが、
現在の canonical adjacent-pair API では
左 endpoint として認証されていない witness
```

そのものじゃ。

今回得られた無条件定理、

```lean
sourcePressurePositiveWitnesses_card_le_pairFamily_add_residue
```

は、

$$
\#Positive\le\#CanonicalPair+\#Residue
$$

を与える。

そして cp-290 の bound を代入して、

```lean
sourcePressurePositiveWitnesses_card_le_half_window_add_one_add_residue
```

および、

```lean
sourcePressurePositiveWitnesses_card_le_nonposPositions_add_residue
```

へ到達した。

## 数学的解説

今回の成果は、次の保存会計として読める。

```text
positive pulse の総量
  ≤ separator が許す幾何容量
    + まだ separator と結ばれていない余剰
```

式では、

$$
Positive\le PackingCapacity+CoverageGap
$$

じゃ。

ここで packing capacity は二通りある。

$$
PackingCapacity_{\mathrm{geom}}
=\frac{hi-lo}{2}+1
$$

$$
PackingCapacity_{\mathrm{sign}}
=\#Nonpos
$$

したがって本質的には、

$$
\#Positive
\le
\min\left(
\frac{hi-lo}{2}+1,\,
\#Nonpos
\right)
+\#Residue
$$

という構造まで見えている。

現在 theorem は二本の不等式として保持しているが、意味はこの `min + residue` じゃ。

## 実装レビュー

実装はよく整理されている。

特に良い点は次の通り。

- `AdjacentPairInList` と `L.zip L.tail` の橋を独立補題にした。
- sortedness を利用して右隣の一意性を証明した。
- conditional theorem と unconditional theorem を混ぜなかった。
- `residue.card ≤ 1` を推測で入れなかった。
- state producer が existential に一組を返すだけであることを正確に認識した。
- build、公開 import、`git diff --check`、no-sorry がすべて通った。

GPT-5.6 Sol は今回も、指示された「閉じなければ exact obstruction を名前にする」を正しく実行している。

## 一点、次の contract は修正した方がよい

今回追加された、

```lean
SourcePressureCanonicalNonterminalPairCoverageInWindow
```

は、次の形になっている。

```text
W が窓内
(W,W') が adjacent
  -> (W,W') は finite-window canonical state
```

しかし finite-window canonical state は、**右中心 `W'` も窓内**であることを要求する。

現在の contract は右中心の窓条件を仮定していないため、

```text
W は hi の内側
W' は hi の外側
```

という右境界 crossing pair に対しても canonical finite-window state を要求してしまう。

これは一般には強すぎる。

したがって、次は contract を次のように弱めるべきじゃ。

```lean
def SourcePressureCanonicalInternalPairCoverageInWindow
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (lo hi : ℕ) : Prop :=
  ∀ W W',
    SourcePressureLocalIslandWitnessAdjacentPairInList L W W' →
    lo ≤ r + W.val →
    r + W'.val ≤ hi →
    SourcePressureCanonicalFiniteWindowPackingState L lo hi W W'
```

sortedness により、

```text
lo ≤ left center < right center ≤ hi
```

となるので、両中心が窓内に入る。

こちらが本当の **internal pair coverage** じゃ。

## residue の正体は三分解できる

現在の residue は、さらに次へ分けられる。

```text
Residue
  =
  unresolved internal left centers
  ∪ right-window-boundary center
  ∪ terminal list center
```

### unresolved internal

左右中心がともに窓内なのに canonical state がない pair。

### right-window-boundary

左中心は窓内だが、直後の右中心が `hi` を越える pair。

### terminal

そもそも右隣を持たない list 最終要素。

sorted list なら、boundary または terminal の残余は合わせて最大一つになる可能性が高い。

なぜなら、窓内から窓外へ出る最初の crossing left endpoint が一つあるなら、それ以後の witness はすべて `hi` より右側にある。したがって terminal は窓内に残らない。

逆に最後まで窓内なら、残る可能性があるのは terminal 一点だけじゃ。

したがって本当に欲しい分解は、

$$
\#Residue\le\#UnresolvedInternal+1
$$

じゃ。

internal coverage が成立すれば、

$$
\#UnresolvedInternal=0
$$

なので、

$$
\#Residue\le1
$$

が出る。

そして初めて、

$$
\#Positive\le\frac{hi-lo}{2}+2
$$

$$
\#Positive\le\#Nonpos+1
$$

という endpoint-corrected local Big が成立する。

## 次の Codex 指示

```text
Goal:
  Refine the opaque positive-coverage residue into:

    unresolved internal adjacent pairs
      + one finite right-boundary/terminal residue.

  Correct the current universal pair-coverage contract so that it applies only
  when both adjacent centers lie inside the finite window.

Phase A — correct the coverage contract:
  Keep the existing
    SourcePressureCanonicalNonterminalPairCoverageInWindow
  for compatibility if desired, but do not target it as the next producer.

  Add:

    def SourcePressureCanonicalInternalPairCoverageInWindow
        {n : OddNat} {k r : ℕ}
        (L : List (SourcePressureLocalIslandWitness n k r))
        (lo hi : ℕ) : Prop :=
      ∀ W W',
        SourcePressureLocalIslandWitnessAdjacentPairInList L W W' →
        lo ≤ r + W.val →
        r + W'.val ≤ hi →
        SourcePressureCanonicalFiniteWindowPackingState L lo hi W W'

  Explain that sorted adjacency supplies the two omitted endpoint inequalities.

Phase B — unresolved internal pair family:
  Define a Finset from `L.zip L.tail` containing exactly adjacent pairs with:

    lo ≤ r + left.val
    r + right.val ≤ hi
    not CanonicalFiniteWindowPackingState L lo hi left right

  Suggested name:

    sourcePressureUnresolvedInternalPairFamily

  Add its membership theorem and its left-endpoint image:

    sourcePressureUnresolvedInternalLeftWitnesses

  Prove that
    SourcePressureCanonicalInternalPairCoverageInWindow
  implies this family is empty.

Phase C — right-boundary and terminal residue:
  Define two witness Finsets.

  1. Right-boundary witnesses:
       W is in-window and has an adjacent right witness W'
       with hi < r + W'.val.

  2. Terminal witnesses:
       W is in-window and has no adjacent right witness.

  Package their union as:

    sourcePressureFiniteWindowBoundaryResidue

Phase D — classify every positive residue witness:
  Prove:

    sourcePressurePositiveCoverageResidue L lo hi
      ⊆
      sourcePressureUnresolvedInternalLeftWitnesses L lo hi
        ∪ sourcePressureFiniteWindowBoundaryResidue L lo hi

  Use list recursion:
    every member of L is either a left endpoint of an adjacent pair or the last
    element;
    for an adjacent pair, its right center is either inside the window or above
    hi;
    in the internal case, either canonical or unresolved.

Phase E — boundary residue has cardinality at most one:
  Under sortedness prove:

    (sourcePressureFiniteWindowBoundaryResidue L lo hi).card ≤ 1

  Required sublemmas:
    - at most one adjacent pair crosses the right boundary;
    - at most one terminal witness;
    - an in-window right-boundary crossing witness and an in-window terminal
      witness cannot both exist.

  Use:
    sourcePressureAdjacentPairs_eq_or_nonoverlap_of_sorted
    sourcePressureSortedWitnessList_head_val_le_of_mem
    adjacency membership/order lemmas
    list last/snoc recursion as appropriate.

Phase F — refined unconditional residue bound:
  Prove:

    positiveCoverageResidue.card
      ≤ unresolvedInternalPairFamily.card + 1

  The left-endpoint image should have card no greater than the unresolved pair
  family; use `Finset.card_image_le` or prove injectivity if useful.

  Combine with cp-291:

    positiveWitnesses.card
      ≤ (hi - lo) / 2 + 2
        + unresolvedInternalPairFamily.card

    positiveWitnesses.card
      ≤ nonposPositions.card + 1
        + unresolvedInternalPairFamily.card

Phase G — endpoint-corrected theorem under internal coverage:
  From
    SourcePressureCanonicalInternalPairCoverageInWindow
  prove the unresolved family is empty and obtain:

    positiveWitnesses.card ≤ (hi - lo) / 2 + 2

    positiveWitnesses.card ≤ nonposPositions.card + 1

  Bundle these as:

    sourcePressurePositiveWitnesses_endpointCorrectedLocalBig_of_internalCoverage

Phase H — inspect the producer obstruction:
  Search the current PressureState / BeamSeed / SortedFailure /
  FailureResolution APIs for a theorem that classifies each individual adjacent
  pair.

  Determine whether internal pair coverage can be produced from:
    sortedness
    + local-island witness properties
    + pair non-overlap exclusion
    + oriented neighbor diagnostics.

  If no universal producer exists, define the exact per-pair unresolved state
  needed to populate `sourcePressureUnresolvedInternalPairFamily`.

  Do not stop after defining the family.  Carry all reachable cardinality and
  endpoint-corrected theorems through the same checkpoint.

Phase I — small API cleanup:
  The finite packing-unit Finset built twice through `attach.image` in cp-291
  should become one named definition, for example:

    sourcePressureCanonicalPackingUnitFamily

  Prove its card equals the canonical pair-family card and reuse it in both the
  sign-capacity theorems.

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 総合評価

cp-290 では、

```text
canonical packing の Core
```

が確定した。

cp-291 では、

```text
全 positive center
  ≤ Core + coverage Gap
```

まで進んだ。

つまり今回は、**local Big が DkMath 本来の Big/Gap 形式になった**。

次に行うのは residue を無理に消すことではない。

```text
residue
  -> unresolved internal Gap
   + 有限境界 Gap
```

へさらに分解することじゃ。

そこで内部 Gap を将来の universal pair theorem に渡し、境界 Gap を `≤ 1` で閉じる。これが次の正しい一手じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean
index 2eb81693..0ff44d4a 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean
@@ -340,4 +340,344 @@ def SourcePressureCanonicalLeftCoverageInWindow
     0 < SourcePressureMarginInt n k (r + W.val) →
     ∃ W', SourcePressureCanonicalFiniteWindowPackingState L lo hi W W'

+/-!
+## Positive centers and the explicit coverage residue
+
+The packing family counts certified adjacent pairs, whereas the observable
+list contains individual positive centers.  The definitions below keep the
+gap between those two populations explicit.  Full coverage is used only by
+the conditional theorems; all unconditional bounds retain a finite residue.
+-/
+
+/-- Explicit in-window local-island witnesses supplied by `L`. -/
+noncomputable def sourcePressurePositiveWitnessesInWindow
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (lo hi : ℕ) : Finset (SourcePressureLocalIslandWitness n k r) :=
+  L.toFinset.filter fun W => lo ≤ r + W.val ∧ r + W.val ≤ hi
+
+@[simp]
+theorem mem_sourcePressurePositiveWitnessesInWindow
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W : SourcePressureLocalIslandWitness n k r} :
+    W ∈ sourcePressurePositiveWitnessesInWindow L lo hi ↔
+      W ∈ L ∧ lo ≤ r + W.val ∧ r + W.val ≤ hi := by
+  classical
+  simp [sourcePressurePositiveWitnessesInWindow]
+
+/-- Every selected witness has positive pressure margin at its center. -/
+theorem sourcePressurePositiveWitnessesInWindow_center_margin_pos
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W : SourcePressureLocalIslandWitness n k r}
+    (_hW : W ∈ sourcePressurePositiveWitnessesInWindow L lo hi) :
+    0 < SourcePressureMarginInt n k (r + W.val) := by
+  have hlocal := (sourcePressureLocalIsland_iff_margin n k r W.val).1 W.property
+  exact hlocal.2.1
+
+/-- Left endpoints represented by the canonical adjacent-pair family. -/
+noncomputable def sourcePressureCanonicalLeftWitnessesInWindow
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (lo hi : ℕ) : Finset (SourcePressureLocalIslandWitness n k r) :=
+  (sourcePressureCanonicalPackingPairFamily L lo hi).image Prod.fst
+
+/-- The recursive adjacent-pair address is exactly represented in `zip L L.tail`. -/
+theorem sourcePressureAdjacentPairInList_mem_zip
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureLocalIslandWitnessAdjacentPairInList L W W') :
+    (W, W') ∈ L.zip L.tail := by
+  induction L with
+  | nil => exact False.elim h
+  | cons A rest ih =>
+      cases rest with
+      | nil => exact False.elim h
+      | cons B rest =>
+          rcases h with hhead | htail
+          · rcases hhead with ⟨rfl, rfl⟩
+            simp
+          · simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]
+            exact Or.inr (ih htail)
+
+@[simp]
+theorem mem_sourcePressureCanonicalLeftWitnessesInWindow
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W : SourcePressureLocalIslandWitness n k r} :
+    W ∈ sourcePressureCanonicalLeftWitnessesInWindow L lo hi ↔
+      ∃ W', SourcePressureCanonicalFiniteWindowPackingState L lo hi W W' := by
+  classical
+  constructor
+  · intro hW
+    rcases Finset.mem_image.1 hW with ⟨P, hP, hfst⟩
+    rcases P with ⟨PL, PR⟩
+    change PL = W at hfst
+    subst PL
+    exact ⟨PR, (mem_sourcePressureCanonicalPackingPairFamily.1 hP).2⟩
+  · rintro ⟨W', hstate⟩
+    apply Finset.mem_image.2
+    exact ⟨(W, W'), mem_sourcePressureCanonicalPackingPairFamily.2
+      ⟨sourcePressureAdjacentPairInList_mem_zip hstate.adjacentPair, hstate⟩, rfl⟩
+
+/-- In a strictly sorted witness list, a left entry has one immediate right neighbor. -/
+theorem sourcePressureAdjacentPairInList_right_unique_of_sorted
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W₁' W₂' : SourcePressureLocalIslandWitness n k r}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (h₁ : SourcePressureLocalIslandWitnessAdjacentPairInList L W W₁')
+    (h₂ : SourcePressureLocalIslandWitnessAdjacentPairInList L W W₂') :
+    W₁' = W₂' := by
+  rcases sourcePressureAdjacentPairs_eq_or_nonoverlap_of_sorted
+      hsorted h₁ h₂ with heq | horder
+  · exact heq.2
+  · have hlt₁ : W.val < W₁'.val :=
+      sourcePressureLocalIslandWitnessBefore_val_lt
+        (sourcePressureAdjacentPairInList_before_of_sorted hsorted h₁)
+    have hlt₂ : W.val < W₂'.val :=
+      sourcePressureLocalIslandWitnessBefore_val_lt
+        (sourcePressureAdjacentPairInList_before_of_sorted hsorted h₂)
+    rcases horder with h₁₂ | h₂₁ <;> omega
+
+/-- Projection to the left endpoint is injective on canonical adjacent pairs. -/
+theorem sourcePressureCanonicalPackingPairFamily_fst_injOn
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    Set.InjOn Prod.fst
+      (↑(sourcePressureCanonicalPackingPairFamily L lo hi) :
+        Set (SourcePressureLocalIslandWitness n k r ×
+          SourcePressureLocalIslandWitness n k r)) := by
+  intro P hP Q hQ hfst
+  have hPstate := (mem_sourcePressureCanonicalPackingPairFamily.1 hP).2
+  have hQstate := (mem_sourcePressureCanonicalPackingPairFamily.1 hQ).2
+  cases P with
+  | mk PL PR =>
+      cases Q with
+      | mk QL QR =>
+          change PL = QL at hfst
+          subst QL
+          have hright : PR = QR :=
+            sourcePressureAdjacentPairInList_right_unique_of_sorted hsorted
+              hPstate.adjacentPair hQstate.adjacentPair
+          subst QR
+          rfl
+
+/-- Canonical left endpoints and canonical pair keys have equal cardinality. -/
+theorem sourcePressureCanonicalLeftWitnesses_card_eq_pairFamily_card
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (lo hi : ℕ)
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    (sourcePressureCanonicalLeftWitnessesInWindow L lo hi).card =
+      (sourcePressureCanonicalPackingPairFamily L lo hi).card := by
+  classical
+  exact Finset.card_image_iff.mpr
+    (sourcePressureCanonicalPackingPairFamily_fst_injOn hsorted)
+
+/-- Full canonical-left coverage includes every selected positive witness. -/
+theorem sourcePressurePositiveWitnesses_subset_canonicalLeft_of_coverage
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hcoverage : SourcePressureCanonicalLeftCoverageInWindow L lo hi) :
+    sourcePressurePositiveWitnessesInWindow L lo hi ⊆
+      sourcePressureCanonicalLeftWitnessesInWindow L lo hi := by
+  intro W hW
+  rcases mem_sourcePressurePositiveWitnessesInWindow.1 hW with
+    ⟨hmem, hlo, hhi⟩
+  exact mem_sourcePressureCanonicalLeftWitnessesInWindow.2
+    (hcoverage W hmem hlo hhi
+      (sourcePressurePositiveWitnessesInWindow_center_margin_pos hW))
+
+/-- Conditional all-positive half-window capacity. -/
+theorem sourcePressurePositiveWitnesses_card_le_half_window_add_one_of_coverage
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (hcoverage : SourcePressureCanonicalLeftCoverageInWindow L lo hi) :
+    (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
+      (hi - lo) / 2 + 1 := by
+  calc
+    _ ≤ (sourcePressureCanonicalLeftWitnessesInWindow L lo hi).card :=
+      Finset.card_le_card
+        (sourcePressurePositiveWitnesses_subset_canonicalLeft_of_coverage hcoverage)
+    _ = (sourcePressureCanonicalPackingPairFamily L lo hi).card :=
+      sourcePressureCanonicalLeftWitnesses_card_eq_pairFamily_card L lo hi hsorted
+    _ ≤ _ := sourcePressureCanonicalPackingPairFamily_card_le_half_window_add_one hsorted
+
+/-- Conditional all-positive sign capacity. -/
+theorem sourcePressurePositiveWitnesses_card_le_nonposPositions_of_coverage
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (hcoverage : SourcePressureCanonicalLeftCoverageInWindow L lo hi) :
+    (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
+      (sourcePressureNonposPositionsInWindow n k lo hi).card := by
+  classical
+  let S : Finset (SourcePressureFiniteWindowPackingUnit L lo hi) :=
+    (sourcePressureCanonicalPackingPairFamily L lo hi).attach.image fun P =>
+      ⟨P.1.1, P.1.2, (mem_sourcePressureCanonicalPackingPairFamily.1 P.2).2⟩
+  have hScard : S.card =
+      (sourcePressureCanonicalPackingPairFamily L lo hi).card := by
+    rw [show S =
+      (sourcePressureCanonicalPackingPairFamily L lo hi).attach.image
+        (fun P => ⟨P.1.1, P.1.2,
+          (mem_sourcePressureCanonicalPackingPairFamily.1 P.2).2⟩) from rfl]
+    rw [Finset.card_image_iff.mpr]
+    · simp
+    · intro P _ Q _ h
+      apply Subtype.ext
+      apply Prod.ext
+      · exact congrArg SourcePressureFiniteWindowPackingUnit.left h
+      · exact congrArg SourcePressureFiniteWindowPackingUnit.right h
+  calc
+    _ ≤ (sourcePressureCanonicalLeftWitnessesInWindow L lo hi).card :=
+      Finset.card_le_card
+        (sourcePressurePositiveWitnesses_subset_canonicalLeft_of_coverage hcoverage)
+    _ = (sourcePressureCanonicalPackingPairFamily L lo hi).card :=
+      sourcePressureCanonicalLeftWitnesses_card_eq_pairFamily_card L lo hi hsorted
+    _ = S.card := hScard.symm
+    _ ≤ _ := sourcePressureFiniteWindowPackingUnit_card_le_nonposPositions hsorted S
+
+/-- Conditional all-positive local-Big surface. -/
+theorem sourcePressurePositiveWitnesses_localBig_of_coverage
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (hcoverage : SourcePressureCanonicalLeftCoverageInWindow L lo hi) :
+    (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
+        (hi - lo) / 2 + 1 ∧
+      (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
+        (sourcePressureNonposPositionsInWindow n k lo hi).card :=
+  ⟨sourcePressurePositiveWitnesses_card_le_half_window_add_one_of_coverage
+      hsorted hcoverage,
+    sourcePressurePositiveWitnesses_card_le_nonposPositions_of_coverage
+      hsorted hcoverage⟩
+
+/-- Positive witnesses not certified as canonical left endpoints. -/
+noncomputable def sourcePressurePositiveCoverageResidue
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (lo hi : ℕ) : Finset (SourcePressureLocalIslandWitness n k r) :=
+  sourcePressurePositiveWitnessesInWindow L lo hi \
+    sourcePressureCanonicalLeftWitnessesInWindow L lo hi
+
+/-- Exact decomposition into certified canonical-left witnesses and residue. -/
+theorem sourcePressurePositiveWitnesses_subset_canonicalLeft_union_residue
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)} :
+    sourcePressurePositiveWitnessesInWindow L lo hi ⊆
+      sourcePressureCanonicalLeftWitnessesInWindow L lo hi ∪
+        sourcePressurePositiveCoverageResidue L lo hi := by
+  classical
+  intro W hW
+  by_cases hC : W ∈ sourcePressureCanonicalLeftWitnessesInWindow L lo hi
+  · exact Finset.mem_union_left _ hC
+  · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hW, hC⟩)
+
+/-- Unconditional center count: certified pairs plus the explicit residue. -/
+theorem sourcePressurePositiveWitnesses_card_le_pairFamily_add_residue
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)} :
+    (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
+      (sourcePressureCanonicalPackingPairFamily L lo hi).card +
+        (sourcePressurePositiveCoverageResidue L lo hi).card := by
+  calc
+    _ ≤ (sourcePressureCanonicalLeftWitnessesInWindow L lo hi ∪
+          sourcePressurePositiveCoverageResidue L lo hi).card :=
+      Finset.card_le_card
+        sourcePressurePositiveWitnesses_subset_canonicalLeft_union_residue
+    _ ≤ (sourcePressureCanonicalLeftWitnessesInWindow L lo hi).card +
+          (sourcePressurePositiveCoverageResidue L lo hi).card :=
+      Finset.card_union_le _ _
+    _ ≤ _ := by
+      exact Nat.add_le_add_right Finset.card_image_le _
+
+/-- Residue-corrected half-window capacity, requiring no coverage claim. -/
+theorem sourcePressurePositiveWitnesses_card_le_half_window_add_one_add_residue
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
+      (hi - lo) / 2 + 1 +
+        (sourcePressurePositiveCoverageResidue L lo hi).card := by
+  exact le_trans sourcePressurePositiveWitnesses_card_le_pairFamily_add_residue
+    (Nat.add_le_add_right
+      (sourcePressureCanonicalPackingPairFamily_card_le_half_window_add_one hsorted) _)
+
+/-- Residue-corrected sign capacity, requiring no coverage claim. -/
+theorem sourcePressurePositiveWitnesses_card_le_nonposPositions_add_residue
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
+      (sourcePressureNonposPositionsInWindow n k lo hi).card +
+        (sourcePressurePositiveCoverageResidue L lo hi).card := by
+  classical
+  let S : Finset (SourcePressureFiniteWindowPackingUnit L lo hi) :=
+    (sourcePressureCanonicalPackingPairFamily L lo hi).attach.image fun P =>
+      ⟨P.1.1, P.1.2, (mem_sourcePressureCanonicalPackingPairFamily.1 P.2).2⟩
+  have hScard : S.card =
+      (sourcePressureCanonicalPackingPairFamily L lo hi).card := by
+    rw [show S =
+      (sourcePressureCanonicalPackingPairFamily L lo hi).attach.image
+        (fun P => ⟨P.1.1, P.1.2,
+          (mem_sourcePressureCanonicalPackingPairFamily.1 P.2).2⟩) from rfl]
+    rw [Finset.card_image_iff.mpr]
+    · simp
+    · intro P _ Q _ h
+      apply Subtype.ext
+      apply Prod.ext
+      · exact congrArg SourcePressureFiniteWindowPackingUnit.left h
+      · exact congrArg SourcePressureFiniteWindowPackingUnit.right h
+  calc
+    _ ≤ (sourcePressureCanonicalPackingPairFamily L lo hi).card +
+          (sourcePressurePositiveCoverageResidue L lo hi).card :=
+      sourcePressurePositiveWitnesses_card_le_pairFamily_add_residue
+    _ = S.card + (sourcePressurePositiveCoverageResidue L lo hi).card := by
+      rw [hScard]
+    _ ≤ _ := Nat.add_le_add_right
+      (sourcePressureFiniteWindowPackingUnit_card_le_nonposPositions hsorted S) _
+
+/-!
+## Boundary of the current state API
+
+The automaton states imported by this module select one diagnosed adjacent
+pair.  They do not quantify over every entry of `L.zip L.tail`.  Consequently
+they cannot, by themselves, show that every nonterminal positive witness is a
+canonical left endpoint.  The precise missing universal contract is named
+below.  Once a producer for it exists, ordinary list recursion can reduce the
+coverage residue to the terminal endpoint; without it, a `card ≤ 1` residue
+claim would silently strengthen an existential diagnosis into list coverage.
+-/
+
+/--
+Every in-window nonterminal witness pair is certified by the canonical packing
+state.  This is the exact pair-level bridge needed before the residue can be
+reduced to a terminal-list boundary.
+-/
+def SourcePressureCanonicalNonterminalPairCoverageInWindow
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (lo hi : ℕ) : Prop :=
+  ∀ W W',
+    SourcePressureLocalIslandWitnessAdjacentPairInList L W W' →
+    lo ≤ r + W.val → r + W.val ≤ hi →
+    SourcePressureCanonicalFiniteWindowPackingState L lo hi W W'
+
+/-- Pair coverage immediately certifies every addressed nonterminal witness. -/
+theorem SourcePressureCanonicalNonterminalPairCoverageInWindow.certifies
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureCanonicalNonterminalPairCoverageInWindow L lo hi)
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hpair : SourcePressureLocalIslandWitnessAdjacentPairInList L W W')
+    (hlo : lo ≤ r + W.val) (hhi : r + W.val ≤ hi) :
+    W ∈ sourcePressureCanonicalLeftWitnessesInWindow L lo hi :=
+  mem_sourcePressureCanonicalLeftWitnessesInWindow.2
+    ⟨W', h W W' hpair hlo hhi⟩
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-291.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-291.md
new file mode 100644
index 00000000..eab23d3e
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-291.md
@@ -0,0 +1,91 @@
+# Petal implementation report cp-291
+
+## Scope
+
+This checkpoint converts canonical-pair packing into positive-center counting
+without turning the existing existential state producers into an unsupported
+global coverage claim.
+
+## Implemented
+
+- `sourcePressurePositiveWitnessesInWindow` selects the explicit in-window
+  local-island witnesses supplied by `L`.
+- `sourcePressureCanonicalLeftWitnessesInWindow` is the left-endpoint image of
+  the canonical adjacent-pair family.
+- Center-margin positivity is exposed directly from the witness property.
+- Recursive adjacent-pair addresses are connected to `L.zip L.tail`.
+- Under sorted-before, one left endpoint has at most one immediate right
+  endpoint.  The sortedness hypothesis is necessary because arbitrary lists
+  may repeat the same witness.
+- Projection by `Prod.fst` is injective on the sorted canonical family, giving
+  equality between canonical-left and canonical-pair cardinalities.
+
+## Conditional complete coverage
+
+Under `SourcePressureCanonicalLeftCoverageInWindow`, the implementation proves:
+
+```text
+positiveWitnesses.card <= (hi - lo) / 2 + 1
+positiveWitnesses.card <= nonposPositions.card
+```
+
+The two inequalities are also bundled as
+`sourcePressurePositiveWitnesses_localBig_of_coverage`.
+
+## Unconditional residue decomposition
+
+`sourcePressurePositiveCoverageResidue` records positive witnesses not yet
+certified as canonical left endpoints.  Without any complete-coverage premise:
+
+```text
+positiveWitnesses.card
+  <= canonicalPairFamily.card + residue.card
+
+positiveWitnesses.card
+  <= (hi - lo) / 2 + 1 + residue.card
+
+positiveWitnesses.card
+  <= nonposPositions.card + residue.card
+```
+
+This is the currently justified all-positive local-Big surface.
+
+## Phase E result
+
+The preferred `residue.card <= 1` theorem does not follow from the current
+constructors.  `BeamSeed`, `SortedFailure`, and `FailureResolution` select an
+existential diagnosed pair.  They do not certify every member of
+`L.zip L.tail`.
+
+The exact missing contract is now represented in Lean as:
+
+```text
+SourcePressureCanonicalNonterminalPairCoverageInWindow L lo hi
+```
+
+It requires every addressed in-window nonterminal pair to carry
+`SourcePressureCanonicalFiniteWindowPackingState`.  A projection theorem shows
+that this contract certifies each addressed nonterminal left endpoint.
+
+No endpoint-corrected `+ 1` theorem was asserted.  Doing so before producing
+this universal pair contract would incorrectly strengthen local existential
+diagnosis into whole-list coverage.
+
+## Established route
+
+```text
+canonical separator two-spacing
+  -> canonical pair density
+  -> canonical left-center density
+  -> conditional all-positive density
+  -> unconditional positive coverage residue
+  -> residue-corrected local Big
+```
+
+## Next implementation
+
+Construct a list-recursive classifier that proves
+`SourcePressureCanonicalNonterminalPairCoverageInWindow`, or weakens it to an
+explicit unresolved-pair Finset.  The latter would refine `residue.card` into
+`terminal boundary + unresolved pair states` without claiming that the
+unresolved family is empty.
````
`````
