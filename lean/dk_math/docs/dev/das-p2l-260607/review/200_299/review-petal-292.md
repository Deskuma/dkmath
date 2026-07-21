# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking

gch: de599570f8cd883175a6394132095ffc6d19103a

## Report

cp-292 を実装しました。

[FiniteWindowPacking.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean:688) に以下を追加しています。

- `SourcePressureCanonicalInternalPairCoverageInWindow`
- `sourcePressureUnresolvedInternalPairFamily`
- unresolved pair の membership theorem
- unresolved pair の left-endpoint image
- `zip` membershipとadjacent-pair predicateの相互変換
- internal coverage 下で unresolved family が空になる定理
- `sourcePressureCanonicalPackingUnitFamily` と cardinality bridge

これにより residue の構造は、

```text
positive residue
  = unresolved internal left endpoints
  + right-boundary / terminal residue
```

まで分解できる基盤ができました。

一方、`residue.card ≤ 1` はまだ主張していません。現在の state producer は existential な pair 診断であり、`L.zip L.tail` 全体の coverage を保証しないためです。次は right-boundary Finset と terminal Finset を定義し、sorted-before の下でそれらの濃度を評価します。

結果は [report-petal-292.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-292.md) に記録しました。

確認済み:

- `lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking`
- `git diff --check`
- 新規 `sorry` / `axiom` なし

## Review

## 判定

**採用。cp-292 は、coverage Gap を実体のある有限集合へ落とした checkpoint じゃ。**

ただし今回は、local Big の数値上界そのものを更新したのではない。cp-291 で一つに残っていた `residue` を、

```text
内部で未認証な adjacent pair
境界または末尾に残る witness
```

へ分解するための、前半部分を Lean 上に固定した。

追加された中心 API は次じゃ。

```lean
SourcePressureCanonicalInternalPairCoverageInWindow
sourcePressureUnresolvedInternalPairFamily
sourcePressureUnresolvedInternalLeftWitnesses
sourcePressureUnresolvedInternalPairFamily_eq_empty_of_internalCoverage
sourcePressureCanonicalPackingUnitFamily
sourcePressureCanonicalPackingUnitFamily_card
```

さらに、`L.zip L.tail` と再帰的な `AdjacentPairInList` が双方向につながった。ビルドと `git diff --check` が通り、`sorry` / `axiom` の追加もない。

## 今回の核心

前回の residue は、

```text
positive witness だが
canonical left endpoint として認証されていない
```

という一枚岩だった。

今回、その内部の一部が明示された。

```text
UnresolvedInternalPair
  =
  左右の中心がともに窓内
  かつ adjacent pair
  かつ canonical packing state ではない
```

Lean 定義では、

```lean
sourcePressureUnresolvedInternalPairFamily L lo hi
```

がこれを正確に保持する。

これにより、residue の構図は次まで進んだ。

```text
positive residue
  ⊆ unresolved internal left endpoints
     ∪ finite right-boundary residue
```

まだこの包含定理自体は未実装じゃが、右辺の第一項が正式な `Finset` になった。

## internal coverage の修正は正しい

今回追加された、

```lean
SourcePressureCanonicalInternalPairCoverageInWindow
```

は、cp-291 の強すぎた contract を正しく修正している。

旧 contract は、左中心だけが窓内であっても、右中心まで窓内に収めた canonical finite-window state を要求していた。右隣が `hi` を越える場合には強すぎる。

今回の contract は、

```lean
lo ≤ r + W.val
r + W'.val ≤ hi
```

を要求する。

つまり、

```text
left center も窓内
right center も窓内
```

である adjacent pair だけを coverage 対象にした。

これは今後、境界 crossing を内部 failure と混同しないための重要な修正じゃ。

## unresolved family が空になる意味

```lean
sourcePressureUnresolvedInternalPairFamily_eq_empty_of_internalCoverage
```

により、

```text
全 internal adjacent pair が canonical
  -> unresolved internal pair family = ∅
```

が確定した。

これは定義上の言い換えだけではない。

証明経路は、

```text
Finset の pair
  -> L.zip L.tail の pair
  -> AdjacentPairInList
  -> internal coverage を適用
  -> 非 canonical 仮定と矛盾
```

となっている。

そのために、

```lean
sourcePressureAdjacentPairInList_mem_zip
sourcePressureAdjacentPairInList_of_mem_zip
```

が双方向で揃った。

ここはよい。list-recursive な adjacency と counting 用の `zip` 表現が、正式に同一の pair 集合として扱えるようになった。

## induction 修正について

既存補題の、

```lean
sourcePressureAdjacentPairInList_mem_zip
```

に対して、

```lean
induction L generalizing W W'
```

へ修正された点も妥当じゃ。

再帰段で pair の端点 `W W'` が変化するため、一般化が必要になる。以前の形がたまたま通っていた、または今後の利用で不安定だった箇所を、正しい帰納法へ直している。

## unresolved left endpoint の意味

```lean
sourcePressureUnresolvedInternalLeftWitnesses
```

は、unresolved pair family を `Prod.fst` で射影したものじゃ。

したがって、

```text
内部に右隣は存在する
右隣も窓内にある
しかし canonical separator を認証できていない
```

という left center だけを集める。

これは最終的に、

$$
\#Residue \le \#UnresolvedInternalLeft + 1
$$

へ進むための正しい carrier じゃ。

現時点では、pair family から left family への cardinality equality はまだ立てていない。ただし sorted list では一つの左端に右隣は一つなので、前 checkpoint の一意性補題を再利用すれば、

$$
\#UnresolvedInternalLeft = \#UnresolvedInternalPair
$$

まで出せるはずじゃ。

少なくとも必要なのは `≤` で十分。

## packing unit family の命名

```lean
sourcePressureCanonicalPackingUnitFamily
```

を名前付き定義へしたのも良い。

cp-291 では同じ `attach.image` 構築が複数箇所に重複していた。今回、

```lean
sourcePressureCanonicalPackingUnitFamily_card
```

により、

$$
\#CanonicalPackingUnitFamily = \#CanonicalPackingPairFamily
$$

まで固定された。

これで、今後の sign-capacity theorem は同じ family を再構築せずに済む。

これは証明力の増加というより、**counting API の正規化**じゃが、必要な整理である。

## 数学的意味

cp-290 では、

```text
canonical Core
  ≤ half-window capacity
  ≤ nonpositive-position capacity
```

が確定した。

cp-291 では、

```text
all positive
  ≤ canonical Core + residue
```

となった。

cp-292 では、その residue の内部に、

```text
unresolved internal Gap
```

という明示的な有限 carrier ができた。

したがって、現在の local Big は概念的に、

$$
Positive \le CanonicalPacking + UnresolvedInternal + Boundary
$$

まで分解された。

さらに cp-290 の上界を代入すれば、目標形は、

$$
\#Positive \le \frac{hi-lo}{2}+1 + \#UnresolvedInternal + \#Boundary
$$

じゃ。

境界項を `≤ 1` で閉じれば、

$$
\#Positive \le \frac{hi-lo}{2}+2 + \#UnresolvedInternal
$$

となる。

internal coverage が成立すれば unresolved は空なので、

$$
\#Positive \le \frac{hi-lo}{2}+2
$$

へ到達する。

## 今回まだ増えていない事実

report の記述どおり、次はまだ証明されていない。

```text
positive residue
  ⊆ unresolved internal left endpoints
     ∪ boundary residue
```

```text
boundary residue.card ≤ 1
```

```text
positive residue.card
  ≤ unresolved internal pair family.card + 1
```

```text
internal coverage
  -> positive witnesses.card ≤ half-window + 2
```

したがって cp-292 は、**residue 分解の基盤確定**であって、endpoint-corrected local Big の完成ではない。

この線引きは正確じゃ。

## 次の実装では境界を二つに分けすぎない方がよい

前回の指示では、

```text
right-boundary witnesses
terminal witnesses
```

を別々の Finset にする案を出した。

しかし実装上は、一つの boundary carrier にまとめる方が鋭い可能性がある。

たとえば、

```lean
sourcePressureFiniteWindowRightBoundaryWitnesses
```

を、

```text
W は窓内
かつ
窓内にある adjacent right witness が存在しない
```

と定義する。

これは、

```text
右隣はあるが hi の外
または
W が list terminal
```

の両方を自動的に含む。

strictly sorted な list では、これは窓内 witness の最大要素にしかなれないため、直接、

$$
\#Boundary\le1
$$

を狙える。

二つの集合を定義して、各 `card ≤ 1` と非共存を別々に証明するより、証明が短くなる可能性が高い。

## 次の Codex 指示

次 checkpoint は、定義追加だけで止めず、**residue 分類から endpoint-corrected local Big まで**通す。

```text
Goal:
  Complete the finite-window residue decomposition.

  Prove that every positive witness not certified as a canonical left endpoint
  is either:
    - the left endpoint of an unresolved internal adjacent pair; or
    - the unique right-boundary/terminal witness of the finite window.

  Carry this through to the endpoint-corrected local-Big theorem.

Phase A — unresolved-left cardinality:
  Prove that projection by Prod.fst is injective on
    sourcePressureUnresolvedInternalPairFamily L lo hi
  under sortedness.

  Reuse:
    sourcePressureAdjacentPairInList_right_unique_of_sorted
    sourcePressureAdjacentPairInList_of_mem_zip

  Obtain:

    sourcePressureUnresolvedInternalLeftWitnesses_card_eq_pairFamily_card

  A `≤` theorem is sufficient if equality creates unnecessary proof overhead.

Phase B — unified finite-window boundary carrier:
  Prefer one boundary Finset rather than separate crossing and terminal Finsets.

  Define the in-window witnesses having no in-window adjacent successor:

    noncomputable def sourcePressureFiniteWindowBoundaryWitnesses
        {n : OddNat} {k r : ℕ}
        (L : List (SourcePressureLocalIslandWitness n k r))
        (lo hi : ℕ) :
        Finset (SourcePressureLocalIslandWitness n k r) :=
      (sourcePressurePositiveWitnessesInWindow L lo hi).filter fun W =>
        ¬ ∃ W',
          SourcePressureLocalIslandWitnessAdjacentPairInList L W W' ∧
            r + W'.val ≤ hi

  This includes exactly:
    - a witness whose actual adjacent successor lies above hi;
    - or the terminal witness of L.

  Add a precise membership theorem.

Phase C — boundary uniqueness:
  Under
    hsorted : SourcePressureLocalIslandWitnessListSortedBefore L

  prove:

    (sourcePressureFiniteWindowBoundaryWitnesses L lo hi).card ≤ 1

  Stronger preferred theorem:

    ∀ W₁ ∈ boundary, ∀ W₂ ∈ boundary, W₁ = W₂

  Proof routes:
    - list recursion on L; or
    - show any earlier in-window witness has a next list entry, and sortedness
      forces that successor to remain no later than a later in-window witness;
      hence it has an in-window adjacent successor and is not boundary.

  Do not separately prove crossing/terminal noncoexistence if the unified
  definition makes it unnecessary.

Phase D — classify the positive coverage residue:
  Prove:

    sourcePressurePositiveCoverageResidue L lo hi ⊆
      sourcePressureUnresolvedInternalLeftWitnesses L lo hi ∪
        sourcePressureFiniteWindowBoundaryWitnesses L lo hi

  For W in the residue:
    1. W is an in-window member of L.
    2. If W has no adjacent successor inside the window, put it in boundary.
    3. Otherwise choose its adjacent successor W'.
    4. If the pair is canonical, W belongs to canonical-left, contradicting
       residue membership.
    5. Therefore the pair belongs to the unresolved internal family.

Phase E — refined residue bound:
  Derive:

    positiveCoverageResidue.card
      ≤ unresolvedInternalLeftWitnesses.card + 1

  and then:

    positiveCoverageResidue.card
      ≤ unresolvedInternalPairFamily.card + 1

  using Phase A and the boundary card bound.

Phase F — unconditional refined local Big:
  Combine with cp-291:

    positiveWitnesses.card
      ≤ (hi - lo) / 2 + 2
        + unresolvedInternalPairFamily.card

    positiveWitnesses.card
      ≤ nonposPositions.card + 1
        + unresolvedInternalPairFamily.card

  Bundle these into a named theorem such as:

    sourcePressurePositiveWitnesses_localBig_with_unresolvedInternal

Phase G — internal-coverage endpoint correction:
  Use:

    sourcePressureUnresolvedInternalPairFamily_eq_empty_of_internalCoverage

  to prove, under
    SourcePressureCanonicalInternalPairCoverageInWindow L lo hi:

    positiveWitnesses.card ≤ (hi - lo) / 2 + 2

    positiveWitnesses.card ≤ nonposPositions.card + 1

  Bundle as:

    sourcePressurePositiveWitnesses_endpointCorrectedLocalBig_of_internalCoverage

Phase H — reuse the named packing-unit family:
  Refactor the two cp-291 sign-capacity proofs to use:

    sourcePressureCanonicalPackingUnitFamily

  and:

    sourcePressureCanonicalPackingUnitFamily_card

  Remove duplicated local `attach.image` constructions without changing theorem
  names.

Phase I — producer audit:
  After the endpoint-corrected theorem closes, inspect the per-pair hypotheses
  needed to prove internal coverage.

  Do not ask only whether BeamSeed globally implies coverage.
  For an arbitrary internal adjacent pair W,W', determine the exact missing
  local proposition required to construct:

    SourcePressureCanonicalFiniteWindowPackingState L lo hi W W'

  Package that local unresolved reason as a state or disjunction only if it is
  not already represented by an existing pair-overlap / pressure-failure state.

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check

Report:
  - whether boundary.card ≤ 1 closed;
  - whether the residue classification closed;
  - the final endpoint-corrected inequalities;
  - the exact per-pair obstruction to internal coverage.
```

## 検証上の補足

今回は、

```text
lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking
```

のみが report に記録されている。

対象モジュール自体の検証としては十分じゃが、前回までの運用に合わせて次回は、

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
```

も記録した方がよい。

これは実装の差し戻し理由ではなく、公開 import 面の回帰確認を揃えるための運用補足じゃ。

## 総合評価

cp-292 は、local Big の Gap を一段深く切った。

```text
cp-290:
  canonical packing Core

cp-291:
  Positive ≤ Core + residue

cp-292:
  residue = internal unresolved Gap + finite boundary Gap
            （分解用 carrier の前半を確定）
```

特に大事なのは、内部で証明できていないものと、有限窓の端だから必然的に残るものを分離したことじゃ。

次に境界項を `≤ 1` で閉じれば、未解決量は純粋に、

```text
unresolved internal adjacent pairs
```

だけになる。

そこまで進めば local Big は、境界誤差を除いて、**内部 pair coverage の問題へ完全に還元される。**

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean
index 0ff44d4a..c7691986 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean
@@ -390,7 +390,7 @@ theorem sourcePressureAdjacentPairInList_mem_zip
     {W W' : SourcePressureLocalIslandWitness n k r}
     (h : SourcePressureLocalIslandWitnessAdjacentPairInList L W W') :
     (W, W') ∈ L.zip L.tail := by
-  induction L with
+  induction L generalizing W W' with
   | nil => exact False.elim h
   | cons A rest ih =>
       cases rest with
@@ -680,4 +680,117 @@ theorem SourcePressureCanonicalNonterminalPairCoverageInWindow.certifies
   mem_sourcePressureCanonicalLeftWitnessesInWindow.2
     ⟨W', h W W' hpair hlo hhi⟩

+/-!
+## Internal pairs and the named packing family
+-/
+
+/-- Internal coverage requires both endpoints to lie in the finite window. -/
+def SourcePressureCanonicalInternalPairCoverageInWindow
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (lo hi : ℕ) : Prop :=
+  ∀ W W',
+    SourcePressureLocalIslandWitnessAdjacentPairInList L W W' →
+    lo ≤ r + W.val → r + W'.val ≤ hi →
+    SourcePressureCanonicalFiniteWindowPackingState L lo hi W W'
+
+/-- Internal adjacent pairs not yet certified as canonical. -/
+noncomputable def sourcePressureUnresolvedInternalPairFamily
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (lo hi : ℕ) : Finset
+      (SourcePressureLocalIslandWitness n k r ×
+        SourcePressureLocalIslandWitness n k r) :=
+  by classical exact (L.zip L.tail).toFinset.filter fun P =>
+    lo ≤ r + P.1.val ∧ r + P.2.val ≤ hi ∧
+      ¬ SourcePressureCanonicalFiniteWindowPackingState L lo hi P.1 P.2
+
+@[simp]
+theorem mem_sourcePressureUnresolvedInternalPairFamily
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {P : SourcePressureLocalIslandWitness n k r ×
+      SourcePressureLocalIslandWitness n k r} :
+    P ∈ sourcePressureUnresolvedInternalPairFamily L lo hi ↔
+      P ∈ L.zip L.tail ∧
+      lo ≤ r + P.1.val ∧ r + P.2.val ≤ hi ∧
+        ¬ SourcePressureCanonicalFiniteWindowPackingState L lo hi P.1 P.2 := by
+  classical
+  simp [sourcePressureUnresolvedInternalPairFamily]
+
+theorem sourcePressureAdjacentPairInList_of_mem_zip
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : (W, W') ∈ L.zip L.tail) :
+    SourcePressureLocalIslandWitnessAdjacentPairInList L W W' := by
+  induction L generalizing W W' with
+  | nil => simp at h
+  | cons A rest ih =>
+      cases rest with
+      | nil => simp at h
+      | cons B rest =>
+          simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at h
+          rcases h with hhead | htail
+          · cases hhead
+            exact SourcePressureLocalIslandWitnessAdjacentPairInList.head
+          · exact SourcePressureLocalIslandWitnessAdjacentPairInList.tail
+              (ih htail)
+
+/-- Left endpoints of unresolved internal pairs. -/
+noncomputable def sourcePressureUnresolvedInternalLeftWitnesses
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (lo hi : ℕ) : Finset (SourcePressureLocalIslandWitness n k r) :=
+  (sourcePressureUnresolvedInternalPairFamily L lo hi).image Prod.fst
+
+@[simp]
+theorem mem_sourcePressureUnresolvedInternalLeftWitnesses
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W : SourcePressureLocalIslandWitness n k r} :
+    W ∈ sourcePressureUnresolvedInternalLeftWitnesses L lo hi ↔
+      ∃ W', (W, W') ∈ sourcePressureUnresolvedInternalPairFamily L lo hi := by
+  classical
+  simp [sourcePressureUnresolvedInternalLeftWitnesses]
+
+/-- Internal coverage makes the unresolved pair family empty. -/
+theorem sourcePressureUnresolvedInternalPairFamily_eq_empty_of_internalCoverage
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hcoverage : SourcePressureCanonicalInternalPairCoverageInWindow L lo hi) :
+    sourcePressureUnresolvedInternalPairFamily L lo hi = ∅ := by
+  classical
+  apply Finset.eq_empty_of_forall_notMem
+  intro P hP
+  rcases mem_sourcePressureUnresolvedInternalPairFamily.1 hP with
+    ⟨hzip, hlo, hhi, hnot⟩
+  exact hnot (hcoverage P.1 P.2
+    (sourcePressureAdjacentPairInList_of_mem_zip hzip) hlo hhi)
+
+/-- A named Finset of canonical packing units, shared by counting theorems. -/
+noncomputable def sourcePressureCanonicalPackingUnitFamily
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (lo hi : ℕ) : Finset (SourcePressureFiniteWindowPackingUnit L lo hi) := by
+  classical
+  exact (sourcePressureCanonicalPackingPairFamily L lo hi).attach.image fun P =>
+    ⟨P.1.1, P.1.2, (mem_sourcePressureCanonicalPackingPairFamily.1 P.2).2⟩
+
+theorem sourcePressureCanonicalPackingUnitFamily_card
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ} :
+    (sourcePressureCanonicalPackingUnitFamily L lo hi).card =
+      (sourcePressureCanonicalPackingPairFamily L lo hi).card := by
+  classical
+  unfold sourcePressureCanonicalPackingUnitFamily
+  rw [Finset.card_image_iff.mpr]
+  · simp
+  · intro P _ Q _ h
+    apply Subtype.ext
+    apply Prod.ext
+    · exact congrArg SourcePressureFiniteWindowPackingUnit.left h
+    · exact congrArg SourcePressureFiniteWindowPackingUnit.right h
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-292.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-292.md
new file mode 100644
index 00000000..dd69ed82
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-292.md
@@ -0,0 +1,59 @@
+# Petal implementation report cp-292
+
+## Implemented
+
+The finite-window layer now distinguishes internal pairs from boundary pairs.
+
+- `SourcePressureCanonicalInternalPairCoverageInWindow` requires both the
+  left and right centers of an adjacent pair to lie in the window.
+- `sourcePressureUnresolvedInternalPairFamily` contains exactly the in-window
+  adjacent pairs that are not canonical packing states.
+- Its membership theorem and left-endpoint image are available.
+- Internal coverage implies that the unresolved internal pair family is empty.
+- `sourcePressureCanonicalPackingUnitFamily` names the previously repeated
+  `attach.image` construction, and its cardinality is equal to the canonical
+  pair family cardinality.
+
+The `zip`/adjacency conversion is now proved in both directions, so the
+unresolved-family emptiness theorem is a genuine list-recursive result rather
+than a definitional shortcut.
+
+## Mathematical status
+
+The positive residue is now conceptually split as:
+
+```text
+positive residue
+  = unresolved internal left endpoints
+  + right-boundary / terminal residue
+```
+
+The first component has a precise Finset carrier and vanishes under the new
+internal coverage contract.  The second component is not yet encoded: proving
+its cardinality bound requires a separate theorem that at most one adjacent
+pair crosses `hi`, at most one terminal witness exists, and those two cases do
+not coexist as distinct in-window witnesses.
+
+## Producer inspection
+
+The current BeamSeed, SortedFailure, and FailureResolution states remain
+existential pair producers.  They do not establish internal coverage for every
+member of `L.zip L.tail`.  Therefore no unconditional `residue.card ≤ 1` or
+endpoint-corrected `+ 1` theorem is asserted here.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking
+```
+
+The new code introduces no `sorry` or `axiom`. Existing unrelated project
+warnings remain unchanged.
+
+## Next target
+
+Add explicit right-boundary and terminal Finsets, then prove their cardinality
+bound under sorted-before. After that, combine it with the unresolved internal
+family to obtain the endpoint-corrected local-Big theorem.
````
`````
