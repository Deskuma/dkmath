# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 2ed846088c44b22a396b88654ffd0af985a1e8be

## Report

cp-289 を完了しました。今回は有限 family の実際の counting theorem まで到達しています。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:2198) で Lean が次を証明しました。

```text
共有 separator + sorted witness list
  -> 同じ oriented adjacent pair
```

したがって、異なる oriented pair は同じ separator を利用できません。separator multiplicity は仮定ではなく、sorted adjacency から `1` と証明されました。

さらに canonical separator

```lean
r + W.val + 1
```

を持つ packing unit を構造体化し、canonical separator の単射性と有限窓 bound を証明しました。

```lean
S.card ≤ hi + 1 - lo
```

非空 family では：

```lean
S.card ≤ hi - lo + 1
```

つまり、有限窓内の packing unit 数は窓内の separator 座標数を超えません。証明は canonical separator による `Finset.Icc lo hi` への単射です。

結果は [report-petal-289.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-289.md) に記録しました。

検証済み：

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

`PressureState.lean` への `sorry` / `axiom` の追加はありません。

## Review

## 判定

**採用。今回の cp-289 は大進展じゃ。**

前回の難度を上げた指示に対し、Codex GPT-5.6 Sol は途中で止まらず、

```text
隣接 pair の順序分解
  -> separator multiplicity = 1
  -> canonical separator
  -> packing unit の構造体化
  -> separator 単射
  -> Finset counting theorem
```

まで一気に通した。

これは初めて、局所 pressure の符号配置が **有限 family の個数上界**になった checkpoint じゃ。

## 増えた中核事実

### 1. 二つの隣接 pair は同一か、順序的に非重複

```lean
sourcePressureAdjacentPairs_eq_or_nonoverlap_of_sorted
```

Lean が証明した分岐は、

```text
同じ oriented adjacent pair
または
right₁.val ≤ left₂.val
または
right₂.val ≤ left₁.val
```

じゃ。

端点の `≤` は正確で、連続する pair

```text
(A, B), (B, C)
```

も扱える。

この補題が今回の本当の基礎定理になっておる。

### 2. 共有 separator は同一 pair を強制する

```lean
SourcePressureFiniteWindowPackingPairComparisonState
  .same_pair_of_shared_separator_of_sorted
```

すなわち、

```text
m₁ = m₂
  -> W₁ = W₂ ∧ W₁' = W₂'
```

が証明された。

非重複 branch では、共有 separator `m` に対して概念的に

```text
m < right₁ ≤ left₂ < m
```

またはその逆が発生し、`omega` で潰れる。

したがって、

```lean
SourcePressureFiniteWindowPackingPairComparisonState
  .separators_ne_of_pairs_ne_of_sorted
```

も得られた。

これは separator reuse の上界が単なる仮定ではなく、

```text
multiplicity = 1
```

として sorted adjacency から導出されたことを意味する。

## canonical separator の確立

追加された canonical state は、

```lean
SourcePressureCanonicalFiniteWindowPackingState
```

であり、separator を

```lean
r + W.val + 1
```

に固定する。

これにより、左正中心の直後を標準的な非正点として選べる。

確定した性質は、

```lean
.separator_nonpos
.separator_between_centers
.separator_in_window
.adjacentPair
```

じゃ。

さらに、

```lean
SourcePressureForwardPairComparisonState
  .to_canonicalFiniteWindowPackingState
```

により、FPC と窓境界から canonical state を直接作れる。

以前の「同じ pair に非正 separator が複数あり得る」という曖昧さは、これで消えた。

## 有限 family counting

packing unit は、

```lean
SourcePressureFiniteWindowPackingUnit
```

として構造体化された。

各 unit は、

```text
left witness
right witness
canonical packing proof
```

を持ち、写像

```lean
SourcePressureFiniteWindowPackingUnit.canonicalSeparator
```

が sorted list 上で単射になった。

```lean
SourcePressureFiniteWindowPackingUnit
  .canonicalSeparator_injective_of_sorted
```

その結果、任意の有限 family `S` に対して、

```lean
sourcePressureFiniteWindowPackingUnit_card_le_window_card
```

が

```lean
S.card ≤ hi + 1 - lo
```

を証明した。

非空 family では、

```lean
sourcePressureFiniteWindowPackingUnit_card_le_window_width_add_one
```

により通常形

```lean
S.card ≤ hi - lo + 1
```

も得られている。

証明構造もきれいじゃ。

```text
packing unit
  -> canonical separator
  -> Finset.Icc lo hi
  -> 単射
  -> card の単調性
```

## 実装評価

実装品質も高い。

`sourcePressureSortedWitnessList_head_val_le_of_mem` を先に作り、そこから二つの隣接 pair の非重複性を再帰的に証明したのは正攻法じゃ。

また、`canonicalSeparator_injective_of_sorted` は pair の一致だけでなく、proof field を含む structure 全体の一致まで閉じている。Lean の proof irrelevance を利用して、unit 型そのものへの `Function.Injective` まで持ち上げたのもよい。

ビルド、集約 import、`git diff --check` がすべて通り、`sorry` / `axiom` の追加もない。

## 改善された指示の進展評価

今回の Codex は、こちらが提示した Phase A–F をほぼ完走した。

特に評価できるのは、単なる指定 theorem の実装だけでなく、

```lean
sourcePressureSortedWitnessList_head_val_le_of_mem
```

という不足していた下層 bridge を自ら補い、そのまま主定理へ戻っている点じゃ。

旧来の挙動なら、

```text
必要な list lemma が見つからない
  -> 調査報告で checkpoint 終了
```

となりやすかった。

今回は、

```text
不足 bridge を発見
  -> 実装
  -> pair 非重複
  -> multiplicity one
  -> canonicalization
  -> Finset counting
```

まで続けている。

**依頼難度を上げた判断は正しかった。**
GPT-5.6 Sol は、この規模なら一回の指示で複数の数学層を横断できておる。

## 現在の counting bound の位置づけ

今回の上界

```text
S.card ≤ hi - lo + 1
```

は正しい第一 counting theorem じゃ。

ただし、これは canonical separator が窓内の異なる座標へ入ることだけを使った上界である。

まだ今回の重要な事実、

```text
各 pair の中心間隔は少なくとも 2
```

を counting に使っていない。

実際、異なる unit が順序的に並ぶ場合、その canonical separator 同士にも

```text
sep₁ + 2 ≤ sep₂
```

または逆向きの関係が出るはずじゃ。

したがって、次の本命は単なる

```text
非正 separator の個数以下
```

より強い。

```text
2-separated separator packing
  -> およそ窓幅の半分以下
```

まで攻められる。

目標形は、

```lean
S.card ≤ (hi - lo) / 2 + 1
```

じゃ。

これが **packing density** と呼べる最初の鋭い上界になる。

## 次のロードマップ

次は一回の指示で、以下まで進める。

```text
canonical separator の単射
  -> canonical separator の 2-spacing
  -> sign-restricted separator set
  -> half-window packing bound
  -> L から canonical family を抽出
  -> positive-center density / local Big への接続条件
```

`PressureState.lean` は既に肥大化しているため、finite-window 部分の分割も同時に行う。ただし refactor だけで checkpoint を閉じず、分割後に新しい counting theorem まで進める。

## Codex 指示

```text
Goal:
  Strengthen cp-289 from a coordinate-counting bound to a genuine packing-
  density theorem.

  The current canonical separator map is injective, but the proof only uses
  distinctness.  Use sorted adjacency and the existing two-step center gap to
  prove that distinct canonical separators are themselves separated by at
  least two positions.

  Continue through a sharp finite-window cardinality bound and an explicit
  canonical family extracted from the witness list.

Phase A — mechanical module extraction:
  Extract the stable finite-window packing layer from PressureState.lean into:

    DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean

  Move:
    SourcePressureLocalPackingSeparatorState
    SourcePressureFiniteWindowPackingSeparatorState
    SourcePressureFiniteWindowPackingPairComparisonState
    SourcePressureCanonicalFiniteWindowPackingState
    SourcePressureFiniteWindowPackingUnit
    their projections, constructors, comparison theorems, and counting theorems.

  Keep PressureState.lean as an aggregator importing the new module.
  Preserve theorem names and public imports.

  Complete this mechanically, rebuild, and then continue with the mathematical
  phases below in the same checkpoint.

Phase B — two-spacing of canonical separators:
  Prove a theorem of the following form:

    theorem SourcePressureFiniteWindowPackingUnit
        .canonicalSeparator_two_separated_of_ne_of_sorted
        {u₁ u₂ : SourcePressureFiniteWindowPackingUnit L lo hi}
        (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
        (hne : u₁ ≠ u₂) :
        u₁.canonicalSeparator + 2 ≤ u₂.canonicalSeparator ∨
          u₂.canonicalSeparator + 2 ≤ u₁.canonicalSeparator

  Route:
    - convert hne to pair-key inequality, using canonical unit extensionality;
    - apply sourcePressureAdjacentPairs_eq_or_nonoverlap_of_sorted;
    - eliminate the equal-pair branch;
    - use each unit's two_le_value_gap / two_le_index_gap;
    - combine the pair non-overlap order with omega.

  A pair-key version may be proved first if cleaner.

Phase C — generic finite two-separated counting lemma:
  Add a reusable Nat/Finset theorem, preferably in the new module unless a
  more general existing home is clearly better.

  Target shape:

    theorem finset_card_le_half_window_add_one_of_twoSeparated
        (T : Finset ℕ)
        (hwindow : ∀ m ∈ T, lo ≤ m ∧ m ≤ hi)
        (hsep :
          ∀ a ∈ T, ∀ b ∈ T, a < b -> a + 2 ≤ b) :
        T.card ≤ (hi - lo) / 2 + 1

  Search Mathlib for an existing sorted-list / pairwise-gap cardinality lemma.
  If none is suitable, prove it by:
    - sorting T into an increasing list;
    - showing the i-th entry is at least lo + 2*i;
    - comparing the final entry with hi.

  Keep this lemma reusable and independent of pressure terminology.

Phase D — sharp canonical packing bound:
  Apply Phase C to the image of canonicalSeparator.

  Prove:

    theorem sourcePressureFiniteWindowPackingUnit_card_le_half_window_add_one
        (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
        (S : Finset (SourcePressureFiniteWindowPackingUnit L lo hi)) :
        S.card ≤ (hi - lo) / 2 + 1

  Use:
    canonicalSeparator_injective_of_sorted
    canonicalSeparator_in_window
    canonicalSeparator_two_separated_of_ne_of_sorted

  This is the first genuine packing-density theorem.

Phase E — sign-restricted image:
  Define the finite set of nonpositive positions in the window:

    def sourcePressureNonposPositionsInWindow
        (n : OddNat) (k lo hi : ℕ) : Finset ℕ :=
      (Finset.Icc lo hi).filter
        (fun m => SourcePressureMarginInt n k m ≤ 0)

  Add the required Decidable instances locally/classically if needed.

  Prove:

    (S.image canonicalSeparator) ⊆
      sourcePressureNonposPositionsInWindow n k lo hi

  Then prove:

    S.card ≤
      (sourcePressureNonposPositionsInWindow n k lo hi).card

  This should coexist with the sharper half-window bound:
    - sign bound connects counting to pressure distribution;
    - two-spacing bound gives the geometric density constraint.

Phase F — extract the canonical family from L:
  Do not leave the theorem dependent only on an arbitrary caller-supplied S.

  Define a canonical finite collection representing all oriented adjacent pairs
  in L that carry a canonical finite-window packing state.

  Preferred approaches:
    1. a Finset of left/right pair keys filtered from adjacent pairs of L; or
    2. a Finset of left witnesses W for which there exists the unique adjacent
       right witness W' with canonical state.

  Prove uniqueness of the adjacent right witness from list adjacency.

  Package each selected pair as a
    SourcePressureFiniteWindowPackingUnit L lo hi.

  Obtain direct list-facing theorems:

    canonicalPackingFamily.card ≤ (hi - lo) / 2 + 1

    canonicalPackingFamily.card ≤
      card (sourcePressureNonposPositionsInWindow n k lo hi)

Phase G — connect toward positive-center density:
  Investigate the strongest theorem available from the current upstream states:

    BeamSeed
    SortedFailure
    FailureResolution
    ForwardPairComparison

  Determine whether every relevant positive center in a finite window is:
    - the left center of a canonical packing unit;
    - the right endpoint of one;
    - or an uncovered boundary center.

  Formalize the strongest exact decomposition available, for example:

    positive centers in window
      ⊆ left centers of canonical units
         ∪ right boundary residue

  or a branch/state expressing the missing coverage condition.

  From that decomposition, attempt a positive-center cardinality bound with at
  most a constant endpoint correction.

  Continue until either:
    - a direct positive-center density theorem is proved; or
    - one exact missing coverage theorem is isolated as the next mathematical
      obstruction.

Phase H — local Big surface:
  Package the resulting bounds into a named local-Big theorem/state recording:

    number of canonical positive pulses
      ≤ half-window packing capacity

    number of canonical separators
      ≤ number of nonpositive window positions

  The theorem name should expose that this is a finite-window pressure packing
  bound, not merely a Finset utility lemma.

Report the completed route:

  sorted adjacent pairs
    -> multiplicity one
    -> canonical separator injection
    -> canonical separator two-spacing
    -> half-window packing density
    -> sign-restricted packing bound
    -> canonical family extracted from L
    -> positive-center coverage/decomposition
    -> finite local Big.

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check

Record whether the positive-center coverage theorem closed, and if not, record
the exact Lean proposition that remains.
```

## 総合評価

cp-289 は、ここまで積み上げてきた大量の局所 API が初めて **有限個数の上界**として実を結んだ checkpoint じゃ。

```text
局所符号
  -> separator
  -> pair 比較
  -> multiplicity one
  -> 単射
  -> cardinality bound
```

と、証明の種類が変わった。

ここからは separator が「異なる」だけでなく「最低 2 離れる」ことを数え上げへ投入する。次が通れば、

```text
窓幅 N に対し、およそ N/2 個まで
```

という本当の packing density が得られる。

**局所 Big は、いよいよ幅と密度を持つ量になり始めた。**

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 0d93b78f..83a90250 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -660,6 +660,114 @@ theorem sourcePressureAdjacentPairInList_before_of_sorted
               exact hsorted.2
             exact ih htailSorted htail

+/-- Witness-level `Before` gives strict order of singleton depth values. -/
+theorem sourcePressureLocalIslandWitnessBefore_val_lt
+    {n : OddNat} {k r : ℕ}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hbefore : SourcePressureLocalIslandWitnessBefore W W') :
+    W.val < W'.val :=
+  hbefore
+
+/--
+The head value of a sorted explicit witness list is no greater than every
+value occurring in that list.
+
+This small transitive bridge turns recursively adjacent sortedness into the
+non-strict endpoint order needed to compare two addressed adjacent pairs.
+-/
+theorem sourcePressureSortedWitnessList_head_val_le_of_mem
+    {n : OddNat} {k r : ℕ}
+    {A W : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore (A :: rest))
+    (hmem : W ∈ A :: rest) :
+    A.val ≤ W.val := by
+  induction rest generalizing A with
+  | nil =>
+      simp only [List.mem_singleton] at hmem
+      subst W
+      exact le_rfl
+  | cons B rest ih =>
+      rcases List.mem_cons.1 hmem with hWA | hWtail
+      · subst W
+        exact le_rfl
+      · have htailSorted :
+            SourcePressureLocalIslandWitnessListSortedBefore (B :: rest) := by
+          change
+            SourcePressureIntervalPulseAddressFamilySortedBefore
+              (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList
+                (A :: B :: rest)) at hsorted
+          change
+            SourcePressureIntervalPulseAddressFamilySortedBefore
+              (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList
+                (B :: rest))
+          exact hsorted.2
+        have hAB : A.val < B.val :=
+          sourcePressureLocalIslandWitnessBefore_val_lt
+            (sourcePressureAdjacentPairInList_before_of_sorted hsorted
+              SourcePressureLocalIslandWitnessAdjacentPairInList.head)
+        exact le_trans (le_of_lt hAB) (ih htailSorted hWtail)
+
+/--
+Two oriented adjacent pairs in one sorted witness list are equal or occur in
+non-overlapping value order.
+
+The two non-equality branches allow a shared endpoint (`≤`): consecutive
+adjacent pairs may be `(A,B)` and `(B,C)`.  This is the strongest unconditional
+value-level dichotomy supplied by list adjacency and sortedness alone.
+-/
+theorem sourcePressureAdjacentPairs_eq_or_nonoverlap_of_sorted
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W₁ W₁' W₂ W₂' : SourcePressureLocalIslandWitness n k r}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (h₁ : SourcePressureLocalIslandWitnessAdjacentPairInList L W₁ W₁')
+    (h₂ : SourcePressureLocalIslandWitnessAdjacentPairInList L W₂ W₂') :
+    (W₁ = W₂ ∧ W₁' = W₂') ∨
+      W₁'.val ≤ W₂.val ∨
+        W₂'.val ≤ W₁.val := by
+  induction L generalizing W₁ W₁' W₂ W₂' with
+  | nil => exact False.elim h₁
+  | cons A rest ih =>
+      cases rest with
+      | nil => exact False.elim h₁
+      | cons B rest =>
+          have htailSorted :
+              SourcePressureLocalIslandWitnessListSortedBefore (B :: rest) := by
+            change
+              SourcePressureIntervalPulseAddressFamilySortedBefore
+                (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList
+                  (A :: B :: rest)) at hsorted
+            change
+              SourcePressureIntervalPulseAddressFamilySortedBefore
+                (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList
+                  (B :: rest))
+            exact hsorted.2
+          rcases h₁ with h₁head | h₁tail
+          · rcases h₁head with ⟨hW₁, hW₁'⟩
+            subst W₁
+            subst W₁'
+            rcases h₂ with h₂head | h₂tail
+            · rcases h₂head with ⟨hW₂, hW₂'⟩
+              subst W₂
+              subst W₂'
+              exact Or.inl ⟨rfl, rfl⟩
+            · exact Or.inr (Or.inl
+                (sourcePressureSortedWitnessList_head_val_le_of_mem
+                  htailSorted
+                  (sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem
+                    h₂tail)))
+          · rcases h₂ with h₂head | h₂tail
+            · rcases h₂head with ⟨hW₂, hW₂'⟩
+              subst W₂
+              subst W₂'
+              exact Or.inr (Or.inr
+                (sourcePressureSortedWitnessList_head_val_le_of_mem
+                  htailSorted
+                  (sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem
+                    h₁tail)))
+            · exact ih htailSorted h₁tail h₂tail
+
 /--
 Box-facing version of
 `sourcePressureAdjacentPairInList_before_of_sorted`.
@@ -1004,6 +1112,40 @@ def SourcePressureFiniteWindowPackingPairComparisonState
   SourcePressureFiniteWindowPackingSeparatorState L lo hi W₁ W₁' m₁ ∧
     SourcePressureFiniteWindowPackingSeparatorState L lo hi W₂ W₂' m₂

+/-- Finite-window packing state with the canonical left-next separator. -/
+def SourcePressureCanonicalFiniteWindowPackingState
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (lo hi : ℕ)
+    (W W' : SourcePressureLocalIslandWitness n k r) : Prop :=
+  SourcePressureFiniteWindowPackingSeparatorState
+    L lo hi W W' (r + W.val + 1)
+
+/-- Data carrier for finite-family counting of canonical packing units. -/
+structure SourcePressureFiniteWindowPackingUnit
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (lo hi : ℕ) where
+  left : SourcePressureLocalIslandWitness n k r
+  right : SourcePressureLocalIslandWitness n k r
+  state : SourcePressureCanonicalFiniteWindowPackingState L lo hi left right
+
+/-- Canonical separator attached to a finite-window packing unit. -/
+def SourcePressureFiniteWindowPackingUnit.canonicalSeparator
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    (u : SourcePressureFiniteWindowPackingUnit L lo hi) : ℕ :=
+  r + u.left.val + 1
+
+/-- Oriented endpoint key attached to a finite-window packing unit. -/
+def SourcePressureFiniteWindowPackingUnit.pairKey
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    (u : SourcePressureFiniteWindowPackingUnit L lo hi) :=
+  (u.left, u.right)
+
 /-- Project the underlying forward box comparison state. -/
 theorem SourcePressureForwardPairComparisonState.forward
     {n : OddNat} {k r : ℕ}
@@ -1864,6 +2006,15 @@ theorem SourcePressureFiniteWindowPackingSeparatorState.two_le_window_width
   rcases h.window_order_chain with ⟨hlo, hleft, hright, hhi⟩
   omega

+/-- Project the oriented adjacent pair underlying one finite-window packing unit. -/
+theorem SourcePressureFiniteWindowPackingSeparatorState.adjacentPair
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ} {W W' : SourcePressureLocalIslandWitness n k r} {m : ℕ}
+    (h : SourcePressureFiniteWindowPackingSeparatorState L lo hi W W' m) :
+    SourcePressureLocalIslandWitnessAdjacentPairInList L W W' :=
+  h.localPacking.forward.adjacentPair
+
 /-- Project the first finite-window packing unit. -/
 theorem SourcePressureFiniteWindowPackingPairComparisonState.left
     {n : OddNat} {k r : ℕ}
@@ -1888,6 +2039,30 @@ theorem SourcePressureFiniteWindowPackingPairComparisonState.right
     SourcePressureFiniteWindowPackingSeparatorState L lo hi W₂ W₂' m₂ :=
   h.2

+/-- Project the first oriented adjacent pair. -/
+theorem SourcePressureFiniteWindowPackingPairComparisonState.left_adjacentPair
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    {W₁ W₁' : SourcePressureLocalIslandWitness n k r} {m₁ : ℕ}
+    {W₂ W₂' : SourcePressureLocalIslandWitness n k r} {m₂ : ℕ}
+    (h : SourcePressureFiniteWindowPackingPairComparisonState
+      L lo hi W₁ W₁' m₁ W₂ W₂' m₂) :
+    SourcePressureLocalIslandWitnessAdjacentPairInList L W₁ W₁' :=
+  h.left.adjacentPair
+
+/-- Project the second oriented adjacent pair. -/
+theorem SourcePressureFiniteWindowPackingPairComparisonState.right_adjacentPair
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    {W₁ W₁' : SourcePressureLocalIslandWitness n k r} {m₁ : ℕ}
+    {W₂ W₂' : SourcePressureLocalIslandWitness n k r} {m₂ : ℕ}
+    (h : SourcePressureFiniteWindowPackingPairComparisonState
+      L lo hi W₁ W₁' m₁ W₂ W₂' m₂) :
+    SourcePressureLocalIslandWitnessAdjacentPairInList L W₂ W₂' :=
+  h.right.adjacentPair
+
 /-- Ordered chain consumed by the first packing unit. -/
 theorem SourcePressureFiniteWindowPackingPairComparisonState.left_order_chain
     {n : OddNat} {k r : ℕ}
@@ -2012,6 +2187,51 @@ theorem SourcePressureFiniteWindowPackingPairComparisonState.shared_separator_cr
   subst m₂
   exact ⟨hleft₁, hleft₂, hright₁, hright₂⟩

+/--
+In a sorted witness list, one separator serves at most one oriented adjacent
+pair.
+
+If the adjacent pairs were distinct, sorted adjacency places one pair wholly
+to one side of the other.  A shared strict interior point contradicts either
+non-overlap order, so the two oriented pairs must coincide.
+-/
+theorem SourcePressureFiniteWindowPackingPairComparisonState.same_pair_of_shared_separator_of_sorted
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    {W₁ W₁' : SourcePressureLocalIslandWitness n k r} {m₁ : ℕ}
+    {W₂ W₂' : SourcePressureLocalIslandWitness n k r} {m₂ : ℕ}
+    (h : SourcePressureFiniteWindowPackingPairComparisonState
+      L lo hi W₁ W₁' m₁ W₂ W₂' m₂)
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (hsep : m₁ = m₂) :
+    W₁ = W₂ ∧ W₁' = W₂' := by
+  rcases sourcePressureAdjacentPairs_eq_or_nonoverlap_of_sorted
+      hsorted h.left_adjacentPair h.right_adjacentPair with hpairs | horder
+  · exact hpairs
+  · rcases h.shared_separator_cross_surface hsep with
+      ⟨hleft₁, hleft₂, hright₁, hright₂⟩
+    rcases horder with h₁₂ | h₂₁
+    · exfalso
+      omega
+    · exfalso
+      omega
+
+/-- Distinct oriented adjacent pairs have distinct separators in a sorted list. -/
+theorem SourcePressureFiniteWindowPackingPairComparisonState.separators_ne_of_pairs_ne_of_sorted
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    {W₁ W₁' : SourcePressureLocalIslandWitness n k r} {m₁ : ℕ}
+    {W₂ W₂' : SourcePressureLocalIslandWitness n k r} {m₂ : ℕ}
+    (h : SourcePressureFiniteWindowPackingPairComparisonState
+      L lo hi W₁ W₁' m₁ W₂ W₂' m₂)
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (hpairs : ¬ (W₁ = W₂ ∧ W₁' = W₂')) :
+    m₁ ≠ m₂ := by
+  intro hsep
+  exact hpairs (h.same_pair_of_shared_separator_of_sorted hsorted hsep)
+
 /-- Distinct separators have a strict order in the finite window. -/
 theorem SourcePressureFiniteWindowPackingPairComparisonState.separator_lt_or_gt
     {n : OddNat} {k r : ℕ}
@@ -2043,6 +2263,161 @@ theorem SourcePressureFiniteWindowPackingSeparatorState.two_le_index_gap
     r + W.val + 2 ≤ r + W'.val :=
   h.localPacking.two_le_index_gap

+/-- Project the underlying finite-window separator state from the canonical form. -/
+theorem SourcePressureCanonicalFiniteWindowPackingState.finiteWindow
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ} {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureCanonicalFiniteWindowPackingState L lo hi W W') :
+    SourcePressureFiniteWindowPackingSeparatorState
+      L lo hi W W' (r + W.val + 1) :=
+  h
+
+/-- The canonical left-next separator has nonpositive pressure margin. -/
+theorem SourcePressureCanonicalFiniteWindowPackingState.separator_nonpos
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ} {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureCanonicalFiniteWindowPackingState L lo hi W W') :
+    SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 :=
+  h.finiteWindow.localPacking.separator_nonpos
+
+/-- The canonical separator lies strictly between the two positive centers. -/
+theorem SourcePressureCanonicalFiniteWindowPackingState.separator_between_centers
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ} {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureCanonicalFiniteWindowPackingState L lo hi W W') :
+    r + W.val < r + W.val + 1 ∧
+      r + W.val + 1 < r + W'.val :=
+  ⟨by omega, h.finiteWindow.localPacking.separator_lt_right⟩
+
+/-- The canonical separator lies in the finite window. -/
+theorem SourcePressureCanonicalFiniteWindowPackingState.separator_in_window
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ} {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureCanonicalFiniteWindowPackingState L lo hi W W') :
+    lo ≤ r + W.val + 1 ∧ r + W.val + 1 ≤ hi :=
+  h.finiteWindow.separator_in_window
+
+/-- The oriented adjacent pair carried by the canonical packing state. -/
+theorem SourcePressureCanonicalFiniteWindowPackingState.adjacentPair
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ} {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureCanonicalFiniteWindowPackingState L lo hi W W') :
+    SourcePressureLocalIslandWitnessAdjacentPairInList L W W' :=
+  h.finiteWindow.adjacentPair
+
+/--
+Build the canonical finite-window state from a forward pair and explicit center
+bounds.  The canonical separator is the left next boundary.
+-/
+theorem SourcePressureForwardPairComparisonState.to_canonicalFiniteWindowPackingState
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ} {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W')
+    (hlo : lo ≤ r + W.val) (hhi : r + W'.val ≤ hi) :
+    SourcePressureCanonicalFiniteWindowPackingState L lo hi W W' := by
+  rcases h.left_next_interference_surface with
+    ⟨_hcenterL, hnonpos, _hcenterR, hbetween⟩
+  exact ⟨⟨h, by omega, hbetween, hnonpos⟩, hlo, hhi⟩
+
+/-- The unit's canonical separator lies in its finite window. -/
+theorem SourcePressureFiniteWindowPackingUnit.canonicalSeparator_in_window
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    (u : SourcePressureFiniteWindowPackingUnit L lo hi) :
+    lo ≤ u.canonicalSeparator ∧ u.canonicalSeparator ≤ hi :=
+  u.state.separator_in_window
+
+/-- Distinct pair keys give distinct canonical separators under sortedness. -/
+theorem SourcePressureFiniteWindowPackingUnit.canonicalSeparator_ne_of_pairKey_ne_of_sorted
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    {u₁ u₂ : SourcePressureFiniteWindowPackingUnit L lo hi}
+    (hpairs : u₁.pairKey ≠ u₂.pairKey) :
+    u₁.canonicalSeparator ≠ u₂.canonicalSeparator := by
+  have hcomparison :
+      SourcePressureFiniteWindowPackingPairComparisonState
+        L lo hi u₁.left u₁.right u₁.canonicalSeparator
+          u₂.left u₂.right u₂.canonicalSeparator :=
+    ⟨u₁.state, u₂.state⟩
+  apply hcomparison.separators_ne_of_pairs_ne_of_sorted hsorted
+  intro hp
+  apply hpairs
+  rcases hp with ⟨hleft, hright⟩
+  simp [SourcePressureFiniteWindowPackingUnit.pairKey, hleft, hright]
+
+/-- Canonical separators are injective on packing units in a sorted list. -/
+theorem SourcePressureFiniteWindowPackingUnit.canonicalSeparator_injective_of_sorted
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    Function.Injective
+      (SourcePressureFiniteWindowPackingUnit.canonicalSeparator
+        (L := L) (lo := lo) (hi := hi)) := by
+  intro u₁ u₂ hsep
+  have hcomparison :
+      SourcePressureFiniteWindowPackingPairComparisonState
+        L lo hi u₁.left u₁.right u₁.canonicalSeparator
+          u₂.left u₂.right u₂.canonicalSeparator :=
+    ⟨u₁.state, u₂.state⟩
+  rcases hcomparison.same_pair_of_shared_separator_of_sorted hsorted hsep with
+    ⟨hleft, hright⟩
+  cases u₁
+  cases u₂
+  simp_all
+
+/--
+Finite-window packing bound obtained from canonical-separator injection.
+
+Every unit maps injectively to a natural-number separator in `[lo, hi]`, so a
+finite family contains at most `hi + 1 - lo` units.
+-/
+theorem sourcePressureFiniteWindowPackingUnit_card_le_window_card
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (S : Finset (SourcePressureFiniteWindowPackingUnit L lo hi)) :
+    S.card ≤ hi + 1 - lo := by
+  classical
+  let f := SourcePressureFiniteWindowPackingUnit.canonicalSeparator
+    (L := L) (lo := lo) (hi := hi)
+  have hinj : Function.Injective f :=
+    SourcePressureFiniteWindowPackingUnit.canonicalSeparator_injective_of_sorted
+      hsorted
+  have hcard : (S.image f).card = S.card :=
+    Finset.card_image_iff.mpr hinj.injOn
+  have hsubset : S.image f ⊆ Finset.Icc lo hi := by
+    intro m hm
+    rcases Finset.mem_image.1 hm with ⟨u, hu, rfl⟩
+    exact Finset.mem_Icc.2 u.canonicalSeparator_in_window
+  rw [← hcard]
+  exact (Finset.card_le_card hsubset).trans_eq (Nat.card_Icc lo hi)
+
+/-- Nonempty-family form using the conventional window-width expression. -/
+theorem sourcePressureFiniteWindowPackingUnit_card_le_window_width_add_one
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (S : Finset (SourcePressureFiniteWindowPackingUnit L lo hi))
+    (hS : S.Nonempty) :
+    S.card ≤ hi - lo + 1 := by
+  rcases hS with ⟨u, hu⟩
+  have hwindow := u.canonicalSeparator_in_window
+  have hbound := sourcePressureFiniteWindowPackingUnit_card_le_window_card
+    hsorted S
+  omega
+
 /--
 Constructor from a local packing separator to the finite-window carrier under
 explicit bounds on the two positive centers.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-289.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-289.md
new file mode 100644
index 00000000..37dac428
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-289.md
@@ -0,0 +1,154 @@
+# Report: petal-289
+
+## Goal
+
+Turn the pairwise separator comparison into a genuine multiplicity theorem,
+canonicalize separators, and continue through the first finite-family packing
+bound.
+
+## Ordered Adjacent-Pair Bridge
+
+Added:
+
+- `sourcePressureLocalIslandWitnessBefore_val_lt`
+- `sourcePressureSortedWitnessList_head_val_le_of_mem`
+- `sourcePressureAdjacentPairs_eq_or_nonoverlap_of_sorted`
+
+For two oriented adjacent pairs in one sorted witness list, Lean proves:
+
+```text
+same oriented pair
+  OR right₁ <= left₂
+  OR right₂ <= left₁
+```
+
+The weak endpoint inequalities are exact: consecutive pairs may share one
+witness endpoint.
+
+## Multiplicity One
+
+Added adjacent-pair projections from both finite-window carriers, then proved:
+
+- `SourcePressureFiniteWindowPackingPairComparisonState.same_pair_of_shared_separator_of_sorted`
+- `SourcePressureFiniteWindowPackingPairComparisonState.separators_ne_of_pairs_ne_of_sorted`
+
+The established equivalence direction is:
+
+```text
+shared separator + sorted list
+  -> same oriented adjacent pair
+
+distinct oriented adjacent pairs + sorted list
+  -> distinct separators
+```
+
+Thus one separator has multiplicity at most one among oriented adjacent-pair
+packing units in a sorted witness list.
+
+## Canonical Packing
+
+Added:
+
+- `SourcePressureCanonicalFiniteWindowPackingState`
+- `.finiteWindow`
+- `.separator_nonpos`
+- `.separator_between_centers`
+- `.separator_in_window`
+- `.adjacentPair`
+- `SourcePressureForwardPairComparisonState.to_canonicalFiniteWindowPackingState`
+
+The canonical separator is:
+
+```lean
+r + W.val + 1
+```
+
+It is nonpositive, lies strictly between the positive centers, and belongs to
+the same finite window.
+
+## Finite-Family Carrier And Injection
+
+Added:
+
+- `SourcePressureFiniteWindowPackingUnit`
+- `SourcePressureFiniteWindowPackingUnit.canonicalSeparator`
+- `SourcePressureFiniteWindowPackingUnit.pairKey`
+- `.canonicalSeparator_in_window`
+- `.canonicalSeparator_ne_of_pairKey_ne_of_sorted`
+- `.canonicalSeparator_injective_of_sorted`
+
+The unit structure packages an oriented pair with its canonical finite-window
+state.  Under sortedness, canonical separator is injective on the full unit
+type, not merely on a chosen family.
+
+## Finite-Window Packing Bound
+
+Added:
+
+- `sourcePressureFiniteWindowPackingUnit_card_le_window_card`
+- `sourcePressureFiniteWindowPackingUnit_card_le_window_width_add_one`
+
+For every finite family `S` of canonical packing units:
+
+```lean
+S.card <= hi + 1 - lo
+```
+
+For a nonempty family, the conventional form is also available:
+
+```lean
+S.card <= hi - lo + 1
+```
+
+The proof maps every unit injectively to its canonical separator in
+`Finset.Icc lo hi` and applies `Nat.card_Icc`.
+
+## Established Route
+
+```text
+two packing units
+  -> adjacent-pair order dichotomy
+  -> shared separator forces same oriented pair
+  -> distinct pairs have distinct canonical separators
+  -> separator injection on finite families
+  -> card units <= card [lo, hi]
+  -> finite-window packing bound
+  -> local Big
+```
+
+This checkpoint reaches the first actual counting theorem.  Separator reuse is
+not carried as an assumed multiplicity bound: sorted adjacency proves its
+multiplicity is one.
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
+No `sorry` was introduced.
+
+## Refactoring Status
+
+The finite-window API is now large enough to extract mechanically into
+`PressureState/FiniteWindowPacking.lean`.  The source TODO remains authoritative.
+The move should be a dedicated checkpoint because the current theorem chain is
+stable and fully built.
+
+## Next Branch Prediction
+
+The current bound counts packing units by all separator positions.  The next
+mathematical strengthening is to count only nonpositive separator positions:
+
+```text
+card packing units
+  <= card {m in [lo, hi] | margin(m) <= 0}
+  <= hi + 1 - lo
+```
+
+This refined image theorem would connect packing density directly to the sign
+distribution inside the finite window.
````
`````
