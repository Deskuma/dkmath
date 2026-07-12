# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 68436fff4612ed474f3a7d8ab28c34f277ffbf25

## Report

cp-288 を完了しました。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean#L996) に二つの packing unit を比較する `SourcePressureFiniteWindowPackingPairComparisonState` を追加しました。

Lean により次が確定しています。

- separator は `m₁ = m₂ ∨ m₁ ≠ m₂` に分岐する。
- 同一の場合、共通 separator は両方の中心区間内部にある。
- 異なる場合、`m₁ < m₂ ∨ m₂ < m₁` と厳密に順序付けられる。
- どちらの branch でも完全な有限窓順序鎖が保持される。

```text
lo ≤ leftCenterᵢ < mᵢ < rightCenterᵢ ≤ hi
```

これで separator 再利用は「二つの開中心区間が共通点を持つ」という具体的な交差現象になりました。次は、この共通点を持てる pair 数の上限、または有限 family 上の bounded multiplicity を定式化する段階です。

肥大化対策として、安定後に `PressureState/FiniteWindowPacking.lean` へ機械的に移設する TODO もソースコメントへ記録しました。

結果は [report-petal-288.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-288.md) にまとめています。

検証済み：

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

## Review

## 判定

採用。
しかも今回は、Codex 側の推論力が一段上がった様子がはっきり出ておる。

指示した基本項目だけでなく、

```lean
SourcePressureFiniteWindowPackingPairComparisonState.shared_separator_cross_surface
SourcePressureFiniteWindowPackingPairComparisonState.separator_lt_or_gt
```

まで自発的に追加した。

すなわち、単なる

```text
m₁ = m₂ ∨ m₁ ≠ m₂
```

で止まらず、

```text
同一 separator
  -> 二つの開中心区間の共通内点

異なる separator
  -> m₁ < m₂ ∨ m₂ < m₁
```

まで進んでいる。これは前回より明確に **「指示されたコードを書く」から「次の数学的構造を読む」へ進歩した** と見てよい。

## 今回固定された構造

新しい carrier は、

```lean
SourcePressureFiniteWindowPackingPairComparisonState
```

であり、同じ有限窓 `[lo, hi]` にある二つの packing unit を保持する。

各 unit は、

```text
lo ≤ leftCenterᵢ < mᵢ < rightCenterᵢ ≤ hi
```

という完全な順序鎖を持つ。

その上で、separator 関係が二分された。

```text
reuse branch:
  m₁ = m₂

distinct branch:
  m₁ ≠ m₂
```

reuse branch ではさらに、

```text
leftCenter₁ < m₁ < rightCenter₁
leftCenter₂ < m₁ < rightCenter₂
```

が得られた。

つまり共通 separator は、二つの中心区間の **明示的な共通内点** じゃ。

## 改善された指示の進展評価

今回の長距離指示は、かなり良く機能した。

以前の進行：

```text
一つの state
  -> projection
  -> projection
  -> surface
```

今回の進行：

```text
一つの packing unit
  -> 二つの packing unit の比較 carrier
  -> separator reuse 分岐
  -> 共通点幾何
  -> distinct separator の厳密順序
  -> multiplicity 問題の入口
```

これは **単発 API 追加ではなく、数え上げに必要な二体問題を立てた** という進展じゃ。

Codex はさらに、

```text
共通 separator を含める pair 数の上限
有限 family における bounded multiplicity
```

を次の問題として自力で認識している。
この先読みはよい。GPT-5.6 Sol への更新効果を実装結果だけから評価するなら、少なくとも今回の応答では、以前より能動的である。

## ただし、本当の難所はここから

現在の

```lean
m₁ = m₂
```

から得られたのは、二つの開区間が交差することまでじゃ。

一般の区間族なら、一つの点を含む区間は何本でも作れる。

たとえば抽象的には、

```text
(1, 100)
(2, 99)
(3, 98)
...
```

は同じ一点を大量に共有できる。

したがって、

```text
shared separator
  -> multiplicity bounded
```

は、現在の順序不等式だけからは出ない。

ここで使うべき DkMath 固有の追加構造は、

```text
各中心対が同じ sorted list L の隣接 pair である
```

という事実じゃ。

`ForwardPairComparisonState` の内部には、

```lean
SourcePressureLocalIslandWitnessAdjacentPairInList L W W'
```

がある。

よって本命は、separator 自体をさらに比較することではなく、

```text
同じ sorted list 内の二つの隣接 pair は、
同一 pair か、順序付きで非重複か
```

を証明することじゃ。

## 次の核心定理

狙うべき中心補題は、概念的にはこれ。

```lean
theorem sourcePressureAdjacentPairs_eq_or_nonoverlap_of_sorted
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
    (h₁ : SourcePressureLocalIslandWitnessAdjacentPairInList L W₁ W₁')
    (h₂ : SourcePressureLocalIslandWitnessAdjacentPairInList L W₂ W₂') :
    (W₁ = W₂ ∧ W₁' = W₂') ∨
      W₁'.val ≤ W₂.val ∨
        W₂'.val ≤ W₁.val
```

意味は、

```text
同じ oriented adjacent pair
または
第一 pair が第二 pair より前
または
第二 pair が第一 pair より前
```

じゃ。

これが出れば、共通 separator を持つ場合には非重複 branch が矛盾する。

第一 pair が先なら、

```text
m < rightCenter₁ ≤ leftCenter₂ < m
```

となる。

逆向きも同様。

したがって、

```text
共通 separator
  -> 同じ adjacent pair
```

が言える。

これこそ、separator multiplicity の核心じゃ。

## 一歩先の推論

しかし、さらに一つ構造上の問題がある。

現在の `LocalPackingSeparatorState` は任意の separator `m` を保持できる。
同じ center pair の区間内に非正点が複数あれば、

```text
同じ pair
異なる separator
```

という複数の packing unit が作れる可能性がある。

よって有限 counting へ進むには、次のどちらかが必要になる。

1. 同じ pair に対する separator を標準化する。
2. 同じ pair に属する複数 separator を同値類として一単位に数える。

この系列では既に、

```lean
m := r + W.val + 1
```

という左中心直後の非正 separator が構成可能だった。

したがって、最も鋭い道は **canonical separator** を採用することじゃ。

```lean
def SourcePressureCanonicalFiniteWindowPackingState
    ...
    (W W' : Witness) : Prop :=
  SourcePressureFiniteWindowPackingSeparatorState
    L lo hi W W' (r + W.val + 1)
```

これなら separator は左 center から一意に決まる。

```text
canonicalSeparator(W) = r + W.val + 1
```

したがって、異なる oriented pair の separator injection を作りやすい。

## 次の Codex 指示

今回は難易度をさらに一段上げる。
単なる `separator_eq` 補題ではなく、**隣接 pair の非交差性から canonical separator injection、可能なら有限 family counting まで** を一つの checkpoint にする。

```text
Goal:
  Move from pairwise separator comparison to the first genuine multiplicity
  theorem.

  Use the fact that every packing unit comes from an oriented adjacent pair in
  the same sorted witness list.  The main target is:

    shared separator
      -> same oriented adjacent pair

  Then introduce a canonical separator for each oriented pair and use it toward
  a finite-family injection/counting theorem.

Phase A — expose the adjacent-pair payload:
  Add projections from
    SourcePressureFiniteWindowPackingSeparatorState
  and
    SourcePressureFiniteWindowPackingPairComparisonState
  to the underlying

    SourcePressureLocalIslandWitnessAdjacentPairInList L W W'

  Reuse:
    localPacking.forward.adjacentPair

Phase B — prove the ordered adjacent-pair dichotomy:
  Inspect existing List adjacency and sorted-before lemmas.

  Prove the strongest available theorem of the form:

    theorem sourcePressureAdjacentPairs_eq_or_nonoverlap_of_sorted
        {n : OddNat} {k r : ℕ}
        {L : List (SourcePressureLocalIslandWitness n k r)}
        {W₁ W₁' W₂ W₂' :
          SourcePressureLocalIslandWitness n k r}
        (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
        (h₁ :
          SourcePressureLocalIslandWitnessAdjacentPairInList L W₁ W₁')
        (h₂ :
          SourcePressureLocalIslandWitnessAdjacentPairInList L W₂ W₂') :
        (W₁ = W₂ ∧ W₁' = W₂') ∨
          W₁'.val ≤ W₂.val ∨
            W₂'.val ≤ W₁.val

  The exact non-overlap relation may use witness-before or address-before
  instead of raw value inequalities.  Use the strongest existing relation and
  derive the value form afterward.

Branch handling:
  - If the theorem follows from existing List adjacency lemmas, prove it.
  - If one list-order lemma is missing, add that reusable lower-level lemma.
  - If strict sortedness is not sufficient because the current state no longer
    carries it, accept `hsorted` as an explicit theorem hypothesis or define a
    sorted pair-comparison carrier.

Phase C — shared separator forces pair identity:
  Prove:

    theorem SourcePressureFiniteWindowPackingPairComparisonState
        .same_pair_of_shared_separator_of_sorted
        ...
        (h :
          SourcePressureFiniteWindowPackingPairComparisonState
            L lo hi W₁ W₁' m₁ W₂ W₂' m₂)
        (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
        (hsep : m₁ = m₂) :
        W₁ = W₂ ∧ W₁' = W₂'

  Use:
    h.shared_separator_cross_surface hsep
    the adjacent-pair equality/non-overlap dichotomy

  In either non-overlap branch, combine the common interior point inequalities
  with the endpoint order and close the contradiction with omega.

Phase D — add the distinct-pair consequence:
  Prove the contrapositive-facing theorem:

    theorem SourcePressureFiniteWindowPackingPairComparisonState
        .separators_ne_of_pairs_ne_of_sorted
        ...
        (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
        (hpairs :
          ¬ (W₁ = W₂ ∧ W₁' = W₂')) :
        m₁ ≠ m₂

  This is the first actual separator multiplicity theorem:
  one separator cannot serve two distinct oriented adjacent pairs.

Phase E — canonicalize the packing unit:
  Define a canonical finite-window packing state whose separator is

    r + W.val + 1

  Suggested definition:

    def SourcePressureCanonicalFiniteWindowPackingState
        {n : OddNat} {k r : ℕ}
        (L : List (SourcePressureLocalIslandWitness n k r))
        (lo hi : ℕ)
        (W W' : SourcePressureLocalIslandWitness n k r) : Prop :=
      SourcePressureFiniteWindowPackingSeparatorState
        L lo hi W W' (r + W.val + 1)

  Add:
    - canonical separator nonpositive
    - canonical separator strictly between centers
    - canonical separator in window
    - constructor from FPC plus explicit window bounds

Phase F — attempt the first finite-family counting carrier:
  If Phases A–E close, define a data carrier suitable for Finset counting:

    structure SourcePressureFiniteWindowPackingUnit
        {n : OddNat} {k r : ℕ}
        (L : List (SourcePressureLocalIslandWitness n k r))
        (lo hi : ℕ) where
      left  : SourcePressureLocalIslandWitness n k r
      right : SourcePressureLocalIslandWitness n k r
      state :
        SourcePressureCanonicalFiniteWindowPackingState
          L lo hi left right

  Define:
    canonicalSeparator unit := r + unit.left.val + 1
    pairKey unit := (unit.left, unit.right)

  Prove, under sortedness:

    pairKey u₁ ≠ pairKey u₂
      -> canonicalSeparator u₁ ≠ canonicalSeparator u₂

  If a Finset family is available, continue to an injection/cardinality result:

    card units ≤ hi - lo + 1

  or the strongest clean finite-window bound Lean permits from the separator
  injection and separator-in-window theorem.

Phase G — report the actual route:
  Record:

    two packing units
      -> adjacent-pair order dichotomy
      -> shared separator forces same pair
      -> distinct pairs have distinct canonical separators
      -> separator injection for a finite family
      -> finite-window packing bound
      -> local Big.

  This checkpoint should advance as far through these phases as the existing
  APIs permit.  If a phase is blocked, identify the exact missing theorem,
  implement the smallest reusable bridge, and continue to the next reachable
  phase rather than stopping after the first small result.

After the mathematical checkpoint stabilizes:
  mechanically extract the finite-window packing API into
  PressureState/FiniteWindowPacking.lean if the move remains straightforward.

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 賢狼が試してほしい実験補題

最も価値が高い実験はこれじゃ。

```lean
example
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
    (h₁ : SourcePressureLocalIslandWitnessAdjacentPairInList L W₁ W₁')
    (h₂ : SourcePressureLocalIslandWitnessAdjacentPairInList L W₂ W₂')
    (hm₁L : r + W₁.val < m)
    (hm₁R : m < r + W₁'.val)
    (hm₂L : r + W₂.val < m)
    (hm₂R : m < r + W₂'.val) :
    W₁ = W₂ ∧ W₁' = W₂' := by
  ...
```

これが通れば、separator multiplicity は一気に **1** まで落ちる可能性が高い。

## 総合評価

cp-288 はよい。
単なる二体 carrier にとどまらず、共通 separator を「区間交差」と読んだところまで Codex が自力で進めた。

次はその交差に、DkMath が既に持つ

```text
sorted list
adjacent pair
oriented value order
```

をぶつける。

ここが通れば、

```text
一つの separator は一つの oriented adjacent pair にしか属せない
```

という初の本格的 multiplicity bound になる。

そこから有限 family の injection と packing count へ進める。今回こそ、local Big の数え上げ層が本当に始まるところじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 9b922793..0d93b78f 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -978,6 +978,32 @@ def SourcePressureFiniteWindowPackingSeparatorState
     lo ≤ r + W.val ∧
       r + W'.val ≤ hi
 
+/--
+Comparison carrier for two finite-window packing units in the same window.
+
+The carrier intentionally assumes no relation between the two separators.
+Its first job is to expose separator reuse as the explicit branch
+`m₁ = m₂ ∨ m₁ ≠ m₂`; later counting layers may refine either branch with an
+injectivity, disjointness, or bounded-multiplicity invariant.
+
+TODO(refactor): `PressureState.lean` now exceeds the package's preferred file
+size.  Once this comparison API stabilizes, move the finite-window packing
+definitions and theorems together into
+`DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking`, preserving this
+module as the public re-export boundary.  Keep the move mechanical and separate
+from theorem strengthening so future agents can verify import changes locally.
+-/
+def SourcePressureFiniteWindowPackingPairComparisonState
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (lo hi : ℕ)
+    (W₁ W₁' : SourcePressureLocalIslandWitness n k r)
+    (m₁ : ℕ)
+    (W₂ W₂' : SourcePressureLocalIslandWitness n k r)
+    (m₂ : ℕ) : Prop :=
+  SourcePressureFiniteWindowPackingSeparatorState L lo hi W₁ W₁' m₁ ∧
+    SourcePressureFiniteWindowPackingSeparatorState L lo hi W₂ W₂' m₂
+
 /-- Project the underlying forward box comparison state. -/
 theorem SourcePressureForwardPairComparisonState.forward
     {n : OddNat} {k r : ℕ}
@@ -1838,6 +1864,167 @@ theorem SourcePressureFiniteWindowPackingSeparatorState.two_le_window_width
   rcases h.window_order_chain with ⟨hlo, hleft, hright, hhi⟩
   omega
 
+/-- Project the first finite-window packing unit. -/
+theorem SourcePressureFiniteWindowPackingPairComparisonState.left
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    {W₁ W₁' : SourcePressureLocalIslandWitness n k r} {m₁ : ℕ}
+    {W₂ W₂' : SourcePressureLocalIslandWitness n k r} {m₂ : ℕ}
+    (h : SourcePressureFiniteWindowPackingPairComparisonState
+      L lo hi W₁ W₁' m₁ W₂ W₂' m₂) :
+    SourcePressureFiniteWindowPackingSeparatorState L lo hi W₁ W₁' m₁ :=
+  h.1
+
+/-- Project the second finite-window packing unit. -/
+theorem SourcePressureFiniteWindowPackingPairComparisonState.right
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    {W₁ W₁' : SourcePressureLocalIslandWitness n k r} {m₁ : ℕ}
+    {W₂ W₂' : SourcePressureLocalIslandWitness n k r} {m₂ : ℕ}
+    (h : SourcePressureFiniteWindowPackingPairComparisonState
+      L lo hi W₁ W₁' m₁ W₂ W₂' m₂) :
+    SourcePressureFiniteWindowPackingSeparatorState L lo hi W₂ W₂' m₂ :=
+  h.2
+
+/-- Ordered chain consumed by the first packing unit. -/
+theorem SourcePressureFiniteWindowPackingPairComparisonState.left_order_chain
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    {W₁ W₁' : SourcePressureLocalIslandWitness n k r} {m₁ : ℕ}
+    {W₂ W₂' : SourcePressureLocalIslandWitness n k r} {m₂ : ℕ}
+    (h : SourcePressureFiniteWindowPackingPairComparisonState
+      L lo hi W₁ W₁' m₁ W₂ W₂' m₂) :
+    lo ≤ r + W₁.val ∧
+      r + W₁.val < m₁ ∧
+        m₁ < r + W₁'.val ∧
+          r + W₁'.val ≤ hi :=
+  h.left.window_order_chain
+
+/-- Ordered chain consumed by the second packing unit. -/
+theorem SourcePressureFiniteWindowPackingPairComparisonState.right_order_chain
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    {W₁ W₁' : SourcePressureLocalIslandWitness n k r} {m₁ : ℕ}
+    {W₂ W₂' : SourcePressureLocalIslandWitness n k r} {m₂ : ℕ}
+    (h : SourcePressureFiniteWindowPackingPairComparisonState
+      L lo hi W₁ W₁' m₁ W₂ W₂' m₂) :
+    lo ≤ r + W₂.val ∧
+      r + W₂.val < m₂ ∧
+        m₂ < r + W₂'.val ∧
+          r + W₂'.val ≤ hi :=
+  h.right.window_order_chain
+
+/-- The common window is wide enough for the first packing unit. -/
+theorem SourcePressureFiniteWindowPackingPairComparisonState.left_window_width
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    {W₁ W₁' : SourcePressureLocalIslandWitness n k r} {m₁ : ℕ}
+    {W₂ W₂' : SourcePressureLocalIslandWitness n k r} {m₂ : ℕ}
+    (h : SourcePressureFiniteWindowPackingPairComparisonState
+      L lo hi W₁ W₁' m₁ W₂ W₂' m₂) :
+    lo + 2 ≤ hi :=
+  h.left.two_le_window_width
+
+/-- The common window is wide enough for the second packing unit. -/
+theorem SourcePressureFiniteWindowPackingPairComparisonState.right_window_width
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    {W₁ W₁' : SourcePressureLocalIslandWitness n k r} {m₁ : ℕ}
+    {W₂ W₂' : SourcePressureLocalIslandWitness n k r} {m₂ : ℕ}
+    (h : SourcePressureFiniteWindowPackingPairComparisonState
+      L lo hi W₁ W₁' m₁ W₂ W₂' m₂) :
+    lo + 2 ≤ hi :=
+  h.right.two_le_window_width
+
+/-- Two packing units either reuse their separator or use distinct separators. -/
+theorem SourcePressureFiniteWindowPackingPairComparisonState.separator_eq_or_ne
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    {W₁ W₁' : SourcePressureLocalIslandWitness n k r} {m₁ : ℕ}
+    {W₂ W₂' : SourcePressureLocalIslandWitness n k r} {m₂ : ℕ}
+    (_h : SourcePressureFiniteWindowPackingPairComparisonState
+      L lo hi W₁ W₁' m₁ W₂ W₂' m₂) :
+    m₁ = m₂ ∨ m₁ ≠ m₂ :=
+  eq_or_ne m₁ m₂
+
+/-- Shared-separator branch with both finite-window order chains exposed. -/
+theorem SourcePressureFiniteWindowPackingPairComparisonState.separator_eq_surface
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    {W₁ W₁' : SourcePressureLocalIslandWitness n k r} {m₁ : ℕ}
+    {W₂ W₂' : SourcePressureLocalIslandWitness n k r} {m₂ : ℕ}
+    (h : SourcePressureFiniteWindowPackingPairComparisonState
+      L lo hi W₁ W₁' m₁ W₂ W₂' m₂)
+    (hsep : m₁ = m₂) :
+    m₁ = m₂ ∧
+      (lo ≤ r + W₁.val ∧ r + W₁.val < m₁ ∧
+        m₁ < r + W₁'.val ∧ r + W₁'.val ≤ hi) ∧
+      (lo ≤ r + W₂.val ∧ r + W₂.val < m₂ ∧
+        m₂ < r + W₂'.val ∧ r + W₂'.val ≤ hi) :=
+  ⟨hsep, h.left_order_chain, h.right_order_chain⟩
+
+/-- Distinct-separator branch with both finite-window order chains exposed. -/
+theorem SourcePressureFiniteWindowPackingPairComparisonState.separator_ne_surface
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    {W₁ W₁' : SourcePressureLocalIslandWitness n k r} {m₁ : ℕ}
+    {W₂ W₂' : SourcePressureLocalIslandWitness n k r} {m₂ : ℕ}
+    (h : SourcePressureFiniteWindowPackingPairComparisonState
+      L lo hi W₁ W₁' m₁ W₂ W₂' m₂)
+    (hsep : m₁ ≠ m₂) :
+    m₁ ≠ m₂ ∧
+      (lo ≤ r + W₁.val ∧ r + W₁.val < m₁ ∧
+        m₁ < r + W₁'.val ∧ r + W₁'.val ≤ hi) ∧
+      (lo ≤ r + W₂.val ∧ r + W₂.val < m₂ ∧
+        m₂ < r + W₂'.val ∧ r + W₂'.val ≤ hi) :=
+  ⟨hsep, h.left_order_chain, h.right_order_chain⟩
+
+/--
+A reused separator lies strictly between both pairs of positive centers.
+
+This is the concrete geometry of separator reuse: the two consumed open center
+intervals have the shared separator as an explicit common point.
+-/
+theorem SourcePressureFiniteWindowPackingPairComparisonState.shared_separator_cross_surface
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    {W₁ W₁' : SourcePressureLocalIslandWitness n k r} {m₁ : ℕ}
+    {W₂ W₂' : SourcePressureLocalIslandWitness n k r} {m₂ : ℕ}
+    (h : SourcePressureFiniteWindowPackingPairComparisonState
+      L lo hi W₁ W₁' m₁ W₂ W₂' m₂)
+    (hsep : m₁ = m₂) :
+    r + W₁.val < m₁ ∧
+      r + W₂.val < m₁ ∧
+        m₁ < r + W₁'.val ∧
+          m₁ < r + W₂'.val := by
+  rcases h.left_order_chain with ⟨_hlo₁, hleft₁, hright₁, _hhi₁⟩
+  rcases h.right_order_chain with ⟨_hlo₂, hleft₂, hright₂, _hhi₂⟩
+  subst m₂
+  exact ⟨hleft₁, hleft₂, hright₁, hright₂⟩
+
+/-- Distinct separators have a strict order in the finite window. -/
+theorem SourcePressureFiniteWindowPackingPairComparisonState.separator_lt_or_gt
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    {W₁ W₁' : SourcePressureLocalIslandWitness n k r} {m₁ : ℕ}
+    {W₂ W₂' : SourcePressureLocalIslandWitness n k r} {m₂ : ℕ}
+    (_h : SourcePressureFiniteWindowPackingPairComparisonState
+      L lo hi W₁ W₁' m₁ W₂ W₂' m₂)
+    (hsep : m₁ ≠ m₂) :
+    m₁ < m₂ ∨ m₂ < m₁ :=
+  Nat.lt_or_gt_of_ne hsep
+
 /-- Value-level two-step spacing inherited by the finite-window state. -/
 theorem SourcePressureFiniteWindowPackingSeparatorState.two_le_value_gap
     {n : OddNat} {k r : ℕ}
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-288.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-288.md
new file mode 100644
index 00000000..4591da3e
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-288.md
@@ -0,0 +1,115 @@
+# Report: petal-288
+
+## Goal
+
+Move from one finite-window packing unit to the first reusable comparison
+carrier for two units, and expose separator reuse as an explicit branch.
+
+## Implemented
+
+Added:
+
+- `SourcePressureFiniteWindowPackingPairComparisonState`
+
+The state stores two `SourcePressureFiniteWindowPackingSeparatorState` values
+in the same witness list and finite window.
+
+Added basic projections:
+
+- `.left`
+- `.right`
+- `.left_order_chain`
+- `.right_order_chain`
+- `.left_window_width`
+- `.right_window_width`
+
+Added the separator branch point and branch surfaces:
+
+- `.separator_eq_or_ne`
+- `.separator_eq_surface`
+- `.separator_ne_surface`
+
+## Additional Results
+
+Added two consequences inferred from the successful comparison surface:
+
+- `.shared_separator_cross_surface`
+- `.separator_lt_or_gt`
+
+In the reuse branch `m₁ = m₂`, Lean proves that the common separator lies
+strictly inside both open center intervals:
+
+```text
+leftCenter₁ < m₁ < rightCenter₁
+leftCenter₂ < m₁ < rightCenter₂
+```
+
+Thus separator reuse is now represented as an explicit intersection witness
+for the two consumed intervals.
+
+In the distinct branch `m₁ ≠ m₂`, Lean proves the strict order split:
+
+```text
+m₁ < m₂ ∨ m₂ < m₁
+```
+
+This gives the next comparison layer a canonical ordered-separator branch.
+
+## Established Facts
+
+For two finite-window packing units, exactly one of the following forms is
+available:
+
+1. They reuse one separator, which is a common point of both open center
+   intervals.
+2. They use distinct separators, which are strictly ordered in the finite
+   window.
+
+Both branches retain the complete ordered chains:
+
+```text
+lo <= leftCenterᵢ < mᵢ < rightCenterᵢ <= hi
+```
+
+This is the first pairwise invariant suitable for analyzing separator
+multiplicity before passing to a finite family.
+
+## Route
+
+```text
+finite-window ordered chain
+  -> one pair consumes three ordered positions
+  -> pair-of-packings comparison
+  -> separator reuse / distinct split
+  -> shared-point geometry or ordered separators
+  -> prepares bounded multiplicity and packing count
+  -> local Big
+```
+
+## Refactoring Note
+
+`PressureState.lean` exceeds the preferred 2,000-line size.  A source-level
+TODO now records the intended mechanical extraction of this stabilized API to
+`PressureState/FiniteWindowPacking.lean`.  No import graph was changed in this
+checkpoint.
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
+## Next Branch Prediction
+
+Refine the reuse branch by comparing pair identities or center intervals.  The
+smallest useful question is whether a common separator plus an existing
+adjacency/sortedness invariant bounds the number of pairs that can contain that
+separator.  If no sharp bound follows, define an explicit separator
+multiplicity predicate for a finite selected-pair family and carry the bound as
+the counting hypothesis.
````
`````
