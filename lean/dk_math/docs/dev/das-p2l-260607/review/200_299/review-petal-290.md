# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking

gch: 6c4af1ce8830faf499fac3aaeab5fe4cba8f59c5

## Report

cp-290 の実装を完了しました。

- 新規モジュール [FiniteWindowPacking.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean) を追加。
- 異なる packing unit の canonical separator が最低 `2` 離れることを証明。
- 一般的な two-separated Finset に対する半窓上界
  `card ≤ (hi - lo) / 2 + 1` を証明。
- Pressure packing unit と、`L` から作る canonical pair family の双方へ上界を適用。
- packing 数が margin 非正位置数以下になる補題と、両上界を束ねた `localBig` を追加。
- 正中心の完全被覆は現行仮定からは導けないため、必要条件を `SourcePressureCanonicalLeftCoverageInWindow` として明示しました。
- 結果を [report-petal-290.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-290.md) に記録。

確認済みです。

- `lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking`
- `lake build DkMath.Collatz.PetalBridge.PressureState`
- `lake build DkMath.Collatz.PetalBridge`
- `git diff --check`
- 追加された `sorry` / `axiom` なし

確定した事実は、canonical pair が占める separator は隣接できず、有限窓内では最大でも概ね窓幅の半分しか配置できない、という離散 packing 制約です。一方、全 positive center がこの canonical family に捕捉されることはまだ証明されていません。

## Review

## 判定

**採用。これは本当に一つの山を越えた。**

cp-290 では、これまでの

```text
正中心
  -> 非正 separator
  -> separator の単射
```

が、初めて本格的な **有限窓 packing-density theorem** へ昇格した。

確定した中心結果は、

```lean
sourcePressureFiniteWindowPackingUnit_card_le_half_window_add_one
```

すなわち、

$$
S.card\le\frac{hi-lo}{2}+1
$$

じゃ。

さらに、separator が非正 margin 位置に入ることから、

```lean
sourcePressureFiniteWindowPackingUnit_card_le_nonposPositions
```

も成立した。

$$
S.card\le#{m\in[lo,hi]\mid SourcePressureMarginInt(n,k,m)\le0}
$$

この二つをまとめた、

```lean
sourcePressureFiniteWindowPackingUnit_localBig
```

まで実装されている。ビルド、公開 import、`git diff --check` が通り、`sorry` / `axiom` の追加もない。

## 今回、何が確定したのか

一言で言えば、

> **canonical positive pulse は、有限窓の中に密集できない。**

という離散密度則が Lean で確定した。

### 1. separator multiplicity から two-spacing へ進んだ

cp-289 では、異なる canonical packing unit が同じ separator を共有できないことまでだった。

今回はさらに、

```lean
SourcePressureFiniteWindowPackingUnit
  .canonicalSeparator_two_separated_of_ne_of_sorted
```

により、

```text
separator₁ + 2 ≤ separator₂
または
separator₂ + 2 ≤ separator₁
```

が証明された。

つまり異なる separator は、単に別座標なのではない。

```text
... separator ... 空き1座標 ... separator ...
```

という最低間隔を要求される。

これが本物の packing 制約じゃ。

## 半窓上界の意味

有限窓を `[lo,hi]` とする。

座標を一つずつ使えるだけなら、最大個数は

$$
hi-lo+1
$$

じゃ。

しかし今回は separator 同士が最低 `2` 離れる。

したがって置ける位置は概念的に、

```text
lo, lo+2, lo+4, lo+6, ...
```

となる。

最大個数は、

$$
\left\lfloor\frac{hi-lo}{2}\right\rfloor+1
$$

になる。

たとえば `[10,18]` なら、

```text
10, 12, 14, 16, 18
```

の最大 5 個。

```text
11, 13, 15, 17
```

から始めても 4 個しかない。

したがって「およそ窓幅の半分」が正確に theorem になった。

## generic Finset 補題も良い

今回追加された、

```lean
finset_card_le_half_window_add_one_of_twoSeparated
```

は Pressure 固有ではない。

任意の `Finset ℕ` について、

```text
全要素が [lo,hi] にある
異なる順序要素は最低 2 離れる
```

なら、

$$
T.card\le\frac{hi-lo}{2}+1
$$

を返す。

証明は、

```lean
m ↦ (m - lo) / 2
```

という圧縮写像を使っている。

two-separated なので、この写像は集合上で単射になる。
そして像は、

```lean
Finset.range ((hi - lo) / 2 + 1)
```

へ入る。

非常に素直で、他の DkMath packing 問題にも再利用できる補題じゃ。

## 符号容量という第二の上界

今回さらに良いのは、幾何的な半窓上界だけで終わらなかったこと。

canonical separator は、

```lean
r + W.val + 1
```

であり、必ず

```lean
SourcePressureMarginInt n k separator ≤ 0
```

を満たす。

そこで、

```lean
sourcePressureNonposPositionsInWindow
```

が定義された。

これは有限集合、

$$
{m\in[lo,hi]\mid M(m)\le0}
$$

じゃ。

そして canonical separator の像が、この非正集合へ入ることが証明された。

よって一つの packing family には二つの容量上界がある。

```text
幾何容量:
  窓幅の半分

符号容量:
  非正位置の個数
```

実際の上限は概念的には、

$$
S.card\le\min\left(\frac{hi-lo}{2}+1,#Nonpos(lo,hi)\right)
$$

となる。

今回の `localBig` は、この二本を conjunction として保持している。

## `localBig` の意味

```lean
sourcePressureFiniteWindowPackingUnit_localBig
```

は、まだ全軌道を包む Big ではない。

しかし、単なる局所 margin 上界でもなくなった。

今回の local Big は、

```text
有限窓内に置ける canonical pulse unit の最大容量
```

を表す。

しかも容量は二方向から決まる。

```text
位置構造:
  separator は 2-separated

符号構造:
  separator は非正位置を消費する
```

つまり、

```text
局所 pulse が一つ存在する
```

という存在定理から、

```text
有限窓には pulse を最大何個まで置けるか
```

という量的定理へ変わった。

証明の種類が明確に変わっている。

## `L` から直接 family を作った点

これも大きい。

それまでは theorem の caller が任意の `Finset S` を渡す必要があった。

今回は、

```lean
sourcePressureCanonicalPackingPairFamily
```

が追加され、

```lean
L.zip L.tail
```

から隣接 pair を直接列挙している。

そこから canonical packing state を満たす pair だけを filter する。

```text
L = [W₀,W₁,W₂,W₃,...]

L.zip L.tail
  = [(W₀,W₁),(W₁,W₂),(W₂,W₃),...]
```

したがって、

```lean
sourcePressureCanonicalPackingPairFamily_card_le_half_window_add_one
```

は、任意の外部 family ではなく、**実際の witness list `L` から抽出された family** に直接適用される。

これで counting theorem が現場データへ接続された。

## モジュール分割

新規モジュール、

```text
DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking
```

の追加も採用でよい。

今回は carrier 定義そのものをまだ `PressureState.lean` に残し、新しい density theorem を分割先へ置いている。

```text
PressureState.lean
  carrier / state layer

FiniteWindowPacking.lean
  two-spacing / counting / family / localBig
```

完全移動ではなく progressive extraction だが、循環 import を避けながら数学的 checkpoint を進めた判断は妥当じゃ。

次の機械的 refactor で carrier 群を移せばよい。今ここで import 構造の大改造を優先しなかったのは正しい。

## 残った Gap

今回、Codex は止まった場所も正確に名前へした。

```lean
SourcePressureCanonicalLeftCoverageInWindow
```

内容は、

```text
L 内の正中心 W が窓内にあるなら、
W を左 endpoint とする canonical pair W,W' が存在する
```

という coverage 契約じゃ。

現在確定した packing bound が数えているのは、

```text
canonical pair として認証された positive center
```

である。

まだ数えていないのは、

```text
L 内の全 positive center
```

じゃ。

この区別は重要。

現在言えること：

```text
canonical pair 数
  ≤ 半窓容量
  ≤ 非正位置容量
```

まだ必要なこと：

```text
全 positive center
  = canonical left center
    + 少数の境界残余
```

ここが次の核心になる。

## coverage が不足する理由

リスト `L` の最後の要素には、通常は右隣がない。

```text
[W₀,W₁,W₂,W₃]
```

の adjacent pair は、

```text
(W₀,W₁)
(W₁,W₂)
(W₂,W₃)
```

まで。

`W₃` は左 endpoint にはならない。

したがって最良の場合でも、

```text
全 positive center
  = canonical left centers
    ∪ terminal center
```

という端点補正が必要になる可能性がある。

ただし、現時点では「最後の一点だけ」とはまだ証明されていない。

なぜなら、各 adjacent pair が必ず canonical packing state を持つことも、現在の state ladder からはまだ出ていないからじゃ。

今回これを推測で埋めず、

```lean
SourcePressureCanonicalLeftCoverageInWindow
```

として不足条件を名前にしたのは正しい。

## 次に証明すべき量的結論

coverage が閉じれば、次はこの形になる。

完全 coverage の場合：

$$
# Positive(lo,hi)\le\frac{hi-lo}{2}+1
$$

さらに符号容量から、

$$
# Positive(lo,hi)\le#Nonpositive(lo,hi)
$$

端点残余が一つある場合：

$$
# Positive(lo,hi)\le\frac{hi-lo}{2}+2
$$

および、

$$
# Positive(lo,hi)\le#Nonpositive(lo,hi)+1
$$

これは非常に強い。

「正 pressure がどれほど発生しても、それを支える非正位置または有限境界補正が必要」という局所収支になる。

## 次の Codex 指示

次は coverage をいきなり仮定なしで断言するのではなく、

1. 正中心集合を定義する
2. canonical left-center 集合を定義する
3. coverage 仮定下で全正中心 counting を閉じる
4. 残余集合を定義する
5. 現行 state constructors から残余が何個までかを攻める

という長距離にする。

```text
Goal:
  Convert the canonical-pair packing bound into a cardinality theorem for
  positive witness centers.

  First prove the exact conditional theorem under
  SourcePressureCanonicalLeftCoverageInWindow.  Then inspect the actual list
  and state constructors to replace full coverage by a provable finite boundary
  residue decomposition.

Phase A — positive-center and canonical-left Finsets:
  Define the finite set of in-window positive witnesses supplied by L.

  Suggested definition:

    noncomputable def sourcePressurePositiveWitnessesInWindow
        {n : OddNat} {k r : ℕ}
        (L : List (SourcePressureLocalIslandWitness n k r))
        (lo hi : ℕ) :
        Finset (SourcePressureLocalIslandWitness n k r) :=
      L.toFinset.filter fun W =>
        lo ≤ r + W.val ∧ r + W.val ≤ hi

  Note:
    W is already a SourcePressureLocalIslandWitness, so positivity follows from
    W.property.  Add a theorem exposing the center-margin positivity.

  Define the left-endpoint image of the canonical pair family:

    sourcePressureCanonicalLeftWitnessesInWindow L lo hi :=
      (sourcePressureCanonicalPackingPairFamily L lo hi).image Prod.fst

Phase B — uniqueness of the adjacent right endpoint:
  Prove that an addressed left witness has at most one immediate right witness:

    AdjacentPairInList L W W₁'
    -> AdjacentPairInList L W W₂'
    -> W₁' = W₂'

  Use list recursion.  This gives injectivity of Prod.fst on the canonical pair
  family and therefore:

    card canonicalLeftWitnesses =
      card canonicalPackingPairFamily

Phase C — conditional complete-coverage theorem:
  Under

    hcoverage : SourcePressureCanonicalLeftCoverageInWindow L lo hi

  prove:

    sourcePressurePositiveWitnessesInWindow L lo hi ⊆
      sourcePressureCanonicalLeftWitnessesInWindow L lo hi

  Then prove:

    theorem sourcePressurePositiveWitnesses_card_le_half_window_add_one_of_coverage
        ...
        (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
        (hcoverage : SourcePressureCanonicalLeftCoverageInWindow L lo hi) :
        (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
          (hi - lo) / 2 + 1

  Also prove the sign-capacity version:

    positiveWitnesses.card ≤
      (sourcePressureNonposPositionsInWindow n k lo hi).card

  Package both as an all-positive conditional local-Big theorem.

Phase D — explicit residue decomposition:
  Define:

    sourcePressurePositiveCoverageResidue L lo hi :=
      sourcePressurePositiveWitnessesInWindow L lo hi \
        sourcePressureCanonicalLeftWitnessesInWindow L lo hi

  Prove the exact finite decomposition and the generic bound:

    positiveWitnesses.card ≤
      canonicalPackingPairFamily.card +
        positiveCoverageResidue.card

  Combine with cp-290:

    positiveWitnesses.card ≤
      (hi - lo) / 2 + 1 +
        positiveCoverageResidue.card

    positiveWitnesses.card ≤
      nonposPositions.card +
        positiveCoverageResidue.card

Phase E — analyze the actual residue:
  Inspect:
    - L.zip L.tail
    - AdjacentPairInList constructors
    - SourcePressureForwardPairComparisonState producers
    - BeamSeed / SortedFailure / FailureResolution state ladders
    - pair-overlap incompatibility with sortedness

  Determine the strongest provable classification:

    every in-window witness is either
      a canonical left endpoint,
      a terminal list endpoint,
      or belongs to one exact unresolved state branch.

  Do not assume that the residue has card ≤ 1.
  Prove it from the current constructors if possible.

  Preferred target:

    positiveCoverageResidue ⊆ {last witness of L}

  which would give:

    positiveCoverageResidue.card ≤ 1

  If this target fails, isolate the precise additional pair-level theorem
  needed to certify every nonterminal adjacent pair.

Phase F — endpoint-corrected local Big:
  If residue.card ≤ 1 closes, prove:

    positiveWitnesses.card ≤ (hi - lo) / 2 + 2

    positiveWitnesses.card ≤ nonposPositions.card + 1

  Package this as the finite-window positive-center local Big.

Phase G — report the route:
  Record:

    canonical separator two-spacing
      -> canonical pair density
      -> canonical left-center density
      -> positive-center coverage decomposition
      -> finite boundary residue
      -> all-positive local Big.

  Continue through all reachable phases in one checkpoint.  If the residue
  theorem does not close, report the exact Lean proposition and the exact
  constructor/state branch blocking it.

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 総合評価

cp-290 で確定したのは、

```text
正中心の間に非正点がある
```

だけではない。

```text
非正 separator は互いに最低 2 離れる
有限窓には最大で半窓分しか置けない
各 separator は非正位置を一つ消費する
実際の witness list から canonical family を抽出できる
```

まで Lean theorem になった。

つまり局所 pressure は、もはや単なる符号模様ではない。

**有限窓の中で、位置と符号の両方を消費する離散 packing 構造**として確定した。

次は、その packing family が全 positive center をどこまで覆うか。
ここが閉じれば、local Big は「認証された pair 数」から「全正中心数」の上界へ昇格する。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index b86c53e5..0a89bc89 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -25,6 +25,7 @@ import DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
 import DkMath.Collatz.PetalBridge.PressureAutomaton
 import DkMath.Collatz.PetalBridge.PressureBeam
 import DkMath.Collatz.PetalBridge.PressureState
+import DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking
 import DkMath.Collatz.PetalBridge.OneCycle
 import DkMath.Collatz.PetalBridge.ValuationFlowBridge
 import DkMath.Collatz.PetalBridge.Collision
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean
new file mode 100644
index 00000000..2eb81693
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean
@@ -0,0 +1,343 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.PressureState
+
+#print "file: DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking"
+
+namespace DkMath.Collatz
+
+/-!
+# Finite-window pressure packing
+
+This module is the first progressive extraction from `PressureState.lean`.
+The established carrier API remains in that module for compatibility; new
+packing-density results live here.  A later mechanical checkpoint may move the
+stable carrier declarations here after splitting the state file into a core
+module, without changing theorem names.
+-/
+
+/-- Equal pair keys determine equal packing units by proof irrelevance. -/
+theorem SourcePressureFiniteWindowPackingUnit.eq_of_pairKey_eq
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    {u₁ u₂ : SourcePressureFiniteWindowPackingUnit L lo hi}
+    (hkey : u₁.pairKey = u₂.pairKey) :
+    u₁ = u₂ := by
+  cases u₁
+  cases u₂
+  simp_all [SourcePressureFiniteWindowPackingUnit.pairKey]
+
+/-- Distinct packing units have distinct oriented endpoint keys. -/
+theorem SourcePressureFiniteWindowPackingUnit.pairKey_ne_of_ne
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    {u₁ u₂ : SourcePressureFiniteWindowPackingUnit L lo hi}
+    (hne : u₁ ≠ u₂) :
+    u₁.pairKey ≠ u₂.pairKey :=
+  fun hkey => hne (SourcePressureFiniteWindowPackingUnit.eq_of_pairKey_eq hkey)
+
+/--
+Distinct canonical separators in a sorted witness list are separated by at
+least two positions.
+
+Sorted adjacency puts one oriented pair wholly before the other.  The
+two-center spacing inside the earlier unit then leaves two steps between the
+canonical left-next separators.
+-/
+theorem SourcePressureFiniteWindowPackingUnit.canonicalSeparator_two_separated_of_ne_of_sorted
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    {u₁ u₂ : SourcePressureFiniteWindowPackingUnit L lo hi}
+    (hne : u₁ ≠ u₂) :
+    u₁.canonicalSeparator + 2 ≤ u₂.canonicalSeparator ∨
+      u₂.canonicalSeparator + 2 ≤ u₁.canonicalSeparator := by
+  rcases sourcePressureAdjacentPairs_eq_or_nonoverlap_of_sorted
+      hsorted u₁.state.adjacentPair u₂.state.adjacentPair with hpairs | horder
+  · exfalso
+    apply hne
+    cases u₁
+    cases u₂
+    simp_all
+  · rcases horder with h₁₂ | h₂₁
+    · left
+      have hgap := u₁.state.finiteWindow.two_le_value_gap
+      simp only [SourcePressureFiniteWindowPackingUnit.canonicalSeparator]
+      omega
+    · right
+      have hgap := u₂.state.finiteWindow.two_le_value_gap
+      simp only [SourcePressureFiniteWindowPackingUnit.canonicalSeparator]
+      omega
+
+/--
+Generic finite-window packing bound for natural numbers separated by two.
+
+The map `m ↦ (m - lo) / 2` is injective on a two-separated set and its image
+lies in `range ((hi - lo) / 2 + 1)`.
+-/
+theorem finset_card_le_half_window_add_one_of_twoSeparated
+    {lo hi : ℕ}
+    (T : Finset ℕ)
+    (hwindow : ∀ m ∈ T, lo ≤ m ∧ m ≤ hi)
+    (hsep : ∀ a ∈ T, ∀ b ∈ T, a < b → a + 2 ≤ b) :
+    T.card ≤ (hi - lo) / 2 + 1 := by
+  classical
+  let f : ℕ → ℕ := fun m => (m - lo) / 2
+  have hinj : Set.InjOn f T := by
+    intro a ha b hb hab
+    by_contra hne
+    rcases Nat.lt_or_gt_of_ne hne with hablt | hbalt
+    · have hgap := hsep a ha b hb hablt
+      have hawa := hwindow a ha
+      simp only [f] at hab
+      omega
+    · have hgap := hsep b hb a ha hbalt
+      have hawb := hwindow b hb
+      simp only [f] at hab
+      omega
+  have hcard : (T.image f).card = T.card :=
+    Finset.card_image_iff.mpr hinj
+  have hsubset : T.image f ⊆ Finset.range ((hi - lo) / 2 + 1) := by
+    intro q hq
+    rcases Finset.mem_image.1 hq with ⟨m, hm, rfl⟩
+    have hwm := hwindow m hm
+    simp only [Finset.mem_range, f]
+    omega
+  rw [← hcard]
+  simpa using Finset.card_le_card hsubset
+
+/-- Nonpositive pressure-margin coordinates in the explicit finite window. -/
+noncomputable def sourcePressureNonposPositionsInWindow
+    (n : OddNat) (k lo hi : ℕ) : Finset ℕ :=
+  (Finset.Icc lo hi).filter
+    (fun m => SourcePressureMarginInt n k m ≤ 0)
+
+@[simp]
+theorem mem_sourcePressureNonposPositionsInWindow
+    {n : OddNat} {k lo hi m : ℕ} :
+    m ∈ sourcePressureNonposPositionsInWindow n k lo hi ↔
+      lo ≤ m ∧ m ≤ hi ∧ SourcePressureMarginInt n k m ≤ 0 := by
+  simp [sourcePressureNonposPositionsInWindow, and_assoc]
+
+/-- Canonical separators of a finite family are nonpositive window positions. -/
+theorem sourcePressureFiniteWindowPackingUnit_image_separator_subset_nonposPositions
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    (S : Finset (SourcePressureFiniteWindowPackingUnit L lo hi)) :
+    S.image (SourcePressureFiniteWindowPackingUnit.canonicalSeparator
+      (L := L) (lo := lo) (hi := hi)) ⊆
+      sourcePressureNonposPositionsInWindow n k lo hi := by
+  classical
+  intro m hm
+  rcases Finset.mem_image.1 hm with ⟨u, _hu, rfl⟩
+  rcases u.canonicalSeparator_in_window with ⟨hlo, hhi⟩
+  exact mem_sourcePressureNonposPositionsInWindow.2
+    ⟨hlo, hhi, u.state.separator_nonpos⟩
+
+/--
+Sign-restricted packing bound: canonical units inject into the nonpositive
+pressure positions of the same finite window.
+-/
+theorem sourcePressureFiniteWindowPackingUnit_card_le_nonposPositions
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (S : Finset (SourcePressureFiniteWindowPackingUnit L lo hi)) :
+    S.card ≤ (sourcePressureNonposPositionsInWindow n k lo hi).card := by
+  classical
+  let f := SourcePressureFiniteWindowPackingUnit.canonicalSeparator
+    (L := L) (lo := lo) (hi := hi)
+  have hinj : Function.Injective f :=
+    SourcePressureFiniteWindowPackingUnit.canonicalSeparator_injective_of_sorted
+      hsorted
+  have hcard : (S.image f).card = S.card :=
+    Finset.card_image_iff.mpr hinj.injOn
+  rw [← hcard]
+  exact Finset.card_le_card
+    (sourcePressureFiniteWindowPackingUnit_image_separator_subset_nonposPositions S)
+
+/--
+Sharp finite-window pressure packing bound from canonical-separator
+two-spacing.
+-/
+theorem sourcePressureFiniteWindowPackingUnit_card_le_half_window_add_one
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (S : Finset (SourcePressureFiniteWindowPackingUnit L lo hi)) :
+    S.card ≤ (hi - lo) / 2 + 1 := by
+  classical
+  let f := SourcePressureFiniteWindowPackingUnit.canonicalSeparator
+    (L := L) (lo := lo) (hi := hi)
+  have hinj : Function.Injective f :=
+    SourcePressureFiniteWindowPackingUnit.canonicalSeparator_injective_of_sorted
+      hsorted
+  have hcard : (S.image f).card = S.card :=
+    Finset.card_image_iff.mpr hinj.injOn
+  have hwindow : ∀ m ∈ S.image f, lo ≤ m ∧ m ≤ hi := by
+    intro m hm
+    rcases Finset.mem_image.1 hm with ⟨u, _hu, rfl⟩
+    exact u.canonicalSeparator_in_window
+  have hsep :
+      ∀ a ∈ S.image f, ∀ b ∈ S.image f, a < b → a + 2 ≤ b := by
+    intro a ha b hb hab
+    rcases Finset.mem_image.1 ha with ⟨u₁, hu₁, rfl⟩
+    rcases Finset.mem_image.1 hb with ⟨u₂, hu₂, hsepEq⟩
+    subst b
+    have hne : u₁ ≠ u₂ := by
+      intro hu
+      subst u₂
+      omega
+    rcases u₁.canonicalSeparator_two_separated_of_ne_of_sorted hsorted hne with
+      hforward | hreverse
+    · simpa only [f] using hforward
+    · simp only [f] at hab hreverse
+      omega
+  rw [← hcard]
+  exact finset_card_le_half_window_add_one_of_twoSeparated
+    (S.image f) hwindow hsep
+
+/--
+Finite local-Big packing surface: geometry supplies half-window capacity while
+pressure signs supply the nonpositive-position capacity.
+-/
+theorem sourcePressureFiniteWindowPackingUnit_localBig
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (S : Finset (SourcePressureFiniteWindowPackingUnit L lo hi)) :
+    S.card ≤ (hi - lo) / 2 + 1 ∧
+      S.card ≤ (sourcePressureNonposPositionsInWindow n k lo hi).card :=
+  ⟨sourcePressureFiniteWindowPackingUnit_card_le_half_window_add_one hsorted S,
+    sourcePressureFiniteWindowPackingUnit_card_le_nonposPositions hsorted S⟩
+
+/--
+Canonical oriented-pair family extracted directly from adjacent entries of `L`.
+
+The zip with `L.tail` enumerates adjacent pair keys; the filter retains exactly
+those carrying the canonical finite-window packing state.
+-/
+noncomputable def sourcePressureCanonicalPackingPairFamily
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (lo hi : ℕ) :
+    Finset (SourcePressureLocalIslandWitness n k r ×
+      SourcePressureLocalIslandWitness n k r) := by
+  classical
+  exact (L.zip L.tail).toFinset.filter fun P =>
+    SourcePressureCanonicalFiniteWindowPackingState L lo hi P.1 P.2
+
+@[simp]
+theorem mem_sourcePressureCanonicalPackingPairFamily
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    {P : SourcePressureLocalIslandWitness n k r ×
+      SourcePressureLocalIslandWitness n k r} :
+    P ∈ sourcePressureCanonicalPackingPairFamily L lo hi ↔
+      P ∈ L.zip L.tail ∧
+        SourcePressureCanonicalFiniteWindowPackingState L lo hi P.1 P.2 := by
+  classical
+  simp [sourcePressureCanonicalPackingPairFamily]
+
+/-- Canonical separator attached directly to an oriented witness-pair key. -/
+def sourcePressureCanonicalPairSeparator
+    {n : OddNat} {k r : ℕ}
+    (P : SourcePressureLocalIslandWitness n k r ×
+      SourcePressureLocalIslandWitness n k r) : ℕ :=
+  r + P.1.val + 1
+
+/-- The extracted canonical pair family satisfies the sharp half-window bound. -/
+theorem sourcePressureCanonicalPackingPairFamily_card_le_half_window_add_one
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {lo hi : ℕ}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    (sourcePressureCanonicalPackingPairFamily L lo hi).card ≤
+      (hi - lo) / 2 + 1 := by
+  classical
+  let F := sourcePressureCanonicalPackingPairFamily L lo hi
+  let f := sourcePressureCanonicalPairSeparator (n := n) (k := k) (r := r)
+  have hstate : ∀ P ∈ F,
+      SourcePressureCanonicalFiniteWindowPackingState L lo hi P.1 P.2 := by
+    intro P hP
+    exact (mem_sourcePressureCanonicalPackingPairFamily.1 hP).2
+  have hinj : Set.InjOn f F := by
+    intro P hP Q hQ hsep
+    let uP : SourcePressureFiniteWindowPackingUnit L lo hi :=
+      ⟨P.1, P.2, hstate P hP⟩
+    let uQ : SourcePressureFiniteWindowPackingUnit L lo hi :=
+      ⟨Q.1, Q.2, hstate Q hQ⟩
+    have hu : uP = uQ :=
+      SourcePressureFiniteWindowPackingUnit.canonicalSeparator_injective_of_sorted
+        hsorted (by
+          simpa only [SourcePressureFiniteWindowPackingUnit.canonicalSeparator,
+            uP, uQ, f, sourcePressureCanonicalPairSeparator] using hsep)
+    cases P
+    cases Q
+    simp_all [uP, uQ]
+  have hcard : (F.image f).card = F.card :=
+    Finset.card_image_iff.mpr hinj
+  have hwindow : ∀ m ∈ F.image f, lo ≤ m ∧ m ≤ hi := by
+    intro m hm
+    rcases Finset.mem_image.1 hm with ⟨P, hP, rfl⟩
+    simpa [f, sourcePressureCanonicalPairSeparator] using
+      (hstate P hP).separator_in_window
+  have hsep : ∀ a ∈ F.image f, ∀ b ∈ F.image f, a < b → a + 2 ≤ b := by
+    intro a ha b hb hab
+    rcases Finset.mem_image.1 ha with ⟨P, hP, rfl⟩
+    rcases Finset.mem_image.1 hb with ⟨Q, hQ, rfl⟩
+    let uP : SourcePressureFiniteWindowPackingUnit L lo hi :=
+      ⟨P.1, P.2, hstate P hP⟩
+    let uQ : SourcePressureFiniteWindowPackingUnit L lo hi :=
+      ⟨Q.1, Q.2, hstate Q hQ⟩
+    have hne : uP ≠ uQ := by
+      intro hu
+      have : f P = f Q := by
+        simpa only [SourcePressureFiniteWindowPackingUnit.canonicalSeparator,
+          uP, uQ, f, sourcePressureCanonicalPairSeparator] using
+          congrArg SourcePressureFiniteWindowPackingUnit.canonicalSeparator hu
+      omega
+    rcases uP.canonicalSeparator_two_separated_of_ne_of_sorted hsorted hne with
+      hforward | hreverse
+    · simpa only [SourcePressureFiniteWindowPackingUnit.canonicalSeparator,
+        uP, uQ, f, sourcePressureCanonicalPairSeparator] using hforward
+    · simp only [SourcePressureFiniteWindowPackingUnit.canonicalSeparator,
+        uP, uQ] at hreverse
+      simp only [f, sourcePressureCanonicalPairSeparator] at hab
+      omega
+  rw [← hcard]
+  exact finset_card_le_half_window_add_one_of_twoSeparated
+    (F.image f) hwindow hsep
+
+/--
+Exact coverage proposition still needed to turn canonical-pair density into a
+bound for every positive center in the witness list.
+
+Current state transitions produce at least one forward pair; they do not prove
+that every positive in-window witness is the left endpoint of such a pair.
+This named proposition is therefore the next coverage contract, not an
+established consequence of `BeamSeed`, `SortedFailure`, or
+`FailureResolution`.
+-/
+def SourcePressureCanonicalLeftCoverageInWindow
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (lo hi : ℕ) : Prop :=
+  ∀ W, W ∈ L →
+    lo ≤ r + W.val → r + W.val ≤ hi →
+    0 < SourcePressureMarginInt n k (r + W.val) →
+    ∃ W', SourcePressureCanonicalFiniteWindowPackingState L lo hi W W'
+
+end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-290.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-290.md
new file mode 100644
index 00000000..78f4203d
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-290.md
@@ -0,0 +1,172 @@
+# Report: petal-290
+
+## Goal
+
+Strengthen separator injection to a genuine half-window packing-density theorem,
+connect the bound to nonpositive pressure positions, and extract a canonical
+family directly from the witness list.
+
+## Progressive Module Split
+
+Created:
+
+- `DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking`
+
+The new density and family theorems live in this module and are re-exported by
+`DkMath.Collatz.PetalBridge`.  Existing carrier declarations remain temporarily
+in `PressureState.lean` to avoid a cyclic aggregator/core rewrite during the
+mathematical checkpoint.  Their later move is recorded as a mechanical API-
+preserving refactor.
+
+## Two-Spacing
+
+Added:
+
+- `SourcePressureFiniteWindowPackingUnit.eq_of_pairKey_eq`
+- `.pairKey_ne_of_ne`
+- `.canonicalSeparator_two_separated_of_ne_of_sorted`
+
+Lean proves that distinct canonical packing units in a sorted witness list
+satisfy:
+
+```text
+separator₁ + 2 <= separator₂
+  OR separator₂ + 2 <= separator₁
+```
+
+Thus separator multiplicity one strengthens to geometric two-spacing.
+
+## Generic Packing Lemma
+
+Added:
+
+- `finset_card_le_half_window_add_one_of_twoSeparated`
+
+For a two-separated `Finset Nat` inside `[lo, hi]`:
+
+```lean
+T.card <= (hi - lo) / 2 + 1
+```
+
+The proof injects `m` into `(m - lo) / 2` and bounds the image by a finite
+range.  This theorem is independent of pressure terminology.
+
+## Sharp Pressure Packing Bound
+
+Added:
+
+- `sourcePressureFiniteWindowPackingUnit_card_le_half_window_add_one`
+
+For every finite family `S` of canonical packing units:
+
+```lean
+S.card <= (hi - lo) / 2 + 1
+```
+
+This improves the previous coordinate bound from full-window capacity to
+half-window packing capacity.
+
+## Sign-Restricted Bound
+
+Added:
+
+- `sourcePressureNonposPositionsInWindow`
+- `mem_sourcePressureNonposPositionsInWindow`
+- `sourcePressureFiniteWindowPackingUnit_image_separator_subset_nonposPositions`
+- `sourcePressureFiniteWindowPackingUnit_card_le_nonposPositions`
+
+Every canonical separator belongs to the finite set of nonpositive margin
+positions, hence:
+
+```lean
+S.card <= card {m in [lo, hi] | SourcePressureMarginInt n k m <= 0}
+```
+
+Added the combined local-Big surface:
+
+- `sourcePressureFiniteWindowPackingUnit_localBig`
+
+It exposes both half-window geometric capacity and nonpositive-position
+capacity in one theorem.
+
+## Canonical Family From The Witness List
+
+Added:
+
+- `sourcePressureCanonicalPackingPairFamily`
+- `mem_sourcePressureCanonicalPackingPairFamily`
+- `sourcePressureCanonicalPairSeparator`
+- `sourcePressureCanonicalPackingPairFamily_card_le_half_window_add_one`
+
+The family is obtained from `L.zip L.tail`, filtered by the canonical packing
+state.  Therefore it represents all adjacent pair keys in `L` currently
+certified as canonical finite-window packing units.
+
+Lean proves the direct list-facing bound:
+
+```lean
+(sourcePressureCanonicalPackingPairFamily L lo hi).card
+  <= (hi - lo) / 2 + 1
+```
+
+## Positive-Center Coverage Status
+
+The canonical pair family is now extracted and bounded, but existing upstream
+states only produce selected forward pairs.  They do not prove that every
+positive in-window witness is a left endpoint of a canonical unit.
+
+The exact missing contract is now named:
+
+- `SourcePressureCanonicalLeftCoverageInWindow`
+
+Its proposition is:
+
+```text
+for every W in L,
+  if its center is positive and lies in [lo, hi],
+  then there exists W' such that (W,W') has canonical packing state.
+```
+
+This did not close from `BeamSeed`, `SortedFailure`, or `FailureResolution`.
+It is the precise obstruction to converting canonical-pair density into a
+cardinality bound for all positive centers without an endpoint correction.
+
+## Established Route
+
+```text
+sorted adjacent pairs
+  -> multiplicity one
+  -> canonical separator injection
+  -> canonical separator two-spacing
+  -> half-window packing density
+  -> sign-restricted packing bound
+  -> canonical family extracted from L
+  -> exact positive-center coverage contract isolated
+  -> finite local Big
+```
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
+No `sorry` was introduced.
+
+## Next Branch Prediction
+
+Analyze list endpoints and the state-ladder selection mechanism to weaken
+`SourcePressureCanonicalLeftCoverageInWindow` to a provable decomposition:
+
+```text
+positive in-window centers
+  subset canonical left centers union finite boundary residue
+```
+
+The expected sharp correction is one uncovered terminal center, but that must
+be derived from the actual list/state constructors rather than assumed.
````
`````
