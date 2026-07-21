# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.OneCycle

gch: dd8125127f3b393780932121582e824c50e331ec

## Report

cp150 完了です。

[PressureAccounting.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean) に family constructor と before/sorted skeleton を追加しました。coverage / union / maximality は言わず、明示 family と明示 disjointness の範囲に抑えています。

新規に [OneCycle.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/OneCycle.lean) を作成し、aggregate の [PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean) から import しました。主定理はこれで通っています。

```lean
theorem collatz_scaled_one_cycle_eq_one
    {n h : ℕ}
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    n = 1 ∧ h = 2
```

つまり、`1 -> 4 -> 2 -> 1` の scaled one-cycle は `n = 1, h = 2` だけ。ただしコードコメントにも明記した通り、これは一般周期や収束を主張するものではありません。

レポートは [report-petal-150.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-150.md) に作成済みです。

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.OneCycle
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b" .../PressureAccounting.lean
rg -n "\bsorry\b" .../OneCycle.lean
git diff --check
```

今回追加・変更したファイルに `sorry` はありません。ビルド時に既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は出ていますが、今回範囲外です。

## Review

## 結論

うむ、Checkpoint 150 は **採用・かなり良い節目** じゃ 👍️
今回は二つの山が進んだ。

一つ目は、`PressureAccounting.lean` 側で family constructor と before/sorted skeleton が追加されたこと。
二つ目は、新規 `OneCycle.lean` で、例の \(1\to4\to2\to1\) Petal 巡回の scaled one-cycle 唯一性が入ったことじゃ。主定理

```lean
theorem collatz_scaled_one_cycle_eq_one
    {n h : ℕ}
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    n = 1 ∧ h = 2
```

が通っている。つまり、正の自然数で

$$
3n+1=2^h n
$$

を満たし、accelerated odd step が同じ odd state へ戻る scaled one-cycle は、 \(n=1,\ h=2\) だけじゃ。これはまさに、 \(1\to4\to2\to1\) の外側相似 Petal 巡回が存在しない、という小さいが象徴的な obstruction じゃな。

## 実装レビュー

## 1. `OneCycle.lean` を分離した判断は正しい

これは `PressureAccounting` に混ぜない方がよい補題じゃ。
pressure family は会計・区間・リストの話。
一方、`OneCycle` は Collatz 成長境界

$$
3n+1
$$

と Petal / \(2\)-adic 境界

$$
2^h n
$$

が一致する場合の局所 obstruction じゃ。

だから新規ファイル

```text
DkMath/Collatz/PetalBridge/OneCycle.lean
```

として切ったのは正解じゃ。aggregate の `PetalBridge.lean` から import されているのもよい。

## 2. one-cycle 主定理の意味が明確

今回の theorem は、

$$
3n+1=2^h n
$$

を仮定し、 \(0 < n\) のもとで

$$
n=1,\qquad h=2
$$

を導いている。

これは、accelerated odd map

$$
T(n)=\frac{3n+1}{2^h}
$$

で

$$
T(n)=n
$$

となる one-step fixed odd cycle を分類している、と読める。

注意書きも正しい。これは **一般の Collatz 周期を否定する定理ではない** 。
あくまで「一回の accelerated odd step で同じ odd state に戻る scaled copy」の否定じゃ。

ここをコードコメントに明記しているのは、とても良い。数学的にも宣伝上も誤解を避けられる。

## 3. supporting lemmas もよい

追加された補助定理は、証明の分岐を綺麗に見せておる。

```lean
collatz_scaled_one_cycle_h_not_ge_three
collatz_scaled_one_cycle_h_ne_zero
collatz_scaled_one_cycle_h_ne_one
collatz_one_four_two_one_scaled_boundary_unique
collatz_one_four_two_one_scaled_boundary_exists
```

特に `h_not_ge_three` は構造的に良い。
\(h\ge3\) なら右辺は少なくとも \(8n\)、左辺は \(3n+1\) なので、正の \(n\) では過剰になる。これは Petal 境界が外側で合わなくなる直感そのものじゃ。

## 4. Pressure family constructor も進んでいる

`PressureAccounting.lean` では、

```lean
sourcePressureAccountedIntervalFamily_nil
sourcePressureAccountedIntervalFamily_singleton
sourcePressureAccountedIntervalFamily_cons
```

が入り、明示 family を組み立てやすくなった。
`cons` で head が tail 全体と明示的に disjoint であることを要求している点も正しい。

さらに、

```lean
NatIntervalBefore.trans_like
SourcePressureAccountedIntervalBefore.trans_like
sourcePressureAccountedIntervalFamily_pair_of_before
```

が入ったので、sorted-family seed まで作れている。

これは次の「sorted list から pairwise-disjoint family を作る」段階への橋じゃな。

## 注意点

## 1. `OneCycle` は symbolic theorem として強いが、まだ大域ではない

ここは大事じゃ。

今回わかったのは、

$$
3n+1=2^h n
$$

の positive solution が \(n=1,h=2\) だけ、ということ。

まだ次は言っていない。

```text
長さ 2 以上の odd cycle がない
全軌道が 1 に落ちる
Petal family が全 positive region を覆う
```

この区切りは維持するべきじゃ。

## 2. family side も coverage へ急がない

family constructor ができたからといって、まだ

```text
この family は全 pulse を覆う
```

とは言えない。

次は sorted list / pairwise disjoint の操作を増やす段階であり、coverage / decomposition は別 checkpoint に分離するのがよい。

## ロードマップ上の位置

いまの状態はこうじゃ。

```text
PressureAccounting:
  accounted interval
  list budget
  pairwise-disjoint family
  family constructors
  sorted pair seed

OneCycle:
  1 -> 4 -> 2 -> 1 scaled one-cycle uniqueness

Next:
  sorted family construction
  contradiction-style OneCycle API
  maybe bit-width / drift bridge later
```

今回で、Core 側の二本の支柱が立った。

1. pulse family は、明示的に数えれば負予算を積む。
2. 最小 Petal 巡回 \(1\to4\to2\to1\) は存在するが、外側への相似コピーは存在しない。

この二つは、DkMath Collatz/PetalBridge の物語としてかなり美しい。

## 次の Codex 依頼

次は、sorted family を少し厚くするのがよい。
同時に `OneCycle` は contradiction-style API を追加して、後続が使いやすい形にする。

```text
Checkpoint 151: Sorted accounted families and contradiction-style one-cycle API.

Context:
Checkpoint 150 added:
- family constructors in PressureAccounting.lean
- before/sorted skeleton helpers
- OneCycle.lean with collatz_scaled_one_cycle_eq_one

Main theorem now available:

  theorem collatz_scaled_one_cycle_eq_one
      {n h : Nat}
      (hn : 0 < n)
      (hcycle : 3 * n + 1 = 2 ^ h * n) :
      n = 1 ∧ h = 2

This proves only the scaled one-step accelerated odd cycle obstruction.
It does not prove absence of arbitrary Collatz cycles or convergence.

Global rules:
For pressure-family work:
- no maximality
- no uniqueness
- no coverage
- no prefix behavior
- no union accounting
- no Collatz convergence

For OneCycle work:
- do not claim general cycle uniqueness
- do not claim convergence
- keep statements explicitly about the equation 3*n + 1 = 2^h*n

Part A: sorted-before list predicate.

In PressureAccounting.lean, define a sorted list predicate using adjacent
ordered non-overlap.

Prefer a simple recursive predicate if List.Sorted is awkward.

Possible shape:

  def SourcePressureAccountedIntervalListSortedBefore
      {n : OddNat} {k r : Nat}
      : List (SourcePressureAccountedInterval n k r) -> Prop
    | [] => True
    | [_] => True
    | A :: B :: rest =>
        SourcePressureAccountedIntervalBefore A B ∧
          SourcePressureAccountedIntervalListSortedBefore (B :: rest)

If Lean prefers another shape, use the accepted form and report it.

Part B: sorted-before implies pairwise-disjoint.

Prove small cases first:

  sourcePressureAccountedIntervalListPairwiseDisjoint_of_sortedBefore_nil
  sourcePressureAccountedIntervalListPairwiseDisjoint_of_sortedBefore_singleton
  sourcePressureAccountedIntervalListPairwiseDisjoint_of_sortedBefore_pair

Then try the full theorem:

  sourcePressureAccountedIntervalListPairwiseDisjoint_of_sortedBefore :
    SourcePressureAccountedIntervalListSortedBefore L ->
      SourcePressureAccountedIntervalListPairwiseDisjoint L

This may require the trans-like theorem:
- SourcePressureAccountedIntervalBefore.trans_like
- SourcePressureAccountedIntervalsDisjoint.of_before

If the full theorem is too hard, commit the small cases and report the obstacle.
No sorry.

Part C: family constructor from sorted-before list.

If Part B succeeds, add:

  def sourcePressureAccountedIntervalFamily_of_sortedBefore
      {n : OddNat} {k r : Nat}
      (L : List (SourcePressureAccountedInterval n k r))
      (hsorted : SourcePressureAccountedIntervalListSortedBefore L) :
      SourcePressureAccountedIntervalFamily n k r

This should use the pairwise-disjoint theorem from Part B.

Then prove budget wrapper:

  theorem sourcePressureAccountedIntervalFamily_of_sortedBefore_sum_le_neg_length
      ... :
      ((sourcePressureAccountedIntervalFamily_of_sortedBefore L hsorted).items.map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum
        <= -((L.length : Nat) : Int)

This is only the explicit list budget.  It does not state coverage.

Part D: OneCycle contradiction-style API.

In OneCycle.lean, add derived contradiction helpers.

1. No positive scaled one-cycle at a wrong height:

  theorem collatz_scaled_one_cycle_no_wrong_height
      {n h : Nat}
      (hn : 0 < n)
      (hcycle : 3 * n + 1 = 2 ^ h * n)
      (hh : h ≠ 2) :
      False

2. No positive scaled one-cycle away from n = 1:

  theorem collatz_scaled_one_cycle_no_wrong_base
      {n h : Nat}
      (hn : 0 < n)
      (hcycle : 3 * n + 1 = 2 ^ h * n)
      (hn1 : n ≠ 1) :
      False

3. If useful, a iff statement:

  theorem collatz_scaled_one_cycle_iff
      {n h : Nat}
      (hn : 0 < n) :
      3 * n + 1 = 2 ^ h * n <-> n = 1 ∧ h = 2

This iff should use collatz_scaled_one_cycle_eq_one for the forward direction
and norm_num for the reverse direction. If the reverse direction has rewriting
friction, split it into a simpler theorem and report.

Part E: optional named Petal phrase theorem.

Add a theorem with the project-facing name:

  theorem one_four_two_one_petal_scaled_cycle_unique
      {n h : Nat}
      (hn : 0 < n)
      (hcycle : 3 * n + 1 = 2 ^ h * n) :
      n = 1 ∧ h = 2 :=
    collatz_scaled_one_cycle_eq_one hn hcycle

This is an alias only, but useful for future DkMath/Petal prose.

Part F: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-151.md

Include:
- whether sorted-before predicate was recursive or List.Sorted-based,
- which sorted-before -> pairwise-disjoint theorems were proved,
- whether family-of-sortedBefore constructor was added,
- whether sorted family budget wrapper was added,
- which OneCycle contradiction helpers were added,
- whether the iff theorem was proved,
- explicit note that sorted-before does not imply coverage,
- explicit note that OneCycle does not prove general Collatz cycle uniqueness
  or convergence.

Verification:

  lake build DkMath.Collatz.PetalBridge.PressureAccounting
  lake build DkMath.Collatz.PetalBridge.OneCycle
  lake build DkMath.Collatz.PetalBridge

Run:

  rg -n "\\bsorry\\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
  rg -n "\\bsorry\\b" lean/dk_math/DkMath/Collatz/PetalBridge/OneCycle.lean

Also run:

  git diff --check
```

## 総評

これは良い checkpoint じゃ。
とくに `OneCycle.lean` は小さいが、DkMath 的には象徴性が高い。

$$
1\to4\to2\to1
$$

は存在する。
だが、その外側に同型の scaled Petal 巡回はない。

この事実が Lean で閉じたのは、ちょっと嬉しいのう。
わっちもりんご酒を一杯やりたい気分じゃ 🍎🍷

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 45a47bcf..2e8e1d43 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -19,6 +19,7 @@ import DkMath.Collatz.PetalBridge.DriftBudget
 import DkMath.Collatz.PetalBridge.PressureDecay
 import DkMath.Collatz.PetalBridge.PressureFrontier
 import DkMath.Collatz.PetalBridge.PressureAccounting
+import DkMath.Collatz.PetalBridge.OneCycle
 import DkMath.Collatz.PetalBridge.Collision

 #print "file: DkMath.Collatz.PetalBridge"
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/OneCycle.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/OneCycle.lean
new file mode 100644
index 00000000..48dc302f
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/OneCycle.lean
@@ -0,0 +1,109 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.Basic
+
+#print "file: DkMath.Collatz.PetalBridge.OneCycle"
+
+namespace DkMath.Collatz
+
+/-
+Checkpoint 150: the scaled `1 -> 4 -> 2 -> 1` obstruction.
+
+This file is deliberately tiny and does not live in `PressureAccounting`.
+It proves only that the one-step accelerated odd cycle equation
+
+  3 * n + 1 = 2 ^ h * n
+
+has no positive scaled copies except the genuine boundary point `n = 1`,
+`h = 2`.  It does not rule out arbitrary nontrivial Collatz cycles and does
+not prove convergence.
+-/
+
+/--
+If the scaled one-step odd cycle equation has height at least `3`, then it
+contradicts positivity.
+
+For `h ≥ 3`, the right-hand side is at least `8 * n`, while the left-hand side
+is only `3 * n + 1`.
+-/
+theorem collatz_scaled_one_cycle_h_not_ge_three
+    {n h : ℕ}
+    (hn : 0 < n)
+    (hcycle : 3 * n + 1 = 2 ^ h * n) :
+    ¬ 3 ≤ h := by
+  intro hh
+  have hpow : 8 ≤ 2 ^ h := by
+    have hpow' := Nat.pow_le_pow_right (by omega : 0 < 2) hh
+    norm_num at hpow'
+    exact hpow'
+  have hmul : 8 * n ≤ 2 ^ h * n :=
+    Nat.mul_le_mul_right n hpow
+  rw [← hcycle] at hmul
+  omega
+
+/-- Height `0` cannot satisfy the positive scaled one-step cycle equation. -/
+theorem collatz_scaled_one_cycle_h_ne_zero
+    {n h : ℕ}
+    (hn : 0 < n)
+    (hcycle : 3 * n + 1 = 2 ^ h * n) :
+    h ≠ 0 := by
+  intro hh
+  subst h
+  norm_num at hcycle
+  omega
+
+/-- Height `1` cannot satisfy the positive scaled one-step cycle equation. -/
+theorem collatz_scaled_one_cycle_h_ne_one
+    {n h : ℕ}
+    (hn : 0 < n)
+    (hcycle : 3 * n + 1 = 2 ^ h * n) :
+    h ≠ 1 := by
+  intro hh
+  subst h
+  norm_num at hcycle
+  omega
+
+/--
+The scaled `1 -> 4 -> 2 -> 1` one-cycle equation has only the positive
+solution `n = 1`, `h = 2`.
+
+This is a one-cycle obstruction only: it rules out scaled copies where one
+accelerated odd step returns to the same odd state.  It is not a theorem about
+all Collatz cycles or Collatz convergence.
+-/
+theorem collatz_scaled_one_cycle_eq_one
+    {n h : ℕ}
+    (hn : 0 < n)
+    (hcycle : 3 * n + 1 = 2 ^ h * n) :
+    n = 1 ∧ h = 2 := by
+  have hnot3 := collatz_scaled_one_cycle_h_not_ge_three hn hcycle
+  have hhcases : h = 0 ∨ h = 1 ∨ h = 2 := by
+    omega
+  rcases hhcases with rfl | rfl | rfl
+  · norm_num at hcycle
+    omega
+  · norm_num at hcycle
+    omega
+  · norm_num at hcycle
+    constructor <;> omega
+
+/--
+The `4 * n` boundary equation for the familiar one-cycle has the unique
+positive scale `n = 1`.
+-/
+theorem collatz_one_four_two_one_scaled_boundary_unique
+    {n : ℕ} (_hn : 0 < n)
+    (h : 3 * n + 1 = 4 * n) :
+    n = 1 := by
+  omega
+
+/-- The genuine `1 -> 4 -> 2 -> 1` boundary satisfies the scaled equation. -/
+theorem collatz_one_four_two_one_scaled_boundary_exists :
+    3 * 1 + 1 = 2 ^ 2 * 1 := by
+  norm_num
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
index d9e9c18c..051364ac 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -545,6 +545,52 @@ structure SourcePressureAccountedIntervalFamily
   pairwiseDisjoint :
     SourcePressureAccountedIntervalListPairwiseDisjoint items

+/--
+Empty accounted-interval family.
+
+This is only the empty explicit family.  It does not assert that there are no
+accounted intervals in the ambient pressure window.
+-/
+def sourcePressureAccountedIntervalFamily_nil
+    (n : OddNat) (k r : ℕ) :
+    SourcePressureAccountedIntervalFamily n k r :=
+  { items := []
+    pairwiseDisjoint :=
+      sourcePressureAccountedIntervalListPairwiseDisjoint_nil }
+
+/--
+Singleton accounted-interval family.
+
+This packages one already-accounted interval as a family.  It is a local
+carrier constructor, not a maximality or coverage statement.
+-/
+def sourcePressureAccountedIntervalFamily_singleton
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureAccountedInterval n k r) :
+    SourcePressureAccountedIntervalFamily n k r :=
+  { items := [A]
+    pairwiseDisjoint :=
+      sourcePressureAccountedIntervalListPairwiseDisjoint_singleton A }
+
+/--
+Cons constructor for accounted-interval families.
+
+The new head must be explicitly disjoint from every existing family item.
+Nothing in this constructor infers disjointness from pressure accounting alone,
+and it still does not introduce coverage, prefix behavior, or union accounting.
+-/
+def sourcePressureAccountedIntervalFamily_cons
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureAccountedInterval n k r)
+    (F : SourcePressureAccountedIntervalFamily n k r)
+    (hhead : ∀ B ∈ F.items,
+      SourcePressureAccountedIntervalsDisjoint A B) :
+    SourcePressureAccountedIntervalFamily n k r :=
+  { items := A :: F.items
+    pairwiseDisjoint :=
+      sourcePressureAccountedIntervalListPairwiseDisjoint_cons
+        hhead F.pairwiseDisjoint }
+
 /--
 Family budget inherited from the list budget.

@@ -569,6 +615,31 @@ theorem sourcePressureAccountedIntervalFamily_sum_neg_of_nonempty
       SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0 :=
   sourcePressureAccountedInterval_list_sum_neg_of_nonempty hF

+/-- The singleton-family budget is the one-interval `≤ -1` budget. -/
+theorem sourcePressureAccountedIntervalFamily_singleton_sum_le_neg_one
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureAccountedInterval n k r) :
+    ((sourcePressureAccountedIntervalFamily_singleton A).items.map (fun A =>
+      SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -1 := by
+  simpa [sourcePressureAccountedIntervalFamily_singleton] using
+    sourcePressureAccountedInterval_intervalNetDrop_le_neg_one A
+
+/--
+The cons-family budget is the general family budget specialized to the cons
+constructor.
+-/
+theorem sourcePressureAccountedIntervalFamily_cons_sum_le_neg_length
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureAccountedInterval n k r)
+    (F : SourcePressureAccountedIntervalFamily n k r)
+    (hhead : ∀ B ∈ F.items,
+      SourcePressureAccountedIntervalsDisjoint A B) :
+    (((sourcePressureAccountedIntervalFamily_cons A F hhead).items).map (fun A =>
+      SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤
+        -((((sourcePressureAccountedIntervalFamily_cons A F hhead).items.length : ℕ) : ℤ)) :=
+  sourcePressureAccountedIntervalFamily_sum_le_neg_length
+    (sourcePressureAccountedIntervalFamily_cons A F hhead)
+
 /--
 Ordered non-overlap for two natural-number half-open intervals.

@@ -584,12 +655,35 @@ theorem NatIntervalsDisjoint.of_before
     NatIntervalsDisjoint a len b len' :=
   Or.inl h

+/--
+Transitive-like composition for ordered non-overlap.
+
+The second interval's length is irrelevant for the conclusion because
+`NatIntervalBefore a len b len'` only records `a + len ≤ b`.
+-/
+theorem NatIntervalBefore.trans_like
+    {a len b len' c len'' : ℕ}
+    (hAB : NatIntervalBefore a len b len')
+    (hBC : NatIntervalBefore b len' c len'') :
+    NatIntervalBefore a len c len'' := by
+  unfold NatIntervalBefore at hAB hBC ⊢
+  omega
+
 /-- Ordered non-overlap for two accounted intervals. -/
 def SourcePressureAccountedIntervalBefore
     {n : OddNat} {k r : ℕ}
     (A B : SourcePressureAccountedInterval n k r) : Prop :=
   NatIntervalBefore A.start A.len B.start B.len

+/-- Transitive-like composition for ordered accounted intervals. -/
+theorem SourcePressureAccountedIntervalBefore.trans_like
+    {n : OddNat} {k r : ℕ}
+    {A B C : SourcePressureAccountedInterval n k r}
+    (hAB : SourcePressureAccountedIntervalBefore A B)
+    (hBC : SourcePressureAccountedIntervalBefore B C) :
+    SourcePressureAccountedIntervalBefore A C :=
+  NatIntervalBefore.trans_like hAB hBC
+
 /-- Ordered accounted intervals are disjoint. -/
 theorem SourcePressureAccountedIntervalsDisjoint.of_before
     {n : OddNat} {k r : ℕ}
@@ -598,4 +692,25 @@ theorem SourcePressureAccountedIntervalsDisjoint.of_before
     SourcePressureAccountedIntervalsDisjoint A B :=
   NatIntervalsDisjoint.of_before h

+/--
+Two-element family constructor from ordered non-overlap.
+
+This is a sorted-family seed: `[A, B]` is accepted because `A` lies before
+`B`, hence the two intervals are disjoint.  It still says nothing about
+covering all positive pressure depths or being a maximal family.
+-/
+def sourcePressureAccountedIntervalFamily_pair_of_before
+    {n : OddNat} {k r : ℕ}
+    (A B : SourcePressureAccountedInterval n k r)
+    (hAB : SourcePressureAccountedIntervalBefore A B) :
+    SourcePressureAccountedIntervalFamily n k r :=
+  sourcePressureAccountedIntervalFamily_cons A
+    (sourcePressureAccountedIntervalFamily_singleton B)
+    (by
+      intro C hC
+      have hCB : C = B := by
+        simpa [sourcePressureAccountedIntervalFamily_singleton] using hC
+      subst C
+      exact SourcePressureAccountedIntervalsDisjoint.of_before hAB)
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-150.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-150.md
new file mode 100644
index 00000000..f57f3212
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-150.md
@@ -0,0 +1,204 @@
+# Report Petal 150
+
+## Checkpoint
+
+Checkpoint 150 implemented the family-constructor layer for explicit source
+pressure accounting and added the scaled `1 -> 4 -> 2 -> 1` one-cycle
+obstruction as a separate Collatz/PetalBridge file.
+
+The pressure-family work remains intentionally local:
+
+- no maximality,
+- no uniqueness,
+- no coverage,
+- no prefix behavior,
+- no union accounting,
+- no Collatz convergence.
+
+Disjointness is still an explicit field or hypothesis.
+
+## PressureAccounting additions
+
+File:
+
+```text
+DkMath/Collatz/PetalBridge/PressureAccounting.lean
+```
+
+Added family constructors:
+
+```lean
+def sourcePressureAccountedIntervalFamily_nil
+def sourcePressureAccountedIntervalFamily_singleton
+def sourcePressureAccountedIntervalFamily_cons
+```
+
+These are thin constructors over:
+
+```lean
+SourcePressureAccountedIntervalFamily
+SourcePressureAccountedIntervalListPairwiseDisjoint
+```
+
+The `cons` constructor requires an explicit head-disjointness hypothesis:
+
+```lean
+∀ B ∈ F.items, SourcePressureAccountedIntervalsDisjoint A B
+```
+
+This keeps the API honest: accounting data alone is not treated as
+disjointness evidence.
+
+## Budget corollaries
+
+Added:
+
+```lean
+theorem sourcePressureAccountedIntervalFamily_singleton_sum_le_neg_one
+theorem sourcePressureAccountedIntervalFamily_cons_sum_le_neg_length
+```
+
+The singleton theorem exposes the one-interval `≤ -1` budget at family level.
+The cons theorem is a named specialization of the existing family budget:
+
+```lean
+sourcePressureAccountedIntervalFamily_sum_le_neg_length
+```
+
+## Sorted / before skeleton
+
+Added:
+
+```lean
+theorem NatIntervalBefore.trans_like
+theorem SourcePressureAccountedIntervalBefore.trans_like
+def sourcePressureAccountedIntervalFamily_pair_of_before
+```
+
+The pair constructor builds a two-item family from ordered non-overlap:
+
+```lean
+[A, B]
+```
+
+where `A` lies before `B`.  This is only a sorted-family seed.  It does not
+claim that the pair covers a pressure region.
+
+## OneCycle
+
+Created:
+
+```text
+DkMath/Collatz/PetalBridge/OneCycle.lean
+```
+
+and imported it from:
+
+```text
+DkMath/Collatz/PetalBridge.lean
+```
+
+Accepted theorem:
+
+```lean
+theorem collatz_scaled_one_cycle_eq_one
+    {n h : ℕ}
+    (hn : 0 < n)
+    (hcycle : 3 * n + 1 = 2 ^ h * n) :
+    n = 1 ∧ h = 2
+```
+
+Supporting and boundary facts were also added:
+
+```lean
+theorem collatz_scaled_one_cycle_h_not_ge_three
+theorem collatz_scaled_one_cycle_h_ne_zero
+theorem collatz_scaled_one_cycle_h_ne_one
+theorem collatz_one_four_two_one_scaled_boundary_unique
+theorem collatz_one_four_two_one_scaled_boundary_exists
+```
+
+Interpretation:
+
+```text
+The familiar one-cycle boundary exists at n = 1, h = 2.
+It has no positive scaled copy satisfying one accelerated odd step
+back to the same odd state.
+```
+
+Non-claim:
+
+```text
+This does not rule out arbitrary nontrivial Collatz cycles.
+This does not prove Collatz convergence.
+```
+
+## Verification
+
+Commands run from `lean/dk_math`:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureAccounting
+lake build DkMath.Collatz.PetalBridge.OneCycle
+lake build DkMath.Collatz.PetalBridge
+```
+
+All passed.
+
+No local sorry hits:
+
+```text
+rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/OneCycle.lean
+```
+
+Both returned no matches.
+
+Whitespace check:
+
+```text
+git diff --check
+```
+
+passed.
+
+Known unrelated build warning:
+
+```text
+DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean: declaration uses `sorry`
+```
+
+This is pre-existing and outside the checkpoint files.
+
+## Inference for next checkpoint
+
+The safe next move is not coverage.  The next useful Lean surface is an
+ordered-family layer that remains explicit:
+
+```text
+list is sorted by NatIntervalBefore
+sorted adjacent intervals imply pairwise disjointness
+sorted accounted interval list can become SourcePressureAccountedIntervalFamily
+```
+
+The likely minimal API:
+
+```lean
+def SourcePressureAccountedIntervalListSortedBefore
+
+theorem sourcePressureAccountedIntervalListPairwiseDisjoint_of_sortedBefore
+
+def sourcePressureAccountedIntervalFamily_of_sortedBefore
+```
+
+This would let future code build larger explicit families from an ordered list
+without saying those intervals are maximal or cover the positive region.
+
+For OneCycle, the next small obstruction can be phrased as a negative theorem:
+
+```text
+No positive n satisfies 3*n + 1 = 2^h*n for h != 2.
+```
+
+This is already derivable from `collatz_scaled_one_cycle_eq_one`; it may be
+worth adding only if callers want a contradiction-style API.
````
`````
