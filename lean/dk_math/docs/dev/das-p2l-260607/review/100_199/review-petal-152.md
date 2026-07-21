# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.*

gch: f0e0977719837112c5abfbf29bc3dfc8f2acce6c

## Report

cp151 完了です。

[PressureAccounting.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean) に recursive な sorted-before predicate を追加し、隣接順序から pairwise disjoint family を作れるところまで固定しました。追加した主な API は以下です。

```lean
def SourcePressureAccountedIntervalListSortedBefore
theorem SourcePressureAccountedIntervalBefore.before_all_of_sorted_tail
theorem sourcePressureAccountedIntervalListPairwiseDisjoint_of_sortedBefore
def sourcePressureAccountedIntervalFamily_of_sortedBefore
theorem sourcePressureAccountedIntervalFamily_of_sortedBefore_sum_le_neg_length
```

[OneCycle.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/OneCycle.lean) には contradiction-style API と iff を追加しました。

```lean
theorem collatz_scaled_one_cycle_no_wrong_height
theorem collatz_scaled_one_cycle_no_wrong_base
theorem collatz_scaled_one_cycle_iff
theorem one_four_two_one_petal_scaled_cycle_unique
```

`collatz_scaled_one_cycle_iff` は、正の `n` について `3 * n + 1 = 2 ^ h * n ↔ n = 1 ∧ h = 2` まで通っています。これはあくまで one-step scaled cycle equation の定理で、一般周期や収束は主張していません。

レポートは [report-petal-151.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-151.md) に作成済みです。

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.OneCycle
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b" .../PressureAccounting.lean
rg -n "\bsorry\b" .../OneCycle.lean
git diff --check
```

今回対象ファイルに `sorry` はありません。既存の `ZsigmondyCyclotomicResearch.lean` の warning は今回範囲外です。

## Review

## 結論

うむ、本線復帰として **採用** じゃ 👍️
Checkpoint 151 は、きれいに「明示 sorted family」へ進んでおる。

今回の主成果は二つ。

```text id="83lkaj"
PressureAccounting:
  adjacent sorted-before list
    -> pairwise disjoint
    -> accounted interval family
    -> explicit list budget

OneCycle:
  scaled one-cycle の contradiction API
  iff 形式
```

特に `PressureAccounting.lean` 側では、recursive な `SourcePressureAccountedIntervalListSortedBefore` を追加し、隣接順序から pairwise disjoint family を作れるところまで固定している。`OneCycle.lean` 側では、`collatz_scaled_one_cycle_iff` まで通っており、正の `n` について `3 * n + 1 = 2 ^ h * n ↔ n = 1 ∧ h = 2` が得られている。これはあくまで one-step scaled cycle equation の定理で、一般周期や収束を主張しない、という整理も正しい。

## 実装内容の解説

## 1. sorted-before predicate

今回追加された predicate は、隣接する accounted interval が順に並んでいることだけを言う。

```lean id="b04ucs"
def SourcePressureAccountedIntervalListSortedBefore
```

形はこうじゃ。

```lean id="1p5gh7"
[]             => True
[_]            => True
A :: B :: rest =>
  SourcePressureAccountedIntervalBefore A B ∧
    SourcePressureAccountedIntervalListSortedBefore (B :: rest)
```

これは `List.Sorted` に寄せず、DkMath の interval address 語彙に合わせて **隣接順序** を明示した判断じゃ。よい。

この predicate は coverage ではない。
maximality でもない。
単に「この明示リストは、隣同士が前後関係を保っている」と言うだけじゃ。

## 2. sorted-before から pairwise disjoint へ

ここが今回の本丸じゃな。

```lean id="tfsh4r"
SourcePressureAccountedIntervalBefore.before_all_of_sorted_tail
```

が入り、

```text id="qxj56u"
A before B
B :: rest が sorted
```

から、

```text id="4xk55y"
A は B :: rest の全要素より before
```

を出す。

これにより、

```lean id="7jrqpk"
sourcePressureAccountedIntervalListPairwiseDisjoint_of_sortedBefore
```

が通っている。

数学的には、

```text id="9d2daf"
隣接順序が鎖として繋がる
  -> 任意の前要素は任意の後要素より前
  -> よって pairwise disjoint
```

ということじゃ。

これはかなり重要な骨格じゃ。
以前は pairwise disjoint を明示仮定として持つ family だった。今回からは、より扱いやすい **sorted list** から family を作れる。

## 3. family from sorted-before

追加された constructor はこれ。

```lean id="qt6lrq"
def sourcePressureAccountedIntervalFamily_of_sortedBefore
```

これは、

```text id="02nsk1"
sorted explicit list
  -> pairwise disjoint family
```

の橋じゃ。

さらに budget wrapper も入っている。

```lean id="z2c74p"
theorem sourcePressureAccountedIntervalFamily_of_sortedBefore_sum_le_neg_length
```

ここで大事なのは、sortedness は family を作るために使われるだけで、budget 自体は依然として explicit list budget だということじゃ。つまり、まだ union accounting はしていない。この境界線は守れている。

## 4. OneCycle API

`OneCycle.lean` 側では、次が追加された。

```lean id="jva4hn"
collatz_scaled_one_cycle_no_wrong_height
collatz_scaled_one_cycle_no_wrong_base
collatz_scaled_one_cycle_iff
one_four_two_one_petal_scaled_cycle_unique
```

特に `iff` は使いやすい。

```lean id="k8z8os"
theorem collatz_scaled_one_cycle_iff
    {n h : ℕ}
    (hn : 0 < n) :
    3 * n + 1 = 2 ^ h * n ↔ n = 1 ∧ h = 2
```

これで、前向きにも後ろ向きにも使える。
後続で「この式が出たなら即 `n=1,h=2`」「`n=1,h=2` なら式が成立」と両方向に書ける。

`one_four_two_one_petal_scaled_cycle_unique` という project-facing alias も良い。後で文書や bridge 側から呼ぶとき、数式名より意味が伝わりやすい。

## レビュー所見

## 良い点

今回の一番良い点は、**明示 family の扱いが一段自然になった** ことじゃ。

以前は、

```text id="uqnwm3"
pairwise disjoint を直接持つ family
```

だった。

今は、

```text id="2omg5b"
sorted list
  -> pairwise disjoint
  -> family
```

になった。

これは人間にとっても Lean にとっても扱いやすい。特に interval は自然に左から右へ並ぶので、sorted-before predicate を持つのは良い設計じゃ。

## 注意点

まだ次は言っていない。

```text id="hq61us"
sorted list が全 positive interval を覆う
sorted family が maximal
sorted family の union 上の pressure accounting が成立する
Collatz convergence
```

ここは未到達じゃ。

今回得たのは、

```text id="t39qvj"
明示された sorted list は pairwise disjoint family にできる
その family の explicit cost budget は負に落ちる
```

までじゃな。

これは Core-family の器であって、coverage ではない。

## ロードマップ上の位置

今の本線はこう見える。

```text id="eb0ib9"
single pulse
  -> accounted interval
  -> list budget
  -> pairwise-disjoint family
  -> sorted listからfamily生成   ← 今ここ
```

次の安全な本線は、

```text id="kp04vb"
sorted family を構成しやすくする
failure / obstruction を明示する
sorted family の head/tail 操作を整える
```

じゃ。

まだ coverage へは行かない。
だが、coverage に進むための「家族操作」は整えてよい。

## 次の Codex 依頼

次 checkpoint は、sorted family の constructor と failure evidence を整えるのがよい。
本線に戻ったので、ABC bridge は一旦横に置く。

```text id="gwh7tc"
Checkpoint 152: Sorted family constructors and obstruction-style failure API.

Context:
Checkpoint 151 added adjacent sorted-before lists for accounted intervals and
proved that sorted-before implies pairwise disjointness.

Main existing objects:

- SourcePressureAccountedInterval
- SourcePressureAccountedIntervalFamily
- SourcePressureAccountedIntervalBefore
- SourcePressureAccountedIntervalsDisjoint
- SourcePressureAccountedIntervalListSortedBefore
- SourcePressureAccountedIntervalBefore.before_all_of_sorted_tail
- sourcePressureAccountedIntervalListPairwiseDisjoint_of_sortedBefore
- sourcePressureAccountedIntervalFamily_of_sortedBefore
- sourcePressureAccountedIntervalFamily_of_sortedBefore_sum_le_neg_length

OneCycle also has contradiction-style API and an iff theorem now, but this
checkpoint should return to the PressureAccounting main line.

Global rules:
- Do not claim maximality.
- Do not claim uniqueness of pressure families.
- Do not claim coverage.
- Do not claim prefix behavior.
- Do not claim union accounting.
- Do not claim Collatz convergence.
- Keep all family/list statements about explicitly provided intervals.

Part A: sorted-before cons constructor.

Add a theorem that constructs sorted-before for cons.

Preferred shape:

  theorem sourcePressureAccountedIntervalListSortedBefore_cons
      {n : OddNat} {k r : Nat}
      {A B : SourcePressureAccountedInterval n k r}
      {rest : List (SourcePressureAccountedInterval n k r)}
      (hAB : SourcePressureAccountedIntervalBefore A B)
      (htail : SourcePressureAccountedIntervalListSortedBefore (B :: rest)) :
      SourcePressureAccountedIntervalListSortedBefore (A :: B :: rest)

Also add simple wrappers if useful:

  sourcePressureAccountedIntervalListSortedBefore_nil
  sourcePressureAccountedIntervalListSortedBefore_singleton

These may already exist; do not duplicate if they do.

Part B: sorted family constructors.

Add constructors that build families from sorted data.

1. Empty sorted family:

  def sourcePressureAccountedIntervalFamily_sorted_nil
      (n : OddNat) (k r : Nat) :
      SourcePressureAccountedIntervalFamily n k r

This can reuse the existing nil family or sortedBefore family.

2. Singleton sorted family:

  def sourcePressureAccountedIntervalFamily_sorted_singleton
      {n : OddNat} {k r : Nat}
      (A : SourcePressureAccountedInterval n k r) :
      SourcePressureAccountedIntervalFamily n k r

3. Cons onto sorted tail:

  def sourcePressureAccountedIntervalFamily_sorted_cons
      {n : OddNat} {k r : Nat}
      (A B : SourcePressureAccountedInterval n k r)
      (rest : List (SourcePressureAccountedInterval n k r))
      (hAB : SourcePressureAccountedIntervalBefore A B)
      (htail : SourcePressureAccountedIntervalListSortedBefore (B :: rest)) :
      SourcePressureAccountedIntervalFamily n k r

This should build the family from the list `A :: B :: rest`.

Part C: head-before-all derived from sorted list.

Expose a theorem at list level:

  theorem sourcePressureAccountedInterval_before_all_tail_of_sortedBefore
      {n : OddNat} {k r : Nat}
      {A : SourcePressureAccountedInterval n k r}
      {L : List (SourcePressureAccountedInterval n k r)}
      (hsorted : SourcePressureAccountedIntervalListSortedBefore (A :: L)) :
      ∀ B ∈ L, SourcePressureAccountedIntervalsDisjoint A B

This should use the existing
SourcePressureAccountedIntervalBefore.before_all_of_sorted_tail
where the tail is nonempty, and handle the empty tail case.

Part D: obstruction-style failure predicate.

Define a lightweight predicate recording adjacent sortedness failure.

Suggested shape:

  def SourcePressureAccountedIntervalListSortedBeforeFailsAt
      {n : OddNat} {k r : Nat}
      (A B : SourcePressureAccountedInterval n k r) : Prop :=
    ¬ SourcePressureAccountedIntervalBefore A B

Then for lists, add an existential failure predicate:

  def SourcePressureAccountedIntervalListHasSortedBeforeFailure
      {n : OddNat} {k r : Nat}
      : List (SourcePressureAccountedInterval n k r) -> Prop
    | [] => False
    | [_] => False
    | A :: B :: rest =>
        ¬ SourcePressureAccountedIntervalBefore A B ∨
          SourcePressureAccountedIntervalListHasSortedBeforeFailure (B :: rest)

Part E: sorted vs failure dichotomy for small shapes.

Do not try to prove a big classical decidability theorem unless easy.

Start with small useful facts:

1. Pair failure:

  theorem sourcePressureAccountedIntervalListHasSortedBeforeFailure_pair
      {A B : SourcePressureAccountedInterval n k r}
      (hfail : ¬ SourcePressureAccountedIntervalBefore A B) :
      SourcePressureAccountedIntervalListHasSortedBeforeFailure [A, B]

2. Pair sorted iff no failure:

  theorem sourcePressureAccountedIntervalListSortedBefore_pair_iff
      {A B : SourcePressureAccountedInterval n k r} :
      SourcePressureAccountedIntervalListSortedBefore [A, B] ↔
        SourcePressureAccountedIntervalBefore A B

3. Optional:
   if Lean has decidability for the before relation, prove a recursive
   dichotomy theorem:

  theorem sourcePressureAccountedIntervalList_sorted_or_failure
      (L : List (SourcePressureAccountedInterval n k r)) :
      SourcePressureAccountedIntervalListSortedBefore L ∨
        SourcePressureAccountedIntervalListHasSortedBeforeFailure L

Only attempt this if Decidable instances are available without pain.
No sorry.

Part F: budget wrappers for sorted constructors.

Add named wrappers for the sorted constructors if easy:

  sourcePressureAccountedIntervalFamily_sorted_cons_sum_le_neg_length
  sourcePressureAccountedIntervalFamily_sorted_singleton_sum_le_neg_one

These are convenience theorems only.  They must not use or imply coverage.

Part G: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-152.md

Include:
- which sorted constructors were added,
- whether before-all-tail theorem was added,
- whether failure predicates were added,
- which small failure/sorted theorems were proved,
- whether any full sorted-or-failure dichotomy was attempted or skipped,
- exact theorem statements accepted by Lean,
- explicit note that this checkpoint does not introduce maximality, uniqueness,
  coverage, prefix behavior, union accounting, or Collatz convergence.

Verification:

  lake build DkMath.Collatz.PetalBridge.PressureAccounting
  lake build DkMath.Collatz.PetalBridge

Run:

  rg -n "\\bsorry\\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean

Also run:

  git diff --check
```

## 総評

うむ、良い復帰じゃ。
割り込みの `OneCycle` / valuation-flow 調査で横の橋も見えたが、本線側では今回、

```text id="b469a9"
sorted explicit list
  -> pairwise disjoint family
  -> negative explicit budget
```

がしっかりした。

次は「sorted であること」と「sorted が壊れること」の両方を first-class にする段階じゃ。
DkMath/PetalBridge は、成功ルートだけでなく failure / obstruction も保存する方が強い。ここを整えると、いよいよ後で Gap を「未支配の余剰」として扱いやすくなるぞ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/OneCycle.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/OneCycle.lean
index 48dc302f..68e327d3 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/OneCycle.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/OneCycle.lean
@@ -106,4 +106,52 @@ theorem collatz_one_four_two_one_scaled_boundary_exists :
     3 * 1 + 1 = 2 ^ 2 * 1 := by
   norm_num

+/-- No positive scaled one-step cycle exists at a height other than `2`. -/
+theorem collatz_scaled_one_cycle_no_wrong_height
+    {n h : ℕ}
+    (hn : 0 < n)
+    (hcycle : 3 * n + 1 = 2 ^ h * n)
+    (hh : h ≠ 2) :
+    False := by
+  have hsol := collatz_scaled_one_cycle_eq_one hn hcycle
+  exact hh hsol.2
+
+/-- No positive scaled one-step cycle exists away from the base `n = 1`. -/
+theorem collatz_scaled_one_cycle_no_wrong_base
+    {n h : ℕ}
+    (hn : 0 < n)
+    (hcycle : 3 * n + 1 = 2 ^ h * n)
+    (hn1 : n ≠ 1) :
+    False := by
+  have hsol := collatz_scaled_one_cycle_eq_one hn hcycle
+  exact hn1 hsol.1
+
+/--
+Iff form of the positive scaled one-step cycle obstruction.
+
+The forward direction is `collatz_scaled_one_cycle_eq_one`; the reverse
+direction is the concrete `1 -> 4 -> 2 -> 1` boundary equation.  This remains
+only a statement about `3 * n + 1 = 2 ^ h * n`.
+-/
+theorem collatz_scaled_one_cycle_iff
+    {n h : ℕ}
+    (hn : 0 < n) :
+    3 * n + 1 = 2 ^ h * n ↔ n = 1 ∧ h = 2 := by
+  constructor
+  · exact collatz_scaled_one_cycle_eq_one hn
+  · intro hsol
+    rcases hsol with ⟨rfl, rfl⟩
+    norm_num
+
+/--
+Project-facing alias for the scaled `1 -> 4 -> 2 -> 1` Petal one-cycle
+uniqueness theorem.
+-/
+theorem one_four_two_one_petal_scaled_cycle_unique
+    {n h : ℕ}
+    (hn : 0 < n)
+    (hcycle : 3 * n + 1 = 2 ^ h * n) :
+    n = 1 ∧ h = 2 :=
+  collatz_scaled_one_cycle_eq_one hn hcycle
+
 end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
index 051364ac..f840477c 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -713,4 +713,153 @@ def sourcePressureAccountedIntervalFamily_pair_of_before
       subst C
       exact SourcePressureAccountedIntervalsDisjoint.of_before hAB)

+/--
+Adjacent sortedness for an explicit accounted-interval list.
+
+This predicate only records local ordered non-overlap between neighboring
+items.  It is not a coverage, maximality, prefix, or union-accounting claim.
+-/
+def SourcePressureAccountedIntervalListSortedBefore
+    {n : OddNat} {k r : ℕ} :
+    List (SourcePressureAccountedInterval n k r) → Prop
+  | [] => True
+  | [_] => True
+  | A :: B :: rest =>
+      SourcePressureAccountedIntervalBefore A B ∧
+        SourcePressureAccountedIntervalListSortedBefore (B :: rest)
+
+/-- The empty list is sorted by adjacent ordered non-overlap. -/
+theorem sourcePressureAccountedIntervalListSortedBefore_nil
+    {n : OddNat} {k r : ℕ} :
+    SourcePressureAccountedIntervalListSortedBefore
+      ([] : List (SourcePressureAccountedInterval n k r)) :=
+  trivial
+
+/-- A singleton list is sorted by adjacent ordered non-overlap. -/
+theorem sourcePressureAccountedIntervalListSortedBefore_singleton
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureAccountedInterval n k r) :
+    SourcePressureAccountedIntervalListSortedBefore [A] :=
+  trivial
+
+/--
+In an adjacent-sorted tail, a predecessor before the head is before every
+element of the tail.
+
+This is the local bridge from adjacent ordering to pairwise disjointness.
+-/
+theorem SourcePressureAccountedIntervalBefore.before_all_of_sorted_tail
+    {n : OddNat} {k r : ℕ}
+    {A B : SourcePressureAccountedInterval n k r}
+    {rest : List (SourcePressureAccountedInterval n k r)}
+    (hAB : SourcePressureAccountedIntervalBefore A B)
+    (hsorted :
+      SourcePressureAccountedIntervalListSortedBefore (B :: rest)) :
+    ∀ C ∈ B :: rest, SourcePressureAccountedIntervalBefore A C := by
+  induction rest generalizing A B with
+  | nil =>
+      intro C hC
+      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
+      subst C
+      exact hAB
+  | cons C rest ih =>
+      have hBC : SourcePressureAccountedIntervalBefore B C := hsorted.1
+      have htail :
+          SourcePressureAccountedIntervalListSortedBefore (C :: rest) :=
+        hsorted.2
+      intro D hD
+      simp only [List.mem_cons] at hD
+      rcases hD with hD | hD
+      · subst D
+        exact hAB
+      · have hAC :
+            SourcePressureAccountedIntervalBefore A C :=
+          SourcePressureAccountedIntervalBefore.trans_like hAB hBC
+        exact ih hAC htail D (by simpa using hD)
+
+/-- Sorted-before empty lists are pairwise disjoint. -/
+theorem sourcePressureAccountedIntervalListPairwiseDisjoint_of_sortedBefore_nil
+    {n : OddNat} {k r : ℕ} :
+    SourcePressureAccountedIntervalListPairwiseDisjoint
+      ([] : List (SourcePressureAccountedInterval n k r)) :=
+  sourcePressureAccountedIntervalListPairwiseDisjoint_nil
+
+/-- Sorted-before singleton lists are pairwise disjoint. -/
+theorem sourcePressureAccountedIntervalListPairwiseDisjoint_of_sortedBefore_singleton
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureAccountedInterval n k r) :
+    SourcePressureAccountedIntervalListPairwiseDisjoint [A] :=
+  sourcePressureAccountedIntervalListPairwiseDisjoint_singleton A
+
+/-- A sorted-before pair is pairwise disjoint. -/
+theorem sourcePressureAccountedIntervalListPairwiseDisjoint_of_sortedBefore_pair
+    {n : OddNat} {k r : ℕ}
+    {A B : SourcePressureAccountedInterval n k r}
+    (hAB : SourcePressureAccountedIntervalBefore A B) :
+    SourcePressureAccountedIntervalListPairwiseDisjoint [A, B] :=
+  (sourcePressureAccountedIntervalFamily_pair_of_before A B hAB).pairwiseDisjoint
+
+/--
+Adjacent sortedness implies pairwise disjointness for explicit accounted
+interval lists.
+
+The proof turns the adjacent order chain into a head-before-all-tail fact and
+then uses `before -> disjoint`.  It still does not say the list covers any
+ambient pressure region.
+-/
+theorem sourcePressureAccountedIntervalListPairwiseDisjoint_of_sortedBefore
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureAccountedInterval n k r)}
+    (hsorted : SourcePressureAccountedIntervalListSortedBefore L) :
+    SourcePressureAccountedIntervalListPairwiseDisjoint L := by
+  induction L with
+  | nil =>
+      exact sourcePressureAccountedIntervalListPairwiseDisjoint_nil
+  | cons A L ih =>
+      cases L with
+      | nil =>
+          exact sourcePressureAccountedIntervalListPairwiseDisjoint_singleton A
+      | cons B rest =>
+          have hAB : SourcePressureAccountedIntervalBefore A B := hsorted.1
+          have htailSorted :
+              SourcePressureAccountedIntervalListSortedBefore (B :: rest) :=
+            hsorted.2
+          refine sourcePressureAccountedIntervalListPairwiseDisjoint_cons ?_ ?_
+          · intro C hC
+            exact SourcePressureAccountedIntervalsDisjoint.of_before
+              (SourcePressureAccountedIntervalBefore.before_all_of_sorted_tail
+                hAB htailSorted C hC)
+          · exact ih htailSorted
+
+/--
+Family constructor from an adjacent-sorted explicit list.
+
+This only packages the list and the derived pairwise disjointness.  It is not
+a coverage or decomposition theorem.
+-/
+def sourcePressureAccountedIntervalFamily_of_sortedBefore
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureAccountedInterval n k r))
+    (hsorted : SourcePressureAccountedIntervalListSortedBefore L) :
+    SourcePressureAccountedIntervalFamily n k r :=
+  { items := L
+    pairwiseDisjoint :=
+      sourcePressureAccountedIntervalListPairwiseDisjoint_of_sortedBefore hsorted }
+
+/--
+Budget wrapper for a family built from an adjacent-sorted list.
+
+The sorted hypothesis is used only to construct the family; the budget remains
+the explicit list budget and does not imply coverage.
+-/
+theorem sourcePressureAccountedIntervalFamily_of_sortedBefore_sum_le_neg_length
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureAccountedInterval n k r))
+    (hsorted : SourcePressureAccountedIntervalListSortedBefore L) :
+    (((sourcePressureAccountedIntervalFamily_of_sortedBefore L hsorted).items).map (fun A =>
+      SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤
+        -((L.length : ℕ) : ℤ) := by
+  simpa [sourcePressureAccountedIntervalFamily_of_sortedBefore] using
+    sourcePressureAccountedInterval_list_sum_le_neg_length L
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-151.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-151.md
new file mode 100644
index 00000000..f34d366c
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-151.md
@@ -0,0 +1,217 @@
+# Report Petal 151
+
+## Checkpoint
+
+Checkpoint 151 thickened the explicit sorted-family side of source-pressure
+accounting and added contradiction-style API around the scaled
+`1 -> 4 -> 2 -> 1` one-cycle obstruction.
+
+The implementation continues to avoid the unsafe jumps:
+
+- no maximality,
+- no uniqueness of pressure families,
+- no coverage,
+- no prefix behavior,
+- no union accounting,
+- no Collatz convergence.
+
+## Sorted-before predicate
+
+File:
+
+```text
+DkMath/Collatz/PetalBridge/PressureAccounting.lean
+```
+
+Added a recursive adjacent-order predicate:
+
+```lean
+def SourcePressureAccountedIntervalListSortedBefore
+```
+
+Shape:
+
+```lean
+[]              => True
+[_]             => True
+A :: B :: rest  =>
+  SourcePressureAccountedIntervalBefore A B ∧
+    SourcePressureAccountedIntervalListSortedBefore (B :: rest)
+```
+
+This was chosen instead of `List.Sorted` because it keeps the local adjacent
+meaning explicit and matches the project vocabulary around interval addresses.
+
+## Sorted-before to pairwise-disjoint
+
+Added small cases:
+
+```lean
+theorem sourcePressureAccountedIntervalListSortedBefore_nil
+theorem sourcePressureAccountedIntervalListSortedBefore_singleton
+theorem sourcePressureAccountedIntervalListPairwiseDisjoint_of_sortedBefore_nil
+theorem sourcePressureAccountedIntervalListPairwiseDisjoint_of_sortedBefore_singleton
+theorem sourcePressureAccountedIntervalListPairwiseDisjoint_of_sortedBefore_pair
+```
+
+Added the bridge lemma:
+
+```lean
+theorem SourcePressureAccountedIntervalBefore.before_all_of_sorted_tail
+```
+
+This turns:
+
+```text
+A before B
+B :: rest is adjacent-sorted
+```
+
+into:
+
+```text
+A before every element of B :: rest
+```
+
+Then the full theorem was proved:
+
+```lean
+theorem sourcePressureAccountedIntervalListPairwiseDisjoint_of_sortedBefore
+```
+
+Meaning:
+
+```text
+adjacent sorted-before list
+  -> pairwise disjoint accounted-interval list
+```
+
+Non-meaning:
+
+```text
+sorted-before does not imply coverage of all positive pressure depths.
+```
+
+## Family from sorted-before
+
+Added:
+
+```lean
+def sourcePressureAccountedIntervalFamily_of_sortedBefore
+```
+
+This packages a sorted explicit list as:
+
+```lean
+SourcePressureAccountedIntervalFamily
+```
+
+using the derived pairwise-disjoint theorem.
+
+Added budget wrapper:
+
+```lean
+theorem sourcePressureAccountedIntervalFamily_of_sortedBefore_sum_le_neg_length
+```
+
+This is still only the explicit list budget.  The sorted hypothesis is used to
+construct the family, not to claim global decomposition.
+
+## OneCycle contradiction API
+
+File:
+
+```text
+DkMath/Collatz/PetalBridge/OneCycle.lean
+```
+
+Added:
+
+```lean
+theorem collatz_scaled_one_cycle_no_wrong_height
+theorem collatz_scaled_one_cycle_no_wrong_base
+theorem collatz_scaled_one_cycle_iff
+theorem one_four_two_one_petal_scaled_cycle_unique
+```
+
+The iff theorem accepted:
+
+```lean
+theorem collatz_scaled_one_cycle_iff
+    {n h : ℕ}
+    (hn : 0 < n) :
+    3 * n + 1 = 2 ^ h * n ↔ n = 1 ∧ h = 2
+```
+
+This remains only a theorem about the equation:
+
+```text
+3 * n + 1 = 2^h * n
+```
+
+It does not prove general Collatz cycle uniqueness and does not prove
+Collatz convergence.
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
+This is outside the checkpoint files.
+
+## Inference for next checkpoint
+
+The next safe family-side target is still not coverage.  A useful next layer
+would be sorted-family convenience constructors that preserve explicitness:
+
+```lean
+sourcePressureAccountedIntervalFamily_sorted_pair
+sourcePressureAccountedIntervalFamily_sorted_cons
+sourcePressureAccountedIntervalListSortedBefore_cons_of_before_all
+```
+
+A second possible route is to expose contradiction-style APIs for sorted
+families:
+
+```text
+if adjacent sortedness fails at some neighbor, the list cannot use
+sourcePressureAccountedIntervalFamily_of_sortedBefore
+```
+
+That would keep failure evidence first-class, matching the obstruction style
+used elsewhere in PetalBridge.
+
+On the OneCycle side, the next thin alias could be a "no scaled boundary except
+unit" theorem that presents `collatz_scaled_one_cycle_iff` in Petal language.
+This is only worthwhile if downstream files start preferring prose-facing names
+over the raw equation name.
````
`````
