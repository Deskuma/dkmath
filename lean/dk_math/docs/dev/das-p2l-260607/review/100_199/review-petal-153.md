# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.ValuationFlowBridge

gch: 25e74e6d4588d2c8390d0c0c7ede455151113328

## Report

実装を進めました。sub root は `ValuationFlowBridge` として薄く閉じ、main root の `PressureAccounting` に戻して sorted family / failure API を追加しています。

変更点:

- 追加: [ValuationFlowBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/ValuationFlowBridge.lean)
- 更新: [PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean)
- 更新: [PressureAccounting.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean)
- 追加レポート: [report-petal-151-b.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-151-b.md)
- 追加レポート: [report-petal-152.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-152.md)

確認済み:

- `lake build DkMath.Collatz.PetalBridge.ValuationFlowBridge`
- `lake build DkMath.Collatz.PetalBridge.PressureAccounting`
- `lake build DkMath.Collatz.PetalBridge`
- 対象 3 ファイルの `sorry` 検索はヒットなし
- `git diff --check` 通過

既存の `ZsigmondyCyclotomicResearch` の `sorry` warning は出ますが、今回の変更範囲外です。

## Review

## 結論

うむ、これは **採用** じゃ 👍️
今回の実装は、割り込み sub root を `ValuationFlowBridge` として薄く閉じ、そのうえで main root の `PressureAccounting` に戻って sorted family / failure API を進めている。流れとしてよい。

ただし、次からはぬしの指示どおり **main root 専念** でよい。
つまり、`OneCycle` / `ValuationFlowBridge` / ABC 接続はしばらく触らず、`PressureAccounting` の本線、特に **explicit pulse address list → accounted family → budget / failure** の方向へ戻す。

今回のレポートでは、`ValuationFlowBridge.lean` が追加され、`PetalBridge.lean` から import されている。また `PressureAccounting.lean` には sorted constructor、sorted family constructors、before-all-tail、failure API、sorted-or-failure dichotomy、budget wrappers が追加されている。対象ファイルの `sorry` 検索も通っている。

## 実装レビュー

## 1. sub root は閉じ方として良い

`ValuationFlowBridge.lean` は、割り込み調査の収納先としては良い。
`OneCycle` そのものに ABC import を入れず、bridge ファイルだけで

```text id="v0p2li"
closed one-step loop
  -> unit product
  -> no prime channel
  -> unit support mass
```

を読む形にしている。

これは「横道を閉じる」実装として正しい。
ただし、ここはもう十分。次 checkpoint では触らない方がよい。

## 2. `PressureAccounting` の sorted constructor は良い

追加された

```lean id="shnjdy"
sourcePressureAccountedIntervalListSortedBefore_cons
```

は、地味だが大事じゃ。
これで sorted list を帰納的に組み立てやすくなった。

さらに、

```lean id="flb6cz"
sourcePressureAccountedIntervalFamily_sorted_nil
sourcePressureAccountedIntervalFamily_sorted_singleton
sourcePressureAccountedIntervalFamily_sorted_cons
```

が入り、明示 sorted list から family を作る導線が太くなった。

これは main root の進展としてよい。

## 3. before-all-tail は次に効く

```lean id="qr3tl4"
sourcePressureAccountedInterval_before_all_tail_of_sortedBefore
```

は、後で head/tail 分解をするときにかなり効く。

意味は、

```text id="ik2zgx"
sorted list の head は、tail の全要素と disjoint
```

じゃ。

これにより、sorted list を cons で伸ばすとき、head が tail 全体と衝突しないことを project-facing theorem として呼べる。
今後 `SourcePressureIntervalPulseAddress` のリストに持ち上げるときにも、この定理が橋になる。

## 4. failure API は良いが、意味を狭く保つべし

今回追加された

```lean id="q6qnnl"
SourcePressureAccountedIntervalListSortedBeforeFailsAt
SourcePressureAccountedIntervalListHasSortedBeforeFailure
sourcePressureAccountedIntervalList_sorted_or_failure
```

は良い。
DkMath/PetalBridge らしく、成功ルートだけでなく failure / obstruction も first-class にした。

ただし注意点がある。

```text id="tck4ne"
not before
```

は、必ずしも overlap ではない。

たとえば、順序が逆なだけでも `A before B` は失敗する。
だからこの failure は、

```text id="0s75no"
sorted-before failure
```

であって、

```text id="s7vqeg"
overlap evidence
```

ではない。

ここは今後コメントで守るべきじゃ。

## 5. sorted-or-failure dichotomy はよい

```lean id="elckvj"
sourcePressureAccountedIntervalList_sorted_or_failure
```

が通ったのは良い。
これは任意の明示 list について、

```text id="hq63dg"
sorted として扱える
または
どこかに adjacent sorted-before failure がある
```

を返す。

これは「反例を捨てず、obstruction として保存する」PetalBridge の方針に合っている。

ただし、これも coverage ではない。
あくまで「与えられた list の内部構造」だけじゃ。

## 数学的意味

今回で main root 側はこうなった。

```text id="9b40rw"
accounted interval
  -> explicit list
  -> sorted-before list
  -> pairwise disjoint family
  -> negative budget

または

explicit list
  -> sorted-before failure
  -> obstruction evidence
```

つまり、成功モードと失敗モードが揃った。

これは大事じゃ。
これで次は、実際の `SourcePressureIntervalPulseAddress` のリストをこの accounting API に乗せられる。

## 次の重点

次は **main root 専念**。
具体的には、`PressureAccounting` 側で、既にある

```lean id="rba6xm"
sourcePressureAccountedInterval_of_intervalPulseAddress
```

を list / family へ持ち上げるのがよい。

今までは `SourcePressureAccountedInterval` という会計済み interval を直接扱っていた。
次は、より実体に近い

```lean id="xmx4fk"
SourcePressureIntervalPulseAddress
```

の明示リストから、accounted family / budget / sorted failure へ流す。

これが main root の自然な次段じゃ。

## 次の Codex 依頼

```text id="dh8bjr"
Checkpoint 153: Main root only — lift interval-pulse address lists into PressureAccounting families.

Context:
Checkpoint 152 closed the interruption branch as a thin ValuationFlowBridge and
advanced the main PressureAccounting root with sorted-family constructors and
failure API.

For this checkpoint, focus only on the main root:
DkMath.Collatz.PetalBridge.PressureAccounting.

Do not modify:
- OneCycle.lean
- ValuationFlowBridge.lean
- ABC files
unless a build import issue forces a tiny fix.

Main goal:
Lift the existing single-address bridge

  sourcePressureAccountedInterval_of_intervalPulseAddress

from one `SourcePressureIntervalPulseAddress` to explicit lists and sorted
families.

Global rules:
- Do not claim maximality.
- Do not claim uniqueness of pressure families.
- Do not claim coverage.
- Do not claim prefix behavior.
- Do not claim union accounting.
- Do not claim Collatz convergence.
- Keep all statements about explicitly supplied interval-pulse addresses.

Part A: list conversion from interval-pulse addresses.

Add a definition:

  def sourcePressureAccountedIntervalList_of_intervalPulseAddressList
      {n : OddNat} {k r : Nat}
      (L : List (SourcePressureIntervalPulseAddress n k r)) :
      List (SourcePressureAccountedInterval n k r) :=
    L.map sourcePressureAccountedInterval_of_intervalPulseAddress

If the long name is painful, choose a Lean-friendly project-facing name and
record it in the report.

Add simp/theorem wrappers for length:

  theorem sourcePressureAccountedIntervalList_of_intervalPulseAddressList_length
      ...
      :
      (sourcePressureAccountedIntervalList_of_intervalPulseAddressList L).length =
        L.length

Part B: pulse-address list budget.

Using the existing list budget for accounted intervals, prove:

  theorem sourcePressureIntervalPulseAddressList_sum_le_neg_length
      {n : OddNat} {k r : Nat}
      (L : List (SourcePressureIntervalPulseAddress n k r)) :
      ((sourcePressureAccountedIntervalList_of_intervalPulseAddressList L).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤
          -((L.length : Nat) : Int)

Important:
This theorem does not require sortedness or disjointness.
It is only the cost sum over explicitly supplied pulse-address witnesses.
It does not state union accounting.

Part C: pulse-address sorted-before predicate.

Define sortedness for interval-pulse address lists by reusing the accounted
list sortedness.

Preferred shape:

  def SourcePressureIntervalPulseAddressListSortedBefore
      {n : OddNat} {k r : Nat}
      (L : List (SourcePressureIntervalPulseAddress n k r)) : Prop :=
    SourcePressureAccountedIntervalListSortedBefore
      (sourcePressureAccountedIntervalList_of_intervalPulseAddressList L)

Also define failure similarly:

  def SourcePressureIntervalPulseAddressListHasSortedBeforeFailure
      {n : OddNat} {k r : Nat}
      (L : List (SourcePressureIntervalPulseAddress n k r)) : Prop :=
    SourcePressureAccountedIntervalListHasSortedBeforeFailure
      (sourcePressureAccountedIntervalList_of_intervalPulseAddressList L)

Part D: pulse-address sorted/failure dichotomy.

Prove:

  theorem sourcePressureIntervalPulseAddressList_sorted_or_failure
      {n : OddNat} {k r : Nat}
      (L : List (SourcePressureIntervalPulseAddress n k r)) :
      SourcePressureIntervalPulseAddressListSortedBefore L ∨
        SourcePressureIntervalPulseAddressListHasSortedBeforeFailure L

This should follow directly from the accounted interval list theorem.

Part E: family from sorted pulse-address list.

Define:

  def sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList
      {n : OddNat} {k r : Nat}
      (L : List (SourcePressureIntervalPulseAddress n k r))
      (hsorted : SourcePressureIntervalPulseAddressListSortedBefore L) :
      SourcePressureAccountedIntervalFamily n k r :=
    sourcePressureAccountedIntervalFamily_of_sortedBefore
      (sourcePressureAccountedIntervalList_of_intervalPulseAddressList L)
      hsorted

Then prove a budget wrapper:

  theorem sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList_sum_le_neg_length
      {n : OddNat} {k r : Nat}
      (L : List (SourcePressureIntervalPulseAddress n k r))
      (hsorted : SourcePressureIntervalPulseAddressListSortedBefore L) :
      (((sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList
          L hsorted).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤
          -((L.length : Nat) : Int)

Part F: optional direct start/len before predicate for pulse addresses.

Only if easy, add a direct predicate:

  def SourcePressureIntervalPulseAddressBefore
      {n : OddNat} {k r : Nat}
      (A B : SourcePressureIntervalPulseAddress n k r) : Prop :=
    A.start + A.len ≤ B.start

Then prove this agrees with the accounted-interval before predicate after
conversion.

If this causes friction, skip it.  The mapped accounted-list predicate is enough.

Part G: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-153.md

Include:
- exact names chosen for list conversion,
- whether length theorem was added,
- whether pulse-address list budget was proved,
- whether sorted/failure predicates for pulse-address lists were added,
- whether sorted-or-failure dichotomy was proved,
- whether sorted pulse-address lists can build accounted families,
- whether any direct `SourcePressureIntervalPulseAddressBefore` predicate was added or skipped,
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

今回は良い。
sub root を閉じ、main root に戻る足場もできた。

次はもう横へ広げない。
`SourcePressureIntervalPulseAddress` の明示リストを `PressureAccounting` の sorted/failure/budget API に流し込む。
これが通れば、

```text id="8r21rl"
実際の pulse address
  -> accounted interval
  -> sorted explicit family
  -> negative budget
  -> failure witness
```

という本線が一本につながるぞ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 2e8e1d43..1d3bea5c 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -20,6 +20,7 @@ import DkMath.Collatz.PetalBridge.PressureDecay
 import DkMath.Collatz.PetalBridge.PressureFrontier
 import DkMath.Collatz.PetalBridge.PressureAccounting
 import DkMath.Collatz.PetalBridge.OneCycle
+import DkMath.Collatz.PetalBridge.ValuationFlowBridge
 import DkMath.Collatz.PetalBridge.Collision
 
 #print "file: DkMath.Collatz.PetalBridge"
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
index f840477c..5b9f2ee7 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -742,6 +742,16 @@ theorem sourcePressureAccountedIntervalListSortedBefore_singleton
     SourcePressureAccountedIntervalListSortedBefore [A] :=
   trivial
 
+/-- Cons constructor for adjacent sorted-before lists. -/
+theorem sourcePressureAccountedIntervalListSortedBefore_cons
+    {n : OddNat} {k r : ℕ}
+    {A B : SourcePressureAccountedInterval n k r}
+    {rest : List (SourcePressureAccountedInterval n k r)}
+    (hAB : SourcePressureAccountedIntervalBefore A B)
+    (htail : SourcePressureAccountedIntervalListSortedBefore (B :: rest)) :
+    SourcePressureAccountedIntervalListSortedBefore (A :: B :: rest) :=
+  ⟨hAB, htail⟩
+
 /--
 In an adjacent-sorted tail, a predecessor before the head is before every
 element of the tail.
@@ -862,4 +872,165 @@ theorem sourcePressureAccountedIntervalFamily_of_sortedBefore_sum_le_neg_length
   simpa [sourcePressureAccountedIntervalFamily_of_sortedBefore] using
     sourcePressureAccountedInterval_list_sum_le_neg_length L
 
+/-- Empty sorted-family constructor. -/
+def sourcePressureAccountedIntervalFamily_sorted_nil
+    (n : OddNat) (k r : ℕ) :
+    SourcePressureAccountedIntervalFamily n k r :=
+  sourcePressureAccountedIntervalFamily_nil n k r
+
+/-- Singleton sorted-family constructor. -/
+def sourcePressureAccountedIntervalFamily_sorted_singleton
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureAccountedInterval n k r) :
+    SourcePressureAccountedIntervalFamily n k r :=
+  sourcePressureAccountedIntervalFamily_singleton A
+
+/--
+Cons a head interval onto an adjacent-sorted nonempty tail and package the
+result as an explicit accounted-interval family.
+
+This is still only a constructor for explicitly supplied intervals.
+-/
+def sourcePressureAccountedIntervalFamily_sorted_cons
+    {n : OddNat} {k r : ℕ}
+    (A B : SourcePressureAccountedInterval n k r)
+    (rest : List (SourcePressureAccountedInterval n k r))
+    (hAB : SourcePressureAccountedIntervalBefore A B)
+    (htail : SourcePressureAccountedIntervalListSortedBefore (B :: rest)) :
+    SourcePressureAccountedIntervalFamily n k r :=
+  sourcePressureAccountedIntervalFamily_of_sortedBefore
+    (A :: B :: rest)
+    (sourcePressureAccountedIntervalListSortedBefore_cons hAB htail)
+
+/--
+The head of an adjacent-sorted accounted-interval list is disjoint from every
+tail item.
+
+This is the list-facing form needed by later family constructors.  It handles
+the empty-tail case directly and the nonempty-tail case through
+`before_all_of_sorted_tail`.
+-/
+theorem sourcePressureAccountedInterval_before_all_tail_of_sortedBefore
+    {n : OddNat} {k r : ℕ}
+    {A : SourcePressureAccountedInterval n k r}
+    {L : List (SourcePressureAccountedInterval n k r)}
+    (hsorted : SourcePressureAccountedIntervalListSortedBefore (A :: L)) :
+    ∀ B ∈ L, SourcePressureAccountedIntervalsDisjoint A B := by
+  cases L with
+  | nil =>
+      intro B hB
+      simp at hB
+  | cons B rest =>
+      intro C hC
+      have hAB : SourcePressureAccountedIntervalBefore A B := hsorted.1
+      have htail :
+          SourcePressureAccountedIntervalListSortedBefore (B :: rest) :=
+        hsorted.2
+      exact SourcePressureAccountedIntervalsDisjoint.of_before
+        (SourcePressureAccountedIntervalBefore.before_all_of_sorted_tail
+          hAB htail C hC)
+
+/-- Adjacent sorted-before failure for one neighboring pair. -/
+def SourcePressureAccountedIntervalListSortedBeforeFailsAt
+    {n : OddNat} {k r : ℕ}
+    (A B : SourcePressureAccountedInterval n k r) : Prop :=
+  ¬ SourcePressureAccountedIntervalBefore A B
+
+/--
+Existential adjacent sorted-before failure for an explicit list.
+
+This is an obstruction-style predicate: it records where adjacent sortedness
+breaks without claiming anything about coverage or dynamics.
+-/
+def SourcePressureAccountedIntervalListHasSortedBeforeFailure
+    {n : OddNat} {k r : ℕ} :
+    List (SourcePressureAccountedInterval n k r) → Prop
+  | [] => False
+  | [_] => False
+  | A :: B :: rest =>
+      ¬ SourcePressureAccountedIntervalBefore A B ∨
+        SourcePressureAccountedIntervalListHasSortedBeforeFailure (B :: rest)
+
+/-- A failed neighboring pair gives a sorted-before failure for the pair list. -/
+theorem sourcePressureAccountedIntervalListHasSortedBeforeFailure_pair
+    {n : OddNat} {k r : ℕ}
+    {A B : SourcePressureAccountedInterval n k r}
+    (hfail : ¬ SourcePressureAccountedIntervalBefore A B) :
+    SourcePressureAccountedIntervalListHasSortedBeforeFailure [A, B] :=
+  Or.inl hfail
+
+/-- A two-element list is sorted exactly when its neighboring pair is before. -/
+theorem sourcePressureAccountedIntervalListSortedBefore_pair_iff
+    {n : OddNat} {k r : ℕ}
+    {A B : SourcePressureAccountedInterval n k r} :
+    SourcePressureAccountedIntervalListSortedBefore [A, B] ↔
+      SourcePressureAccountedIntervalBefore A B := by
+  constructor
+  · intro h
+    exact h.1
+  · intro h
+    exact ⟨h, trivial⟩
+
+/-- Pair-level sortedness and failure are exact negations. -/
+theorem sourcePressureAccountedIntervalListHasSortedBeforeFailure_pair_iff
+    {n : OddNat} {k r : ℕ}
+    {A B : SourcePressureAccountedInterval n k r} :
+    SourcePressureAccountedIntervalListHasSortedBeforeFailure [A, B] ↔
+      ¬ SourcePressureAccountedIntervalBefore A B := by
+  constructor
+  · intro h
+    exact h.elim id False.elim
+  · exact sourcePressureAccountedIntervalListHasSortedBeforeFailure_pair
+
+/--
+Every explicit accounted-interval list is either adjacent-sorted or carries an
+adjacent sorted-before failure.
+
+This is not a coverage dichotomy.  It is only a first-class split for the
+explicit list that a caller has already supplied.
+-/
+theorem sourcePressureAccountedIntervalList_sorted_or_failure
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureAccountedInterval n k r)) :
+    SourcePressureAccountedIntervalListSortedBefore L ∨
+      SourcePressureAccountedIntervalListHasSortedBeforeFailure L := by
+  induction L with
+  | nil =>
+      exact Or.inl trivial
+  | cons A L ih =>
+      cases L with
+      | nil =>
+          exact Or.inl trivial
+      | cons B rest =>
+          by_cases hAB : SourcePressureAccountedIntervalBefore A B
+          · rcases ih with htail | htail
+            · exact Or.inl
+                (sourcePressureAccountedIntervalListSortedBefore_cons hAB htail)
+            · exact Or.inr (Or.inr htail)
+          · exact Or.inr (Or.inl hAB)
+
+/-- Singleton sorted-family budget wrapper. -/
+theorem sourcePressureAccountedIntervalFamily_sorted_singleton_sum_le_neg_one
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureAccountedInterval n k r) :
+    ((sourcePressureAccountedIntervalFamily_sorted_singleton A).items.map (fun A =>
+      SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -1 := by
+  simpa [sourcePressureAccountedIntervalFamily_sorted_singleton] using
+    sourcePressureAccountedIntervalFamily_singleton_sum_le_neg_one A
+
+/-- Sorted-cons family budget wrapper. -/
+theorem sourcePressureAccountedIntervalFamily_sorted_cons_sum_le_neg_length
+    {n : OddNat} {k r : ℕ}
+    (A B : SourcePressureAccountedInterval n k r)
+    (rest : List (SourcePressureAccountedInterval n k r))
+    (hAB : SourcePressureAccountedIntervalBefore A B)
+    (htail : SourcePressureAccountedIntervalListSortedBefore (B :: rest)) :
+    (((sourcePressureAccountedIntervalFamily_sorted_cons A B rest hAB htail).items).map (fun A =>
+      SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤
+        -(((A :: B :: rest).length : ℕ) : ℤ) := by
+  simpa [sourcePressureAccountedIntervalFamily_sorted_cons] using
+    sourcePressureAccountedIntervalFamily_of_sortedBefore_sum_le_neg_length
+      (A :: B :: rest)
+      (sourcePressureAccountedIntervalListSortedBefore_cons hAB htail)
+
 end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/ValuationFlowBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/ValuationFlowBridge.lean
new file mode 100644
index 00000000..dd6b0ce9
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/ValuationFlowBridge.lean
@@ -0,0 +1,114 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.OneCycle
+import DkMath.ABC.ValuationFlowBridge
+
+#print "file: DkMath.Collatz.PetalBridge.ValuationFlowBridge"
+
+namespace DkMath.Collatz
+
+/-
+Checkpoint 151-b / 152 sub root: thin valuation-flow bridge for the one-cycle
+unit boundary.
+
+This file is intentionally a bridge, not a new Collatz cycle theorem.  The
+ABC valuation-flow API talks about primitive channels for `a^d - b^d`; the
+one-cycle obstruction talks about the local equation
+
+  3 * n + 1 = 2^h * n.
+
+The shared vocabulary exposed here is therefore deliberately thin:
+
+  closed one-step loop -> unit product -> no prime channel -> unit support mass.
+
+Do not read this as general cycle uniqueness or convergence.
+-/
+
+/-- The scaled one-cycle equation closes only at the unit boundary. -/
+theorem oneCycle_unit_boundary_only
+    {n h : ℕ}
+    (hn : 0 < n)
+    (hcycle : 3 * n + 1 = 2 ^ h * n) :
+    n = 1 ∧ h = 2 :=
+  collatz_scaled_one_cycle_is_unit_boundary hn hcycle
+
+/-- Natural unit-product form for the scaled one-cycle bridge. -/
+theorem oneCycle_unit_product_nat
+    {n h : ℕ}
+    (hn : 0 < n)
+    (hcycle : 3 * n + 1 = 2 ^ h * n) :
+    n * (2 ^ h - 3) = 1 :=
+  collatz_scaled_one_cycle_nat_unit_product hn hcycle
+
+/-- Integer unit-product form for the scaled one-cycle bridge. -/
+theorem oneCycle_unit_product_int
+    {n h : ℕ}
+    (hn : 0 < n)
+    (hcycle : 3 * n + 1 = 2 ^ h * n) :
+    (((2 ^ h : ℕ) : ℤ) - 3) * (n : ℤ) = 1 :=
+  collatz_scaled_one_cycle_int_unit_product hn hcycle
+
+/-- No prime valuation-flow channel remains on the base of a closed one-cycle. -/
+theorem oneCycle_no_prime_channel_on_base
+    {p n h : ℕ}
+    (hp : Nat.Prime p)
+    (hn : 0 < n)
+    (hcycle : 3 * n + 1 = 2 ^ h * n) :
+    ¬ p ∣ n :=
+  collatz_scaled_one_cycle_no_prime_channel_on_base hp hn hcycle
+
+/-- No prime valuation-flow channel remains on the scale gap of a closed one-cycle. -/
+theorem oneCycle_no_prime_channel_on_scaleGap
+    {p n h : ℕ}
+    (hp : Nat.Prime p)
+    (hn : 0 < n)
+    (hcycle : 3 * n + 1 = 2 ^ h * n) :
+    ¬ p ∣ 2 ^ h - 3 :=
+  collatz_scaled_one_cycle_no_prime_channel_on_scale_gap hp hn hcycle
+
+/-- No prime valuation-flow channel remains on the explicit unit product. -/
+theorem oneCycle_no_prime_channel_on_unitProduct
+    {p n h : ℕ}
+    (hp : Nat.Prime p)
+    (hn : 0 < n)
+    (hcycle : 3 * n + 1 = 2 ^ h * n) :
+    ¬ p ∣ n * (2 ^ h - 3) :=
+  collatz_scaled_one_cycle_no_prime_channel_on_unit_product hp hn hcycle
+
+/-- The ABC support mass of the closed one-cycle unit product is `1`. -/
+theorem oneCycle_supportMass_unitProduct_eq_one
+    {n h : ℕ}
+    (hn : 0 < n)
+    (hcycle : 3 * n + 1 = 2 ^ h * n) :
+    DkMath.ABC.supportMass (n * (2 ^ h - 3)) = 1 := by
+  have hunit := oneCycle_unit_product_nat hn hcycle
+  rw [hunit]
+  simp [DkMath.ABC.supportMass]
+
+/-- The ABC radical of the closed one-cycle unit product is `1`. -/
+theorem oneCycle_rad_unitProduct_eq_one
+    {n h : ℕ}
+    (hn : 0 < n)
+    (hcycle : 3 * n + 1 = 2 ^ h * n) :
+    DkMath.ABC.rad (n * (2 ^ h - 3)) = 1 := by
+  have hunit := oneCycle_unit_product_nat hn hcycle
+  rw [hunit]
+  simp
+
+/--
+Closed one-cycle support has no growth beyond the unit.
+
+This is a convenience inequality for later valuation-flow bridge code.
+-/
+theorem oneCycle_no_supportMass_growth
+    {n h : ℕ}
+    (hn : 0 < n)
+    (hcycle : 3 * n + 1 = 2 ^ h * n) :
+    DkMath.ABC.supportMass (n * (2 ^ h - 3)) ≤ 1 := by
+  rw [oneCycle_supportMass_unitProduct_eq_one hn hcycle]
+
+end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-151-b.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-151-b.md
new file mode 100644
index 00000000..438da4fb
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-151-b.md
@@ -0,0 +1,113 @@
+# report-petal-151-b
+
+Checkpoint: 151-b / 152 sub root
+
+Subject: converge the interruption around OneCycle valuation-flow reading.
+
+## Summary
+
+The interruption branch has been contained as a thin bridge:
+
+```text
+DkMath.Collatz.PetalBridge.OneCycle
+  -> DkMath.Collatz.PetalBridge.ValuationFlowBridge
+  -> DkMath.ABC.ValuationFlowBridge
+```
+
+The new file does not expand the general Collatz theory.  It records the
+valuation-flow reading of the already proved one-cycle boundary result.
+
+## Added File
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge/ValuationFlowBridge.lean
+```
+
+This file imports:
+
+```lean
+import DkMath.Collatz.PetalBridge.OneCycle
+import DkMath.ABC.ValuationFlowBridge
+```
+
+The ABC import is intentional.  The bridge is not a replacement for
+`DkMath.ABC.ValuationFlowBridge`; it is a Collatz-facing window into that
+language.
+
+## Implemented Theorems
+
+The bridge exposes the one-cycle result through names that match the
+valuation-flow interpretation:
+
+```lean
+theorem oneCycle_unit_boundary_only
+theorem oneCycle_unit_product_nat
+theorem oneCycle_unit_product_int
+theorem oneCycle_no_prime_channel_on_base
+theorem oneCycle_no_prime_channel_on_scaleGap
+theorem oneCycle_no_prime_channel_on_unitProduct
+```
+
+It also fixes the support/rad reading of the unit-product boundary:
+
+```lean
+theorem oneCycle_supportMass_unitProduct_eq_one
+theorem oneCycle_rad_unitProduct_eq_one
+theorem oneCycle_no_supportMass_growth
+```
+
+The key meaning is:
+
+```text
+3 * n + 1 = 2^h * n and 0 < n
+  -> n = 1 and h = 2
+  -> n * (2^h - 3) = 1
+  -> no prime support channel remains on the product
+  -> supportMass and rad are both 1
+```
+
+## Aggregate Import
+
+The aggregate module was updated:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+It now imports:
+
+```lean
+import DkMath.Collatz.PetalBridge.ValuationFlowBridge
+```
+
+## Non-Claims
+
+This checkpoint does not prove general Collatz convergence.
+
+This checkpoint does not classify all cycles.
+
+This checkpoint only records that the one-step scaled cycle equation has no
+nontrivial prime-support channel: the only positive solution is the unit
+boundary.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.ValuationFlowBridge
+lake build DkMath.Collatz.PetalBridge
+rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/ValuationFlowBridge.lean
+rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/OneCycle.lean
+git diff --check
+```
+
+The `rg` checks returned no matches.
+
+## Next Inference
+
+The sub-root branch should now stay closed unless a later proof needs a more
+general valuation-flow API.
+
+The main-root work should resume in `PressureAccounting`: sorted explicit
+families, failure witnesses, and budget wrappers are the next stable surface.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-152.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-152.md
new file mode 100644
index 00000000..b309b84e
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-152.md
@@ -0,0 +1,180 @@
+# report-petal-152
+
+Checkpoint: 152
+
+Subject: return to the main root, `PressureAccounting`, after closing the
+OneCycle valuation-flow interruption.
+
+## Summary
+
+The main-root implementation advanced the explicit accounted-interval API.
+
+The new surface keeps the current design deliberately narrow:
+
+```text
+explicit intervals
+  -> adjacent sorted-before predicate
+  -> pairwise disjoint family
+  -> budget wrapper
+```
+
+It also adds a first-class obstruction window:
+
+```text
+not adjacent-sorted
+  -> sorted-before failure witness
+```
+
+This gives later checkpoints a place to attach negative evidence without
+claiming coverage, maximality, or global Collatz behavior.
+
+## Implemented Additions
+
+### Sorted Constructor
+
+Added a direct cons constructor for adjacent sorted-before lists:
+
+```lean
+theorem sourcePressureAccountedIntervalListSortedBefore_cons
+```
+
+This makes recursive sorted-family construction easier to use.
+
+### Sorted Family Constructors
+
+Added named family constructors:
+
+```lean
+def sourcePressureAccountedIntervalFamily_sorted_nil
+def sourcePressureAccountedIntervalFamily_sorted_singleton
+def sourcePressureAccountedIntervalFamily_sorted_cons
+```
+
+These are wrappers around the existing explicit family constructors.  They do
+not generate intervals and do not assert coverage.
+
+### Tail Disjointness
+
+Added:
+
+```lean
+theorem sourcePressureAccountedInterval_before_all_tail_of_sortedBefore
+```
+
+This records that the head interval of an adjacent-sorted explicit list is
+disjoint from every tail interval.
+
+### Failure API
+
+Added:
+
+```lean
+def SourcePressureAccountedIntervalListSortedBeforeFailsAt
+def SourcePressureAccountedIntervalListHasSortedBeforeFailure
+```
+
+The failure predicate is an obstruction tool for explicit lists.  It says that
+some neighboring pair fails the sorted-before condition.
+
+### Pair-Level Obstruction Facts
+
+Added:
+
+```lean
+theorem sourcePressureAccountedIntervalListHasSortedBeforeFailure_pair
+theorem sourcePressureAccountedIntervalListSortedBefore_pair_iff
+theorem sourcePressureAccountedIntervalListHasSortedBeforeFailure_pair_iff
+```
+
+For a two-element list, sortedness and failure are exact negations of the same
+neighboring relation.
+
+### Explicit List Dichotomy
+
+Added:
+
+```lean
+theorem sourcePressureAccountedIntervalList_sorted_or_failure
+```
+
+Every explicit list is either adjacent-sorted or carries a first-class
+sorted-before failure.
+
+This is a local list-level dichotomy only.  It is not a coverage theorem.
+
+### Budget Wrappers
+
+Added:
+
+```lean
+theorem sourcePressureAccountedIntervalFamily_sorted_singleton_sum_le_neg_one
+theorem sourcePressureAccountedIntervalFamily_sorted_cons_sum_le_neg_length
+```
+
+These preserve the existing pressure-budget bounds through the new sorted
+family constructors.
+
+## Mathematical Reading
+
+The pressure-accounting layer now has two complementary modes:
+
+```text
+sorted mode:
+  intervals are explicitly ordered by before-relations
+  -> pairwise disjoint family
+  -> additive negative budget bound
+
+failure mode:
+  some adjacent before-relation fails
+  -> obstruction evidence is visible
+```
+
+This matches the current Petal/Collatz workflow: prove what can be cleanly
+budgeted, and make failure conditions explicit when the clean route breaks.
+
+## Non-Claims
+
+This checkpoint does not prove maximality of an interval family.
+
+This checkpoint does not prove uniqueness of sorted representations.
+
+This checkpoint does not prove that the intervals cover an orbit prefix.
+
+This checkpoint does not prove global convergence or cycle exclusion beyond
+the already isolated one-cycle boundary facts.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureAccounting
+lake build DkMath.Collatz.PetalBridge
+rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+git diff --check
+```
+
+The `rg` check returned no matches.
+
+The build still reports the existing unrelated warning from:
+
+```text
+DkMath.NumberTheory.ZsigmondyCyclotomicResearch
+```
+
+That warning is outside this checkpoint.
+
+## Next Implementation Direction
+
+The next stable target is to connect this explicit-list obstruction API to the
+next Collatz pressure object:
+
+```text
+adjacent failure
+  -> overlapping / non-before interval evidence
+  -> obstruction comment or theorem near the caller
+```
+
+If this closes cleanly, the following step should be a small bridge from sorted
+explicit families to the orbit-window objects already present in the Collatz
+PetalBridge tree.
````
`````
