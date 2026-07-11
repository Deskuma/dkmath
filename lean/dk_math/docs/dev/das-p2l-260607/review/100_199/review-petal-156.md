# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAccounting

gch: 2481d6bfdf606491693c9be24a1b02430cdb39d7

## Report

cp155 を実装しました。更新は [PressureAccounting.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean) のみです。

追加内容:

- `SourcePressureLocalIslandWitness`
  - Lean では `Σ j, Prop` ではなく `{ j : Nat // SourcePressureLocalIsland n k r j }` として実装
- `sourcePressureIntervalPulseAddress_of_localIslandWitness`
- local-island witness list から pulse-address family への変換
- witness list の sorted / failure predicate
- sorted/failure split theorem
- sorted witness list から accounted family への lift
- length / budget / nonempty negative budget wrappers
- singleton local-island witness wrapper

レポート追加済み:
[report-petal-155.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-155.md)

確認:

- `lake build DkMath.Collatz.PetalBridge.PressureAccounting` 通過
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier` 通過
- `lake build DkMath.Collatz.PetalBridge` 通過
- 対象 2 ファイルの `sorry` 検索ヒットなし
- `git diff --check` 通過

今回も「明示的に与えられた local-island witnesses」だけを扱い、全 local island の列挙・coverage・maximality・union accounting・収束主張は入れていません。

## Review

## 結論

うむ、Checkpoint 155 は **採用** じゃ 👍️
今回も main root に集中できておる。`PressureAccounting.lean` のみ更新し、`PressureFrontier`、`OneCycle`、`ValuationFlowBridge`、ABC、NumberTheory には触れていない。これは方針どおりじゃ。

今回の中心は、

```text id="upjaq6"
local island witness
  -> interval-pulse address
  -> pulse-address family
  -> sorted / failure split
  -> sorted branch で accounted family
  -> budget
```

という、かなり実体寄りの main root 接続じゃな。

## 実装内容の解説

## 1. `SourcePressureLocalIslandWitness`

今回追加された carrier はこれじゃ。

```lean id="3ukcne"
abbrev SourcePressureLocalIslandWitness
    (n : OddNat) (k r : ℕ) :=
  { j : ℕ // SourcePressureLocalIsland n k r j }
```

これは良い判断じゃ。
数学的には `Σ j, SourcePressureLocalIsland n k r j` と読みたいところだが、`SourcePressureLocalIsland ...` は `Prop` なので、Lean で list carrier として扱うには `{ j : Nat // ... }` の `Subtype` が自然じゃ。

つまり、

```text id="cz7d27"
深さ j と、その j が local island である証拠
```

を一つの witness として包んだ。

これは、これまでの address family よりさらに frontier 実体に近い。

## 2. one witness から address へ

追加された変換はこれじゃ。

```lean id="l92ezy"
sourcePressureIntervalPulseAddress_of_localIslandWitness
```

これは既存の

```lean id="tjb1ut"
sourcePressureIntervalPulseAddress_of_localIsland
```

を使い、indexed witness を `SourcePressureIntervalPulseAddress` に変換する。
この接続はかなり重要じゃ。

前回までは、

```text id="33tqav"
address を明示的に与える
```

だった。

今回からは、

```text id="jrprg0"
local island witness を明示的に与えれば address を得られる
```

になった。

## 3. witness list から pulse-address family へ

追加された定義はこれ。

```lean id="cczmyf"
sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList
```

中身は明示 witness list を map するだけ。

```text id="4qi0o7"
List local-island witnesses
  -> List interval-pulse addresses
  -> SourcePressureIntervalPulseAddressFamily
```

ここでも「全 local islands を列挙した」とは言っていない。
報告でも、明示的に与えられた witness list だけを扱い、coverage や maximality は主張していないと整理されている。

これは安全じゃ。

## 4. sorted / failure split も witness list へ上がった

追加されたもの。

```lean id="lf7f3l"
SourcePressureLocalIslandWitnessListSortedBefore
SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
sourcePressureLocalIslandWitnessList_sorted_or_failure
```

これで、local-island witness list に対しても、

```text id="e2ihsc"
変換後に sorted
または
変換後に sorted-before failure
```

の分岐が使える。

ここでも failure は overlap ではない。
あくまで変換後 address family の order obstruction じゃ。

## 5. sorted witness list から accounted family へ

追加された lift はこれ。

```lean id="f0ed93"
sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList
```

これで、

```text id="b2nudb"
sorted local-island witness list
  -> pulse-address family
  -> accounted interval family
```

が通る。

さらに、

```lean id="ds7qvf"
sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList_length
sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList_sum_le_neg_length
sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList_sum_neg_of_nonempty
```

まで揃っている。

つまり、明示 witness list が sorted なら、

```text id="ne99h9"
accounted family の length = witness list length
net drop sum ≤ -length
nonempty なら net drop sum < 0
```

が読める。

これは main root の大きな接続じゃ。

## 良い点

今回の良いところは、**producer を捏造していない** ことじゃ。

まだ canonical な全 local-island list producer はない。
だから今回は、

```text id="c9gyx6"
明示的に与えた local-island witnesses
```

だけを扱っている。

この慎重さが大事じゃ。
今の段階で「全 local islands を列挙した」と言ってしまうと、coverage へ飛びすぎる。そこを避けている。

## 注意点

## 1. まだ全列挙ではない

今回の API は、

```text id="ibnz3j"
given explicit witness list
```

が主語じゃ。

まだ次は言っていない。

```text id="lk9aiq"
全 local island を生成する
全 pulse を列挙する
orbit window を覆う
maximal family である
```

ここは未到達じゃ。

## 2. sorted branch の budget は union accounting ではない

今回の budget は、あくまで明示 witness list を変換した各 interval の cost sum じゃ。

まだ、

```text id="mj98cm"
区間合併上の net drop
```

ではない。

この境界は維持するべし。

## 数学的な意味

今回で、main root はかなり美しく一本になった。

```text id="6rv5zh"
local island witness
  -> address
  -> address family
  -> sorted/failure
  -> accounted family
  -> negative budget
```

これは、`PressureFrontier` の局所幾何と `PressureAccounting` の会計が、witness list レベルで繋がったということじゃ。

ここまで来ると、次の自然な一手は report にもある通り、

```text id="cpvw92"
singleton local island witness
  -> singleton family
  -> sorted branch immediate
  -> accounted family length 1
  -> net drop ≤ -1
```

を名前付き API にすることじゃ。

これは main root のまま進められるし、coverage へ飛ばない。

## 次の Codex 依頼

```text id="0ghrhv"
Checkpoint 156: Main root only — singleton local-island witness accounting wrappers.

Scope:
Focus only on the main root.

Allowed files:
- DkMath/Collatz/PetalBridge/PressureAccounting.lean
- DkMath/Collatz/PetalBridge/PressureFrontier.lean only if needed for imports or names

Do not modify:
- OneCycle.lean
- ValuationFlowBridge.lean
- ABC files
- NumberTheory files

unless a build/import issue forces a tiny fix.

Context:
Checkpoint 155 added:

- SourcePressureLocalIslandWitness
- sourcePressureIntervalPulseAddress_of_localIslandWitness
- sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList
- SourcePressureLocalIslandWitnessListSortedBefore
- SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
- sourcePressureLocalIslandWitnessList_sorted_or_failure
- sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList
- sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList_sum_le_neg_length
- sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList_sum_neg_of_nonempty
- sourcePressureIntervalPulseAddressFamily_singleton_of_localIslandWitness

Global rules:
- Do not claim maximality.
- Do not claim uniqueness of pressure families.
- Do not claim coverage.
- Do not claim prefix behavior.
- Do not claim union accounting.
- Do not claim Collatz convergence.
- Keep all statements about explicitly supplied local-island witnesses.
- Failure means sorted-before failure, not overlap, unless extra hypotheses prove overlap.

Main goal:
Add named singleton wrappers for one explicit local-island witness.

Part A: singleton witness sortedness.

Prove:

  theorem sourcePressureLocalIslandWitnessListSortedBefore_singleton
      {n : OddNat} {k r : Nat}
      (W : SourcePressureLocalIslandWitness n k r) :
      SourcePressureLocalIslandWitnessListSortedBefore [W]

This should be trivial via the underlying pulse-address family/list sortedness.

Also prove, if easy:

  theorem sourcePressureLocalIslandWitnessList_no_failure_singleton
      {n : OddNat} {k r : Nat}
      (W : SourcePressureLocalIslandWitness n k r) :
      ¬ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W]

Only add this if it is easy.  No sorry.

Part B: singleton witness accounted family.

Define:

  def sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness
      {n : OddNat} {k r : Nat}
      (W : SourcePressureLocalIslandWitness n k r) :
      SourcePressureAccountedIntervalFamily n k r :=
    sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList
      [W]
      (sourcePressureLocalIslandWitnessListSortedBefore_singleton W)

Prove length:

  theorem sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_length
      {n : OddNat} {k r : Nat}
      (W : SourcePressureLocalIslandWitness n k r) :
      (sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness W).items.length = 1

Part C: singleton witness budget.

Prove:

  theorem sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_sum_le_neg_one
      {n : OddNat} {k r : Nat}
      (W : SourcePressureLocalIslandWitness n k r) :
      (((sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness W).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -1

Also prove strict negativity:

  theorem sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_sum_neg
      {n : OddNat} {k r : Nat}
      (W : SourcePressureLocalIslandWitness n k r) :
      (((sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness W).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0

Part D: direct address consistency.

If easy, prove that the singleton witness accounted family contains the same
accounted interval as the direct conversion:

  theorem sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_items
      {n : OddNat} {k r : Nat}
      (W : SourcePressureLocalIslandWitness n k r) :
      (sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness W).items =
        [sourcePressureAccountedInterval_of_intervalPulseAddress
          (sourcePressureIntervalPulseAddress_of_localIslandWitness W)]

This is a convenience theorem only.

Part E: local island direct theorem.

If useful, also add theorem versions with raw arguments:

  theorem sourcePressureLocalIsland_singleton_sum_le_neg_one
      (n : OddNat) (k r j : Nat)
      (hisland : SourcePressureLocalIsland n k r j) :
      ...

Construct `W : SourcePressureLocalIslandWitness n k r` internally as
`⟨j, hisland⟩`.

Only add this if it does not create theorem statement clutter.

Part F: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-156.md

Include:
- singleton sortedness theorem,
- whether singleton no-failure theorem was added,
- singleton accounted-family constructor,
- length theorem,
- budget ≤ -1 theorem,
- strict negative theorem,
- item-consistency theorem if added,
- raw local-island theorem if added,
- explicit note that this checkpoint still does not enumerate all local islands,
- explicit note that it does not introduce maximality, uniqueness, coverage,
  prefix behavior, union accounting, or Collatz convergence.

Verification:

  lake build DkMath.Collatz.PetalBridge.PressureAccounting
  lake build DkMath.Collatz.PetalBridge.PressureFrontier
  lake build DkMath.Collatz.PetalBridge

Run:

  rg -n "\\bsorry\\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
  rg -n "\\bsorry\\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean

Also run:

  git diff --check
```

## 総評

良いぞ。
今回で main root は、

```text id="ep5n7i"
local island witness list
  -> pulse-address family
  -> sorted/failure
  -> accounted family
  -> budget
```

まで伸びた。

次は singleton の名前付き定理を整えて、「local island 1 個なら即 budget が負」という使いやすい API にする。
これは小さいが、後で producer が出てきたときの呼び口としてかなり効くぞ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
index 3db563e9..6376fa84 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -1399,6 +1399,172 @@ theorem sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily_sum_ne
       sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList_sum_neg_of_nonempty
         hsorted hF
 
+/--
+Explicit local-island witness with its pressure-depth index.
+
+The index `j` is part of the witness.  Mathematically this is the intended
+`Σ j, SourcePressureLocalIsland n k r j` carrier, but the island predicate
+lives in `Prop`, so Lean represents the executable list carrier as a
+`Subtype`.
+-/
+abbrev SourcePressureLocalIslandWitness
+    (n : OddNat) (k r : ℕ) :=
+  { j : ℕ // SourcePressureLocalIsland n k r j }
+
+/--
+Convert one explicit local-island witness to an interval-pulse address.
+
+This uses the existing singleton producer from `PressureFrontier`.  It does
+not claim that the witness is part of a complete list of all local islands.
+-/
+def sourcePressureIntervalPulseAddress_of_localIslandWitness
+    {n : OddNat} {k r : ℕ}
+    (W : SourcePressureLocalIslandWitness n k r) :
+    SourcePressureIntervalPulseAddress n k r :=
+  sourcePressureIntervalPulseAddress_of_localIsland n k r W.val W.property
+
+/--
+Convert an explicit local-island witness list to a pulse-address family.
+
+The result is only the mapped list of supplied witnesses.  It does not
+enumerate all local islands, prove coverage, or identify a canonical frontier
+producer.
+-/
+def sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r)) :
+    SourcePressureIntervalPulseAddressFamily n k r :=
+  { items := L.map sourcePressureIntervalPulseAddress_of_localIslandWitness }
+
+@[simp]
+theorem sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList_length
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r)) :
+    (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList
+      L).items.length = L.length := by
+  simp [sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList]
+
+/--
+Sortedness for an explicit local-island witness list after conversion to
+interval-pulse addresses.
+-/
+def SourcePressureLocalIslandWitnessListSortedBefore
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
+  SourcePressureIntervalPulseAddressFamilySortedBefore
+    (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList L)
+
+/--
+Sorted-before failure for an explicit local-island witness list.
+
+This is still only an order obstruction after conversion.  It does not prove
+overlap and does not say that the list covers all local islands.
+-/
+def SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
+  SourcePressureIntervalPulseAddressFamilyHasSortedBeforeFailure
+    (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList L)
+
+/--
+Every explicit local-island witness list is either sorted after conversion or
+carries a sorted-before failure.
+
+This is a statement about the supplied list only; it does not enumerate all
+local islands.
+-/
+theorem sourcePressureLocalIslandWitnessList_sorted_or_failure
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r)) :
+    SourcePressureLocalIslandWitnessListSortedBefore L ∨
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L :=
+  sourcePressureIntervalPulseAddressFamily_sorted_or_failure
+    (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList L)
+
+/--
+Lift a sorted explicit local-island witness list to an accounted interval
+family.
+
+The sorted hypothesis is inherited through the pulse-address family conversion.
+No coverage, maximality, or union accounting is introduced.
+-/
+def sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    SourcePressureAccountedIntervalFamily n k r :=
+  sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily
+    (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList L)
+    hsorted
+
+@[simp]
+theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList_length
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    (sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList
+      L hsorted).items.length = L.length := by
+  simp [sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList]
+
+/--
+Budget wrapper for a sorted explicit local-island witness list.
+-/
+theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList_sum_le_neg_length
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    (((sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList
+      L hsorted).items).map
+      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤
+        -((L.length : ℕ) : ℤ) := by
+  simpa [sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList]
+    using
+      sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily_sum_le_neg_length
+        (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList L)
+        hsorted
+
+/--
+Nonempty budget wrapper for a sorted explicit local-island witness list.
+-/
+theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList_sum_neg_of_nonempty
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
+    (hL : L ≠ []) :
+    (((sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList
+      L hsorted).items).map
+      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0 := by
+  have hitems :
+      (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList
+        L).items ≠ [] := by
+    intro h
+    apply hL
+    simpa [sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList]
+      using h
+  simpa [sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList]
+    using
+      sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily_sum_neg_of_nonempty
+        (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList L)
+        hsorted hitems
+
+/--
+Singleton pulse-address family from one local-island witness.
+-/
+def sourcePressureIntervalPulseAddressFamily_singleton_of_localIslandWitness
+    {n : OddNat} {k r : ℕ}
+    (W : SourcePressureLocalIslandWitness n k r) :
+    SourcePressureIntervalPulseAddressFamily n k r :=
+  sourcePressureIntervalPulseAddressFamily_singleton
+    (sourcePressureIntervalPulseAddress_of_localIslandWitness W)
+
+@[simp]
+theorem sourcePressureIntervalPulseAddressFamily_singleton_of_localIslandWitness_length
+    {n : OddNat} {k r : ℕ}
+    (W : SourcePressureLocalIslandWitness n k r) :
+    (sourcePressureIntervalPulseAddressFamily_singleton_of_localIslandWitness
+      W).items.length = 1 := by
+  rfl
+
 /-- Singleton sorted-family budget wrapper. -/
 theorem sourcePressureAccountedIntervalFamily_sorted_singleton_sum_le_neg_one
     {n : OddNat} {k r : ℕ}
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-155.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-155.md
new file mode 100644
index 00000000..9399b8c3
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-155.md
@@ -0,0 +1,176 @@
+# report-petal-155
+
+Checkpoint: 155
+
+Subject: lift explicit local-island witness lists to pulse-address families.
+
+## Summary
+
+This checkpoint extended:
+
+```text
+DkMath.Collatz.PetalBridge.PressureAccounting
+```
+
+No `PressureFrontier`, `OneCycle`, `ValuationFlowBridge`, ABC, or
+NumberTheory files were modified.
+
+The new layer accepts an explicit list of local-island witnesses and maps it
+to the pulse-address family API introduced in checkpoints 153-154.
+
+## Witness Carrier
+
+Added:
+
+```lean
+abbrev SourcePressureLocalIslandWitness
+    (n : OddNat) (k r : Nat)
+```
+
+The implementation uses:
+
+```lean
+{ j : Nat // SourcePressureLocalIsland n k r j }
+```
+
+This is the Lean-safe form of the intended mathematical carrier:
+
+```text
+Sigma j, SourcePressureLocalIsland n k r j
+```
+
+The reason is that `SourcePressureLocalIsland n k r j` lives in `Prop`, so a
+plain dependent sigma over it is not the right executable list carrier here.
+
+## One-Witness Conversion
+
+Added:
+
+```lean
+def sourcePressureIntervalPulseAddress_of_localIslandWitness
+```
+
+This uses the existing producer:
+
+```lean
+sourcePressureIntervalPulseAddress_of_localIsland
+```
+
+and converts one indexed local-island witness into one
+`SourcePressureIntervalPulseAddress`.
+
+## Witness List Conversion
+
+Added:
+
+```lean
+def sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList
+```
+
+It maps the explicitly supplied witness list into a
+`SourcePressureIntervalPulseAddressFamily`.
+
+Length wrapper:
+
+```lean
+theorem sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList_length
+```
+
+## Sorted / Failure Layer
+
+Added:
+
+```lean
+def SourcePressureLocalIslandWitnessListSortedBefore
+def SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+theorem sourcePressureLocalIslandWitnessList_sorted_or_failure
+```
+
+The sorted/failure split is inherited from the produced pulse-address family.
+
+The failure side remains only sorted-before failure after conversion.  It does
+not imply overlap and does not say the list is complete.
+
+## Accounted-Family Lift
+
+Added:
+
+```lean
+def sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList
+```
+
+and wrappers:
+
+```lean
+theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList_length
+theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList_sum_le_neg_length
+theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList_sum_neg_of_nonempty
+```
+
+These reuse the sorted pulse-address family budget API.  The cost statement is
+still only over the explicitly supplied witness list.
+
+## Singleton Convenience
+
+Added:
+
+```lean
+def sourcePressureIntervalPulseAddressFamily_singleton_of_localIslandWitness
+theorem sourcePressureIntervalPulseAddressFamily_singleton_of_localIslandWitness_length
+```
+
+This is a small convenience wrapper for one indexed local-island witness.
+
+## Non-Claims
+
+This checkpoint does not enumerate all local islands.
+
+This checkpoint does not introduce:
+
+```text
+maximality
+uniqueness
+coverage
+prefix behavior
+union accounting
+Collatz convergence
+```
+
+All statements remain about explicitly supplied local-island witnesses.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureAccounting
+lake build DkMath.Collatz.PetalBridge.PressureFrontier
+lake build DkMath.Collatz.PetalBridge
+rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+```
+
+The `rg` checks returned no matches.
+
+The build still reports the existing unrelated warning:
+
+```text
+DkMath.NumberTheory.ZsigmondyCyclotomicResearch uses sorry
+```
+
+That warning is outside checkpoint 155.
+
+## Next Inference
+
+The next conservative step is to add small bridge facts for singleton local
+island witnesses:
+
+```text
+one witness
+  -> singleton family
+  -> sorted branch is immediate
+  -> accounted family has length 1 and net drop <= -1
+```
+
+This would stay within explicit witness accounting and still avoid any claim
+that all local islands have been found.
````
`````
