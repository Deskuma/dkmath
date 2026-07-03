# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAccounting

gch: 8653adf6e8ebb9bcb17bbbe0b15320c15aae2ce3

## Report

cp156 を実装しました。更新は [PressureAccounting.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean) のみです。

追加内容:

- singleton witness sortedness
  - `sourcePressureLocalIslandWitnessListSortedBefore_singleton`
- singleton no-failure
  - `sourcePressureLocalIslandWitnessList_no_failure_singleton`
- singleton accounted family constructor
  - `sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness`
- length / budget / strict negative wrappers
- direct item consistency theorem
- raw local-island 引数版
  - `sourcePressureLocalIsland_singleton_sum_le_neg_one`
  - `sourcePressureLocalIsland_singleton_sum_neg`

レポート追加済み:
[report-petal-156.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-156.md)

確認:

- `lake build DkMath.Collatz.PetalBridge.PressureAccounting` 通過
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier` 通過
- `lake build DkMath.Collatz.PetalBridge` 通過
- 対象 2 ファイルの `sorry` 検索ヒットなし
- `git diff --check` 通過

今回も「1つの明示 local-island witness」に限定し、全列挙・coverage・maximality・union accounting・収束主張は入れていません。

## Review

## 結論

うむ、Checkpoint 156 は **採用** じゃ 👍️
今回も main root に集中できておる。`PressureAccounting.lean` のみ更新し、`PressureFrontier`、`OneCycle`、`ValuationFlowBridge`、ABC、NumberTheory には触れていない。方針どおりじゃ。

今回の主成果は、

```text id="84q6zj"
one local-island witness
  -> singleton witness list
  -> sorted branch immediate
  -> singleton accounted family
  -> net drop ≤ -1
  -> net drop < 0
```

を名前付き API として固定したことじゃな。

これで「local island 1 個を見つけたら、その 1 個だけで会計上は負のコストを持つ」と即座に呼べるようになった。

## 実装内容の解説

## 1. singleton sortedness

追加された定理はこれ。

```lean id="5ww8kc"
theorem sourcePressureLocalIslandWitnessListSortedBefore_singleton
```

これは `[W]` が sorted であることを言う。
一要素なので当然だが、後続 API ではかなり便利じゃ。

さらに、

```lean id="0794js"
theorem sourcePressureLocalIslandWitnessList_no_failure_singleton
```

も入った。
一要素 list には隣接ペアがないので、sorted-before failure もない。

これで singleton case の sorted / failure 分岐が綺麗に閉じた。

## 2. singleton accounted family

追加された constructor はこれ。

```lean id="es3bwv"
def sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness
```

これは、前回までに作った

```lean id="8m11qn"
sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList
```

の singleton specialization じゃ。

つまり、ユーザー側・後続 theorem 側は、もう `[W]` と sorted 証明を毎回書かずに済む。

## 3. singleton budget

今回の中核はこの二つ。

```lean id="yi1e2m"
theorem sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_sum_le_neg_one
theorem sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_sum_neg
```

意味は、

```text id="xaczjt"
明示 local-island witness 1 個から作った accounted family の listed net drop は ≤ -1
```

かつ、

```text id="bajhqs"
strictly negative
```

じゃ。

これは小さいが強い。
今後 `SourcePressureLocalIsland` が出てきた瞬間に、局所的な負予算を直接取り出せる。

## 4. item consistency theorem

追加された、

```lean id="ovahgh"
theorem sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_items
```

も良い。

これは singleton family の中身が、直接変換した accounted interval と一致することを固定している。

```text id="40fn2s"
singleton witness family の items
  =
[direct accounted interval]
```

このような中身確認 theorem は、後で `simp` や rewrite で効く。
特に producer 側と accounting 側の表現が増えてきたので、こういう consistency theorem は大切じゃ。

## 5. raw local-island 引数版

追加された二つ。

```lean id="4h4ggl"
theorem sourcePressureLocalIsland_singleton_sum_le_neg_one
theorem sourcePressureLocalIsland_singleton_sum_neg
```

これは `W : SourcePressureLocalIslandWitness n k r` を作らずに、

```lean id="zg7nvs"
(j : ℕ)
(hisland : SourcePressureLocalIsland n k r j)
```

から直接呼べる wrapper じゃ。

実用性が高い。
後続の theorem は多くの場合、`j` と `hisland` を持っているはずなので、この raw 版があると使いやすい。

## 良い点

## 1. singleton API として閉じている

今回の checkpoint は、かなり小さいが完成度が高い。
一つの local island witness から、

```text id="sv3a00"
address
accounted interval
accounted family
length
items
budget
strict negativity
```

まで呼べる。

これは後続の producer / frontier theorem の使い勝手をかなり上げる。

## 2. non-claim が守られている

今回も、全 local islands の列挙、coverage、maximality、union accounting、収束主張は入っていない。レポートにも「1つの明示 local-island witness」に限定していると明記されておる。

これは重要じゃ。
今はまだ「見つけたものを会計する」段階であって、「全てを見つけた」と言う段階ではない。

## 注意点

## 1. singleton は強いが、大域情報ではない

今回の theorem は、

```text id="ztihgy"
one explicit local-island witness
```

が主語じゃ。

したがって、まだ次は言っていない。

```text id="9lnong"
local islands が必ず存在する
全 local islands を列挙できる
sorted family が orbit window を覆う
```

ここは未到達じゃ。

## 2. strict negative は listed cost の話

`sum_neg` は、singleton accounted family の listed net drop が負であるという話じゃ。
これは union accounting ではない。

つまり、

```text id="vlizvy"
この witness から得た会計項目の listed cost が負
```

であって、

```text id="7qi2za"
周辺全体の pressure region が負に支配された
```

ではない。

この線引きは維持するべし。

## 数学的な意味

ここまでで main root は、かなり階段が揃った。

```text id="yf63uu"
local island
  -> witness
  -> pulse address
  -> pulse-address family
  -> accounted family
  -> negative budget
```

今回で、その最小単位である singleton が閉じた。

これは DkMath 的には、

```text id="0gl9bq"
局所 pressure island は、会計上 1 単位以上の負予算を持つ
```

と読める。

もちろん「明示 witness があるなら」という条件つきじゃ。
しかし、これは後の finite family budget の atom になる。

## 次の重点

次はレポートにもある通り、two-witness layer が自然じゃ。

一要素は閉じた。
次は二要素。

```text id="0us8mt"
[W1, W2]
  -> sorted iff address(W1) before address(W2)
  -> failure iff not before
  -> sorted branch gives length 2
  -> budget ≤ -2
```

これを作ると、failure が「順序失敗」であることも、二要素で扱いやすくなる。

ただし、ここでも overlap は言わない。
`not before` は order failure であって、overlap ではない。

## 次の Codex 依頼

```text id="5w5myb"
Checkpoint 157: Main root only — two local-island witness accounting wrappers.

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
Checkpoint 156 added singleton local-island witness accounting wrappers:

- sourcePressureLocalIslandWitnessListSortedBefore_singleton
- sourcePressureLocalIslandWitnessList_no_failure_singleton
- sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness
- sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_length
- sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_sum_le_neg_one
- sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_sum_neg
- sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_items
- sourcePressureLocalIsland_singleton_sum_le_neg_one
- sourcePressureLocalIsland_singleton_sum_neg

Global rules:
- Do not claim maximality.
- Do not claim uniqueness of pressure families.
- Do not claim coverage.
- Do not claim prefix behavior.
- Do not claim union accounting.
- Do not claim Collatz convergence.
- Keep all statements about explicitly supplied local-island witnesses.
- Failure means sorted-before failure, not overlap, unless extra hypotheses
  prove overlap.

Main goal:
Add named two-witness wrappers for explicit local-island witness pairs.

Part A: direct before predicate for local-island witnesses.

Define:

  def SourcePressureLocalIslandWitnessBefore
      {n : OddNat} {k r : Nat}
      (W1 W2 : SourcePressureLocalIslandWitness n k r) : Prop :=
    SourcePressureIntervalPulseAddressBefore
      (sourcePressureIntervalPulseAddress_of_localIslandWitness W1)
      (sourcePressureIntervalPulseAddress_of_localIslandWitness W2)

Add theorem:

  theorem sourcePressureLocalIslandWitnessBefore_iff_addressBefore
      ...
      :
      SourcePressureLocalIslandWitnessBefore W1 W2 ↔
        SourcePressureIntervalPulseAddressBefore
          (sourcePressureIntervalPulseAddress_of_localIslandWitness W1)
          (sourcePressureIntervalPulseAddress_of_localIslandWitness W2)

This may be rfl.

Part B: pair sorted/failure iff.

Prove:

  theorem sourcePressureLocalIslandWitnessListSortedBefore_pair_iff
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r} :
      SourcePressureLocalIslandWitnessListSortedBefore [W1, W2] ↔
        SourcePressureLocalIslandWitnessBefore W1 W2

Prove:

  theorem sourcePressureLocalIslandWitnessListHasSortedBeforeFailure_pair_iff
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r} :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2] ↔
        ¬ SourcePressureLocalIslandWitnessBefore W1 W2

Make the comments explicit:
not before is an order failure only, not overlap evidence.

Part C: sorted pair accounted family.

Define:

  def sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair
      {n : OddNat} {k r : Nat}
      (W1 W2 : SourcePressureLocalIslandWitness n k r)
      (hbefore : SourcePressureLocalIslandWitnessBefore W1 W2) :
      SourcePressureAccountedIntervalFamily n k r :=
    sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList
      [W1, W2]
      ((sourcePressureLocalIslandWitnessListSortedBefore_pair_iff).2 hbefore)

Adjust theorem invocation syntax if needed.

Part D: pair length and item consistency.

Prove:

  theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_length
      ...
      :
      (sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair
        W1 W2 hbefore).items.length = 2

If easy, prove items theorem:

  theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_items
      ...
      :
      (sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair
        W1 W2 hbefore).items =
        [ sourcePressureAccountedInterval_of_intervalPulseAddress
            (sourcePressureIntervalPulseAddress_of_localIslandWitness W1),
          sourcePressureAccountedInterval_of_intervalPulseAddress
            (sourcePressureIntervalPulseAddress_of_localIslandWitness W2) ]

Part E: pair budget.

Prove:

  theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_sum_le_neg_two
      ...
      :
      (((sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair
        W1 W2 hbefore).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2

Also prove strict negativity:

  theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_sum_neg
      ...
      :
      (((sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair
        W1 W2 hbefore).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0

Part F: raw local-island pair theorem.

Only if the theorem statement remains readable, add raw argument versions:

  theorem sourcePressureLocalIsland_pair_sum_le_neg_two
      (n : OddNat) (k r j1 j2 : Nat)
      (h1 : SourcePressureLocalIsland n k r j1)
      (h2 : SourcePressureLocalIsland n k r j2)
      (hbefore :
        SourcePressureLocalIslandWitnessBefore
          (⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r)
          (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)) :
      ...

  theorem sourcePressureLocalIsland_pair_sum_neg
      ...

If these statements become too bulky, skip them and report that witness-level
theorems are preferable.

Part G: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-157.md

Include:
- direct witness-before predicate,
- pair sorted iff theorem,
- pair failure iff theorem,
- sorted pair accounted-family constructor,
- length theorem,
- item consistency theorem if added,
- budget ≤ -2 theorem,
- strict negative theorem,
- raw local-island pair theorem if added or skipped,
- explicit note that pair failure is not overlap evidence,
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

よいぞ。
singleton が閉じたことで、local island witness の最小会計単位が完成した。

次は two-witness。
二つ並べたときに sorted なら `≤ -2`、sorted が壊れるなら order failure として保存する。
この「成功と失敗を両方 first-class にする」方針が、いまの PetalBridge main root には一番合っておる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
index 6376fa84..58f64bff 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -1565,6 +1565,120 @@ theorem sourcePressureIntervalPulseAddressFamily_singleton_of_localIslandWitness
       W).items.length = 1 := by
   rfl
 
+/--
+A singleton local-island witness list is sorted after conversion.
+
+This is only the singleton case for an explicitly supplied witness.
+-/
+theorem sourcePressureLocalIslandWitnessListSortedBefore_singleton
+    {n : OddNat} {k r : ℕ}
+    (W : SourcePressureLocalIslandWitness n k r) :
+    SourcePressureLocalIslandWitnessListSortedBefore [W] := by
+  trivial
+
+/--
+A singleton local-island witness list has no adjacent sorted-before failure.
+-/
+theorem sourcePressureLocalIslandWitnessList_no_failure_singleton
+    {n : OddNat} {k r : ℕ}
+    (W : SourcePressureLocalIslandWitness n k r) :
+    ¬ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W] := by
+  intro h
+  simpa [SourcePressureLocalIslandWitnessListHasSortedBeforeFailure,
+    sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList,
+    SourcePressureIntervalPulseAddressFamilyHasSortedBeforeFailure,
+    SourcePressureIntervalPulseAddressListHasSortedBeforeFailure,
+    sourcePressureAccountedIntervalList_of_intervalPulseAddressList] using h
+
+/--
+Accounted interval family generated by one explicit local-island witness.
+
+This is the singleton specialization of the sorted witness-list lift.  It does
+not claim that this witness is the only local island.
+-/
+def sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness
+    {n : OddNat} {k r : ℕ}
+    (W : SourcePressureLocalIslandWitness n k r) :
+    SourcePressureAccountedIntervalFamily n k r :=
+  sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList
+    [W]
+    (sourcePressureLocalIslandWitnessListSortedBefore_singleton W)
+
+@[simp]
+theorem sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_length
+    {n : OddNat} {k r : ℕ}
+    (W : SourcePressureLocalIslandWitness n k r) :
+    (sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness
+      W).items.length = 1 := by
+  simp [sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness]
+
+/--
+The singleton local-island witness family carries at most one unit of negative
+net drop.
+-/
+theorem sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_sum_le_neg_one
+    {n : OddNat} {k r : ℕ}
+    (W : SourcePressureLocalIslandWitness n k r) :
+    (((sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness
+      W).items).map
+      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -1 := by
+  simpa [sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness]
+    using
+      sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList_sum_le_neg_length
+        [W]
+        (sourcePressureLocalIslandWitnessListSortedBefore_singleton W)
+
+/-- The singleton local-island witness family has strictly negative listed cost. -/
+theorem sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_sum_neg
+    {n : OddNat} {k r : ℕ}
+    (W : SourcePressureLocalIslandWitness n k r) :
+    (((sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness
+      W).items).map
+      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0 := by
+  simpa [sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness]
+    using
+      sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList_sum_neg_of_nonempty
+        (sourcePressureLocalIslandWitnessListSortedBefore_singleton W)
+        (by simp)
+
+/--
+The singleton local-island witness family contains exactly the accounted
+interval obtained by direct conversion.
+-/
+theorem sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_items
+    {n : OddNat} {k r : ℕ}
+    (W : SourcePressureLocalIslandWitness n k r) :
+    (sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness W).items =
+      [sourcePressureAccountedInterval_of_intervalPulseAddress
+        (sourcePressureIntervalPulseAddress_of_localIslandWitness W)] := by
+  rfl
+
+/--
+Raw-argument version of the singleton local-island witness budget.
+
+This packages `j` and `hisland` internally as one explicit witness.
+-/
+theorem sourcePressureLocalIsland_singleton_sum_le_neg_one
+    (n : OddNat) (k r j : ℕ)
+    (hisland : SourcePressureLocalIsland n k r j) :
+    (((sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness
+      (⟨j, hisland⟩ : SourcePressureLocalIslandWitness n k r)).items).map
+      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -1 :=
+  sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_sum_le_neg_one
+    (⟨j, hisland⟩ : SourcePressureLocalIslandWitness n k r)
+
+/--
+Raw-argument strict negative version for one explicit local-island witness.
+-/
+theorem sourcePressureLocalIsland_singleton_sum_neg
+    (n : OddNat) (k r j : ℕ)
+    (hisland : SourcePressureLocalIsland n k r j) :
+    (((sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness
+      (⟨j, hisland⟩ : SourcePressureLocalIslandWitness n k r)).items).map
+      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0 :=
+  sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_sum_neg
+    (⟨j, hisland⟩ : SourcePressureLocalIslandWitness n k r)
+
 /-- Singleton sorted-family budget wrapper. -/
 theorem sourcePressureAccountedIntervalFamily_sorted_singleton_sum_le_neg_one
     {n : OddNat} {k r : ℕ}
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-156.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-156.md
new file mode 100644
index 00000000..df72baef
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-156.md
@@ -0,0 +1,149 @@
+# report-petal-156
+
+Checkpoint: 156
+
+Subject: singleton local-island witness accounting wrappers.
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
+The new API specializes the checkpoint-155 explicit local-island witness list
+layer to the singleton case.
+
+## Singleton Sortedness
+
+Added:
+
+```lean
+theorem sourcePressureLocalIslandWitnessListSortedBefore_singleton
+```
+
+This proves that `[W]` is sorted after conversion to a pulse-address family.
+
+Also added:
+
+```lean
+theorem sourcePressureLocalIslandWitnessList_no_failure_singleton
+```
+
+This records that a singleton witness list cannot carry an adjacent
+sorted-before failure.
+
+## Singleton Accounted Family
+
+Added:
+
+```lean
+def sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness
+```
+
+This is the singleton specialization of:
+
+```lean
+sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList
+```
+
+Length wrapper:
+
+```lean
+theorem sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_length
+```
+
+## Singleton Budget
+
+Added:
+
+```lean
+theorem sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_sum_le_neg_one
+theorem sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_sum_neg
+```
+
+These are the singleton `<= -1` and strict-negative listed-cost facts.
+
+## Item Consistency
+
+Added:
+
+```lean
+theorem sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_items
+```
+
+This proves that the singleton accounted family contains exactly the direct
+accounted interval obtained from:
+
+```lean
+sourcePressureIntervalPulseAddress_of_localIslandWitness W
+```
+
+## Raw Local-Island Theorems
+
+Added raw-argument wrappers:
+
+```lean
+theorem sourcePressureLocalIsland_singleton_sum_le_neg_one
+theorem sourcePressureLocalIsland_singleton_sum_neg
+```
+
+These package `(j, hisland)` internally as one explicit
+`SourcePressureLocalIslandWitness`.
+
+## Non-Claims
+
+This checkpoint still does not enumerate all local islands.
+
+It also does not introduce:
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
+All statements remain about one explicitly supplied local-island witness.
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
+That warning is outside checkpoint 156.
+
+## Next Inference
+
+The next natural step is the two-witness layer:
+
+```text
+[W1, W2]
+  -> sorted iff first converted address is before the second
+  -> failure iff that ordered relation fails
+  -> sorted branch gives length 2 and budget <= -2
+```
+
+This should remain an explicit-list theorem.  It must not be read as an
+overlap theorem unless additional hypotheses are supplied.
````
`````
