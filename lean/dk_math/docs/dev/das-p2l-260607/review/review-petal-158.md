# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAccounting

gch: a0b0999e89e110c8436be8ca2f3f95fbe0b431f7

## Report

cp157 完了です。

`PressureAccounting.lean` に、local-island witness 2点版の accounting API を追加しました。主な追加は以下です。

- `SourcePressureLocalIslandWitnessBefore`
- witness-before と address-before の `iff`
- 2 witness list の sorted / failure `iff`
- sorted witness pair から `SourcePressureAccountedIntervalFamily` を作る wrapper
- pair family の `length = 2` / `items` 固定
- `sum ≤ -2` と `sum < 0`
- raw `SourcePressureLocalIsland` 2点版 wrapper

レポートも新規作成しました。

- `lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-157.md`

確認済みです。

- `lake build DkMath.Collatz.PetalBridge.PressureAccounting` pass
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier` pass
- `lake build DkMath.Collatz.PetalBridge` pass
- `PressureAccounting.lean` / `PressureFrontier.lean` no-sorry check pass
- `git diff --check` pass

今回も主張範囲は明示 witness pair の sorted-before に限定しています。overlap 判定、最大性、coverage、Collatz 収束の主張は入れていません。

## Review

## 結論

うむ、Checkpoint 157 は **採用** じゃ 👍️
今回も main root に集中できておる。`PressureAccounting.lean` のみ更新し、`PressureFrontier`、`OneCycle`、`ValuationFlowBridge`、ABC、NumberTheory には触れていない。ここまでの本線管理はかなり安定してきた。

今回の中心は、

```text id="p7k8m2"
two local-island witnesses
  -> witness-before
  -> pair sorted/failure iff
  -> sorted pair accounted family
  -> length = 2
  -> net drop sum ≤ -2
  -> net drop sum < 0
```

を固定したことじゃな。

## 実装内容の解説

## 1. `SourcePressureLocalIslandWitnessBefore`

追加された witness-level before はこれじゃ。

```lean id="zuq7cb"
def SourcePressureLocalIslandWitnessBefore
```

これは、二つの local-island witness をそれぞれ interval-pulse address に変換してから、

```lean id="bw0iu5"
SourcePressureIntervalPulseAddressBefore
```

で比較する。

つまり、local island の世界で直接「前にある」を言うのではなく、

```text id="6tlt26"
local island witness
  -> pulse address
  -> address-level before
```

へ落としている。

これは正しい。
`SourcePressureLocalIsland` 自体は pressure の局所性を持つ witness であり、順序・長さ・start/end の具体比較は address 側に任せるのが筋じゃ。

## 2. pair sorted / failure iff

追加された二つ。

```lean id="pp5xme"
sourcePressureLocalIslandWitnessListSortedBefore_pair_iff
sourcePressureLocalIslandWitnessListHasSortedBeforeFailure_pair_iff
```

これで、

```text id="3mss0y"
[W1, W2] が sorted
  ↔ W1 before W2
```

および、

```text id="igfib1"
[W1, W2] が sorted-before failure
  ↔ not W1 before W2
```

が言えるようになった。

これは二要素 list の API として非常に使いやすい。

ただし、ここでも大事なのは report にもある通り、

```text id="i5wagk"
failure は overlap 証拠ではない
```

という点じゃ。

`not before` は、順序が逆でも起きる。
したがって、これは **order obstruction** であって、重なり判定ではない。

## 3. sorted pair accounted family

追加された constructor はこれ。

```lean id="3nvx7t"
sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair
```

これは、

```text id="h4u7rf"
W1 before W2
```

という明示仮定のもとで、

```text id="ysgc3t"
[W1, W2]
  -> sorted local-island witness list
  -> accounted interval family
```

を作る。

これにより、二つの local island witness を明示的に並べて、会計 family として扱えるようになった。

## 4. length / items 固定

追加された、

```lean id="afbjvw"
sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_length
sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_items
```

も良い。

特に `items` theorem は重要じゃ。

```text id="aybc5s"
family の中身が、W1/W2 から直接変換した accounted intervals そのものである
```

を固定している。

この種の theorem は、後で `simp` や `rw` で family の中身を具体化したいときに効く。

## 5. pair budget

今回の主砲はこの二つじゃ。

```lean id="u0i9ni"
sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_sum_le_neg_two
sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_sum_neg
```

意味は明確。

```text id="uwvpch"
sorted two-witness family の listed net drop sum は ≤ -2
```

さらに、

```text id="4qlsv5"
strictly negative
```

じゃ。

これで singleton の `≤ -1` に続き、二要素 sorted pair の `≤ -2` が閉じた。

## 6. raw local-island pair wrappers

追加された raw 版も実用的じゃ。

```lean id="zmk2c8"
sourcePressureLocalIsland_pair_sum_le_neg_two
sourcePressureLocalIsland_pair_sum_neg
```

これは、

```lean id="thkz8d"
j1 j2 : ℕ
h1 : SourcePressureLocalIsland n k r j1
h2 : SourcePressureLocalIsland n k r j2
```

を直接受け取り、内部で witness に包む。

後続の frontier 側 theorem では、たぶん `W1/W2` より `j1 h1 j2 h2` の形で持っていることが多い。なので、この raw wrapper は呼び口としてかなり良い。

## 良い点

## 1. singleton から pair へ自然に進んでいる

ここまでの流れがきれいじゃ。

```text id="meycb2"
single witness:
  sum ≤ -1

sorted pair:
  sum ≤ -2
```

この形は、後で finite list の一般形へ戻るときにも読みやすい。

## 2. 成功 branch と失敗 branch が対になっている

今回の pair API は、

```text id="i9np4t"
sorted branch:
  W1 before W2
  -> accounted family
  -> budget ≤ -2

failure branch:
  not W1 before W2
  -> sorted-before failure
```

という対になっている。

これは DkMath/PetalBridge の今の方針に合っている。
成功だけでなく、失敗も first-class に保存する。良い。

## 注意点

## 1. pair theorem はまだ list producer ではない

今回も、主語は **明示的に与えた二つの witness** じゃ。

まだ次は言っていない。

```text id="rgfzki"
全 local islands から隣接 pair を生成する
frontier が pair list を返す
orbit window を覆う pair family を作る
```

ここは未到達。

## 2. `not before` は overlap ではない

これは何度でも守るべき境界じゃ。

```text id="onwczv"
¬ SourcePressureLocalIslandWitnessBefore W1 W2
```

は、

```text id="6l5xwd"
W1 と W2 が重なる
```

ではない。

ただの order failure。
overlap を言うには、たとえば「逆順でも before ではない」など、追加条件が必要になる。

## 数学的な意味

今回で local island witness accounting は、最小単位から二点単位へ進んだ。

```text id="3qmjl9"
1 island:
  local negative atom

2 sorted islands:
  additive negative pair
```

DkMath 的には、

```text id="vvm7da"
局所 island witness は、sorted に並べられたぶんだけ
listed net drop の負予算を足し込める
```

という読みになる。

これは、有限 family budget の直感とぴったり一致している。

## 次の重点

次は report にもある通り、**failure-facing pair API** が自然じゃ。

つまり、今ある

```lean id="tjrmw7"
sourcePressureLocalIslandWitnessListHasSortedBeforeFailure_pair_iff
```

を使いやすい theorem 名で包む。

主眼は、

```text id="s4p18p"
not W1 before W2
  -> [W1, W2] has sorted-before failure
```

を直接呼べるようにすること。

さらに可能なら、

```text id="cotkad"
pair sorted-or-failure
```

も名前付きで置く。

まだ overlap は言わない。
failure は order obstruction として保存するだけじゃ。

## 次の Codex 依頼

```text id="l9y6x2"
Checkpoint 158: Main root only — failure-facing pair API for local-island witnesses.

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
Checkpoint 157 added two local-island witness accounting wrappers:

- SourcePressureLocalIslandWitnessBefore
- sourcePressureLocalIslandWitnessBefore_iff_addressBefore
- sourcePressureLocalIslandWitnessListSortedBefore_pair_iff
- sourcePressureLocalIslandWitnessListHasSortedBeforeFailure_pair_iff
- sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair
- sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_length
- sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_items
- sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_sum_le_neg_two
- sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_sum_neg
- sourcePressureLocalIsland_pair_sum_le_neg_two
- sourcePressureLocalIsland_pair_sum_neg

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
Add direct failure-facing theorem wrappers for explicit local-island witness pairs.

Part A: pair failure constructor.

Prove:

  theorem sourcePressureLocalIslandWitnessPair_hasSortedBeforeFailure_of_not_before
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      (hfail : ¬ SourcePressureLocalIslandWitnessBefore W1 W2) :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]

This should follow from
sourcePressureLocalIslandWitnessListHasSortedBeforeFailure_pair_iff.

Add comment:
This is only order failure, not overlap evidence.

Part B: pair no-failure from before.

Prove:

  theorem sourcePressureLocalIslandWitnessPair_no_failure_of_before
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      (hbefore : SourcePressureLocalIslandWitnessBefore W1 W2) :
      ¬ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]

This should follow from the pair failure iff.

Part C: pair sorted-or-failure theorem.

Prove a convenient two-witness split:

  theorem sourcePressureLocalIslandWitnessPair_sorted_or_failure
      {n : OddNat} {k r : Nat}
      (W1 W2 : SourcePressureLocalIslandWitness n k r) :
      SourcePressureLocalIslandWitnessListSortedBefore [W1, W2] ∨
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]

This may be a direct specialization of
sourcePressureLocalIslandWitnessList_sorted_or_failure [W1, W2].

Part D: raw local-island failure wrappers.

If statement size remains acceptable, add raw versions:

  theorem sourcePressureLocalIsland_pair_hasSortedBeforeFailure_of_not_before
      (n : OddNat) (k r j1 j2 : Nat)
      (h1 : SourcePressureLocalIsland n k r j1)
      (h2 : SourcePressureLocalIsland n k r j2)
      (hfail :
        ¬ SourcePressureLocalIslandWitnessBefore
          (⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r)
          (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)) :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        [(⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r),
         (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)]

Optional raw no-failure from before if not too bulky.

Part E: explicit non-overlap warning theorem comment.

Do not add an overlap theorem.

Add a comment near the new failure-facing theorem:

  "This theorem deliberately does not conclude interval overlap.  The failure
   may be caused by reversed order."

Part F: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-158.md

Include:
- pair failure constructor theorem,
- pair no-failure theorem if added,
- pair sorted-or-failure theorem,
- raw local-island failure wrappers if added or skipped,
- explicit note that pair failure is order obstruction only and not overlap,
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
二点版が閉じた。

次は、その失敗側を名前付き API にして、pair の成功・失敗がどちらも直接呼べるようにする。
この段階ではまだ overlap を言わず、order obstruction として保存する。これで main root の failure handling がかなり扱いやすくなるぞ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
index 58f64bff..74e8e554 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -1679,6 +1679,178 @@ theorem sourcePressureLocalIsland_singleton_sum_neg
   sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_sum_neg
     (⟨j, hisland⟩ : SourcePressureLocalIslandWitness n k r)
 
+/--
+Ordered non-overlap for two explicit local-island witnesses.
+
+This is defined by converting both witnesses to interval-pulse addresses and
+using the address-level before predicate.
+-/
+def SourcePressureLocalIslandWitnessBefore
+    {n : OddNat} {k r : ℕ}
+    (W1 W2 : SourcePressureLocalIslandWitness n k r) : Prop :=
+  SourcePressureIntervalPulseAddressBefore
+    (sourcePressureIntervalPulseAddress_of_localIslandWitness W1)
+    (sourcePressureIntervalPulseAddress_of_localIslandWitness W2)
+
+theorem sourcePressureLocalIslandWitnessBefore_iff_addressBefore
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r} :
+    SourcePressureLocalIslandWitnessBefore W1 W2 ↔
+      SourcePressureIntervalPulseAddressBefore
+        (sourcePressureIntervalPulseAddress_of_localIslandWitness W1)
+        (sourcePressureIntervalPulseAddress_of_localIslandWitness W2) := by
+  rfl
+
+/--
+A two-witness list is sorted exactly when the first converted address lies
+before the second.
+-/
+theorem sourcePressureLocalIslandWitnessListSortedBefore_pair_iff
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r} :
+    SourcePressureLocalIslandWitnessListSortedBefore [W1, W2] ↔
+      SourcePressureLocalIslandWitnessBefore W1 W2 := by
+  change
+    SourcePressureIntervalPulseAddressListSortedBefore
+      [sourcePressureIntervalPulseAddress_of_localIslandWitness W1,
+        sourcePressureIntervalPulseAddress_of_localIslandWitness W2] ↔
+      SourcePressureLocalIslandWitnessBefore W1 W2
+  rw [sourcePressureIntervalPulseAddressListSortedBefore_pair_iff]
+  rfl
+
+/--
+A two-witness list has a sorted-before failure exactly when the first converted
+address is not before the second.
+
+This is only an order failure.  It is not overlap evidence without additional
+hypotheses.
+-/
+theorem sourcePressureLocalIslandWitnessListHasSortedBeforeFailure_pair_iff
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r} :
+    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2] ↔
+      ¬ SourcePressureLocalIslandWitnessBefore W1 W2 := by
+  change
+    SourcePressureIntervalPulseAddressListHasSortedBeforeFailure
+      [sourcePressureIntervalPulseAddress_of_localIslandWitness W1,
+        sourcePressureIntervalPulseAddress_of_localIslandWitness W2] ↔
+      ¬ SourcePressureLocalIslandWitnessBefore W1 W2
+  rw [sourcePressureIntervalPulseAddressListHasSortedBeforeFailure_pair_iff]
+  rfl
+
+/--
+Accounted interval family generated by two explicitly sorted local-island
+witnesses.
+
+The `hbefore` hypothesis is just the supplied order relation.  No coverage,
+maximality, or uniqueness is inferred.
+-/
+def sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair
+    {n : OddNat} {k r : ℕ}
+    (W1 W2 : SourcePressureLocalIslandWitness n k r)
+    (hbefore : SourcePressureLocalIslandWitnessBefore W1 W2) :
+    SourcePressureAccountedIntervalFamily n k r :=
+  sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList
+    [W1, W2]
+    (sourcePressureLocalIslandWitnessListSortedBefore_pair_iff.2 hbefore)
+
+@[simp]
+theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_length
+    {n : OddNat} {k r : ℕ}
+    (W1 W2 : SourcePressureLocalIslandWitness n k r)
+    (hbefore : SourcePressureLocalIslandWitnessBefore W1 W2) :
+    (sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair
+      W1 W2 hbefore).items.length = 2 := by
+  simp [sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair]
+
+/--
+The sorted two-witness family contains exactly the two directly converted
+accounted intervals.
+-/
+theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_items
+    {n : OddNat} {k r : ℕ}
+    (W1 W2 : SourcePressureLocalIslandWitness n k r)
+    (hbefore : SourcePressureLocalIslandWitnessBefore W1 W2) :
+    (sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair
+      W1 W2 hbefore).items =
+      [sourcePressureAccountedInterval_of_intervalPulseAddress
+        (sourcePressureIntervalPulseAddress_of_localIslandWitness W1),
+       sourcePressureAccountedInterval_of_intervalPulseAddress
+        (sourcePressureIntervalPulseAddress_of_localIslandWitness W2)] := by
+  rfl
+
+/--
+The listed cost of a sorted two-witness family is at most `-2`.
+-/
+theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_sum_le_neg_two
+    {n : OddNat} {k r : ℕ}
+    (W1 W2 : SourcePressureLocalIslandWitness n k r)
+    (hbefore : SourcePressureLocalIslandWitnessBefore W1 W2) :
+    (((sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair
+      W1 W2 hbefore).items).map
+      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2 := by
+  simpa [sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair]
+    using
+      sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList_sum_le_neg_length
+        [W1, W2]
+        (sourcePressureLocalIslandWitnessListSortedBefore_pair_iff.2 hbefore)
+
+/-- The sorted two-witness family has strictly negative listed cost. -/
+theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_sum_neg
+    {n : OddNat} {k r : ℕ}
+    (W1 W2 : SourcePressureLocalIslandWitness n k r)
+    (hbefore : SourcePressureLocalIslandWitnessBefore W1 W2) :
+    (((sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair
+      W1 W2 hbefore).items).map
+      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0 := by
+  simpa [sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair]
+    using
+      sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList_sum_neg_of_nonempty
+        (sourcePressureLocalIslandWitnessListSortedBefore_pair_iff.2 hbefore)
+        (by simp)
+
+/--
+Raw-argument version of the sorted pair budget.
+-/
+theorem sourcePressureLocalIsland_pair_sum_le_neg_two
+    (n : OddNat) (k r j1 j2 : ℕ)
+    (h1 : SourcePressureLocalIsland n k r j1)
+    (h2 : SourcePressureLocalIsland n k r j2)
+    (hbefore :
+      SourcePressureLocalIslandWitnessBefore
+        (⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r)
+        (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)) :
+    (((sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair
+      (⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r)
+      (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)
+      hbefore).items).map
+      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2 :=
+  sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_sum_le_neg_two
+    (⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r)
+    (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)
+    hbefore
+
+/--
+Raw-argument strict negative version of the sorted pair budget.
+-/
+theorem sourcePressureLocalIsland_pair_sum_neg
+    (n : OddNat) (k r j1 j2 : ℕ)
+    (h1 : SourcePressureLocalIsland n k r j1)
+    (h2 : SourcePressureLocalIsland n k r j2)
+    (hbefore :
+      SourcePressureLocalIslandWitnessBefore
+        (⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r)
+        (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)) :
+    (((sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair
+      (⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r)
+      (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)
+      hbefore).items).map
+      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0 :=
+  sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_sum_neg
+    (⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r)
+    (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)
+    hbefore
+
 /-- Singleton sorted-family budget wrapper. -/
 theorem sourcePressureAccountedIntervalFamily_sorted_singleton_sum_le_neg_one
     {n : OddNat} {k r : ℕ}
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-157.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-157.md
new file mode 100644
index 00000000..bf29ed85
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-157.md
@@ -0,0 +1,154 @@
+# report-petal-157
+
+Checkpoint: 157
+
+Subject: two local-island witness accounting wrappers.
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
+The new API specializes the explicit local-island witness list layer to
+two supplied witnesses.
+
+## Witness-Before Predicate
+
+Added:
+
+```lean
+def SourcePressureLocalIslandWitnessBefore
+```
+
+This is the witness-level ordered relation obtained by converting both
+witnesses to interval-pulse addresses and using:
+
+```lean
+SourcePressureIntervalPulseAddressBefore
+```
+
+Also added:
+
+```lean
+theorem sourcePressureLocalIslandWitnessBefore_iff_addressBefore
+```
+
+## Pair Sorted / Failure Iff
+
+Added:
+
+```lean
+theorem sourcePressureLocalIslandWitnessListSortedBefore_pair_iff
+theorem sourcePressureLocalIslandWitnessListHasSortedBeforeFailure_pair_iff
+```
+
+The failure theorem is explicitly documented as order failure only.
+
+It is not overlap evidence unless additional hypotheses are supplied.
+
+## Sorted Pair Accounted Family
+
+Added:
+
+```lean
+def sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair
+```
+
+This packages `[W1, W2]` as an accounted family under an explicit
+`SourcePressureLocalIslandWitnessBefore W1 W2` hypothesis.
+
+## Length And Items
+
+Added:
+
+```lean
+theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_length
+theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_items
+```
+
+The item theorem records that the family contains exactly the two directly
+converted accounted intervals.
+
+## Pair Budget
+
+Added:
+
+```lean
+theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_sum_le_neg_two
+theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_sum_neg
+```
+
+These prove the sorted two-witness listed-cost bounds:
+
+```text
+sum <= -2
+sum < 0
+```
+
+## Raw Local-Island Pair Wrappers
+
+The raw argument versions were added:
+
+```lean
+theorem sourcePressureLocalIsland_pair_sum_le_neg_two
+theorem sourcePressureLocalIsland_pair_sum_neg
+```
+
+They package `(j1, h1)` and `(j2, h2)` internally as explicit witnesses.
+
+## Non-Claims
+
+This checkpoint still does not enumerate all local islands.
+
+It does not introduce:
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
+The pair failure theorem is not an overlap theorem.
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
+That warning is outside checkpoint 157.
+
+## Next Inference
+
+The next conservative layer is a failure-facing pair API:
+
+```text
+not SourcePressureLocalIslandWitnessBefore W1 W2
+  -> pair sorted-before failure
+```
+
+This should continue to say only "order obstruction", not overlap.  Any overlap
+claim needs an extra hypothesis excluding reversed order.
````
`````
