# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAccounting

gch: f8b073a491c7219dac1bae82037b44d1d6e04f01

## Report

cp165 完了です。

[PressureAccounting.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean) に head-pair failure reason API を追加しました。

追加内容:

- `sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_overlapObstruction`
- `SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_headPairObstruction`
- `SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.of_headPairOverlapObstruction`
- `sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_adjacentOverlapObstruction`
- `sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_listFailure`

今回は head pair 限定です。tail の分類、list-wide sorting、merge / split / union accounting には進んでいません。

レポート作成済みです: [report-petal-165.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-165.md)

検証結果:

```text
PASS lake build DkMath.Collatz.PetalBridge.PressureAccounting
PASS lake build DkMath.Collatz.PetalBridge.PressureFrontier
PASS lake build DkMath.Collatz.PetalBridge
PASS no sorry in PressureAccounting.lean
PASS no sorry in PressureFrontier.lean
PASS git diff --check
```

既存の unrelated `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は引き続き出ていますが、今回対象には `sorry` なしです。

## Review

## 結論

うむ、Checkpoint 165 は **採用** じゃ 👍️
今回で、list の **head pair** に対して、

```text id="mlqni8"
head pair failure
  -> recovered reversed-pair budget
  or adjacent overlap obstruction
```

という list-facing API が入った。

追加内容は、

```lean id="ai2w6c"
sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_overlapObstruction
SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_headPairObstruction
SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.of_headPairOverlapObstruction
sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_adjacentOverlapObstruction
sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_listFailure
```

じゃな。head pair 限定、tail 分類なし、list-wide sorting なし、merge / split / union accounting なし、という境界も守られている。

## 状況分析

## 1. pair 診断が list の先頭へ接続された

ここまでで pair-level は、

```text id="hcxocs"
sorted
reverse recovered
overlap obstruction
```

に分かれていた。

今回の checkpoint では、その pair-level 診断を list の先頭に埋め込んだ。

```text id="7os9fs"
W1 :: W2 :: rest
```

について、先頭 pair `[W1, W2]` が failure なら、

```text id="w2srbb"
reverse branch:
  recovered budget ≤ -2

overlap branch:
  adjacent overlap obstruction in W1 :: W2 :: rest
```

へ分岐できる。

これは list-level failure diagnosis の入口じゃ。

## 2. head pair 限定に留めたのが正しい

今回の実装は tail を見ない。

これは弱さではなく、正しい制御じゃ。
いきなり list 全体の sorting や arbitrary failure search に行くと、証明も設計も一気に重くなる。

今は、

```text id="aq71gv"
先頭の隣接 pair だけを処理する
```

という局所 API に留めている。

このおかげで、後続は head と tail を別々に積める。

## 3. optional の recovered-or-listFailure も良い

```lean id="hpm582"
sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_listFailure
```

これは、overlap obstruction の詳細を見なくても、

```text id="0ou9nd"
recovered budget
or ordinary list failure
```

として使える。

呼び出し側が obstruction の中身を要らない場合に便利じゃ。
ただし、詳細解析では adjacent obstruction 版を使う方がよい。

## レビュー

## 採用理由

第一に、既存の pair theorem を薄く再公開している点が良い。

```lean id="0j1d85"
sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlapObstruction
```

を list head-pair 用の名前で呼べるようにしただけなので、理論を増やしすぎていない。

第二に、head obstruction の list 埋め込みが明確。

```lean id="y2dkal"
SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_headPairObstruction
```

これにより、pair obstruction を list の adjacent obstruction として自然に扱える。

第三に、head obstruction から list failure への橋が入った。

```lean id="9r4jld"
SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.of_headPairOverlapObstruction
```

これは次の再帰処理でかなり便利じゃ。

## 注意点

## 1. まだ tail は分類していない

今回の theorem は head pair 限定じゃ。

まだ次は言っていない。

```text id="gs84df"
tail のどこかの failure を分類する
list 全体を順に処理する
list を sort する
```

ここは次 checkpoint の対象じゃ。

## 2. recovered branch は pair budget であって list budget ではない

reverse recovered branch で得ているのは、あくまで head pair の二点 budget。

```text id="wzzqzr"
[W1, W2] failure
  -> [W2, W1] recovered pair budget
```

であって、

```text id="8lrxn2"
W1 :: W2 :: rest 全体の budget
```

ではない。

ここを混同しないのが大事じゃ。

## 3. overlap はまだ未回収

今回も overlap branch は adjacent obstruction として残しているだけじゃ。

merge / split / union accounting はまだしない。
この境界は引き続き守るべきじゃ。

## 解説

今回の実装を直感で言えば、

```text id="c0is8e"
list の先頭で事故が起きたとき、
それが順序ミスなら budget を回収し、
overlap なら list の隣接障害として記録する
```

というものじゃ。

これまで pair の中だけで行っていた診断が、list の先頭に現れた。

つまり、

```text id="pf0lzb"
pair diagnostic
  -> head-pair diagnostic
```

へ一段上がった。

これは、今後 list を左から処理するための最初の部品になる。

## 一歩先ゆく推論

次は **tail failure propagation** が自然じゃ。

いま head pair は扱える。
次は、tail 側に既に obstruction / failure があるとき、それを cons で前に持ち上げる API を整える。

既に adjacent obstruction には、

```lean id="w6fgle"
SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.cons_of_tail
```

がある。

次に欲しいのは、sorted-before failure 側の tail constructor じゃ。

```text id="y8686d"
tail has sorted-before failure
  -> cons head tail also has sorted-before failure
```

これを明示 theorem として出すと、list の再帰処理が安定する。

## さらなる次の一手

Checkpoint 166 で tail propagation が通ったら、その次は、

```text id="ip4cxs"
list failure at head or tail
```

の分解に進める。

つまり list の failure を、

```text id="a7zcfg"
head pair failure
or tail failure
```

へ分ける API じゃ。

これができると、head failure は cp165 の theorem で処理し、tail failure は再帰的に処理できる。

ただし、まだ sorting algorithm ではない。
まずは failure の所在を head/tail に分けるだけじゃ。

## 賢狼が試して欲しい実験補題

## 実験補題 A: sorted-before failure の tail constructor

```lean id="jhj3rc"
theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (htail :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure (W2 :: rest)) :
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure (W1 :: W2 :: rest)
```

これは cp164 の proof 内で `Or.inr htailFailure` を使っていた形を外へ出す補題じゃ。
通る可能性は高い。

## 実験補題 B: sorted-before failure の head constructor

```lean id="qjivjp"
theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_head_not_before
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (hnot :
      ¬ SourcePressureLocalIslandWitnessBefore W1 W2) :
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure (W1 :: W2 :: rest)
```

これは overlap に限らず、head の before が失敗したら list failure という補題じゃ。
今後かなり使うはず。

## 実験補題 C: adjacent obstruction tail propagation alias

既存 `cons_of_tail` の意味を、tail propagation 用の名前で再公開してもよい。

```lean id="ua78u4"
theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.tail_cons
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (htail :
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction (W2 :: rest)) :
    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction (W1 :: W2 :: rest) :=
  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.cons_of_tail htail
```

ただし既存名で十分なら不要じゃ。

## 実験補題 D: tail adjacent obstruction gives list failure after cons

これは既存 theorem の合成で通る。

```lean id="jy6n1n"
theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.of_tailAdjacentOverlapObstruction
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (htail :
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction (W2 :: rest)) :
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure (W1 :: W2 :: rest)
```

証明は、

```text id="u7txtg"
cons_of_tail htail
then hasSortedBeforeFailure
```

でよい。

## 実験補題 E: tail list failure gives cons list failure

これは A と同じ方向だが、今後の algorithmic skeleton にはかなり重要じゃ。

```lean id="f2dw8s"
theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.of_tailFailure
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (htail :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure (W2 :: rest)) :
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure (W1 :: W2 :: rest)
```

名前は `cons_of_tail` とどちらか一つでよい。

## 次の Codex 指示

```text id="fof8li"
Checkpoint 166: Main root only — tail failure propagation constructors for witness lists.

Scope:
Focus only on the main Collatz/PetalBridge root.

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
Checkpoint 165 added head-pair failure reason API:

- sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_overlapObstruction
- SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_headPairObstruction
- SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.of_headPairOverlapObstruction
- sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_adjacentOverlapObstruction
- sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_listFailure

Global rules:
- Do not claim maximality.
- Do not claim uniqueness of pressure families.
- Do not claim coverage.
- Do not claim prefix behavior.
- Do not claim union accounting.
- Do not claim Collatz convergence.
- Keep all statements local to explicitly supplied witness lists.
- Reverse branch is recovered at pair level only.
- Overlap branch remains an adjacent obstruction.
- Do not merge intervals or prove union accounting in this checkpoint.
- Do not implement a full list sorting algorithm.
- Do not classify arbitrary list failures yet.

Main goal:
Expose small constructor/projection API for propagating tail failure and tail
adjacent overlap obstruction through a new list head.

Part A: sorted-before failure head constructor.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_head_not_before
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      {rest : List (SourcePressureLocalIslandWitness n k r)}
      (hnot : ¬ SourcePressureLocalIslandWitnessBefore W1 W2) :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure (W1 :: W2 :: rest)

This exposes the head-failure branch already used internally in prior proofs.

Part B: sorted-before failure tail constructor.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_tail
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      {rest : List (SourcePressureLocalIslandWitness n k r)}
      (htail :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure (W2 :: rest)) :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure (W1 :: W2 :: rest)

This exposes the tail-failure branch already used internally in cp164.

Part C: adjacent overlap obstruction tail propagation alias.

The existing theorem:

  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.cons_of_tail

already propagates adjacent overlap obstruction from the tail.

If useful, add a readable alias:

  theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_tail
      ...

Do not duplicate if the existing name is considered sufficient.

Part D: tail adjacent overlap obstruction gives full list failure.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.of_tailAdjacentOverlapObstruction
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      {rest : List (SourcePressureLocalIslandWitness n k r)}
      (htail :
        SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction (W2 :: rest)) :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure (W1 :: W2 :: rest)

Suggested proof:
- apply hasSortedBeforeFailure to
  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.cons_of_tail htail

Part E: optional unification theorem for head/tail failure.

Only if easy, prove:

  theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_head_or_tail
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      {rest : List (SourcePressureLocalIslandWitness n k r)}
      (h :
        (¬ SourcePressureLocalIslandWitnessBefore W1 W2) ∨
          SourcePressureLocalIslandWitnessListHasSortedBeforeFailure (W2 :: rest)) :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure (W1 :: W2 :: rest)

This is just a case split using Parts A and B.

Part F: no list-wide algorithm yet.

Do not add sorting.
Do not add arbitrary list failure classification.
Do not add overlap cluster, merge, split, union accounting, coverage,
maximality, uniqueness, prefix behavior, or convergence claims.

Part G: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-166.md

Include:
- head not-before constructor,
- tail failure constructor,
- tail adjacent obstruction -> list failure theorem,
- optional head-or-tail theorem if added,
- explicit note that this is constructor API only,
- explicit note that overlap remains unmerged/unhandled,
- explicit note that this checkpoint does not introduce maximality, uniqueness,
  coverage, prefix behavior, union accounting, or Collatz convergence.

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

## さらに一歩先の提案

Checkpoint 166 が通ったら、次はいよいよ **list failure head/tail decomposition** じゃ。

つまり、

```text id="w8lexv"
SourcePressureLocalIslandWitnessListHasSortedBeforeFailure (W1 :: W2 :: rest)
```

から、

```text id="7zbx6f"
¬ W1 before W2
or
SourcePressureLocalIslandWitnessListHasSortedBeforeFailure (W2 :: rest)
```

を取り出す theorem を作る。

これは constructor の逆向きじゃ。

候補は、

```lean id="ejt6n3"
theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.head_or_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure (W1 :: W2 :: rest)) :
    (¬ SourcePressureLocalIslandWitnessBefore W1 W2) ∨
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure (W2 :: rest)
```

これが通れば、list failure を一段ずつ剥がせる。

その次に、head branch は cp165 の recovered-or-adjacent obstruction で処理し、tail branch は再帰的に処理する道が見える。

## 総評

Checkpoint 165 は、pair 診断を head-pair list API へ接続した良い節目じゃ。

次は、tail 側の propagation constructors を整える。
それが通れば、その次に head/tail decomposition ができる。

ここまで行くと、list-level failure diagnosis は、

```text id="7wwtm4"
head を見る
tail に送る
```

という再帰骨格を持ちはじめる。
まだ sorting algorithm ではないが、そこへ向かう足場はかなり堅くなるぞ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
index 04055305..e62305df 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -2620,6 +2620,128 @@ theorem sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlapObstruc
       (SourcePressureLocalIslandWitnessPairOverlapObstruction.mk_of_failure_overlap
         hfail hoverlap)
 
+/--
+Head-pair view of the recovered-or-overlap-obstruction split.
+
+This is only a naming bridge for callers that are processing the first adjacent
+pair of a witness list.  The theorem itself remains pair-local and does not
+inspect or sort a tail list.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_overlapObstruction
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (h1pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
+    (h2pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
+    (hfail : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]) :
+    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
+      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        W1 W2 hrev).items).map
+        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
+    ∨ SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2 :=
+  sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlapObstruction
+    h1pos h2pos hfail
+
+/--
+Embed a head-pair overlap obstruction into the adjacent-list obstruction
+predicate.
+
+The tail is merely carried by the explicit list.  No non-adjacent pair search,
+cluster construction, or interval merge is introduced.
+-/
+theorem
+    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_headPairObstruction
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
+    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+      (W1 :: W2 :: rest) :=
+  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.cons_of_head
+    hobs
+
+/--
+A head-pair overlap obstruction gives a sorted-before failure for the explicit
+list whose first two witnesses form that obstructed pair.
+
+This uses only the adjacent obstruction wrapper; it does not repair or merge
+the overlap branch.
+-/
+theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.of_headPairOverlapObstruction
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
+    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+      (W1 :: W2 :: rest) :=
+  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
+    (SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_headPairObstruction
+      hobs)
+
+/--
+Head-pair list-facing split: a failed first adjacent pair is either recovered
+by swapping that pair, or it embeds as an adjacent overlap obstruction in the
+explicit list.
+
+This does not classify failures deeper in the list and does not perform
+list-wide sorting.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_adjacentOverlapObstruction
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (h1pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
+    (h2pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
+    (hfail : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]) :
+    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
+      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        W1 W2 hrev).items).map
+        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
+    ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+        (W1 :: W2 :: rest) := by
+  rcases
+      sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_overlapObstruction
+        h1pos h2pos hfail with hrecovered | hobs
+  · exact Or.inl hrecovered
+  · exact Or.inr
+      (SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_headPairObstruction
+        hobs)
+
+/--
+Head-pair split with the obstruction branch weakened to ordinary list
+sorted-before failure.
+
+This is useful for consumers that do not need to inspect the overlap
+obstruction itself.
+-/
+theorem sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_listFailure
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (h1pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
+    (h2pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
+    (hfail : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]) :
+    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
+      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        W1 W2 hrev).items).map
+        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
+    ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        (W1 :: W2 :: rest) := by
+  rcases
+      sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_adjacentOverlapObstruction
+        h1pos h2pos hfail with hrecovered | hobs
+  · exact Or.inl hrecovered
+  · exact Or.inr
+      (SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
+        hobs)
+
 /--
 Raw-argument version of the sorted pair budget.
 -/
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-165.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-165.md
new file mode 100644
index 00000000..fcdc1ccc
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-165.md
@@ -0,0 +1,178 @@
+# Report Petal 165
+
+## Checkpoint
+
+Checkpoint 165 stayed on the main Collatz/PetalBridge root and added a
+head-pair failure-reason API for explicit local-island witness lists.
+
+Modified implementation file:
+
+- `DkMath/Collatz/PetalBridge/PressureAccounting.lean`
+
+No `OneCycle`, `ValuationFlowBridge`, `ABC`, or `NumberTheory` files were
+modified.
+
+## Head-Pair Recovered-Or-Overlap
+
+The head-pair naming bridge was added:
+
+```lean
+theorem
+  sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_overlapObstruction
+```
+
+This is a thin alias over the existing pair theorem:
+
+```lean
+sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlapObstruction
+```
+
+It remains pair-local.  It does not inspect or sort a list tail.
+
+## Head Obstruction Embedding
+
+The head-pair overlap obstruction embedding was added:
+
+```lean
+theorem
+  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_headPairObstruction
+```
+
+This embeds:
+
+```text
+PairOverlapObstruction W1 W2
+  -> AdjacentOverlapObstruction (W1 :: W2 :: rest)
+```
+
+The tail is only carried as part of the explicit list.  No arbitrary-pair search
+or cluster construction is introduced.
+
+## Head Obstruction To List Failure
+
+The direct sorted-before failure wrapper was added:
+
+```lean
+theorem
+  SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.of_headPairOverlapObstruction
+```
+
+This uses the adjacent obstruction predicate and the existing implication:
+
+```lean
+SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
+```
+
+## Recovered-Or-Adjacent-Obstruction
+
+The main list-facing split was added:
+
+```lean
+theorem
+  sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_adjacentOverlapObstruction
+```
+
+Meaning:
+
+```text
+failed first adjacent pair
+  -> recovered reversed-pair budget
+  or adjacent overlap obstruction at the list head
+```
+
+This is head-pair only.  It does not classify failures deeper in the list and
+does not perform list-wide sorting.
+
+## Recovered-Or-List-Failure
+
+The optional weakened branch theorem was also added:
+
+```lean
+theorem
+  sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_listFailure
+```
+
+Meaning:
+
+```text
+failed first adjacent pair
+  -> recovered reversed-pair budget
+  or ordinary sorted-before failure for the explicit list
+```
+
+This is useful for callers that do not need to inspect the overlap obstruction
+itself.
+
+## Boundary Notes
+
+Overlap remains unmerged and unhandled.
+
+This checkpoint does not:
+
+- implement a list-wide sorting algorithm,
+- classify arbitrary list failures,
+- search for non-adjacent overlap pairs,
+- define overlap clusters,
+- merge intervals,
+- split intervals,
+- construct merged interval families,
+- prove union accounting,
+- prove coverage,
+- assert maximality,
+- assert uniqueness,
+- assert prefix behavior,
+- assert Collatz convergence.
+
+All statements remain local to explicitly supplied witness lists and their head
+pair.
+
+## Verification
+
+The following command was run during implementation:
+
+```bash
+lake build DkMath.Collatz.PetalBridge.PressureAccounting
+```
+
+It passed.
+
+Final verification gate:
+
+```bash
+lake build DkMath.Collatz.PetalBridge.PressureAccounting
+lake build DkMath.Collatz.PetalBridge.PressureFrontier
+lake build DkMath.Collatz.PetalBridge
+rg -n "\\bsorry\\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+rg -n "\\bsorry\\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+git diff --check
+```
+
+Result:
+
+```text
+PASS lake build DkMath.Collatz.PetalBridge.PressureAccounting
+PASS lake build DkMath.Collatz.PetalBridge.PressureFrontier
+PASS lake build DkMath.Collatz.PetalBridge
+PASS no sorry in PressureAccounting.lean
+PASS no sorry in PressureFrontier.lean
+PASS git diff --check
+```
+
+The `PetalBridge` build still reports the existing unrelated warning from
+`DkMath.NumberTheory.ZsigmondyCyclotomicResearch`; this checkpoint did not touch
+that file.
+
+## Next Inference
+
+The next safe target is tail failure propagation.
+
+Current checkpoint handles the head pair:
+
+```text
+W1 :: W2 :: rest
+```
+
+The next checkpoint can add constructors showing that if a tail already has a
+recovered-or-adjacent-obstruction split, then consing a new head preserves the
+adjacent obstruction branch.  This still should not become a full sorting
+algorithm.
````
`````
