# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAccounting

gch: 57cc635c9ec98949407c0637a67b6b0d9fb8e8ed

## Report

cp168 完了です。

[PressureAccounting.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean) に tail-cons 伝播の弱い診断補題を追加しました。

- `sourcePressureLocalIslandWitnessList_tail_failure_oneStepDiagnosis`
- `sourcePressureLocalIslandWitnessList_tailDiagnosis_overlap_lift`
- `sourcePressureLocalIslandWitnessList_tailFailure_oneStepDiagnosis_under_cons`
- おまけ: `sourcePressureLocalIslandWitnessList_tailFailure_oneStepDiagnosis_under_cons_or_listFailure`

tail の recovered budget は tail pair `W2, W3` に留め、full-list budget へ昇格していません。レポートは [report-petal-168.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-168.md) に作成しました。

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureAccounting` PASS
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier` PASS
- `lake build DkMath.Collatz.PetalBridge` PASS
- 対象 2 ファイルの `sorry` 検索: ヒットなし
- `git diff --check` PASS

既存の `ZsigmondyCyclotomicResearch` の `sorry` 警告は今回も無関係です。

## Review

## 結論

うむ、Checkpoint 168 は **採用** じゃ 👍️
今回で、tail 側の one-step diagnosis を、新しい head の下でも **弱く安全に持ち上げる API** が入った。

追加された中心は、

```lean id="lp34kb"
sourcePressureLocalIslandWitnessList_tail_failure_oneStepDiagnosis
sourcePressureLocalIslandWitnessList_tailDiagnosis_overlap_lift
sourcePressureLocalIslandWitnessList_tailFailure_oneStepDiagnosis_under_cons
sourcePressureLocalIslandWitnessList_tailFailure_oneStepDiagnosis_under_cons_or_listFailure
```

じゃな。特に重要なのは、tail の recovered budget を full-list budget に昇格せず、あくまで tail pair `W2, W3` の budget として保持している点じゃ。これは安全で正しい。

## 状況分析

## 1. tail diagnosis を head の下へ持ち上げられるようになった

Checkpoint 167 では、list failure を一段だけ診断できるようになった。

```text id="or4fu5"
failure (W1 :: W2 :: rest)
  -> head diagnosis
  or tail failure
```

今回の cp168 では、その tail failure に対して、

```text id="ex53mu"
failure (W2 :: W3 :: rest)
  -> tail head pair W2,W3 の diagnosis
```

を行い、その結果を `W1 :: W2 :: W3 :: rest` の文脈に持ち上げられるようになった。

これで、list failure 診断は一段だけでなく、**次の tail 一段** へ進める準備ができた。

## 2. recovered budget を full-list budget にしていないのが良い

今回の最重要ポイントはここじゃ。

tail 側で、

```text id="vi90ou"
W2,W3 の reverse recovered budget
```

が得られても、それはあくまで `W2,W3` pair の budget である。

それを、

```text id="jfd8h8"
W1 :: W2 :: W3 :: rest 全体の budget
```

とは言っていない。

これは非常に大事じゃ。
list-level accounting には disjointness / ordering / family accounting の追加仮定が必要になる可能性があるからの。

今回の theorem は「診断結果を文脈上持ち上げる」が、「会計を勝手に拡張しない」。
この節度が良い。

## 3. overlap branch だけを adjacent obstruction として持ち上げた

tail の overlap obstruction は、

```lean id="msy2mt"
sourcePressureLocalIslandWitnessList_tailDiagnosis_overlap_lift
```

で full list 側の adjacent overlap obstruction にできる。

これは自然じゃ。
overlap obstruction は list のどこか隣接 pair に存在する、という性質なので、新しい head を付けても残る。

一方、recovered budget は局所 pair の budget なので、full list へは昇格しない。

この非対称性が、今回の実装の正しい読みじゃ。

## レビュー

## 採用理由

第一に、`tail_failure_oneStepDiagnosis` の alias が良い。

```lean id="vgmjs9"
sourcePressureLocalIslandWitnessList_tail_failure_oneStepDiagnosis
```

これは中身としては既存の one-step diagnosis を tail に適用するだけだが、後続の theorem で読みやすくなる。

第二に、tail overlap lift が適切。

```lean id="p4v1kw"
sourcePressureLocalIslandWitnessList_tailDiagnosis_overlap_lift
```

これは `of_tail` の読み替えだが、「tail diagnosis の overlap branch を head の下へ運ぶ」という意味が明確になる。

第三に、main theorem の shape が安全。

```lean id="ujj5vv"
sourcePressureLocalIslandWitnessList_tailFailure_oneStepDiagnosis_under_cons
```

結果は、

```text id="kwdmaj"
tail recovered budget
or full-list adjacent overlap obstruction
or deeper tail failure
```

であって、tail recovered budget を full-list accounting にしていない。

第四に、optional wrapper も便利。

```lean id="iwvotn"
sourcePressureLocalIslandWitnessList_tailFailure_oneStepDiagnosis_under_cons_or_listFailure
```

obstruction の中身を必要としない caller には、ordinary list failure へ弱めた形が使える。

## 注意点

## 1. まだ一般 recursive classifier ではない

今回も一段分の構文補題じゃ。

まだ次は言っていない。

```text id="p8x56k"
任意長 list を完全分類する
全 recovered budget を集計する
list-wide sorting を行う
```

これはまだ先じゃ。

## 2. recovered branch の位置情報が重要

tail recovered branch は `W2,W3` に属する。

今後 length-3 / length-4 の bounded diagnosis を作るときは、recovered branch がどの adjacent pair 由来なのかを theorem 名または result shape に残した方がよい。

たとえば、

```text id="j7tgdd"
head recovered: W1,W2
tail recovered: W2,W3
```

を混ぜないことじゃ。

## 3. ordinary list failure wrapper は弱い

`under_cons_or_listFailure` は便利だが、情報を落としている。

```text id="65uu5d"
adjacent overlap obstruction
  -> ordinary list failure
```

へ弱めているため、後で obstruction branch を解析したい場面では sharper な `under_cons` を使うべきじゃ。

## 解説

今回の実装を直感で言えば、

```text id="mmvkhp"
tail で起きた診断結果を、
新しい head を付けた list の中でも失わないようにした
```

ということじゃ。

たとえば、

```text id="5zpyyj"
[W1, W2, W3]
```

で、tail `[W2, W3]` に failure があるとする。

その tail failure は、

```text id="81jf7f"
W2,W3 が逆順で recovered
または
W2,W3 が overlap obstruction
または
さらに tail へ送る
```

と診断される。

今回の API により、`W2,W3` の overlap obstruction は `[W1,W2,W3]` の adjacent obstruction として持ち上がる。
一方、`W2,W3` の recovered budget は、`W2,W3` の recovered budget のまま保持される。

この区別が非常に良い。

## 一歩先ゆく推論

次は report の通り、**固定長 list の bounded recursive diagnosis skeleton** が自然じゃ。

まずは length 3 がよい。

```text id="abv6ix"
failure [W1, W2, W3]
  -> head recovered
  or head overlap obstruction
  or tail recovered
  or tail overlap obstruction
```

これを一般再帰ではなく、まず長さ 3 の定理として作る。

なぜ長さ 3 か。
`[W1,W2,W3]` には adjacent pair が二つしかない。

```text id="wq8b2j"
head pair: W1,W2
tail pair: W2,W3
```

したがって、分類結果を安全に書ける。

## さらなる次の一手

length 3 が通ったら、次は length 4 じゃ。

```text id="5d53oj"
failure [W1, W2, W3, W4]
  -> pair W1,W2 diagnosis
  or pair W2,W3 diagnosis
  or pair W3,W4 diagnosis
```

これを見れば、fuel-indexed diagnosis の shape が見えてくる。

ただし、まだ budget 集計はしない。
まずは「どの隣接 pair が診断されたか」を返すだけにする。

## 賢狼が試して欲しい実験補題

## 実験補題 A: length-3 failure diagnosis

まずはこの形が本命じゃ。

```lean id="w4ejgc"
theorem sourcePressureLocalIslandWitnessList_failure_threeDiagnosis
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
    (h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (h3pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        [W1, W2, W3]) :
    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W1 W2 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
          [W1, W2, W3])
    ∨
    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W2 W3 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
          [W1, W2, W3])
```

証明方針はこうじゃ。

```text id="575u8n"
oneStepDiagnosis on [W1,W2,W3]

head branch:
  left side

tail branch:
  tail is [W2,W3]
  apply tailFailure_oneStepDiagnosis_under_cons
  deeper tail is [W3], impossible / no failure
```

ただし tail one-step theorem の deeper branch は `SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W3]` になる。
これは `False` に落とせるはずだが、専用 lemma があると楽じゃ。

## 実験補題 B: singleton has no sorted-before failure

```lean id="l4be1k"
theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure_singleton_false
    {n : OddNat} {k r : ℕ}
    {W : SourcePressureLocalIslandWitness n k r} :
    ¬ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W]
```

定義から `simp` で落ちる可能性が高い。
`[]` 版もあるとよい。

```lean id="ebauhn"
theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure_nil_false
    {n : OddNat} {k r : ℕ} :
    ¬ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
      ([] : List (SourcePressureLocalIslandWitness n k r))
```

## 実験補題 C: pair failure threeDiagnosis tail simplification

もし length-3 theorem の tail deeper branch が邪魔なら、まず tail pair 用に、

```lean id="trxov8"
theorem sourcePressureLocalIslandWitnessList_tailPair_failure_under_cons_diagnosis
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (h3pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
    (htail :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W2, W3]) :
    (∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W2 W3 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
    ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
        [W1, W2, W3]
```

これなら `sourcePressureLocalIslandWitnessList_tailFailure_oneStepDiagnosis_under_cons` を使い、deeper tail `[W3]` を false で潰せる。

## 実験補題 D: length-3 ordinary failure wrapper

情報を落とした版もあると便利じゃ。

```lean id="wlcrcx"
theorem sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_or_listFailure
```

ただし、まず sharper 版だけでよい。

## 次の Codex 指示

```text id="txqol8"
Checkpoint 169: Main root only — bounded length-three failure diagnosis.

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
Checkpoint 168 added weak tail-cons propagation:

- sourcePressureLocalIslandWitnessList_tail_failure_oneStepDiagnosis
- sourcePressureLocalIslandWitnessList_tailDiagnosis_overlap_lift
- sourcePressureLocalIslandWitnessList_tailFailure_oneStepDiagnosis_under_cons
- sourcePressureLocalIslandWitnessList_tailFailure_oneStepDiagnosis_under_cons_or_listFailure

Global rules:
- Do not claim maximality.
- Do not claim uniqueness of pressure families.
- Do not claim coverage.
- Do not claim prefix behavior.
- Do not claim union accounting.
- Do not claim Collatz convergence.
- Keep all statements local to explicitly supplied witness lists.
- Reverse branch is recovered at pair level only.
- Recovered budgets must remain attached to the adjacent pair that produced them.
- Overlap branch remains an adjacent obstruction.
- Do not merge intervals or prove union accounting in this checkpoint.
- Do not implement a full list sorting algorithm.
- Do not introduce a general recursive classifier yet.

Main goal:
Add a bounded diagnosis theorem for length-three witness lists.  A failure in
`[W1, W2, W3]` should be diagnosed as either the head pair `W1,W2`, or the tail
pair `W2,W3`.

Part A: base false lemmas for empty and singleton lists.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure_nil_false
      {n : OddNat} {k r : Nat} :
      ¬ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        ([] : List (SourcePressureLocalIslandWitness n k r))

  theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure_singleton_false
      {n : OddNat} {k r : Nat}
      {W : SourcePressureLocalIslandWitness n k r} :
      ¬ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W]

Expected proof:
- simp/unfold the same definitions used in previous list-failure lemmas.

Part B: tail pair diagnosis under a new head.

Prove:

  theorem sourcePressureLocalIslandWitnessList_tailPair_failure_under_cons_diagnosis
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
      (h2pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
      (h3pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
      (htail :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W2, W3]) :
      (∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
        (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          W2 W3 hrev).items).map
          (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
          [W1, W2, W3]

Suggested proof:
- use sourcePressureLocalIslandWitnessList_tailFailure_oneStepDiagnosis_under_cons
    h2pos h3pos htail
- cases:
  - recovered: left
  - overlap obstruction: right
  - deeper singleton failure: contradiction using singleton_false

Part C: length-three diagnosis.

Prove:

  theorem sourcePressureLocalIslandWitnessList_failure_threeDiagnosis
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
      (h1pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
      (h2pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
      (h3pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
      (h :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2, W3]) :
      ((∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
        (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          W1 W2 hrev).items).map
          (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
        ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
            [W1, W2, W3])
      ∨
      ((∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
        (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          W2 W3 hrev).items).map
          (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
        ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
            [W1, W2, W3])

Suggested proof:
- use sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis
    h1pos h2pos h
- head branch: left
- tail failure branch:
  apply sourcePressureLocalIslandWitnessList_tailPair_failure_under_cons_diagnosis
    h2pos h3pos to htail
  and wrap as right.

Part D: optional ordinary-failure weakened wrapper.

Only if easy, add a theorem that weakens both overlap branches to ordinary
sorted-before failure of `[W1, W2, W3]`.  Do not force this.

Part E: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-169.md

Include:
- nil/singleton no-failure lemmas,
- tail pair diagnosis under cons,
- length-three diagnosis theorem,
- explicit note that recovered budgets remain pair-local:
  head pair `W1,W2` or tail pair `W2,W3`,
- explicit note that this is bounded length-three only,
- explicit note that no general recursive classifier/sorting algorithm was added,
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

Checkpoint 169 が通ったら、次は length 4 じゃ。

ただし length 4 では branch が増える。

```text id="f9z9t9"
failure [W1,W2,W3,W4]
  -> pair W1,W2 diagnosis
  or pair W2,W3 diagnosis
  or pair W3,W4 diagnosis
```

ここで theorem shape が急に長くなる。
そこで、length 4 の前に、diagnosis result を小さな inductive / structure に包む設計を考えてもよい。

例えば、

```lean id="8yw3ki"
inductive SourcePressureLocalIslandWitnessAdjacentDiagnosis
```

のような型を置き、

```text id="fdy3zr"
recovered pair
overlap obstruction
```

を一つの result にまとめる。

ただし、これを入れるのはまだ少し早いかもしれぬ。
まず length 3 を定理だけで通し、返り値がどれだけ重くなるかを見るのがよい。

## 総評

Checkpoint 168 は、tail 診断を head の下でも安全に扱えるようにした良い一手じゃ。

次は length 3。
ここを通せば、

```text id="6pbe4g"
failure [W1,W2,W3]
```

が、隣接 pair 2 本のどちらかの診断へ落ちる。

これができると、list-level failure diagnosis は、燃料付き一般化の手前まで来る。
焦らず、まず短い list で型の形を観測するのが賢いぞ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
index 07d8b573..daf3f5b2 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -2905,6 +2905,124 @@ theorem sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis
         h1pos h2pos hhead)
   · exact Or.inr htail
 
+/--
+Tail-facing alias for one-step diagnosis.
+
+The recovered branch is still the reversed budget for the tail head pair
+`W2, W3`; this theorem only chooses names that make the tail role explicit.
+-/
+theorem sourcePressureLocalIslandWitnessList_tail_failure_oneStepDiagnosis
+    {n : OddNat} {k r : ℕ}
+    {W2 W3 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (h2pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
+    (h3pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
+    (htail :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        (W2 :: W3 :: rest)) :
+    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
+      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        W2 W3 hrev).items).map
+        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
+      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+          (W2 :: W3 :: rest))
+    ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        (W3 :: rest) :=
+  sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis
+    h2pos h3pos htail
+
+/--
+Lift an adjacent-overlap obstruction in the tail under a newly supplied head.
+
+This is only propagation of the obstruction predicate.  It does not merge
+intervals, repair overlap, or create a full-list recovered budget.
+-/
+theorem sourcePressureLocalIslandWitnessList_tailDiagnosis_overlap_lift
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (hobs :
+      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+        (W2 :: W3 :: rest)) :
+    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+      (W1 :: W2 :: W3 :: rest) :=
+  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_tail
+    hobs
+
+/--
+Weakly view a tail one-step diagnosis under a new head.
+
+The left recovered branch remains the recovered budget for the tail pair
+`W2, W3`.  The new head can only carry the tail overlap obstruction forward;
+it does not turn a tail-pair recovery into accounting for the full list.
+-/
+theorem sourcePressureLocalIslandWitnessList_tailFailure_oneStepDiagnosis_under_cons
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (h2pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
+    (h3pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
+    (htail :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        (W2 :: W3 :: rest)) :
+    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
+      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        W2 W3 hrev).items).map
+        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
+      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+          (W1 :: W2 :: W3 :: rest))
+    ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        (W3 :: rest) := by
+  rcases sourcePressureLocalIslandWitnessList_tail_failure_oneStepDiagnosis
+      h2pos h3pos htail with htailDiag | hdeep
+  · rcases htailDiag with hrecovered | hobs
+    · exact Or.inl (Or.inl hrecovered)
+    · exact Or.inl (Or.inr
+        (sourcePressureLocalIslandWitnessList_tailDiagnosis_overlap_lift
+          hobs))
+  · exact Or.inr hdeep
+
+/--
+Weak tail diagnosis with the lifted overlap branch downgraded to ordinary
+full-list sorted-before failure.
+
+The recovered branch is still only the tail-pair recovered budget.  This wrapper
+is useful for callers that only need to know that the enlarged list fails, while
+the obstruction-specific theorem above keeps the sharper evidence.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_tailFailure_oneStepDiagnosis_under_cons_or_listFailure
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (h2pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
+    (h3pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
+    (htail :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        (W2 :: W3 :: rest)) :
+    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
+      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        W2 W3 hrev).items).map
+        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
+      ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+          (W1 :: W2 :: W3 :: rest))
+    ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        (W3 :: rest) := by
+  rcases sourcePressureLocalIslandWitnessList_tailFailure_oneStepDiagnosis_under_cons
+      h2pos h3pos htail with hdiag | hdeep
+  · rcases hdiag with hrecovered | hobs
+    · exact Or.inl (Or.inl hrecovered)
+    · exact Or.inl (Or.inr
+        (SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
+          hobs))
+  · exact Or.inr hdeep
+
 /--
 Head-pair split with the obstruction branch weakened to ordinary list
 sorted-before failure.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-168.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-168.md
new file mode 100644
index 00000000..017bd2b9
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-168.md
@@ -0,0 +1,170 @@
+# Report Petal 168
+
+## Checkpoint
+
+Checkpoint 168 adds weak tail-cons propagation for the one-step sorted-before
+failure diagnosis built in checkpoint 167.
+
+The scope remains local to explicit witness lists.  A diagnosis of the tail
+list `W2 :: W3 :: rest` can be viewed under a newly supplied head `W1`, but a
+recovered branch remains a budget for the tail head pair `W2, W3`.
+
+## Implemented Lean Surface
+
+File:
+
+- `DkMath.Collatz.PetalBridge.PressureAccounting`
+
+### 1. Tail one-step diagnosis alias
+
+```lean
+theorem sourcePressureLocalIslandWitnessList_tail_failure_oneStepDiagnosis
+    {n : OddNat} {k r : ℕ}
+    {W2 W3 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (h2pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
+    (h3pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
+    (htail :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        (W2 :: W3 :: rest)) :
+    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
+      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        W2 W3 hrev).items).map
+        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
+      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+          (W2 :: W3 :: rest))
+    ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        (W3 :: rest)
+```
+
+This is a naming alias for applying the existing one-step diagnosis to a tail
+list.  The unused `W1` from the suggested shape was intentionally omitted,
+because the theorem itself does not depend on a new head.
+
+### 2. Tail overlap lift
+
+```lean
+theorem sourcePressureLocalIslandWitnessList_tailDiagnosis_overlap_lift
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (hobs :
+      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+        (W2 :: W3 :: rest)) :
+    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+      (W1 :: W2 :: W3 :: rest)
+```
+
+This propagates a tail adjacent-overlap obstruction under a new head.  It does
+not merge or repair the overlap.
+
+### 3. Weak tail diagnosis under cons
+
+```lean
+theorem sourcePressureLocalIslandWitnessList_tailFailure_oneStepDiagnosis_under_cons
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (h2pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
+    (h3pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
+    (htail :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        (W2 :: W3 :: rest)) :
+    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
+      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        W2 W3 hrev).items).map
+        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
+      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+          (W1 :: W2 :: W3 :: rest))
+    ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        (W3 :: rest)
+```
+
+This is the main cp168 theorem.  It lifts only the obstruction branch through
+the new head.  The recovered branch remains the tail-pair recovered budget.
+
+### 4. Optional ordinary failure wrapper
+
+```lean
+theorem
+    sourcePressureLocalIslandWitnessList_tailFailure_oneStepDiagnosis_under_cons_or_listFailure
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (h2pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
+    (h3pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
+    (htail :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        (W2 :: W3 :: rest)) :
+    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
+      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        W2 W3 hrev).items).map
+        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
+      ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+          (W1 :: W2 :: W3 :: rest))
+    ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        (W3 :: rest)
+```
+
+This wrapper weakens the lifted overlap obstruction to ordinary full-list
+sorted-before failure for callers that do not need obstruction-specific
+evidence.
+
+## Boundary Notes
+
+This checkpoint intentionally does not introduce:
+
+- maximality,
+- uniqueness of pressure families,
+- coverage,
+- prefix behavior,
+- union accounting,
+- interval merging,
+- arbitrary list sorting,
+- arbitrary list failure classification,
+- Collatz convergence.
+
+Recovered budget remains a tail-pair budget.  It is not promoted into a
+full-list budget.
+
+Overlap remains unmerged and unhandled.  The code only propagates the local
+adjacent obstruction.
+
+## Next Inference
+
+The next safe direction is a bounded recursive diagnosis skeleton for a fixed
+short list, starting with length three:
+
+```text
+failure [W1, W2, W3]
+  -> head recovered
+  or head overlap obstruction
+  or tail recovered
+  or tail overlap obstruction
+```
+
+This should still avoid a general sorting algorithm.  Once length-three and
+length-four surfaces stabilize, a fuel-indexed diagnosis structure can be
+designed from the observed pattern.
+
+## Verification
+
+- PASS: `lake build DkMath.Collatz.PetalBridge.PressureAccounting`
+- PASS: `lake build DkMath.Collatz.PetalBridge.PressureFrontier`
+- PASS: `lake build DkMath.Collatz.PetalBridge`
+- PASS: `rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean`
+  produced no hits.
+- PASS: `rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean`
+  produced no hits.
+- PASS: `git diff --check`
+
+Build note: the existing unrelated warning from
+`DkMath.NumberTheory.ZsigmondyCyclotomicResearch` still reports a declaration
+using `sorry`.  This checkpoint did not edit that file, and the two target
+Collatz/PetalBridge files checked above have no `sorry` hits.
````
`````
