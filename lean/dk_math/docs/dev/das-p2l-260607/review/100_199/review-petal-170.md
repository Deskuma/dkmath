# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAccounting

gch: 18566cdd48c71b24eec750e1064977fe2a8deced

## Report

cp169 完了です。

[PressureAccounting.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean) に length-three 固定の診断補題を追加しました。

- `SourcePressureLocalIslandWitnessListHasSortedBeforeFailure_nil_false`
- `SourcePressureLocalIslandWitnessListHasSortedBeforeFailure_singleton_false`
- `sourcePressureLocalIslandWitnessList_tailPair_failure_under_cons_diagnosis`
- `sourcePressureLocalIslandWitnessList_failure_threeDiagnosis`
- おまけ: `sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_or_listFailure`

`[W1, W2, W3]` の failure を、隣接 pair `W1,W2` または `W2,W3` の診断へ落とす形です。recovered budget は各 pair 局所のままで、full-list budget には昇格していません。

レポート: [report-petal-169.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-169.md)

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureAccounting` PASS
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier` PASS
- `lake build DkMath.Collatz.PetalBridge` PASS
- 対象 2 ファイルの `sorry` 検索: ヒットなし
- `git diff --check` PASS

既存の `ZsigmondyCyclotomicResearch` の `sorry` 警告は今回も無関係です。

## Review

## 結論

うむ、Checkpoint 169 は **採用** じゃ 👍️
今回で、長さ 3 の witness list に対して、

```text
failure [W1, W2, W3]
  -> pair W1,W2 の診断
  or pair W2,W3 の診断
```

という固定長診断が通った。

追加された主補題は、

```lean
SourcePressureLocalIslandWitnessListHasSortedBeforeFailure_nil_false
SourcePressureLocalIslandWitnessListHasSortedBeforeFailure_singleton_false
sourcePressureLocalIslandWitnessList_tailPair_failure_under_cons_diagnosis
sourcePressureLocalIslandWitnessList_failure_threeDiagnosis
sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_or_listFailure
```

じゃな。recovered budget は `W1,W2` または `W2,W3` の pair-local budget のまま保持されており、full-list budget へ昇格していない。この境界管理はとても良い。

## 状況分析

## 1. bounded diagnosis が初めて形になった

これまでの流れは、

```text
pair diagnosis
head-pair diagnosis
one-step list diagnosis
tail-cons propagation
```

じゃった。

今回、そこから一歩進んで、長さ 3 に固定した bounded diagnosis が入った。

```text
[W1, W2, W3]
```

には隣接 pair が二つしかない。

```text
head pair: W1,W2
tail pair: W2,W3
```

したがって、list failure が起きたとき、その原因はこの二本のどちらかに落ちる。今回の theorem は、その構造を Lean で閉じたものじゃ。

## 2. nil / singleton false が地味に重要

```lean
SourcePressureLocalIslandWitnessListHasSortedBeforeFailure_nil_false
SourcePressureLocalIslandWitnessListHasSortedBeforeFailure_singleton_false
```

この二つは小さいが、固定長診断には必須になる。

長さ 3 の tail branch をさらに剥がすと、最後に singleton failure が出る。
そこを false で潰せるので、tail pair `W2,W3` の診断で閉じられる。

今後、長さ 4、長さ 5 と進む場合にも、末端処理としてこの二つは使い回せる。

## 3. Or 型がすでに重くなり始めた

今回の `sourcePressureLocalIslandWitnessList_failure_threeDiagnosis` は正しいが、返り値がすでに大きい。

```text
(head recovered or overlap)
or
(tail recovered or overlap)
```

長さ 4 へ行くと、

```text
pair W1,W2
or pair W2,W3
or pair W3,W4
```

になり、各 pair がさらに

```text
recovered or overlap
```

を持つ。

つまり直接 `Or` を入れ子にすると、型がかなり読みにくくなる。
report の Next Inference にある通り、次は carrier を考える価値がある。

## レビュー

## 採用理由

第一に、length-three に限定したのがよい。

いきなり一般 recursive classifier を作らず、短い list で返り値の形を観測した。これは Lean 実装としても設計探索としても安全じゃ。

第二に、pair-local budget の位置を守っている。

```text
head recovered:
  W1,W2 の budget

tail recovered:
  W2,W3 の budget
```

これを full-list budget と読んでいない。
ここを誤ると union accounting を暗黙に主張してしまうので、今回の制限は正しい。

第三に、ordinary failure wrapper を別に置いたのもよい。

```lean
sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_or_listFailure
```

これは情報を弱めるが、consumer が obstruction の詳細を必要としない場合に便利じゃ。
一方で、sharp な theorem も残っているので、今後の解析にも耐える。

## 注意点

## 1. length-three theorem は一般分類ではない

今回言えたのは、

```text
長さ 3 の明示 list に対する bounded diagnosis
```

だけじゃ。

まだ次は言っていない。

```text
任意長 list の全 failure を分類する
list-wide sorting を行う
recovered budget を合算する
```

ここは引き続き禁止領域。

## 2. overlap obstruction はまだ未回収

overlap branch は、

```text
SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction [W1,W2,W3]
```

として記録されるだけじゃ。

まだ merge しない。
まだ split しない。
まだ union accounting しない。

これは今後も守るべき境界じゃ。

## 3. 次に length-four へ直行すると型が肥大化する

長さ 4 を直接 theorem にしても、おそらく通る。
しかし型がかなり重くなる。

ここで carrier を入れるか、length-four を一度だけ直書きして肥大化を観測するか、分岐点じゃ。

わっちのおすすめは、**まず軽い carrier を入れる** ことじゃ。

## 次の設計判断

## carrier を入れる案

次は、隣接 pair の診断結果を小さく包むのが良い。

目的は、こういう入れ子を避けることじゃ。

```text
(recovered W1,W2 or overlap L)
or
(recovered W2,W3 or overlap L)
or
(recovered W3,W4 or overlap L)
```

これを、

```text
AdjacentDiagnosis L A B
```

のように包む。

## 候補定義

一番軽いのは `Prop` 型の inductive じゃ。

```lean
inductive SourcePressureLocalIslandWitnessAdjacentDiagnosis
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (A B : SourcePressureLocalIslandWitness n k r) : Prop
  | recovered
      (hrev : SourcePressureLocalIslandWitnessBefore B A)
      (hbudget :
        (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          A B hrev).items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) :
      SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B
  | overlap
      (hobs : SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
      SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B
```

ここで `L` は enclosing list。
`A B` は診断対象の adjacent pair。

recovered branch は `A,B` の pair-local budget。
overlap branch は enclosing list `L` の adjacent obstruction。

これなら length-three theorem は次のように短くなる。

```lean
theorem sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_carrier
    ...
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2, W3]) :
    SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3] W1 W2 ∨
      SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3] W2 W3
```

かなり読みやすい。

## さらに安全な案

いきなり `inductive` が重ければ、`def` でもよい。

```lean
def SourcePressureLocalIslandWitnessAdjacentDiagnosis
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (A B : SourcePressureLocalIslandWitness n k r) : Prop :=
  (∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
    (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
      A B hrev).items).map
      (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2)
  ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
```

こちらは theorem が簡単になる。
ただし constructor 名が持てないので、後続で branch を扱うなら `inductive` の方が読みやすい。

わっちなら、今回は `def` で始めてもよいと思う。
DkMath の今の段階では、「証明を軽く進める」方が大事じゃ。

## 次の Codex 指示

```text
Checkpoint 170: Main root only — introduce a bounded adjacent-diagnosis carrier.

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
Checkpoint 169 added bounded length-three diagnosis:

- SourcePressureLocalIslandWitnessListHasSortedBeforeFailure_nil_false
- SourcePressureLocalIslandWitnessListHasSortedBeforeFailure_singleton_false
- sourcePressureLocalIslandWitnessList_tailPair_failure_under_cons_diagnosis
- sourcePressureLocalIslandWitnessList_failure_threeDiagnosis
- sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_or_listFailure

Global rules:
- Do not claim maximality.
- Do not claim uniqueness of pressure families.
- Do not claim coverage.
- Do not claim prefix behavior.
- Do not claim union accounting.
- Do not claim Collatz convergence.
- Keep all statements local to explicitly supplied witness lists.
- Recovered budgets must remain attached to the adjacent pair that produced them.
- Overlap branch remains an adjacent obstruction on the enclosing list.
- Do not merge intervals or prove union accounting.
- Do not implement a full list sorting algorithm.
- Do not introduce a general recursive classifier yet.

Main goal:
Introduce a small carrier predicate for adjacent-pair diagnosis so that bounded
length-three and later length-four diagnosis theorems do not explode into nested
Or types.

Part A: define a lightweight adjacent diagnosis predicate.

Prefer a `def` first, unless an inductive type is clearly easier.

  def SourcePressureLocalIslandWitnessAdjacentDiagnosis
      {n : OddNat} {k r : Nat}
      (L : List (SourcePressureLocalIslandWitness n k r))
      (A B : SourcePressureLocalIslandWitness n k r) : Prop :=
    (∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        A B hrev).items).map
        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2)
    ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L

Meaning:
- recovered branch is pair-local for A,B;
- overlap branch is obstruction evidence on the enclosing list L;
- no union accounting is implied.

Part B: constructors.

Prove:

  theorem SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {A B : SourcePressureLocalIslandWitness n k r}
      (hrev : SourcePressureLocalIslandWitnessBefore B A)
      (hbudget :
        (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          A B hrev).items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) :
      SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B

  theorem SourcePressureLocalIslandWitnessAdjacentDiagnosis.overlap
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {A B : SourcePressureLocalIslandWitness n k r}
      (hobs : SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
      SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B

These should be `Or.inl` and `Or.inr`.

Part C: wrappers from existing length-three branches.

Prove head wrapper:

  theorem sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_carrier
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
      SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3] W1 W2 ∨
        SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3] W2 W3

Suggested proof:
- use sourcePressureLocalIslandWitnessList_failure_threeDiagnosis
- map each recovered/overlap branch into the carrier constructors.

Part D: optional elimination theorem.

Only if useful, prove:

  theorem SourcePressureLocalIslandWitnessAdjacentDiagnosis.elim
      ...
      (hdiag : SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B)
      (hrecovered : (∃ hrev : ..., budget ...) -> P)
      (hoverlap : SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L -> P) :
      P

Do not force this if the def unfolds easily.

Part E: optional ordinary failure wrapper.

If useful, prove that an adjacent diagnosis implies either pair-local recovered
budget or ordinary sorted-before failure for L:

  theorem SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered_or_listFailure
      ...

This should simply weaken overlap by
`SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure`.

Do not force this.

Part F: no length-four yet unless the carrier is completely stable.

Do not add length-four diagnosis in this checkpoint unless all carrier lemmas
are trivial and build remains clean.  The goal is to stabilize the return type.

Part G: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-170.md

Include:
- the adjacent diagnosis carrier definition,
- recovered/overlap constructors,
- length-three carrier theorem,
- optional elimination/weakened wrapper if added,
- explicit note that recovered budget is pair-local,
- explicit note that overlap remains unmerged/unhandled,
- explicit note that this is only a result carrier, not a recursive classifier,
- explicit note that no sorting, coverage, maximality, uniqueness, prefix behavior,
  union accounting, or Collatz convergence was introduced.

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

Checkpoint 170 で carrier が通ったら、次に length 4 を試すのがよい。

carrier があれば、形はこう書ける。

```lean
theorem sourcePressureLocalIslandWitnessList_failure_fourDiagnosis_carrier
    ...
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2, W3, W4]) :
    SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3, W4] W1 W2 ∨
      SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3, W4] W2 W3 ∨
        SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3, W4] W3 W4
```

この形なら、長さ 4 でも読みやすい。
そして length 4 が通ったら、fuel-indexed generalization の形がかなりはっきり見える。

## 総評

Checkpoint 169 は良い節目じゃ。
ついに list failure が、固定長 3 で adjacent pair diagnosis に落ちた。

ここまでで、

```text
pair diagnosis
one-step list diagnosis
tail-cons diagnosis
length-three bounded diagnosis
```

が揃った。

次は返り値の整理。
carrier を入れておけば、length 4 以降も無理なく伸ばせる。
ここで焦って一般 recursive classifier に行かず、型の形を整えるのが賢い一手じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
index daf3f5b2..51b4b507 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -1785,6 +1785,25 @@ theorem sourcePressureLocalIslandWitnessList_no_failure_singleton
     SourcePressureIntervalPulseAddressListHasSortedBeforeFailure,
     sourcePressureAccountedIntervalList_of_intervalPulseAddressList] using h

+/-- The empty witness list has no adjacent sorted-before failure. -/
+theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure_nil_false
+    {n : OddNat} {k r : ℕ} :
+    ¬ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+      ([] : List (SourcePressureLocalIslandWitness n k r)) := by
+  intro h
+  simpa [SourcePressureLocalIslandWitnessListHasSortedBeforeFailure,
+    sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList,
+    SourcePressureIntervalPulseAddressFamilyHasSortedBeforeFailure,
+    SourcePressureIntervalPulseAddressListHasSortedBeforeFailure,
+    sourcePressureAccountedIntervalList_of_intervalPulseAddressList] using h
+
+/-- Name aligned with the failure predicate: singleton lists cannot fail. -/
+theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure_singleton_false
+    {n : OddNat} {k r : ℕ}
+    {W : SourcePressureLocalIslandWitness n k r} :
+    ¬ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W] :=
+  sourcePressureLocalIslandWitnessList_no_failure_singleton W
+
 /--
 Accounted interval family generated by one explicit local-island witness.

@@ -3023,6 +3042,116 @@ theorem
           hobs))
   · exact Or.inr hdeep

+/--
+Diagnose a tail pair failure under a newly supplied head.
+
+The recovered branch is attached to the tail pair `W2, W3`.  The obstruction
+branch is the lifted adjacent overlap on the bounded three-witness list.
+-/
+theorem sourcePressureLocalIslandWitnessList_tailPair_failure_under_cons_diagnosis
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
+    (h2pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
+    (h3pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
+    (htail :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W2, W3]) :
+    (∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
+      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        W2 W3 hrev).items).map
+        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
+    ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+        [W1, W2, W3] := by
+  rcases sourcePressureLocalIslandWitnessList_tailFailure_oneStepDiagnosis_under_cons
+      h2pos h3pos htail with hdiag | hsingle
+  · exact hdiag
+  · exact False.elim
+      (SourcePressureLocalIslandWitnessListHasSortedBeforeFailure_singleton_false
+        hsingle)
+
+/--
+Bounded diagnosis for a three-witness sorted-before failure.
+
+The failure of `[W1, W2, W3]` is diagnosed by one of its two adjacent pairs.
+Recovered budgets remain pair-local: either `W1, W2` or `W2, W3`.  This is a
+fixed length-three theorem, not a recursive classifier.
+-/
+theorem sourcePressureLocalIslandWitnessList_failure_threeDiagnosis
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
+    (h1pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
+    (h2pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
+    (h3pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2, W3]) :
+    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
+      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        W1 W2 hrev).items).map
+        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
+      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+          [W1, W2, W3])
+    ∨
+    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
+      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        W2 W3 hrev).items).map
+        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
+      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+          [W1, W2, W3]) := by
+  rcases sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis
+      h1pos h2pos h with hhead | htail
+  · exact Or.inl hhead
+  · exact Or.inr
+      (sourcePressureLocalIslandWitnessList_tailPair_failure_under_cons_diagnosis
+        h2pos h3pos htail)
+
+/--
+Length-three diagnosis with overlap branches weakened to ordinary failure of
+the same three-witness list.
+
+The recovered alternatives are still pair-local.  This wrapper is deliberately
+bounded to length three and does not perform list sorting or union accounting.
+-/
+theorem sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_or_listFailure
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
+    (h1pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
+    (h2pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
+    (h3pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2, W3]) :
+    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
+      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        W1 W2 hrev).items).map
+        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
+      ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+          [W1, W2, W3])
+    ∨
+    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
+      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        W2 W3 hrev).items).map
+        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
+      ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+          [W1, W2, W3]) := by
+  rcases sourcePressureLocalIslandWitnessList_failure_threeDiagnosis
+      h1pos h2pos h3pos h with hhead | htail
+  · rcases hhead with hrecovered | hobs
+    · exact Or.inl (Or.inl hrecovered)
+    · exact Or.inl (Or.inr
+        (SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
+          hobs))
+  · rcases htail with hrecovered | hobs
+    · exact Or.inr (Or.inl hrecovered)
+    · exact Or.inr (Or.inr
+        (SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
+          hobs))
+
 /--
 Head-pair split with the obstruction branch weakened to ordinary list
 sorted-before failure.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-169.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-169.md
new file mode 100644
index 00000000..c123027b
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-169.md
@@ -0,0 +1,180 @@
+# Report Petal 169
+
+## Checkpoint
+
+Checkpoint 169 adds a bounded length-three diagnosis theorem for explicit
+local-island witness lists.
+
+The theorem is deliberately not recursive.  It only says that a failure in
+`[W1, W2, W3]` is diagnosed by one of its two adjacent pairs:
+
+- head pair `W1, W2`,
+- tail pair `W2, W3`.
+
+Recovered budgets remain attached to the adjacent pair that produced them.
+
+## Implemented Lean Surface
+
+File:
+
+- `DkMath.Collatz.PetalBridge.PressureAccounting`
+
+### 1. Empty and singleton no-failure facts
+
+```lean
+theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure_nil_false
+    {n : OddNat} {k r : ℕ} :
+    ¬ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+      ([] : List (SourcePressureLocalIslandWitness n k r))
+```
+
+```lean
+theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure_singleton_false
+    {n : OddNat} {k r : ℕ}
+    {W : SourcePressureLocalIslandWitness n k r} :
+    ¬ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W]
+```
+
+The singleton theorem is a name-aligned alias of the older
+`sourcePressureLocalIslandWitnessList_no_failure_singleton`.
+
+### 2. Tail pair diagnosis under a new head
+
+```lean
+theorem sourcePressureLocalIslandWitnessList_tailPair_failure_under_cons_diagnosis
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
+    (h2pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
+    (h3pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
+    (htail :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W2, W3]) :
+    (∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
+      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        W2 W3 hrev).items).map
+        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
+    ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+        [W1, W2, W3]
+```
+
+This consumes the cp168 weak tail diagnosis under cons.  The impossible deeper
+branch is `SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W3]`,
+which is eliminated by the singleton no-failure theorem.
+
+### 3. Length-three diagnosis
+
+```lean
+theorem sourcePressureLocalIslandWitnessList_failure_threeDiagnosis
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
+    (h1pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
+    (h2pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
+    (h3pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2, W3]) :
+    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
+      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        W1 W2 hrev).items).map
+        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
+      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+          [W1, W2, W3])
+    ∨
+    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
+      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        W2 W3 hrev).items).map
+        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
+      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+          [W1, W2, W3])
+```
+
+The first branch is the head pair diagnosis.  The second branch is the tail
+pair diagnosis lifted under the original head.
+
+### 4. Optional ordinary-failure wrapper
+
+```lean
+theorem sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_or_listFailure
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
+    (h1pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
+    (h2pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
+    (h3pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2, W3]) :
+    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
+      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        W1 W2 hrev).items).map
+        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
+      ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+          [W1, W2, W3])
+    ∨
+    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
+      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        W2 W3 hrev).items).map
+        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
+      ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+          [W1, W2, W3])
+```
+
+This weakens overlap branches to ordinary sorted-before failure of the same
+three-witness list.
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
+The theorem is bounded to length three only.  Recovered budgets remain
+pair-local:
+
+- `W1, W2` in the head recovered branch,
+- `W2, W3` in the tail recovered branch.
+
+Overlap remains unmerged and unhandled.
+
+## Next Inference
+
+The length-three theorem shows that direct nested `Or` return types are already
+large.  Before length four, it may be worth introducing a small bounded result
+type, for example a local adjacent-pair diagnosis carrier with two constructors:
+
+```text
+recovered pair-local budget
+adjacent overlap obstruction on the enclosing list
+```
+
+That would keep a length-four theorem readable without introducing a general
+recursive classifier.  The alternative is to add length-four directly and use
+the resulting type verbosity as evidence for the final carrier shape.
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
