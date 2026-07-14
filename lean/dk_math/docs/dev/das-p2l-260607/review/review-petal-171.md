# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAccounting

gch: 7a8adb2c34afeb77601517abeb5cdee59866a9b5

## Report

cp170 完了です。

[PressureAccounting.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean) に adjacent diagnosis carrier を追加しました。

- `SourcePressureLocalIslandWitnessAdjacentDiagnosis`
- `SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered`
- `SourcePressureLocalIslandWitnessAdjacentDiagnosis.overlap`
- `SourcePressureLocalIslandWitnessAdjacentDiagnosis.elim`
- `SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered_or_listFailure`
- `sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_carrier`

carrier は result type の整理だけで、recursive classifier ではありません。recovered budget は pair-local、overlap は enclosing list の adjacent obstruction のままです。length-four にはまだ進めていません。

レポート: [report-petal-170.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-170.md)

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureAccounting` PASS
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier` PASS
- `lake build DkMath.Collatz.PetalBridge` PASS
- 対象 2 ファイルの `sorry` 検索: ヒットなし
- `git diff --check` PASS

既存の `ZsigmondyCyclotomicResearch` の `sorry` 警告は今回も無関係です。

## Review

## 結論

うむ、Checkpoint 170 は **採用** じゃ 👍️
今回で、固定長診断の返り値を整理するための **adjacent diagnosis carrier** が入った。

追加された中心は、

```lean id="ck6r75"
SourcePressureLocalIslandWitnessAdjacentDiagnosis
SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered
SourcePressureLocalIslandWitnessAdjacentDiagnosis.overlap
SourcePressureLocalIslandWitnessAdjacentDiagnosis.elim
SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered_or_listFailure
sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_carrier
```

じゃな。carrier は recursive classifier ではなく、bounded diagnosis theorem の返り値を軽くするための `Prop` 型の包みである、という境界も明確に守られておる。recovered budget は pair-local、overlap は enclosing list の adjacent obstruction のままじゃ。

## 状況分析

## 1. 返り値の爆発を抑える準備ができた

Checkpoint 169 の length-three theorem は正しかったが、返り値がすでに重かった。

```text id="sfm0po"
(head recovered or overlap)
or
(tail recovered or overlap)
```

今回の carrier によって、これを

```lean id="kl99ua"
SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B
```

として包めるようになった。

これで length-four 以降の theorem がだいぶ読みやすくなる。

## 2. carrier の設計が安全

今回の定義はかなり良い。

```lean id="avfdwh"
def SourcePressureLocalIslandWitnessAdjacentDiagnosis
    (L : List ...)
    (A B : SourcePressureLocalIslandWitness n k r) : Prop :=
  recovered budget for A,B
  ∨ adjacent overlap obstruction on L
```

ここで大事なのは、`A B` と `L` の役割が分かれていることじゃ。

```text id="59hf0n"
A,B:
  recovered budget の局所 pair

L:
  overlap obstruction を観測する enclosing list
```

つまり recovered は pair-local、overlap は list-local。
この非対称性がちゃんと型に出ている。

## 3. length-three theorem が綺麗になった

```lean id="qfhjjv"
sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_carrier
```

により、

```text id="rz4wv5"
failure [W1,W2,W3]
  -> diagnosis [W1,W2]
  or diagnosis [W2,W3]
```

という自然な形になった。

これは次の length-four theorem へ進む準備として、とてもよい。

## レビュー

## 採用理由

第一に、carrier を `def` に留めたのが良い。

`inductive` にすると constructor は綺麗になるが、最初から構造が重くなる。
今回は「返り値を軽くする」ことが目的なので、`def` + constructor theorem で十分じゃ。

第二に、constructor / elim / weakening が揃っている。

```lean id="mq88bq"
.recovered
.overlap
.elim
.recovered_or_listFailure
```

これだけあれば、carrier を直接 unfold せずに扱える。

第三に、length-four に進まず、carrier の安定化で止めたのが良い。

今回は result carrier の導入 checkpoint。
ここで length-four まで欲張らなかったのは正しい判断じゃ。

## 注意点

## 1. carrier は診断器ではない

これは重要じゃ。

```lean id="l2r1se"
SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B
```

は「診断結果を表す carrier」であって、list から自動で診断を探す関数ではない。

まだ次は言っていない。

```text id="gwt580"
任意 list のどこかに diagnosis がある
fuel 付きで全探索する
list を sort する
```

ここはまだ先じゃ。

## 2. overlap branch は enclosing list 依存

同じ pair `A,B` でも、enclosing list `L` が違えば overlap branch の意味が違う。

これは悪いことではない。
むしろ、今の設計では overlap obstruction は list 内の adjacent obstruction として扱うので、`L` を持たせるのが正しい。

## 3. recovered branch は pair-local のまま

これは今後も守るべき。

carrier に入ったからといって、

```text id="3wl9bh"
diagnosis L A B
```

を full-list accounting と読んではならぬ。

recovered branch は `A,B` の reversed pair budget じゃ。

## 解説

今回の実装を直感的に言うと、

```text id="0krvqy"
隣接 pair の診断結果を、小さな箱に入れた
```

ということじゃ。

箱の中身は二種類。

```text id="2fz9h5"
recovered:
  pair A,B を逆順にすれば budget ≤ -2 が得られる

overlap:
  enclosing list L に adjacent overlap obstruction がある
```

この二つを一つの carrier にしたことで、以後は theorem の返り値を短くできる。

これは、fuel-indexed generalization へ進む前の良い下準備じゃ。

## 一歩先ゆく推論

次は report の通り、**length-four carrier theorem** を試すのが自然じゃ。

目標は、

```text id="x5lg1c"
failure [W1,W2,W3,W4]
  -> diagnosis [W1,W2]
  or diagnosis [W2,W3]
  or diagnosis [W3,W4]
```

じゃ。

carrier があるので、返り値は次の形にできる。

```lean id="y3d20o"
SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1,W2,W3,W4] W1 W2 ∨
  SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1,W2,W3,W4] W2 W3 ∨
    SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1,W2,W3,W4] W3 W4
```

ここで注意すべきは、tail の length-three diagnosis は enclosing list が `[W2,W3,W4]` になる点じゃ。
それを `[W1,W2,W3,W4]` に持ち上げる wrapper が要る。

## 賢狼が試して欲しい実験補題

## 実験補題 A: carrier の overlap lift

tail list の carrier を full list 側へ持ち上げるには、overlap branch の `L` を変える必要がある。
まずこれを作るのがよい。

```lean id="r1a5ja"
theorem SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    {A B : SourcePressureLocalIslandWitness n k r}
    (hdiag :
      SourcePressureLocalIslandWitnessAdjacentDiagnosis (W2 :: rest) A B) :
    SourcePressureLocalIslandWitnessAdjacentDiagnosis (W1 :: W2 :: rest) A B
```

証明方針は carrier を分解。

```text id="he27o5"
recovered:
  same recovered budget をそのまま recovered constructor へ

overlap:
  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_tail
  で enclosing list を拡張
```

この補題があれば length-four が綺麗になる。

## 実験補題 B: length-four carrier theorem

```lean id="n7ub9o"
theorem sourcePressureLocalIslandWitnessList_failure_fourDiagnosis_carrier
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r}
    (h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (h3pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
    (h4pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W4).len)
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        [W1, W2, W3, W4]) :
    SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3, W4] W1 W2 ∨
      SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3, W4] W2 W3 ∨
        SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3, W4] W3 W4
```

証明方針はこう。

```text id="q8rc9g"
oneStepDiagnosis on [W1,W2,W3,W4]

head branch:
  diagnosis [W1,W2] を carrier に入れて left

tail branch:
  failure [W2,W3,W4]
  length-three carrier theorem を適用
  tail carrier を lift_tail で full list carrier へ持ち上げる
```

## 実験補題 C: carrier ordinary failure weakening after lift

これは optional。

```lean id="m8ht7k"
theorem SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail_recovered_or_listFailure
```

ただし、これは現時点では不要かもしれぬ。
まず length-four theorem を通す方が優先じゃ。

## 次の Codex 指示

```text id="v8o5dk"
Checkpoint 171: Main root only — bounded length-four failure diagnosis using adjacent diagnosis carrier.

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
Checkpoint 170 introduced the adjacent diagnosis carrier:

- SourcePressureLocalIslandWitnessAdjacentDiagnosis
- SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered
- SourcePressureLocalIslandWitnessAdjacentDiagnosis.overlap
- SourcePressureLocalIslandWitnessAdjacentDiagnosis.elim
- SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered_or_listFailure
- sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_carrier

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
Use the carrier to prove a bounded length-four diagnosis theorem.  A failure in
`[W1, W2, W3, W4]` should be diagnosed by one of its three adjacent pairs.

Part A: lift adjacent diagnosis through a new list head.

Prove:

  theorem SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      {rest : List (SourcePressureLocalIslandWitness n k r)}
      {A B : SourcePressureLocalIslandWitness n k r}
      (hdiag :
        SourcePressureLocalIslandWitnessAdjacentDiagnosis (W2 :: rest) A B) :
      SourcePressureLocalIslandWitnessAdjacentDiagnosis (W1 :: W2 :: rest) A B

Suggested proof:
- rcases hdiag with hrecovered | hobs
- recovered branch:
    exact SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered
      hrecovered.choose ?budget
  or simply use Or.inl hrecovered if the carrier is still a def.
- overlap branch:
    exact SourcePressureLocalIslandWitnessAdjacentDiagnosis.overlap
      (SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_tail hobs)

If using `Or.inl` directly is cleaner, do that.

Part B: bounded length-four carrier theorem.

Prove:

  theorem sourcePressureLocalIslandWitnessList_failure_fourDiagnosis_carrier
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r}
      (h1pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
      (h2pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
      (h3pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
      (h4pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W4).len)
      (h :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
          [W1, W2, W3, W4]) :
      SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3, W4] W1 W2 ∨
        SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3, W4] W2 W3 ∨
          SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3, W4] W3 W4

Suggested proof:
- Apply sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis
    h1pos h2pos h.
- Head branch:
    map recovered/overlap into SourcePressureLocalIslandWitnessAdjacentDiagnosis
    for [W1,W2,W3,W4] W1 W2, then return Or.inl.
- Tail branch:
    apply sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_carrier
      h2pos h3pos h4pos to the tail failure [W2,W3,W4].
    This returns diagnosis on enclosing list [W2,W3,W4].
    Lift each result by SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail
    to enclosing list [W1,W2,W3,W4].
    Return Or.inr (Or.inl ...) or Or.inr (Or.inr ...).

Part C: optional ordinary-failure weakening.

Only if easy, prove a wrapper that maps every carrier through
`SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered_or_listFailure`.
Do not force this if it becomes verbose.

Part D: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-171.md

Include:
- carrier tail-lift theorem,
- length-four carrier theorem,
- optional weakened wrapper if added,
- explicit note that recovered budgets remain pair-local:
  W1,W2; W2,W3; or W3,W4,
- explicit note that this is bounded length-four only,
- explicit note that no general recursive classifier/sorting algorithm was added,
- explicit note that overlap remains unmerged/unhandled,
- explicit note that no maximality, uniqueness, coverage, prefix behavior,
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

Checkpoint 171 で length-four carrier theorem が通ったら、次は **finite index carrier** を考える段階じゃ。

いまは、

```text id="7ne2rw"
length 3:
  pair 1 or pair 2

length 4:
  pair 1 or pair 2 or pair 3
```

となる。

この pattern は、次の形へ一般化できる。

```text id="rrv97b"
there exists adjacent index i
such that diagnosis at pair i,i+1
```

ただし、いきなり `∃ i` へ飛ぶと、list indexing / nth / Fin が重くなる。

そのため、次は length 5 へ行くより、`List` 用の小さな bounded carrier を設計するのがよさそうじゃ。

候補は、

```lean id="hz7q3f"
def SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
  ∃ A B, AdjacentPairInList L A B ∧
    SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B
```

ただし `AdjacentPairInList` の設計が要る。

ここは慎重にやるべきじゃ。
まずは length-four の結果を見てからでよい。

## 総評

Checkpoint 170 は、返り値の整理として良い節目じゃ。

これで length-three theorem はかなり読みやすくなった。
次は length-four。

length-four が carrier で綺麗に通れば、いよいよ「任意長へ進むには何を持てばよいか」が見えてくる。

まだ一般化しない。
まず固定長 4 で型の手触りを見る。
この慎重さが、後で大きく効くはずじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
index 51b4b507..8a046838 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -3152,6 +3152,117 @@ theorem sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_or_listFailu
         (SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
           hobs))
 
+/--
+Carrier predicate for a local adjacent-pair diagnosis inside an enclosing list.
+
+The recovered branch is always pair-local for `A, B`.  The overlap branch is an
+adjacent-overlap obstruction on the enclosing list `L`.  This carrier is only a
+return-type abbreviation for bounded diagnosis theorems; it does not perform
+sorting, merging, coverage, or union accounting.
+-/
+def SourcePressureLocalIslandWitnessAdjacentDiagnosis
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (A B : SourcePressureLocalIslandWitness n k r) : Prop :=
+  (∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
+    (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+      A B hrev).items).map
+      (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2)
+  ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
+
+/-- Constructor for the pair-local recovered branch of adjacent diagnosis. -/
+theorem SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {A B : SourcePressureLocalIslandWitness n k r}
+    (hrev : SourcePressureLocalIslandWitnessBefore B A)
+    (hbudget :
+      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        A B hrev).items).map
+        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) :
+    SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B :=
+  Or.inl ⟨hrev, hbudget⟩
+
+/-- Constructor for the enclosing-list overlap branch of adjacent diagnosis. -/
+theorem SourcePressureLocalIslandWitnessAdjacentDiagnosis.overlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {A B : SourcePressureLocalIslandWitness n k r}
+    (hobs : SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
+    SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B :=
+  Or.inr hobs
+
+/-- Eliminate an adjacent diagnosis by handling its two stored branches. -/
+theorem SourcePressureLocalIslandWitnessAdjacentDiagnosis.elim
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {A B : SourcePressureLocalIslandWitness n k r}
+    {P : Prop}
+    (hdiag : SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B)
+    (hrecovered :
+      (∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
+        (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+          A B hrev).items).map
+          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) → P)
+    (hoverlap : SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L → P) :
+    P := by
+  rcases hdiag with hrec | hobs
+  · exact hrecovered hrec
+  · exact hoverlap hobs
+
+/--
+Forget the obstruction-specific part of an adjacent diagnosis.
+
+The recovered branch remains pair-local; the overlap branch is weakened to
+ordinary sorted-before failure for the enclosing list.
+-/
+theorem SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered_or_listFailure
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {A B : SourcePressureLocalIslandWitness n k r}
+    (hdiag : SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B) :
+    (∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
+      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        A B hrev).items).map
+        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2)
+    ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L := by
+  rcases hdiag with hrec | hobs
+  · exact Or.inl hrec
+  · exact Or.inr
+      (SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
+        hobs)
+
+/--
+Length-three diagnosis with the nested branches packed into the adjacent
+diagnosis carrier.
+
+This is still bounded to `[W1, W2, W3]`.  The carrier keeps recovered budgets
+attached to the adjacent pair that produced them.
+-/
+theorem sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_carrier
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
+    SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3] W1 W2 ∨
+      SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3] W2 W3 := by
+  rcases sourcePressureLocalIslandWitnessList_failure_threeDiagnosis
+      h1pos h2pos h3pos h with hhead | htail
+  · rcases hhead with hrecovered | hobs
+    · exact Or.inl (Or.inl hrecovered)
+    · exact Or.inl
+        (SourcePressureLocalIslandWitnessAdjacentDiagnosis.overlap hobs)
+  · rcases htail with hrecovered | hobs
+    · exact Or.inr (Or.inl hrecovered)
+    · exact Or.inr
+        (SourcePressureLocalIslandWitnessAdjacentDiagnosis.overlap hobs)
+
 /--
 Head-pair split with the obstruction branch weakened to ordinary list
 sorted-before failure.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-170.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-170.md
new file mode 100644
index 00000000..5655e2c8
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-170.md
@@ -0,0 +1,171 @@
+# Report Petal 170
+
+## Checkpoint
+
+Checkpoint 170 introduces a bounded adjacent-diagnosis carrier for explicit
+local-island witness lists.
+
+The goal is to keep fixed-length diagnosis theorems readable before attempting
+length four or a fuel-indexed generalization.  The carrier is only a result
+predicate.  It is not a recursive classifier.
+
+## Implemented Lean Surface
+
+File:
+
+- `DkMath.Collatz.PetalBridge.PressureAccounting`
+
+### 1. Adjacent diagnosis carrier
+
+```lean
+def SourcePressureLocalIslandWitnessAdjacentDiagnosis
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (A B : SourcePressureLocalIslandWitness n k r) : Prop :=
+  (∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
+    (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+      A B hrev).items).map
+      (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2)
+  ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
+```
+
+Meaning:
+
+- the recovered branch is pair-local for `A, B`,
+- the overlap branch is an adjacent obstruction on the enclosing list `L`,
+- no sorting, merging, coverage, or union accounting is implied.
+
+### 2. Constructors
+
+```lean
+theorem SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {A B : SourcePressureLocalIslandWitness n k r}
+    (hrev : SourcePressureLocalIslandWitnessBefore B A)
+    (hbudget :
+      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        A B hrev).items).map
+        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) :
+    SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B
+```
+
+```lean
+theorem SourcePressureLocalIslandWitnessAdjacentDiagnosis.overlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {A B : SourcePressureLocalIslandWitness n k r}
+    (hobs : SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
+    SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B
+```
+
+These are thin `Or` constructors.
+
+### 3. Elimination theorem
+
+```lean
+theorem SourcePressureLocalIslandWitnessAdjacentDiagnosis.elim
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {A B : SourcePressureLocalIslandWitness n k r}
+    {P : Prop}
+    (hdiag : SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B)
+    (hrecovered :
+      (∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
+        (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+          A B hrev).items).map
+          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) → P)
+    (hoverlap : SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L → P) :
+    P
+```
+
+This is useful when callers should not unfold the carrier directly.
+
+### 4. Ordinary-failure weakening
+
+```lean
+theorem SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered_or_listFailure
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {A B : SourcePressureLocalIslandWitness n k r}
+    (hdiag : SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B) :
+    (∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
+      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        A B hrev).items).map
+        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2)
+    ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L
+```
+
+This weakens only the overlap branch.  The recovered branch remains pair-local.
+
+### 5. Length-three carrier theorem
+
+```lean
+theorem sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_carrier
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
+    SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3] W1 W2 ∨
+      SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3] W2 W3
+```
+
+This repackages checkpoint 169's nested theorem into a compact carrier shape.
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
+- length-four diagnosis,
+- Collatz convergence.
+
+Recovered budgets remain pair-local.  Overlap remains unmerged and unhandled.
+
+The carrier is a return type for bounded diagnosis theorems, not a recursive
+classifier.
+
+## Next Inference
+
+The carrier is stable enough to try a bounded length-four theorem next:
+
+```text
+failure [W1,W2,W3,W4]
+  -> diagnosis [W1,W2]
+  or diagnosis [W2,W3]
+  or diagnosis [W3,W4]
+```
+
+If the length-four theorem stays readable with the carrier, it will be good
+evidence for a later fuel-indexed generalization.  If it still becomes verbose,
+the next step should be a more structured finite diagnosis result before any
+general recursion.
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
