# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAccounting

gch: 44cc2688b766c1c48096261e741c3f1e03ae8a29

## Report

cp171 完了です。

[PressureAccounting.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean) に length-four carrier 診断を追加しました。

- `SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail`
- `sourcePressureLocalIslandWitnessList_failure_fourDiagnosis_carrier`

`[W1,W2,W3,W4]` の failure を、隣接 pair `W1,W2` / `W2,W3` / `W3,W4` のいずれかの `SourcePressureLocalIslandWitnessAdjacentDiagnosis` へ落とす形です。recovered budget は各 pair 局所のままです。

レポート: [report-petal-171.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-171.md)

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureAccounting` PASS
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier` PASS
- `lake build DkMath.Collatz.PetalBridge` PASS
- 対象 2 ファイルの `sorry` 検索: ヒットなし
- `git diff --check` PASS

既存の `ZsigmondyCyclotomicResearch` の `sorry` 警告は今回も無関係です。

## Review

## 結論

うむ、Checkpoint 171 は **採用** じゃ 👍️
今回で、carrier を使った **length-four 固定診断** が通った。

追加された中心は、

```lean id="jwr3lm"
SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail
sourcePressureLocalIslandWitnessList_failure_fourDiagnosis_carrier
```

じゃな。

これにより、

```text id="i6h7gk"
failure [W1, W2, W3, W4]
  -> diagnosis at W1,W2
  or diagnosis at W2,W3
  or diagnosis at W3,W4
```

という形が Lean で閉じた。recovered budget はそれぞれの adjacent pair 局所に留まり、overlap は enclosing list `[W1,W2,W3,W4]` の adjacent obstruction として扱われている。境界管理もよい。

## 状況分析

## 1. carrier 導入は成功

Checkpoint 170 で入れた

```lean id="fi1oe0"
SourcePressureLocalIslandWitnessAdjacentDiagnosis
```

が、今回の length-four でちゃんと効いている。

もし carrier がなければ、返り値はかなり大きな nested `Or` になっていたはずじゃ。
しかし今回の theorem は、

```lean id="hfvbuw"
SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3, W4] W1 W2 ∨
  SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3, W4] W2 W3 ∨
    SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3, W4] W3 W4
```

で収まっている。

これは読みやすい。
length-four でこの形が維持できたのは大きい。

## 2. `lift_tail` が正しく効いている

今回の要は、

```lean id="djigwc"
SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail
```

じゃ。

tail 側 `[W2,W3,W4]` の diagnosis を、full list `[W1,W2,W3,W4]` の diagnosis として持ち上げる。

このとき、

```text id="5fnca7"
recovered:
  証拠はそのまま。pair-local budget は変えない。

overlap:
  enclosing list を of_tail で大きくする。
```

という処理になっている。

この設計は安全じゃ。
recovered budget を full-list budget に昇格していない。

## 3. length-five 直行は避けたい

report の Next Inference にある通り、次に length-five を手書きで作るより、list-level bounded carrier を考える方がよい。

ここまでで pattern は十分見えた。

```text id="nyrz1r"
長さ 3:
  adjacent pair 2 本のどれか

長さ 4:
  adjacent pair 3 本のどれか
```

つまり、次の自然形は、

```text id="4mznkn"
list L の中に、隣接 pair A,B があり、
その pair に adjacent diagnosis がある
```

じゃ。

## レビュー

## 採用理由

第一に、length-four theorem が carrier で十分読める。

これで、carrier の導入目的は達成された。

第二に、optional ordinary-failure wrapper を入れなかった判断がよい。

今回の目的は「bounded diagnosis result を compact に保つ」ことなので、wrapper で返り値を再肥大化させる必要はない。必要な caller は既存の

```lean id="ar9srw"
SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered_or_listFailure
```

を使えばよい。

第三に、境界が守られている。

今回も、

```text id="9jeuz7"
sorting なし
coverage なし
maximality なし
union accounting なし
recursive classifier なし
Collatz convergence なし
```

が維持されている。

## 注意点

## 1. `AdjacentPairInList` の設計が次の難所

次に進むなら、list 内の隣接 pair を表す述語が必要になる。

ここを雑に作ると後で苦しくなる。

特に注意する点は、

```text id="l4ri37"
任意 pair ではなく adjacent pair である
順序 A,B を保持する
enclosing list L と pair A,B の関係を明示する
```

じゃ。

## 2. equality だけで足りるか

素直には、

```lean id="mdp8t9"
A = W1 ∧ B = W2
```

で head pair を表せる。

`SourcePressureLocalIslandWitness` は subtype なので equality は使えるはずじゃ。
ただし、後で address equality や start/len equality で扱いたくなる可能性もある。

今の段階では、まず witness 自体の equality でよいと思う。

## 3. まだ fuel-indexed generalization には行かない

`AdjacentPairInList` と `ListHasAdjacentDiagnosis` が安定するまでは、fuel 付き分類器は早い。

まずは、

```text id="lzz09w"
length-three carrier theorem
length-four carrier theorem
```

を list-level carrier へ再包装するのが安全じゃ。

## 次の設計案

次 checkpoint では、まずこの二つを入れるのがよい。

```lean id="4urjaa"
SourcePressureLocalIslandWitnessAdjacentPairInList
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
```

イメージはこうじゃ。

```lean id="y04vbg"
def SourcePressureLocalIslandWitnessAdjacentPairInList
    {n : OddNat} {k r : ℕ} :
    List (SourcePressureLocalIslandWitness n k r) →
      SourcePressureLocalIslandWitness n k r →
      SourcePressureLocalIslandWitness n k r →
      Prop
  | [], _, _ => False
  | [_], _, _ => False
  | W1 :: W2 :: rest, A, B =>
      (A = W1 ∧ B = W2) ∨
        SourcePressureLocalIslandWitnessAdjacentPairInList
          (W2 :: rest) A B
```

そして、

```lean id="3g2idr"
def SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
  ∃ A B,
    SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
      SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B
```

これができれば、length-three / length-four はこう再包装できる。

```lean id="r7jc6v"
sourcePressureLocalIslandWitnessList_failure_three_hasAdjacentDiagnosis
sourcePressureLocalIslandWitnessList_failure_four_hasAdjacentDiagnosis
```

意味は、

```text id="be24fh"
failure [W1,W2,W3]
  -> ListHasAdjacentDiagnosis [W1,W2,W3]

failure [W1,W2,W3,W4]
  -> ListHasAdjacentDiagnosis [W1,W2,W3,W4]
```

じゃ。

これで返り値は一気に安定する。

## 次の Codex 指示

```text id="o6ied9"
Checkpoint 172: Main root only — list-level adjacent diagnosis carrier.

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
Checkpoint 171 added length-four carrier diagnosis:

- SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail
- sourcePressureLocalIslandWitnessList_failure_fourDiagnosis_carrier

The adjacent diagnosis carrier is already available:

- SourcePressureLocalIslandWitnessAdjacentDiagnosis
- SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered
- SourcePressureLocalIslandWitnessAdjacentDiagnosis.overlap
- SourcePressureLocalIslandWitnessAdjacentDiagnosis.elim
- SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered_or_listFailure

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
Introduce a small list-level carrier saying that an explicit witness list has
some adjacent pair with adjacent diagnosis.  This is a wrapper around bounded
diagnosis results, not a recursive classifier.

Part A: adjacent pair in list predicate.

Define:

  def SourcePressureLocalIslandWitnessAdjacentPairInList
      {n : OddNat} {k r : Nat} :
      List (SourcePressureLocalIslandWitness n k r) →
        SourcePressureLocalIslandWitness n k r →
        SourcePressureLocalIslandWitness n k r →
        Prop
    | [], _, _ => False
    | [_], _, _ => False
    | W1 :: W2 :: rest, A, B =>
        (A = W1 ∧ B = W2) ∨
          SourcePressureLocalIslandWitnessAdjacentPairInList
            (W2 :: rest) A B

Meaning:
- only neighboring pairs are recognized;
- order matters;
- this is not arbitrary pair membership.

Part B: constructors for adjacent pair predicate.

Prove:

  theorem SourcePressureLocalIslandWitnessAdjacentPairInList.head
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      {rest : List (SourcePressureLocalIslandWitness n k r)} :
      SourcePressureLocalIslandWitnessAdjacentPairInList
        (W1 :: W2 :: rest) W1 W2

  theorem SourcePressureLocalIslandWitnessAdjacentPairInList.tail
      {n : OddNat} {k r : Nat}
      {W1 W2 A B : SourcePressureLocalIslandWitness n k r}
      {rest : List (SourcePressureLocalIslandWitness n k r)}
      (h :
        SourcePressureLocalIslandWitnessAdjacentPairInList
          (W2 :: rest) A B) :
      SourcePressureLocalIslandWitnessAdjacentPairInList
        (W1 :: W2 :: rest) A B

Expected proof:
- head: Or.inl with rfl/rfl
- tail: Or.inr h

Part C: list-level adjacent diagnosis carrier.

Define:

  def SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
      {n : OddNat} {k r : Nat}
      (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
    ∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B

Part D: constructors for list-level carrier.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_adjacent
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {A B : SourcePressureLocalIslandWitness n k r}
      (hin :
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B)
      (hdiag :
        SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B) :
      SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L

Part E: length-three wrapper.

Prove:

  theorem sourcePressureLocalIslandWitnessList_failure_three_hasAdjacentDiagnosis
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
      SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis [W1, W2, W3]

Suggested proof:
- use sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_carrier
- branch W1,W2:
    use of_adjacent with AdjacentPairInList.head
- branch W2,W3:
    use of_adjacent with AdjacentPairInList.tail AdjacentPairInList.head

Part F: length-four wrapper.

Prove:

  theorem sourcePressureLocalIslandWitnessList_failure_four_hasAdjacentDiagnosis
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
      SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis [W1, W2, W3, W4]

Suggested proof:
- use sourcePressureLocalIslandWitnessList_failure_fourDiagnosis_carrier
- branch W1,W2:
    use head
- branch W2,W3:
    use tail head
- branch W3,W4:
    use tail (tail head)

Part G: optional no-diagnosis for short lists.

Only if easy, prove:
- no adjacent pair in []
- no adjacent pair in singleton
- no adjacent diagnosis in []
- no adjacent diagnosis in singleton

Do not force this.

Part H: no general recursive diagnosis yet.

Do not prove:
- arbitrary length failure -> has adjacent diagnosis,
- fuel-indexed classifier,
- sorting,
- coverage,
- maximality,
- uniqueness,
- union accounting,
- Collatz convergence.

Part I: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-172.md

Include:
- adjacent pair predicate,
- head/tail constructors,
- list-level adjacent diagnosis carrier,
- length-three wrapper,
- length-four wrapper,
- explicit note that this is a wrapper over bounded results,
- explicit note that it is not a general recursive classifier,
- explicit note that recovered budgets remain pair-local,
- explicit note that overlap remains unmerged/unhandled,
- explicit note that no maximality, uniqueness, coverage, prefix behavior,
  union accounting, sorting, or Collatz convergence was introduced.

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

Checkpoint 172 が通ったら、次はまだ fuel-indexed classifier へ行かず、まずは `AdjacentPairInList` の基礎 API を厚くするのがよい。

欲しくなる補題は、

```lean id="we1vai"
SourcePressureLocalIslandWitnessAdjacentPairInList.head_or_tail
SourcePressureLocalIslandWitnessAdjacentPairInList.cons_iff_head_or_tail
```

じゃ。

つまり、

```text id="u4lj70"
adjacent pair in W1 :: W2 :: rest
  -> pair is W1,W2
  or adjacent pair in W2 :: rest
```

これがあると、後で一般化するときの分解がかなり楽になる。

## 総評

Checkpoint 171 は良い。
length-four まで carrier で綺麗に通った。

これで、

```text id="1iexzm"
failure [W1,W2,W3,W4]
```

を、三本の adjacent pair のどれかへ落とす形が固定された。

次は list-level carrier。
`there exists adjacent pair with diagnosis` という形を作れば、bounded result と将来の一般化の橋ができる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
index 8a046838..cb412cd1 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -3263,6 +3263,66 @@ theorem sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_carrier
     · exact Or.inr
         (SourcePressureLocalIslandWitnessAdjacentDiagnosis.overlap hobs)

+/--
+Lift an adjacent diagnosis on a tail list through a newly supplied head.
+
+Recovered evidence is unchanged and remains attached to the same adjacent pair
+`A, B`.  Only overlap evidence is transported to the larger enclosing list.
+-/
+theorem SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    {A B : SourcePressureLocalIslandWitness n k r}
+    (hdiag :
+      SourcePressureLocalIslandWitnessAdjacentDiagnosis (W2 :: rest) A B) :
+    SourcePressureLocalIslandWitnessAdjacentDiagnosis (W1 :: W2 :: rest) A B := by
+  rcases hdiag with hrecovered | hobs
+  · exact Or.inl hrecovered
+  · exact Or.inr
+      (SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_tail
+        hobs)
+
+/--
+Bounded diagnosis for a four-witness sorted-before failure.
+
+The result is one adjacent diagnosis for one of the three adjacent pairs:
+`W1,W2`, `W2,W3`, or `W3,W4`.  Recovered budgets remain attached to the pair
+that produced them, and overlap evidence stays an obstruction on the enclosing
+four-witness list.
+-/
+theorem sourcePressureLocalIslandWitnessList_failure_fourDiagnosis_carrier
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r}
+    (h1pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
+    (h2pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
+    (h3pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
+    (h4pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W4).len)
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        [W1, W2, W3, W4]) :
+    SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3, W4] W1 W2 ∨
+      SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3, W4] W2 W3 ∨
+        SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3, W4] W3 W4 := by
+  rcases sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis
+      h1pos h2pos h with hhead | htail
+  · rcases hhead with hrecovered | hobs
+    · exact Or.inl (Or.inl hrecovered)
+    · exact Or.inl
+        (SourcePressureLocalIslandWitnessAdjacentDiagnosis.overlap hobs)
+  · rcases sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_carrier
+        h2pos h3pos h4pos htail with htailHead | htailTail
+    · exact Or.inr (Or.inl
+        (SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail
+          htailHead))
+    · exact Or.inr (Or.inr
+        (SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail
+          htailTail))
+
 /--
 Head-pair split with the obstruction branch weakened to ordinary list
 sorted-before failure.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-171.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-171.md
new file mode 100644
index 00000000..b90f61c7
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-171.md
@@ -0,0 +1,133 @@
+# Report Petal 171
+
+## Checkpoint
+
+Checkpoint 171 proves a bounded length-four failure diagnosis theorem using the
+adjacent diagnosis carrier introduced in checkpoint 170.
+
+The result remains fixed-length.  It is not a recursive classifier.
+
+## Implemented Lean Surface
+
+File:
+
+- `DkMath.Collatz.PetalBridge.PressureAccounting`
+
+### 1. Carrier tail lift
+
+```lean
+theorem SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    {A B : SourcePressureLocalIslandWitness n k r}
+    (hdiag :
+      SourcePressureLocalIslandWitnessAdjacentDiagnosis (W2 :: rest) A B) :
+    SourcePressureLocalIslandWitnessAdjacentDiagnosis (W1 :: W2 :: rest) A B
+```
+
+This lifts a tail diagnosis under a newly supplied head.
+
+- recovered evidence is unchanged and remains pair-local for `A, B`;
+- overlap evidence is transported to the larger enclosing list by
+  `SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_tail`.
+
+### 2. Length-four carrier theorem
+
+```lean
+theorem sourcePressureLocalIslandWitnessList_failure_fourDiagnosis_carrier
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r}
+    (h1pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
+    (h2pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
+    (h3pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
+    (h4pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W4).len)
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        [W1, W2, W3, W4]) :
+    SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3, W4] W1 W2 ∨
+      SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3, W4] W2 W3 ∨
+        SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3, W4] W3 W4
+```
+
+The proof uses:
+
+- `sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis` for the head
+  split;
+- `sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_carrier` for the
+  tail `[W2, W3, W4]`;
+- `SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail` to move tail
+  diagnoses into the enclosing four-witness list.
+
+## Optional Wrapper Decision
+
+The optional ordinary-failure wrapper was not added.  It would expand the
+return type again and work against this checkpoint's purpose: keeping bounded
+diagnosis results compact through the carrier.
+
+Callers can still use:
+
+```lean
+SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered_or_listFailure
+```
+
+on whichever branch they consume.
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
+- a general recursive classifier,
+- Collatz convergence.
+
+Recovered budgets remain pair-local:
+
+- `W1, W2`,
+- `W2, W3`,
+- `W3, W4`.
+
+Overlap remains unmerged and unhandled, only propagated as adjacent obstruction
+evidence on the enclosing list.
+
+## Next Inference
+
+The length-four theorem confirms that the adjacent diagnosis carrier keeps the
+bounded result shape readable.
+
+The next natural step is not length five by brute force.  A better next design
+target is a small list-level bounded carrier such as:
+
+```text
+there exists an adjacent pair inside L with an adjacent diagnosis on L
+```
+
+The hard part is the `AdjacentPairInList` predicate.  It should be designed
+carefully before introducing any fuel-indexed general classifier.
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
