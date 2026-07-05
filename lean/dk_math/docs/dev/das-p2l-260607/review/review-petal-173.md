# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAccounting

gch: faa25ac6038c97acc968545bbc4efe0fa6aa3e37

## Report

cp172 実装完了です。

[PressureAccounting.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean:3335) に list-level adjacent diagnosis carrier を追加しました。隣接ペア predicate、head/tail constructor、空/単元リストの否定補題、list-level carrier、3要素/4要素 bounded wrapper まで入っています。一般再帰 classifier や coverage/union accounting には広げていません。

[report-petal-172.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-172.md:1) も新規作成し、実装内容・境界・検証結果を記録しました。

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureAccounting` PASS
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier` PASS
- `lake build DkMath.Collatz.PetalBridge` PASS
- `rg -n "\bsorry\b"` 対象2ファイルはヒットなし
- `git diff --check` PASS

既存の無関係 warning として `DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6 declaration uses sorry` は引き続き表示されています。

## Review

## 結論

うむ、Checkpoint 172 は **採用** じゃ 👍️
今回で、bounded diagnosis の結果をさらに外側へ包む **list-level adjacent diagnosis carrier** が入った。

追加された中心は、

```lean
SourcePressureLocalIslandWitnessAdjacentPairInList
SourcePressureLocalIslandWitnessAdjacentPairInList.head
SourcePressureLocalIslandWitnessAdjacentPairInList.tail
SourcePressureLocalIslandWitnessAdjacentPairInList.nil_false
SourcePressureLocalIslandWitnessAdjacentPairInList.singleton_false
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_adjacent
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.nil_false
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.singleton_false
sourcePressureLocalIslandWitnessList_failure_three_hasAdjacentDiagnosis
sourcePressureLocalIslandWitnessList_failure_four_hasAdjacentDiagnosis
```

じゃな。`[W1,W2,W3]` と `[W1,W2,W3,W4]` の bounded diagnosis を、「この明示 list のどこかの隣接 pair に診断がある」という public surface へ包めた。一般再帰 classifier、coverage、union accounting には進んでいない点も正しい。

## 状況分析

## 1. pair-local diagnosis から list-level existence へ上がった

前 checkpoint までは、

```text
SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B
```

で、「list `L` の文脈において、隣接 pair `A,B` が診断を持つ」と表していた。

今回、それをさらに包んで、

```lean
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L
```

が入った。

意味は、

```text
list L の中に隣接 pair A,B があり、
その A,B に adjacent diagnosis がある
```

じゃ。

これで、bounded theorem の利用者は「head pair か tail pair か」を直接分解しなくてもよくなった。

## 2. `AdjacentPairInList` の導入が大きい

今回の肝はこれじゃ。

```lean
SourcePressureLocalIslandWitnessAdjacentPairInList L A B
```

これは arbitrary pair membership ではなく、**順序付きの隣接 pair** だけを認識する。

定義も安全じゃ。

```text
[]:
  false

[_]:
  false

W1 :: W2 :: rest:
  A = W1 and B = W2
  or adjacent pair in W2 :: rest
```

つまり、順序を保ったまま list の隣接構造を追える。
これは後の一般化でかなり重要になる。

## 3. length-three / length-four wrapper が public surface になった

今回の二つ、

```lean
sourcePressureLocalIslandWitnessList_failure_three_hasAdjacentDiagnosis
sourcePressureLocalIslandWitnessList_failure_four_hasAdjacentDiagnosis
```

は、かなり良い表面 API じゃ。

以前の theorem は、

```text
どの pair が診断されたか
どの branch が recovered / overlap か
```

を返していた。

今回の wrapper は、そこをまとめて、

```text
この list には隣接診断が存在する
```

として返せる。

これは「内部では bounded diagnosis、外部には存在 carrier」という分離になっていて、設計が綺麗じゃ。

## レビュー

## 採用理由

第一に、`AdjacentPairInList` の境界が明確。

任意 pair ではなく、隣接 pair のみ。
sorting なし。
unique / maximal なし。
この制限が良い。

第二に、short-list negative facts が入っている。

```lean
SourcePressureLocalIslandWitnessAdjacentPairInList.nil_false
SourcePressureLocalIslandWitnessAdjacentPairInList.singleton_false
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.nil_false
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.singleton_false
```

空 list / singleton list に隣接 pair はない。
この末端条件は、後の再帰・fuel 化で必ず効いてくる。

第三に、bounded wrapper が入っている。

length-three / length-four の結果が、list-level carrier に接続された。
これで「固定長診断」から「list-level 存在診断」へ橋がかかった。

## 注意点

## 1. まだ任意長 theorem ではない

今回の wrapper は length 3 と length 4 だけじゃ。

まだ次は言っていない。

```text
任意長 list の failure なら adjacent diagnosis がある
fuel-indexed classifier がある
全 failure を列挙できる
```

ここは未到達。
今は bounded results の surface を整えている段階じゃ。

## 2. `ListHasAdjacentDiagnosis` は存在主張であって列挙ではない

```lean
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L
```

は、

```text
少なくとも一つ、隣接診断がある
```

という存在主張じゃ。

全ての隣接 pair を調べたわけではない。
coverage でも maximality でも uniqueness でもない。

## 3. overlap branch はまだ未処理

これまで通り、overlap は adjacent obstruction として保持されているだけ。

merge なし。
split なし。
union accounting なし。

この境界は引き続き守るべきじゃ。

## 次の一手

次は report の通り、**projection / elimination helpers** が安全じゃ。

いきなり一般 classifier へ行かず、まず今回の list-level carrier を扱いやすくする。

具体的には、

```lean
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.elim
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_pair
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail
```

あたりが良い。

特に `of_tail` は今後かなり使う。

```text
tail list に adjacent diagnosis がある
  -> head を追加した list にも adjacent diagnosis がある
```

これは、`AdjacentPairInList.tail` と `AdjacentDiagnosis.lift_tail` の合成で通るはずじゃ。

## 賢狼が試して欲しい実験補題

## 実験補題 A: list-level carrier elimination

```lean
theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.elim
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {P : Prop}
    (h : SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L)
    (hp :
      ∀ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B →
        SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B →
        P) :
    P := by
  rcases h with ⟨A, B, hin, hdiag⟩
  exact hp A B hin hdiag
```

これは、carrier を unfold せずに使うための基本 eliminator じゃ。

## 実験補題 B: adjacent diagnosis in tail lifts to full list

```lean
theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
        (W2 :: rest)) :
    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
      (W1 :: W2 :: rest) := by
  rcases h with ⟨A, B, hin, hdiag⟩
  exact SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_adjacent
    (SourcePressureLocalIslandWitnessAdjacentPairInList.tail hin)
    (SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail hdiag)
```

これは次の再帰化の基礎になる。

## 実験補題 C: head adjacent diagnosis gives list diagnosis

```lean
theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_head
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (hdiag :
      SourcePressureLocalIslandWitnessAdjacentDiagnosis
        (W1 :: W2 :: rest) W1 W2) :
    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
      (W1 :: W2 :: rest) :=
  SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_adjacent
    SourcePressureLocalIslandWitnessAdjacentPairInList.head
    hdiag
```

これは `of_adjacent head` の読みやすい別名じゃ。

## 実験補題 D: adjacent pair head_or_tail

```lean
theorem SourcePressureLocalIslandWitnessAdjacentPairInList.head_or_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 A B : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessAdjacentPairInList
        (W1 :: W2 :: rest) A B) :
    (A = W1 ∧ B = W2) ∨
      SourcePressureLocalIslandWitnessAdjacentPairInList
        (W2 :: rest) A B
```

定義そのものの逆向きじゃ。
後の一般化で必ず使う。

## 実験補題 E: adjacent pair iff

```lean
theorem SourcePressureLocalIslandWitnessAdjacentPairInList.cons_iff_head_or_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 A B : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)} :
    SourcePressureLocalIslandWitnessAdjacentPairInList
      (W1 :: W2 :: rest) A B ↔
    (A = W1 ∧ B = W2) ∨
      SourcePressureLocalIslandWitnessAdjacentPairInList
        (W2 :: rest) A B
```

これは `head_or_tail` と constructor をまとめた iff じゃ。
`rw` しやすくなる。

## 次の Codex 指示

```text
Checkpoint 173: Main root only — projection and propagation helpers for list-level adjacent diagnosis.

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
Checkpoint 172 added the list-level adjacent diagnosis carrier:

- SourcePressureLocalIslandWitnessAdjacentPairInList
- SourcePressureLocalIslandWitnessAdjacentPairInList.head
- SourcePressureLocalIslandWitnessAdjacentPairInList.tail
- SourcePressureLocalIslandWitnessAdjacentPairInList.nil_false
- SourcePressureLocalIslandWitnessAdjacentPairInList.singleton_false
- SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
- SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_adjacent
- SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.nil_false
- SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.singleton_false
- sourcePressureLocalIslandWitnessList_failure_three_hasAdjacentDiagnosis
- sourcePressureLocalIslandWitnessList_failure_four_hasAdjacentDiagnosis

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
- This checkpoint should only add projection, elimination, and propagation helpers.

Part A: adjacent-pair decomposition.

Prove:

  theorem SourcePressureLocalIslandWitnessAdjacentPairInList.head_or_tail
      {n : OddNat} {k r : Nat}
      {W1 W2 A B : SourcePressureLocalIslandWitness n k r}
      {rest : List (SourcePressureLocalIslandWitness n k r)}
      (h :
        SourcePressureLocalIslandWitnessAdjacentPairInList
          (W1 :: W2 :: rest) A B) :
      (A = W1 ∧ B = W2) ∨
        SourcePressureLocalIslandWitnessAdjacentPairInList
          (W2 :: rest) A B

Expected proof:
- simpa [SourcePressureLocalIslandWitnessAdjacentPairInList] using h

Part B: adjacent-pair iff.

Prove:

  theorem SourcePressureLocalIslandWitnessAdjacentPairInList.cons_iff_head_or_tail
      {n : OddNat} {k r : Nat}
      {W1 W2 A B : SourcePressureLocalIslandWitness n k r}
      {rest : List (SourcePressureLocalIslandWitness n k r)} :
      SourcePressureLocalIslandWitnessAdjacentPairInList
        (W1 :: W2 :: rest) A B ↔
      (A = W1 ∧ B = W2) ∨
        SourcePressureLocalIslandWitnessAdjacentPairInList
          (W2 :: rest) A B

Suggested proof:
- constructor
- forward: head_or_tail
- backward:
  rcases h with hhead | htail
  · exact Or.inl hhead
  · exact SourcePressureLocalIslandWitnessAdjacentPairInList.tail htail
  or use `simpa [SourcePressureLocalIslandWitnessAdjacentPairInList]`.

Part C: list-level carrier eliminator.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.elim
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {P : Prop}
      (h : SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L)
      (hp :
        ∀ A B,
          SourcePressureLocalIslandWitnessAdjacentPairInList L A B →
          SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B →
          P) :
      P

Suggested proof:
- rcases h with ⟨A, B, hin, hdiag⟩
- exact hp A B hin hdiag

Part D: list-level head constructor.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_head
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      {rest : List (SourcePressureLocalIslandWitness n k r)}
      (hdiag :
        SourcePressureLocalIslandWitnessAdjacentDiagnosis
          (W1 :: W2 :: rest) W1 W2) :
      SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
        (W1 :: W2 :: rest)

Suggested proof:
- of_adjacent AdjacentPairInList.head hdiag

Part E: list-level tail propagation.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      {rest : List (SourcePressureLocalIslandWitness n k r)}
      (h :
        SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
          (W2 :: rest)) :
      SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
        (W1 :: W2 :: rest)

Suggested proof:
- rcases h with ⟨A, B, hin, hdiag⟩
- use SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_adjacent
    (SourcePressureLocalIslandWitnessAdjacentPairInList.tail hin)
    (SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail hdiag)

Part F: optional recovered_or_listFailure for list-level carrier.

Only if easy, prove:

  theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_listFailure
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h : SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L) :
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          ((∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
            (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
              A B hrev).items).map
              (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2)
          ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)

This follows by unpacking h and applying
SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered_or_listFailure.

Do not force this if it becomes verbose.

Part G: no general classifier.

Do not prove:
- arbitrary-length failure -> has adjacent diagnosis,
- fuel-indexed classifier,
- sorting,
- coverage,
- maximality,
- uniqueness,
- union accounting,
- Collatz convergence.

Part H: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-173.md

Include:
- adjacent-pair head_or_tail and iff,
- list-level carrier eliminator,
- of_head/of_tail constructors,
- optional recovered_or_listFailure wrapper if added,
- explicit note that this is helper API only,
- explicit note that no general recursive classifier was introduced,
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

Checkpoint 173 が通ったら、次はいよいよ小さな一般化に触れる段階じゃ。

ただし、まだ

```text
arbitrary failure -> adjacent diagnosis
```

には行かない方がよい。

先に、

```lean
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail_iterated
```

のように、tail propagation を 2 回・3 回だけ合成する bounded helper を作るとよい。

あるいは、`AdjacentPairInList` の `tail` を繰り返すための小さな補題を作る。

```lean
SourcePressureLocalIslandWitnessAdjacentPairInList.tail_tail
```

ただし、これは実装価値があるかは微妙じゃ。
今回の `of_tail` があれば、まずは次の bounded length 5 wrapper も作れる。

## 総評

Checkpoint 172 は、bounded diagnosis の public surface をかなり綺麗にした。

ここまでで、

```text
failure [W1,W2,W3]
  -> list has adjacent diagnosis

failure [W1,W2,W3,W4]
  -> list has adjacent diagnosis
```

が得られた。

次は helper API を整え、list-level carrier を扱いやすくする段階じゃ。
焦って一般再帰に入らず、まず eliminator と of_tail を固めるのが賢い。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
index cb412cd1..4725375b 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -3323,6 +3323,173 @@ theorem sourcePressureLocalIslandWitnessList_failure_fourDiagnosis_carrier
         (SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail
           htailTail))
 
+/--
+An ordered adjacent pair occurring in an explicitly supplied witness list.
+
+This predicate recognizes neighboring entries only.  It does not express
+arbitrary pair membership, does not sort the list, and does not claim that the
+recognized pair is unique or maximal.  It is a small address layer for bounded
+diagnosis theorems, so later consumers can say "some adjacent pair in this
+list carries the local diagnosis" without introducing a recursive classifier.
+-/
+def SourcePressureLocalIslandWitnessAdjacentPairInList
+    {n : OddNat} {k r : ℕ} :
+    List (SourcePressureLocalIslandWitness n k r) →
+      SourcePressureLocalIslandWitness n k r →
+      SourcePressureLocalIslandWitness n k r →
+      Prop
+  | [], _, _ => False
+  | [_], _, _ => False
+  | W1 :: W2 :: rest, A, B =>
+      (A = W1 ∧ B = W2) ∨
+        SourcePressureLocalIslandWitnessAdjacentPairInList
+          (W2 :: rest) A B
+
+/-- The head pair of a list with at least two witnesses is adjacent in that list. -/
+theorem SourcePressureLocalIslandWitnessAdjacentPairInList.head
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)} :
+    SourcePressureLocalIslandWitnessAdjacentPairInList
+      (W1 :: W2 :: rest) W1 W2 :=
+  Or.inl ⟨rfl, rfl⟩
+
+/--
+An adjacent pair in the tail remains an adjacent pair after adding a new head.
+-/
+theorem SourcePressureLocalIslandWitnessAdjacentPairInList.tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 A B : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessAdjacentPairInList
+        (W2 :: rest) A B) :
+    SourcePressureLocalIslandWitnessAdjacentPairInList
+      (W1 :: W2 :: rest) A B :=
+  Or.inr h
+
+/-- There is no adjacent pair in the empty witness list. -/
+theorem SourcePressureLocalIslandWitnessAdjacentPairInList.nil_false
+    {n : OddNat} {k r : ℕ}
+    {A B : SourcePressureLocalIslandWitness n k r} :
+    ¬ SourcePressureLocalIslandWitnessAdjacentPairInList
+      ([] : List (SourcePressureLocalIslandWitness n k r)) A B := by
+  intro h
+  exact h
+
+/-- There is no adjacent pair in a singleton witness list. -/
+theorem SourcePressureLocalIslandWitnessAdjacentPairInList.singleton_false
+    {n : OddNat} {k r : ℕ}
+    {W A B : SourcePressureLocalIslandWitness n k r} :
+    ¬ SourcePressureLocalIslandWitnessAdjacentPairInList [W] A B := by
+  intro h
+  exact h
+
+/--
+A list-level carrier for "some adjacent pair in this explicit list has an
+adjacent diagnosis".
+
+The diagnosis is still local to the pair `A, B`.  In particular, recovered
+budget evidence remains attached to the adjacent pair that produced it, while
+overlap evidence remains an obstruction on the enclosing list.
+-/
+def SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
+  ∃ A B,
+    SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+      SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B
+
+/-- Package an adjacent-pair address and its diagnosis into the list-level carrier. -/
+theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_adjacent
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {A B : SourcePressureLocalIslandWitness n k r}
+    (hin :
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B)
+    (hdiag :
+      SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B) :
+    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L :=
+  ⟨A, B, hin, hdiag⟩
+
+/-- The empty witness list cannot carry a list-level adjacent diagnosis. -/
+theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.nil_false
+    {n : OddNat} {k r : ℕ} :
+    ¬ SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
+      ([] : List (SourcePressureLocalIslandWitness n k r)) := by
+  rintro ⟨A, B, hin, _⟩
+  exact SourcePressureLocalIslandWitnessAdjacentPairInList.nil_false hin
+
+/-- A singleton witness list cannot carry a list-level adjacent diagnosis. -/
+theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.singleton_false
+    {n : OddNat} {k r : ℕ}
+    {W : SourcePressureLocalIslandWitness n k r} :
+    ¬ SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis [W] := by
+  rintro ⟨A, B, hin, _⟩
+  exact SourcePressureLocalIslandWitnessAdjacentPairInList.singleton_false hin
+
+/--
+Length-three sorted-before failure yields a list-level adjacent diagnosis.
+
+This is only a wrapper over the bounded three-witness carrier: it records that
+the diagnosed pair is one of the adjacent pairs already present in the supplied
+list, without adding a general list classifier.
+-/
+theorem sourcePressureLocalIslandWitnessList_failure_three_hasAdjacentDiagnosis
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
+    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis [W1, W2, W3] := by
+  rcases sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_carrier
+      h1pos h2pos h3pos h with h12 | h23
+  · exact SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_adjacent
+      SourcePressureLocalIslandWitnessAdjacentPairInList.head h12
+  · exact SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_adjacent
+      (SourcePressureLocalIslandWitnessAdjacentPairInList.tail
+        SourcePressureLocalIslandWitnessAdjacentPairInList.head) h23
+
+/--
+Length-four sorted-before failure yields a list-level adjacent diagnosis.
+
+The result exposes only that one adjacent pair in the explicit four-witness
+list has a local diagnosis.  It intentionally avoids coverage, maximality,
+union accounting, or a recursive failure classifier.
+-/
+theorem sourcePressureLocalIslandWitnessList_failure_four_hasAdjacentDiagnosis
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
+    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis [W1, W2, W3, W4] := by
+  rcases sourcePressureLocalIslandWitnessList_failure_fourDiagnosis_carrier
+      h1pos h2pos h3pos h4pos h with h12 | htail
+  · exact SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_adjacent
+      SourcePressureLocalIslandWitnessAdjacentPairInList.head h12
+  · rcases htail with h23 | h34
+    · exact SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_adjacent
+        (SourcePressureLocalIslandWitnessAdjacentPairInList.tail
+          SourcePressureLocalIslandWitnessAdjacentPairInList.head) h23
+    · exact SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_adjacent
+        (SourcePressureLocalIslandWitnessAdjacentPairInList.tail
+          (SourcePressureLocalIslandWitnessAdjacentPairInList.tail
+            SourcePressureLocalIslandWitnessAdjacentPairInList.head)) h34
+
 /--
 Head-pair split with the obstruction branch weakened to ordinary list
 sorted-before failure.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-172.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-172.md
new file mode 100644
index 00000000..49568a38
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-172.md
@@ -0,0 +1,144 @@
+# Report Petal 172
+
+## Checkpoint
+
+`cp: 172`
+
+Main root only: list-level adjacent diagnosis carrier.
+
+## Implemented
+
+### Adjacent pair address predicate
+
+Added:
+
+```lean
+def SourcePressureLocalIslandWitnessAdjacentPairInList
+```
+
+This predicate recognizes only ordered neighboring pairs in an explicitly
+supplied witness list.  It is intentionally weaker than arbitrary pair
+membership and does not sort, merge, classify, or claim uniqueness.
+
+### Constructors
+
+Added:
+
+```lean
+theorem SourcePressureLocalIslandWitnessAdjacentPairInList.head
+theorem SourcePressureLocalIslandWitnessAdjacentPairInList.tail
+```
+
+These give the two intended address moves:
+
+- the head pair is adjacent;
+- an adjacent pair in the tail remains adjacent after a new head is added.
+
+### Short-list negative facts
+
+Added:
+
+```lean
+theorem SourcePressureLocalIslandWitnessAdjacentPairInList.nil_false
+theorem SourcePressureLocalIslandWitnessAdjacentPairInList.singleton_false
+```
+
+These fix the boundary condition that empty and singleton witness lists have no
+adjacent pair.
+
+### List-level adjacent diagnosis carrier
+
+Added:
+
+```lean
+def SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
+theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_adjacent
+```
+
+This packages:
+
+```text
+some adjacent pair in this explicit list
++ an adjacent diagnosis attached to that pair
+```
+
+Recovered budget evidence remains attached to the adjacent pair that produced
+it.  Overlap evidence remains an obstruction on the enclosing list.
+
+### Short-list no-diagnosis facts
+
+Added:
+
+```lean
+theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.nil_false
+theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.singleton_false
+```
+
+These follow by projecting the adjacent-pair address and using the short-list
+negative facts.
+
+### Bounded wrappers
+
+Added:
+
+```lean
+theorem sourcePressureLocalIslandWitnessList_failure_three_hasAdjacentDiagnosis
+theorem sourcePressureLocalIslandWitnessList_failure_four_hasAdjacentDiagnosis
+```
+
+These wrap the already available bounded three- and four-witness diagnosis
+carriers into the new list-level carrier.
+
+## Boundary
+
+This checkpoint does not introduce:
+
+- arbitrary-length failure to adjacent diagnosis;
+- a recursive classifier;
+- sorting;
+- coverage;
+- maximality;
+- uniqueness;
+- union accounting;
+- Collatz convergence.
+
+The new layer is only an address carrier over explicit bounded witness lists.
+
+## Verification
+
+Builds completed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureAccounting
+lake build DkMath.Collatz.PetalBridge.PressureFrontier
+lake build DkMath.Collatz.PetalBridge
+```
+
+No-sorry checks completed for:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+```
+
+Whitespace check completed:
+
+```text
+git diff --check
+```
+
+The build still reports the existing unrelated warning:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+## Next Inference
+
+The new carrier creates a cleaner public surface for bounded diagnostics:
+future callers can consume `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis`
+without destructuring whether the evidence came from the head pair or a tail
+pair.  The next natural step, if requested, is still bounded: add small
+projection/elimination helpers for this list-level carrier, not a general
+classifier.
````
`````
