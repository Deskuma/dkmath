# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAccounting

gch: 5b42941547b73ad46fab750127c64141c5d2faba

## Report

cp173 実装完了です。

[PressureAccounting.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean:3364) に projection/propagation helper を追加しました。

追加内容:

- `SourcePressureLocalIslandWitnessAdjacentPairInList.head_or_tail`
- `SourcePressureLocalIslandWitnessAdjacentPairInList.cons_iff_head_or_tail`
- `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.elim`
- `of_head`
- `of_tail`
- おまけの bounded helper: `of_tail_tail`, `of_tail_tail_tail`
- `exists_recovered_or_listFailure`

[report-petal-173.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-173.md:1) も作成済みです。今回も一般再帰 classifier、coverage、union accounting、Collatz convergence には踏み込んでいません。

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureAccounting` PASS
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier` PASS
- `lake build DkMath.Collatz.PetalBridge` PASS
- 対象2ファイルの `sorry` 検索ヒットなし
- `git diff --check` PASS

既存の無関係 warning として `DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6 declaration uses sorry` は引き続き表示されています。

## Review

## 結論

うむ、Checkpoint 173 は **採用** じゃ 👍️
今回で、list-level adjacent diagnosis carrier を扱うための **projection / propagation helper API** が揃った。

追加内容は、

```lean
SourcePressureLocalIslandWitnessAdjacentPairInList.head_or_tail
SourcePressureLocalIslandWitnessAdjacentPairInList.cons_iff_head_or_tail
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.elim
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_head
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail_tail
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail_tail_tail
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_listFailure
```

じゃな。今回も一般再帰 classifier、coverage、union accounting、Collatz convergence には踏み込んでいない。helper API に限定されているのが良い。

## 状況分析

## 1. `AdjacentPairInList` が分解可能になった

今回の

```lean
SourcePressureLocalIslandWitnessAdjacentPairInList.head_or_tail
SourcePressureLocalIslandWitnessAdjacentPairInList.cons_iff_head_or_tail
```

は、隣接 pair address の再帰構造を外部 API にしたものじゃ。

つまり、

```text
adjacent pair in W1 :: W2 :: rest
  -> head pair W1,W2
  or adjacent pair in W2 :: rest
```

が明示的に使えるようになった。

これは後で一般化を考えるときに重要じゃ。
`AdjacentPairInList` がただの存在述語ではなく、head/tail に剥がせる address predicate になった。

## 2. list-level carrier の head/tail propagation が揃った

今回の中心は、

```lean
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_head
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail
```

じゃ。

`of_head` は head pair の diagnosis を list-level carrier に包む。
`of_tail` は tail list の diagnosis を、新しい head の下へ持ち上げる。

この `of_tail` はかなり重要で、

```text
tail に adjacent diagnosis がある
  -> head を足した list にも adjacent diagnosis がある
```

を言っている。

ただし recovered budget は同じ adjacent pair に残る。
overlap branch だけが enclosing list の拡大に合わせて運ばれる。ここが正しい。

## 3. bounded helper は便利だが、増やしすぎ注意

今回のおまけ、

```lean
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail_tail
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail_tail_tail
```

は、bounded wrapper を書くには便利じゃ。

ただし、今後 `of_tail_tail_tail_tail` のように増やし続けると、API が肥大化する。
長さ 5 までは便利補助として許容できるが、その先は `Nat` fuel や fold 的な設計に移る判断点になる。

## レビュー

## 採用理由

第一に、今回の helper 群は既存の bounded diagnosis surface を壊さず、使いやすさだけを上げている。

第二に、`exists_recovered_or_listFailure` が良い。

```lean
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_listFailure
```

これは list-level carrier から、

```text
some addressed adjacent pair has pair-local recovered budget
or
the enclosing list has ordinary sorted-before failure
```

へ弱める projection じゃ。

consumer が overlap obstruction の詳細を要らない場合に使える。
一方、sharp な diagnosis は carrier 内に残っているので、情報落ちの制御もできている。

第三に、report の境界線が安定している。
今回も、任意長 failure から adjacent diagnosis への theorem はまだ作っていない。これは正しい。

## 注意点

## 1. `ListHasAdjacentDiagnosis` は「存在」だけ

```lean
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L
```

は、あくまで「少なくとも一つの adjacent diagnosis がある」という主張じゃ。

これは、

```text
全 adjacent pair を列挙した
全 failure を分類した
最初の failure を特定した
最大 cluster を作った
```

という意味ではない。

## 2. `exists_recovered_or_listFailure` の右 branch は弱い

右 branch は ordinary sorted-before failure なので、overlap obstruction の位置情報は失われる。

したがって、後で overlap branch を解析したい場面では、

```lean
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.elim
```

で中身を取り出す方がよい。

## 3. 次に length-five へ行くなら carrier を使うべき

length-five を直に nested `Or` で書くのは避けたい。
今は list-level carrier があるので、

```text
failure [W1,W2,W3,W4,W5]
  -> ListHasAdjacentDiagnosis [W1,W2,W3,W4,W5]
```

という wrapper theorem にするのがよい。

## 次の一手

次は二択じゃ。

## A案: length-five wrapper

今ある length-four carrier と `of_tail` を使って、長さ 5 の bounded wrapper を作る。

これはかなり自然じゃ。

```text
failure [W1,W2,W3,W4,W5]
  -> head diagnosis on W1,W2
  or tail has adjacent diagnosis
  -> list has adjacent diagnosis
```

ただし、返り値は `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis [W1,W2,W3,W4,W5]` にする。
もう pair ごとの nested result は不要じゃ。

## B案: recovered / overlap 分離 eliminator

list-level carrier から、より structured に、

```text
exists pair with recovered budget
or
overlap obstruction on L
```

へ分ける theorem を作る。

今の `exists_recovered_or_listFailure` は overlap を ordinary failure に弱めている。
それとは別に、sharp 版として、

```text
exists pair-local recovered budget
or
adjacent overlap obstruction on L
```

があると便利じゃ。

わっちのおすすめは **B案を先** じゃ。
理由は、length-five wrapper を作る前に、list-level carrier の projection API をもう一段整えておくと後続が楽になるからじゃ。

## 賢狼が試して欲しい実験補題

## 実験補題 A: sharp recovered-or-overlap projection

```lean
theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_overlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L) :
    (∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
          (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
            A B hrev).items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2)
    ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
```

これは `hdiag` を分解して、recovered なら左、overlap なら右へ送るだけのはずじゃ。

## 実験補題 B: list-level overlap implies list failure

既存の合成だが、名前があると便利。

```lean
theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.overlap_or_recovered_to_failure
```

ただしこれは名前が重いので、A の sharp projection と既存 `hasSortedBeforeFailure` で十分かもしれぬ。

## 実験補題 C: length-five wrapper

A が通った後なら、次にこれ。

```lean
theorem sourcePressureLocalIslandWitnessList_failure_five_hasAdjacentDiagnosis
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 W4 W5 : SourcePressureLocalIslandWitness n k r}
    (h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (h3pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
    (h4pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W4).len)
    (h5pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W5).len)
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        [W1, W2, W3, W4, W5]) :
    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis [W1, W2, W3, W4, W5]
```

証明方針は、

```text
oneStepDiagnosis on [W1,W2,W3,W4,W5]

head branch:
  build AdjacentDiagnosis for W1,W2
  use ListHasAdjacentDiagnosis.of_head

tail branch:
  apply sourcePressureLocalIslandWitnessList_failure_four_hasAdjacentDiagnosis
    to [W2,W3,W4,W5]
  lift by ListHasAdjacentDiagnosis.of_tail
```

じゃ。

## 次の Codex 指示

```text
Checkpoint 174: Main root only — sharp projection for list-level adjacent diagnosis, then optional length-five wrapper.

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
Checkpoint 173 added projection and propagation helpers:

- SourcePressureLocalIslandWitnessAdjacentPairInList.head_or_tail
- SourcePressureLocalIslandWitnessAdjacentPairInList.cons_iff_head_or_tail
- SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.elim
- SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_head
- SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail
- SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail_tail
- SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail_tail_tail
- SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_listFailure

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
- Do not implement sorting.
- Do not introduce a general recursive classifier yet.

Main goal:
Add a sharper projection theorem for the list-level adjacent diagnosis carrier.
If that is stable, add a bounded length-five wrapper using the existing
length-four wrapper and `of_tail`.

Part A: sharp recovered-or-overlap projection.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_overlap
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h : SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L) :
      (∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
            (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
              A B hrev).items).map
              (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2)
      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L

Suggested proof:
- rcases h with ⟨A, B, hin, hdiag⟩
- rcases hdiag with hrecovered | hobs
- recovered branch:
    exact Or.inl ⟨A, B, hin, hrecovered⟩
- overlap branch:
    exact Or.inr hobs

Part B: optional ordinary failure wrapper from sharp projection.

Only if useful, prove a wrapper that maps the overlap branch to ordinary
sorted-before failure of L.  This is similar to the existing
`exists_recovered_or_listFailure`; do not duplicate if the existing theorem is
enough.

Part C: bounded length-five wrapper.

If Part A is stable and build is clean, prove:

  theorem sourcePressureLocalIslandWitnessList_failure_five_hasAdjacentDiagnosis
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 W4 W5 : SourcePressureLocalIslandWitness n k r}
      (h1pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
      (h2pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
      (h3pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
      (h4pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W4).len)
      (h5pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W5).len)
      (h :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
          [W1, W2, W3, W4, W5]) :
      SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis [W1, W2, W3, W4, W5]

Suggested proof:
- use sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis
    h1pos h2pos h
- head branch:
    rcases hhead with hrecovered | hobs
    recovered:
      build SourcePressureLocalIslandWitnessAdjacentDiagnosis for W1 W2
      then use SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_head
    overlap:
      build adjacent diagnosis by `SourcePressureLocalIslandWitnessAdjacentDiagnosis.overlap hobs`
      then use of_head, or directly use of_adjacent head.
- tail branch:
    apply sourcePressureLocalIslandWitnessList_failure_four_hasAdjacentDiagnosis
      h2pos h3pos h4pos h5pos to the tail failure [W2,W3,W4,W5]
    then lift to the full list by
      SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail

Part D: no general classifier.

Do not prove:
- arbitrary-length failure -> has adjacent diagnosis,
- fuel-indexed classifier,
- sorting,
- coverage,
- maximality,
- uniqueness,
- union accounting,
- Collatz convergence.

Part E: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-174.md

Include:
- sharp recovered-or-overlap projection theorem,
- length-five wrapper if added,
- explicit note that recovered budgets remain pair-local,
- explicit note that overlap remains unmerged/unhandled,
- explicit note that this is bounded/helper API only,
- explicit note that no general recursive classifier was introduced,
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

Checkpoint 174 で length-five wrapper が通ったら、もう固定長 wrapper を増やし続けるより、次は **fuel-indexed ではなく、まず “bounded recursion helper” の型だけ** を考えるのがよい。

いきなり実装するのではなく、候補 shape を比較する段階じゃ。

候補は、

```lean
def SourcePressureLocalIslandWitnessListHasAdjacentDiagnosisUpTo
```

または、

```lean
def SourcePressureLocalIslandWitnessListFailureSearchFuel
```

のような名前になるかもしれぬ。

ただし、まだ焦らない。
length-five まで通れば、pattern は十分観測できる。次は型設計の checkpoint にするのがよい。

## 総評

Checkpoint 173 は、地味だがかなり重要じゃ。

ここまでで、

```text
bounded diagnosis result
  -> list-level carrier
  -> projection / propagation helper
```

が揃った。

これで list-level adjacent diagnosis は、外部から使える API になった。
次は sharp projection と length-five wrapper。そこまで行けば、一般化へ入る前の観測材料は十分になる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
index 4725375b..9b906d8d 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -3368,6 +3368,31 @@ theorem SourcePressureLocalIslandWitnessAdjacentPairInList.tail
       (W1 :: W2 :: rest) A B :=
   Or.inr h
 
+/-- Decompose an adjacent-pair address in a nontrivial cons list. -/
+theorem SourcePressureLocalIslandWitnessAdjacentPairInList.head_or_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 A B : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessAdjacentPairInList
+        (W1 :: W2 :: rest) A B) :
+    (A = W1 ∧ B = W2) ∨
+      SourcePressureLocalIslandWitnessAdjacentPairInList
+        (W2 :: rest) A B :=
+  h
+
+/-- Adjacent-pair address in a cons list is exactly head-pair or tail-pair. -/
+theorem SourcePressureLocalIslandWitnessAdjacentPairInList.cons_iff_head_or_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 A B : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)} :
+    SourcePressureLocalIslandWitnessAdjacentPairInList
+      (W1 :: W2 :: rest) A B ↔
+    (A = W1 ∧ B = W2) ∨
+      SourcePressureLocalIslandWitnessAdjacentPairInList
+        (W2 :: rest) A B :=
+  Iff.rfl
+
 /-- There is no adjacent pair in the empty witness list. -/
 theorem SourcePressureLocalIslandWitnessAdjacentPairInList.nil_false
     {n : OddNat} {k r : ℕ}
@@ -3412,6 +3437,109 @@ theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_adjacent
     SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L :=
   ⟨A, B, hin, hdiag⟩
 
+/-- Eliminate a list-level adjacent diagnosis by exposing its addressed pair. -/
+theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.elim
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {P : Prop}
+    (h : SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L)
+    (hp :
+      ∀ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B →
+        SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B →
+        P) :
+    P := by
+  rcases h with ⟨A, B, hin, hdiag⟩
+  exact hp A B hin hdiag
+
+/-- Build a list-level adjacent diagnosis from a diagnosis on the head pair. -/
+theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_head
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (hdiag :
+      SourcePressureLocalIslandWitnessAdjacentDiagnosis
+        (W1 :: W2 :: rest) W1 W2) :
+    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
+      (W1 :: W2 :: rest) :=
+  SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_adjacent
+    SourcePressureLocalIslandWitnessAdjacentPairInList.head hdiag
+
+/--
+Propagate a list-level adjacent diagnosis through a new head.
+
+This only transports the address and the enclosing-list obstruction branch.
+Recovered budget evidence remains attached to the same adjacent pair.
+-/
+theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
+        (W2 :: rest)) :
+    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
+      (W1 :: W2 :: rest) := by
+  rcases h with ⟨A, B, hin, hdiag⟩
+  exact SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_adjacent
+    (SourcePressureLocalIslandWitnessAdjacentPairInList.tail hin)
+    (SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail hdiag)
+
+/--
+Two-step tail propagation for bounded address plumbing.
+
+This is deliberately not a general recursive classifier; it is only a named
+composition of `of_tail` for small explicit lists.
+-/
+theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
+        (W3 :: rest)) :
+    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
+      (W1 :: W2 :: W3 :: rest) :=
+  SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail
+    (SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail h)
+
+/--
+Three-step tail propagation for bounded address plumbing.
+
+This helper keeps the current API bounded and explicit; it does not inspect or
+classify an arbitrary witness list.
+-/
+theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail_tail_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
+        (W4 :: rest)) :
+    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
+      (W1 :: W2 :: W3 :: W4 :: rest) :=
+  SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail
+    (SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail_tail h)
+
+/--
+Project a list-level adjacent diagnosis to either pair-local recovered budget
+evidence or ordinary sorted-before failure of the enclosing list.
+-/
+theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_listFailure
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L) :
+    ∃ A B,
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+        ((∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
+          (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+            A B hrev).items).map
+            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2)
+        ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L) := by
+  rcases h with ⟨A, B, hin, hdiag⟩
+  exact ⟨A, B, hin,
+    SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered_or_listFailure hdiag⟩
+
 /-- The empty witness list cannot carry a list-level adjacent diagnosis. -/
 theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.nil_false
     {n : OddNat} {k r : ℕ} :
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-173.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-173.md
new file mode 100644
index 00000000..11a6e1a9
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-173.md
@@ -0,0 +1,143 @@
+# Report Petal 173
+
+## Checkpoint
+
+`cp: 173`
+
+Main root only: projection and propagation helpers for list-level adjacent
+diagnosis.
+
+## Implemented
+
+### Adjacent-pair decomposition
+
+Added:
+
+```lean
+theorem SourcePressureLocalIslandWitnessAdjacentPairInList.head_or_tail
+theorem SourcePressureLocalIslandWitnessAdjacentPairInList.cons_iff_head_or_tail
+```
+
+These expose the definitional split of an adjacent-pair address in a cons list:
+
+```text
+head pair, or adjacent pair in the tail
+```
+
+The theorem is address plumbing only.  It does not turn adjacent-pair evidence
+into arbitrary pair membership.
+
+### List-level carrier eliminator
+
+Added:
+
+```lean
+theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.elim
+```
+
+This exposes the addressed pair and its local adjacent diagnosis to downstream
+callers.
+
+### Head and tail constructors
+
+Added:
+
+```lean
+theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_head
+theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail
+```
+
+`of_head` packages a diagnosis on the head pair.  `of_tail` propagates a
+diagnosis through a newly supplied head by lifting the adjacent-pair address and
+using `SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail`.
+
+Recovered budget evidence remains attached to the same adjacent pair.  Only the
+enclosing-list overlap branch is transported to the larger list.
+
+### Bounded tail propagation helpers
+
+Added:
+
+```lean
+theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail_tail
+theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail_tail_tail
+```
+
+These are named two-step and three-step compositions of `of_tail`.  They are
+bounded helper API, not a general recursive classifier.
+
+### Recovered-or-list-failure projection
+
+Added:
+
+```lean
+theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_listFailure
+```
+
+This projects a list-level adjacent diagnosis into:
+
+```text
+some addressed adjacent pair with pair-local recovered budget
+or
+ordinary sorted-before failure of the enclosing list
+```
+
+It is a wrapper around
+`SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered_or_listFailure`.
+
+## Boundary
+
+This checkpoint introduced helper API only.
+
+It did not introduce:
+
+- arbitrary-length failure to adjacent diagnosis;
+- a fuel-indexed classifier;
+- sorting;
+- coverage;
+- maximality;
+- uniqueness;
+- prefix behavior;
+- union accounting;
+- interval merging;
+- Collatz convergence.
+
+Overlap remains unmerged and unresolved as an enclosing-list obstruction.
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
+The API now has enough projection and propagation helpers for bounded
+diagnostic consumers.  The next useful step should still remain bounded:
+either build a small length-five wrapper from the existing four-witness carrier
+and `of_tail`, or add eliminators that separate recovered evidence from overlap
+without introducing a general recursive classifier.
````
`````
