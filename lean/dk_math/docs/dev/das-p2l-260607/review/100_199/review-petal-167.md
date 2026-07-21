# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAccounting

gch: f302ef2138afeb80a4eb77cd332976df3a196e29

## Report

cp166 完了です。

[PressureAccounting.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean) に tail failure propagation 用の constructor API を追加しました。

追加内容:

- `SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_head_not_before`
- `SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_tail`
- `SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_head_or_tail`
- `SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_tail`
- `SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.of_tailAdjacentOverlapObstruction`

今回は constructor / propagation API のみです。list-wide sorting、arbitrary failure classification、merge / split / union accounting には進んでいません。

レポート作成済みです: [report-petal-166.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-166.md)

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

うむ、Checkpoint 166 は **採用** じゃ 👍️
今回で、list failure の **constructor / propagation API** が整った。

追加された中心は、

```lean id="z41r4x"
SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_head_not_before
SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_tail
SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_head_or_tail
SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_tail
SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.of_tailAdjacentOverlapObstruction
```

じゃな。今回は constructor API のみで、list-wide sorting、arbitrary failure classification、merge / split / union accounting には進んでいない。境界がよく守られておる。

## 状況分析

## 1. list failure の再帰骨格が見えてきた

これまでの流れはこうじゃ。

```text id="djzn2v"
pair:
  sorted / reverse recovered / overlap obstruction

head pair:
  recovered budget or adjacent obstruction

list:
  adjacent obstruction -> sorted-before failure
```

今回で、さらに list failure そのものについて、

```text id="1y9g7i"
head が壊れたら list failure
tail が壊れていたら list failure
```

という constructor が外に出た。

つまり、list failure を **作る側** の API が整った。

## 2. cp164 の内部証明が外部 API になった

今回の `cons_of_head_not_before` と `cons_of_tail` は、cp164 の proof 内で使っていた構造を外へ出したものじゃ。

これは良い。
今後、同じ `simpa [...] using Or.inl/Or.inr` を何度も書かなくて済む。

特に `cons_of_tail` は、次の再帰処理で重要になる。

```text id="0ykd2m"
tail に failure がある
  -> 新しい head を付けても failure は残る
```

これは list-level diagnosis の基本伝播じゃ。

## 3. 次は逆向き decomposition

今回作ったのは constructor、つまり、

```text id="rwbf1q"
head not-before or tail failure
  -> full list failure
```

じゃ。

次に欲しいのは逆向き。

```text id="y4xjaz"
full list failure
  -> head not-before or tail failure
```

これが通ると、list failure を一段ずつ剥がせる。

つまり、list failure の再帰処理が本格的に始まる。

## レビュー

## 採用理由

第一に、今回の theorem 群は全部「薄い API」になっている。

新しい理論主張ではなく、既存 failure predicate の head/tail branch を読みやすくしたものじゃ。これは保守しやすい。

第二に、`cons_of_head_or_tail` まで入ったのが良い。

```lean id="ew7dnh"
SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_head_or_tail
```

これにより、case split した後の戻しが一発になる。

第三に、tail adjacent obstruction から full-list failure への橋が入った。

```lean id="vx8p9x"
SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.of_tailAdjacentOverlapObstruction
```

これは、tail 側で見つかった overlap obstruction を、前に head を足した list でも failure として保持するための補題じゃ。

## 注意点

## 1. まだ failure の分解ではない

今回の theorem は failure を作る方向じゃ。

まだ次は未実装。

```lean id="z5yntl"
SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.head_or_tail
```

つまり、

```text id="ry06wo"
failure を受け取って、
head branch か tail branch かに分ける
```

ところは次 checkpoint。

## 2. tail の中身は解析していない

`cons_of_tail` は、tail failure をそのまま持ち上げるだけじゃ。

```text id="7i12wc"
tail がなぜ failure なのか
```

は分類していない。

ここは意図通り。今は propagation、次が decomposition、その後に recursive diagnosis じゃ。

## 3. list-wide sorting ではない

今回も sorting algorithm ではない。

まだ次は言っていない。

```text id="g1iwfy"
list を並べ替える
全 failure を分類する
canonical sorted family を作る
```

これはまだ先。
今は failure の head/tail 構文を固めている段階じゃ。

## 解説

今回の実装を一言で言えば、

```text id="8hdth4"
list failure の構文規則を外部 API にした
```

じゃ。

隣接 sorted-before failure は、再帰的に見ると、

```text id="5bmz66"
先頭 pair が壊れている
または
tail 側に failure がある
```

という構造を持つ。

今回入ったのは、その「または」から full list failure を作る方向。

```text id="y9r213"
not W1 before W2
  -> failure (W1 :: W2 :: rest)

failure (W2 :: rest)
  -> failure (W1 :: W2 :: rest)
```

これで、後続の theorem は定義を直接 unfold せずに、API として書ける。

## 一歩先ゆく推論

次は **head_or_tail decomposition** じゃ。

候補はこれ。

```lean id="w8w356"
theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.head_or_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W1 :: W2 :: rest)) :
    (¬ SourcePressureLocalIslandWitnessBefore W1 W2) ∨
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure (W2 :: rest)
```

これが通れば、list failure を一段剥がせる。

つまり、

```text id="smfg75"
full list failure
  -> head failure:
       cp165 の head-pair recovered-or-obstruction へ
  -> tail failure:
       再帰的に後ろへ送る
```

という処理が可能になる。

これはまだ algorithm ではないが、algorithmic skeleton の核心になる。

## さらなる次の一手

Checkpoint 167 で `head_or_tail` が通ったら、次は **head/tail failure reason split** じゃ。

つまり、

```text id="xytx5p"
failure (W1 :: W2 :: rest)
  -> head recovered budget
  or head adjacent obstruction
  or tail failure
```

を作る。

候補はこう。

```lean id="0r7ykq"
theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
    .headRecovered_or_headAdjacentObstruction_or_tail
```

ただし theorem 名は長くなるので、実装では短めが良い。

形は、

```lean id="8g7tmz"
theorem sourcePressureLocalIslandWitnessList_failure_headRecovered_or_headAdjacentObstruction_or_tail
    ...
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W1 :: W2 :: rest)) :
    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      ... sum ≤ -2)
    ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
        (W1 :: W2 :: rest)
    ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W2 :: rest)
```

この theorem が通ると、list failure の一段処理が完成する。

## 賢狼が試して欲しい実験補題

## 実験補題 A: head_or_tail decomposition

```lean id="m3ewr3"
theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.head_or_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W1 :: W2 :: rest)) :
    (¬ SourcePressureLocalIslandWitnessBefore W1 W2) ∨
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W2 :: rest)
```

証明は、定義を展開して `simpa` で `h` を Or へ戻す形になりそうじゃ。
もし unfold が重ければ、cp166 の `cons_of_head_or_tail` と同じ展開セットを逆向きに使う。

## 実験補題 B: iff 版

可能なら、constructor と decomposition をまとめて iff にする。

```lean id="g3mnrq"
theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_iff_head_or_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)} :
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
      (W1 :: W2 :: rest) ↔
    (¬ SourcePressureLocalIslandWitnessBefore W1 W2) ∨
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W2 :: rest)
```

これはかなり便利。
左向きは A、右向きは `cons_of_head_or_tail`。

## 実験補題 C: head failure recovered-or-obstruction from full list failure

`head_or_tail` だけでは head branch の中身までは分からない。
まず head branch を取り出せた場合に、既存 theorem へ渡す補題が欲しい。

```lean id="tsbemr"
theorem sourcePressureLocalIslandWitnessList_headNotBefore_recovered_or_adjacentOverlapObstruction
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (hnot : ¬ SourcePressureLocalIslandWitnessBefore W1 W2) :
    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W1 W2 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
    ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
        (W1 :: W2 :: rest)
```

証明は、`hnot` から pair failure を作る必要がある。

既に pair-level で、

```lean id="t6tf4r"
sourcePressureLocalIslandWitnessPair_hasSortedBeforeFailure_of_not_before
```

系があるはずなので、それを使う。
なければ `[W1, W2]` failure を `pair_iff.2 hnot` で作る。

## 実験補題 D: full list failure one-step diagnosis

これが本命じゃ。

```lean id="i69qvu"
theorem sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W1 :: W2 :: rest)) :
    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W1 W2 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
          (W1 :: W2 :: rest))
    ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W2 :: rest)
```

これは `head_or_tail h` で分ける。

head branch なら、実験補題 C を使う。
tail branch なら右へ送る。

## 次の Codex 指示

```text id="j36vc2"
Checkpoint 167: Main root only — decompose list sorted-before failure into head or tail.

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
Checkpoint 166 added constructor / propagation API:

- SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_head_not_before
- SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_tail
- SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_head_or_tail
- SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_tail
- SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.of_tailAdjacentOverlapObstruction

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
- Do not classify arbitrary list failures beyond one recursive head/tail split.

Main goal:
Add the inverse direction for the recursive sorted-before failure predicate:
a failure in `W1 :: W2 :: rest` comes from either the head pair or the tail.

Part A: head_or_tail decomposition.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.head_or_tail
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      {rest : List (SourcePressureLocalIslandWitness n k r)}
      (h :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
          (W1 :: W2 :: rest)) :
      (¬ SourcePressureLocalIslandWitnessBefore W1 W2) ∨
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
          (W2 :: rest)

Suggested proof:
- unfold/simp the same definitions used in cons_of_head_not_before and
  cons_of_tail:
  SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
  sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList
  SourcePressureIntervalPulseAddressFamilyHasSortedBeforeFailure
  SourcePressureIntervalPulseAddressListHasSortedBeforeFailure
  sourcePressureAccountedIntervalList_of_intervalPulseAddressList
  SourcePressureAccountedIntervalListHasSortedBeforeFailure
- then exact/simpa using h.

Part B: iff version.

If Part A closes cleanly, prove:

  theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_iff_head_or_tail
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      {rest : List (SourcePressureLocalIslandWitness n k r)} :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W1 :: W2 :: rest) ↔
      (¬ SourcePressureLocalIslandWitnessBefore W1 W2) ∨
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
          (W2 :: rest)

Suggested proof:
- constructor
- forward: head_or_tail
- backward: cons_of_head_or_tail

Part C: head not-before to recovered-or-adjacent-obstruction.

Prove:

  theorem sourcePressureLocalIslandWitnessList_headNotBefore_recovered_or_adjacentOverlapObstruction
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      {rest : List (SourcePressureLocalIslandWitness n k r)}
      (h1pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
      (h2pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
      (hnot : ¬ SourcePressureLocalIslandWitnessBefore W1 W2) :
      (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
        (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          W1 W2 hrev).items).map
          (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
          (W1 :: W2 :: rest)

Suggested proof:
- build pair failure for [W1, W2] from hnot using the existing pair iff:
  sourcePressureLocalIslandWitnessListHasSortedBeforeFailure_pair_iff.2 hnot
  or the existing raw constructor if available.
- apply sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_adjacentOverlapObstruction
  h1pos h2pos to that pair failure.

Part D: one-step diagnosis from full list failure.

Prove:

  theorem sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      {rest : List (SourcePressureLocalIslandWitness n k r)}
      (h1pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
      (h2pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
      (h :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
          (W1 :: W2 :: rest)) :
      ((∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
        (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          W1 W2 hrev).items).map
          (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
        ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
            (W1 :: W2 :: rest))
      ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
          (W2 :: rest)

Suggested proof:
- rcases SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.head_or_tail h
  with hhead | htail
- head branch:
  apply sourcePressureLocalIslandWitnessList_headNotBefore_recovered_or_adjacentOverlapObstruction
  then wrap as Or.inl
- tail branch:
  exact Or.inr htail

Part E: no full list algorithm.

Do not add sorting.
Do not add arbitrary list failure classification.
Do not add overlap cluster, merge, split, union accounting, coverage,
maximality, uniqueness, prefix behavior, or convergence claims.

Part F: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-167.md

Include:
- head_or_tail theorem,
- iff theorem if added,
- head not-before recovered-or-adjacent theorem,
- one-step diagnosis theorem,
- explicit note that this is one recursive head/tail split only,
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

Checkpoint 167 が通ったら、次は **one-step diagnosis の tail-cons propagation** じゃ。

つまり tail 側で、

```text id="w1cnd4"
tail failure one-step diagnosis
```

が得られるなら、前に head を足しても、

```text id="xk3w1h"
full list failure one-step diagnosis
```

として扱えるようにする。

ただし、これは慎重にやる。
なぜなら recovered budget は tail 内の pair に対するものなので、head を足した full list の budget ではないからじゃ。

まずは theorem を「tail diagnosis can be lifted as tail failure branch」として弱く置くのが安全じゃ。

## 総評

Checkpoint 166 は地味だが重要じゃ。
list failure を作る head/tail constructor が揃った。

次はその逆、failure を head/tail に分解する。
ここが通ると、list-level failure diagnosis は一段ずつ剥がせる構文を持つ。

PressureAccounting はいよいよ、

```text id="lpf1va"
pair diagnosis
head diagnosis
list one-step diagnosis
```

へ進む段階に入っておるぞ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
index e62305df..c9504ee8 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -2069,6 +2069,68 @@ theorem sourcePressureLocalIslandWitnessPair_no_failure_of_before
   rw [sourcePressureLocalIslandWitnessListHasSortedBeforeFailure_pair_iff]
   exact not_not_intro hbefore

+/--
+Head constructor for adjacent sorted-before failure in a witness list.
+
+This exposes the first recursive branch of the failure predicate.  It is only
+an order-failure constructor for the explicit list.
+-/
+theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_head_not_before
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (hnot : ¬ SourcePressureLocalIslandWitnessBefore W1 W2) :
+    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+      (W1 :: W2 :: rest) := by
+  simpa [SourcePressureLocalIslandWitnessListHasSortedBeforeFailure,
+    sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList,
+    SourcePressureIntervalPulseAddressFamilyHasSortedBeforeFailure,
+    SourcePressureIntervalPulseAddressListHasSortedBeforeFailure,
+    sourcePressureAccountedIntervalList_of_intervalPulseAddressList,
+    SourcePressureAccountedIntervalListHasSortedBeforeFailure] using
+    (Or.inl hnot)
+
+/--
+Tail constructor for adjacent sorted-before failure in a witness list.
+
+This exposes the second recursive branch of the failure predicate.  It does
+not classify the tail; it only carries an already supplied tail failure.
+-/
+theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (htail :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        (W2 :: rest)) :
+    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+      (W1 :: W2 :: rest) := by
+  simpa [SourcePressureLocalIslandWitnessListHasSortedBeforeFailure,
+    sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList,
+    SourcePressureIntervalPulseAddressFamilyHasSortedBeforeFailure,
+    SourcePressureIntervalPulseAddressListHasSortedBeforeFailure,
+    sourcePressureAccountedIntervalList_of_intervalPulseAddressList,
+    SourcePressureAccountedIntervalListHasSortedBeforeFailure] using
+    (Or.inr htail)
+
+/-- Case-split constructor for head-or-tail sorted-before failure. -/
+theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_head_or_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      (¬ SourcePressureLocalIslandWitnessBefore W1 W2) ∨
+        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+          (W2 :: rest)) :
+    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+      (W1 :: W2 :: rest) := by
+  rcases h with hhead | htail
+  · exact
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_head_not_before
+        hhead
+  · exact SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_tail
+      htail
+
 /--
 Every explicit local-island witness pair is either sorted or carries a
 sorted-before failure.
@@ -2283,6 +2345,19 @@ theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.cons_o
       (W1 :: W2 :: rest) :=
   Or.inr htail

+/-- Readable alias for propagating adjacent overlap obstruction from the tail. -/
+theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (htail :
+      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+        (W2 :: rest)) :
+    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+      (W1 :: W2 :: rest) :=
+  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.cons_of_tail
+    htail
+
 /-- Adjacent overlap obstruction for a pair is symmetric. -/
 theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction_pair_symm
     {n : OddNat} {k r : ℕ}
@@ -2349,6 +2424,27 @@ theorem
   SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
     hobs

+/--
+Tail adjacent-overlap obstruction gives sorted-before failure for the full
+explicit list.
+
+This is only propagation through a new head.  It does not inspect or repair the
+tail obstruction.
+-/
+theorem
+    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.of_tailAdjacentOverlapObstruction
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (htail :
+      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+        (W2 :: rest)) :
+    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+      (W1 :: W2 :: rest) :=
+  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
+    (SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_tail
+      htail)
+
 /--
 Reverse-recovery helper for a pair whose failure reason is merely reversed
 order.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-166.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-166.md
new file mode 100644
index 00000000..061f4d89
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-166.md
@@ -0,0 +1,160 @@
+# Report Petal 166
+
+## Checkpoint
+
+Checkpoint 166 stayed on the main Collatz/PetalBridge root and exposed small
+constructor/projection API for propagating tail failure and tail adjacent
+overlap obstruction through a new list head.
+
+Modified implementation file:
+
+- `DkMath/Collatz/PetalBridge/PressureAccounting.lean`
+
+No `OneCycle`, `ValuationFlowBridge`, `ABC`, or `NumberTheory` files were
+modified.
+
+## Sorted-Before Failure Constructors
+
+The head not-before constructor was added:
+
+```lean
+theorem
+  SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_head_not_before
+```
+
+Meaning:
+
+```text
+not (W1 before W2)
+  -> failure for W1 :: W2 :: rest
+```
+
+The tail failure constructor was added:
+
+```lean
+theorem
+  SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_tail
+```
+
+Meaning:
+
+```text
+failure for W2 :: rest
+  -> failure for W1 :: W2 :: rest
+```
+
+The optional unification theorem was also added:
+
+```lean
+theorem
+  SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_head_or_tail
+```
+
+This is just a case split over the two recursive failure branches.
+
+## Adjacent Overlap Tail Propagation
+
+A readable alias for adjacent-overlap tail propagation was added:
+
+```lean
+theorem
+  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_tail
+```
+
+This aliases the existing `cons_of_tail` constructor.
+
+## Tail Adjacent Obstruction To List Failure
+
+The tail adjacent-overlap obstruction to full-list failure theorem was added:
+
+```lean
+theorem
+  SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.of_tailAdjacentOverlapObstruction
+```
+
+Meaning:
+
+```text
+adjacent overlap obstruction in W2 :: rest
+  -> sorted-before failure in W1 :: W2 :: rest
+```
+
+This is propagation only.  It does not inspect or repair the tail obstruction.
+
+## Boundary Notes
+
+This checkpoint is constructor API only.
+
+Overlap remains unmerged and unhandled.
+
+This checkpoint does not:
+
+- implement sorting,
+- classify arbitrary list failures,
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
+All statements remain local to explicitly supplied witness lists.
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
+The next safe target is the inverse direction:
+
+```lean
+theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.head_or_tail
+```
+
+Expected shape:
+
+```text
+failure for W1 :: W2 :: rest
+  -> not (W1 before W2)
+  or failure for W2 :: rest
+```
+
+This would let callers peel one adjacent failure layer at a time.  It should
+still remain a decomposition theorem, not a sorting algorithm.
````
`````
