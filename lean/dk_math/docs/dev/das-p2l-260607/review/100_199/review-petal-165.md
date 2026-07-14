# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAccounting

gch: 92c5933198f9b194c25895f08c11eaf60428793d

## Report

cp164 完了です。

[PressureAccounting.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean) に、adjacent-list 用の overlap obstruction API を追加しました。

追加内容:

- `SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction`
- pair iff
- head / tail constructors
- pair symmetry
- full-list `hasSortedBeforeFailure`
- pair specialization `pair_hasSortedBeforeFailure`

full-list の `adjacent overlap obstruction -> sorted-before failure` まで通りました。これは adjacent recursive 構造に限った話で、任意ペア探索、cluster、merge、union accounting には進んでいません。

レポート作成済みです: [report-petal-164.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-164.md)

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

うむ、Checkpoint 164 は **採用** じゃ 👍️
今回で、pair-level の overlap obstruction が、最小限の **adjacent-list API** へ持ち上がった。

追加された中心はこれじゃ。

```lean id="l7fp2r"
SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
```

そして、pair iff、head/tail constructor、pair symmetry、さらに full-list の

```lean id="p5skzv"
SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
```

まで通っておる。これは良い進展じゃ。隣接 overlap obstruction があれば、その list には普通の sorted-before failure がある、という方向が Lean で閉じた。

## 状況分析

## 1. pair から adjacent-list へ一段上がった

ここまでの pair-level はかなり整理されていた。

```text id="xv545h"
pair failure:
  reverse branch:
    swap で budget 回収

  overlap branch:
    swap では回復不能な obstruction
```

今回の cp164 では、この overlap branch を list の隣接構造へ持ち上げた。

```text id="rhtn0x"
W1 :: W2 :: rest
  -> obstruction W1 W2
  or obstruction in W2 :: rest
```

これは任意 pair 探索ではなく、隣接 pair の再帰だけを見る。
この制限が良い。いきなり list 全体の cluster や任意 pair membership に行くと、Lean でも概念でも重くなるからじゃ。

## 2. full-list `hasSortedBeforeFailure` まで通ったのが大きい

今回の一番の成果は、これが defer されずに通ったことじゃ。

```lean id="o23uxa"
SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
```

意味は、

```text id="bigj6o"
adjacent overlap obstruction が list 内にある
  -> その list は sorted-before failure を持つ
```

じゃ。

これで、overlap obstruction は単に「隣接 pair の局所情報」ではなく、既存の list-level failure API と接続された。

これは次の head-pair / list-failure diagnosis へ進む足場になる。

## 3. まだ cluster / union accounting ではない

今回も境界線は守られている。

report でも、任意非隣接 pair、overlap cluster、merge、split、union accounting、coverage、convergence には踏み込んでいないと明記されている。

これは正しい。
今はまだ、

```text id="t11tiu"
list 内の隣接 overlap obstruction を検出する
```

段階じゃ。

## レビュー

## 採用理由

今回の採用理由は三つある。

第一に、recursive predicate の形が軽い。

```lean id="fwzvfd"
| [] => False
| [_] => False
| W1 :: W2 :: rest =>
    SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2 ∨
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction (W2 :: rest)
```

membership や duplicate equality を避け、adjacent だけに絞っている。これは Lean 的にも正しい。

第二に、pair API が揃っている。

```lean id="uyhsh7"
SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction_pair_iff
SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.cons_of_head
SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.cons_of_tail
SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction_pair_symm
```

これで後続 theorem の入口がかなり楽になる。

第三に、list failure への接続ができた。

```lean id="v4g3kq"
SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
```

これは pair-level obstruction を list-level failure 診断エンジンへつなぐ橋じゃ。

## 注意点

## 1. adjacent-only である

これは弱点ではなく、意図された制限じゃ。

まだ次は言っていない。

```text id="y0qj8s"
任意の二点が overlap している
非隣接 overlap を探す
overlap cluster を作る
```

今は隣接だけ。
この制限を外すのは、もう少し API が揃ってからでよい。

## 2. `hasSortedBeforeFailure` は一方向

今回示したのは、

```text id="jo7ntk"
adjacent overlap obstruction
  -> sorted-before failure
```

じゃ。

逆はまだ違う。

```text id="ovdlej"
sorted-before failure
  -> adjacent overlap obstruction
```

ではない。
failure には reverse branch もあるからじゃ。

ここを混同してはいけない。

## 3. full-list proof はやや unfold 依存

`hasSortedBeforeFailure` の証明は、複数の定義を `simpa` で展開して通している。ビルドが通っているので採用だが、今後このあたりの定義を変更すると壊れやすい可能性はある。

後で必要になったら、list failure の head/tail constructor API を別途作ると安定する。

## 解説

今回の実装を直感的に言うと、

```text id="mb81a5"
list のどこか隣で overlap obstruction が起きているなら、
その list は sorted にはなれない
```

じゃ。

たとえば、

```text id="xrauyd"
[W1, W2, W3, W4]
```

で、

```text id="c0wfug"
W2 と W3 が overlap obstruction
```

なら、この list は sorted-before failure を持つ。

これは当然のように見えるが、Lean 上では重要じゃ。
pair-level の obstruction が、list-level の failure predicate とつながったからの。

ここまでで構造はこうなった。

```text id="s4tnmy"
pair:
  sorted
  reverse recoverable
  overlap obstruction

list:
  adjacent overlap obstruction
    -> sorted-before failure
```

つまり、pair 診断が list の隣接診断へ昇格した。

## 一歩先ゆく推論

次は report の通り、**head-pair failure reason theorem** が自然じゃ。

いま list の隣接 overlap obstruction は作れた。
次に欲しいのは、list の先頭隣接 pair について、

```text id="isxhle"
head pair failure
  -> reverse-recovered budget
  or overlap obstruction
```

を出すことじゃ。

ただし list 全体の failure を分類するのではなく、まず head pair 限定でよい。

なぜなら、head pair は構造が明確だからじゃ。

```text id="l5hk3d"
W1 :: W2 :: rest
```

の head pair failure は、実質的に

```text id="apvmf6"
[W1, W2] failure
```

として pair theorem に落とせる。

既にある、

```lean id="f4yp9l"
sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlapObstruction
```

をそのまま使えるはずじゃ。

## さらなる次の一手

Checkpoint 165 で head-pair failure reason が通ったら、その次は **head-pair failure を list に埋め戻す API** が欲しくなる。

つまり、

```text id="lqld1b"
head pair overlap obstruction
  -> list has adjacent overlap obstruction
  -> list has sorted-before failure
```

は今回の constructor と theorem でいける。

一方、

```text id="oadfgi"
head pair reverse branch
  -> swapped pair has recovered budget
```

は pair-level では回収済み。

これをまとめると、list 先頭で failure が起きたとき、

```text id="lfkoid"
reverse:
  head pair は swap すれば回収可能

overlap:
  list は adjacent overlap obstruction を持つ
```

という algorithmic skeleton が見えてくる。

ただし、まだ list 全体を sort しない。
まずは「先頭 failure 一個を処理する」だけでよい。

## 賢狼が試して欲しい実験補題

## 実験補題 A: head-pair failure predicate

まず、head pair failure を名前にしておくと読みやすい。

```lean id="pxbzqm"
def SourcePressureLocalIslandWitnessListHeadPairHasSortedBeforeFailure
    {n : OddNat} {k r : ℕ}
    : List (SourcePressureLocalIslandWitness n k r) → Prop
  | [] => False
  | [_] => False
  | W1 :: W2 :: _ =>
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]
```

ただし、定義を増やしすぎたくないなら、theorem の仮定に直接 `[W1, W2]` failure を置く方が軽い。

## 実験補題 B: head-pair recovered-or-obstruction

```lean id="pmxdqw"
theorem sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_overlapObstruction
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (hfail : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]) :
    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W1 W2 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
    ∨ SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2
```

`rest` は statement の意味づけ用で、証明には使わない可能性が高い。未使用が気になるなら、list 版と pair 版を分ける。

## 実験補題 C: head overlap obstruction embeds into adjacent-list obstruction

```lean id="slz4mm"
theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_headPairObstruction
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
      (W1 :: W2 :: rest) :=
  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.cons_of_head hobs
```

これは既存 `cons_of_head` の alias でもよい。

## 実験補題 D: head overlap obstruction gives list failure

```lean id="jr8g2n"
theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.of_headPairOverlapObstruction
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
      (W1 :: W2 :: rest) :=
  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
    (SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.cons_of_head hobs)
```

これはかなり便利になる。

## 実験補題 E: head failure recovered or list adjacent obstruction

これが本命じゃ。

```lean id="g8rh61"
theorem sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_adjacentOverlapObstruction
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (hfail : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]) :
    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W1 W2 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
    ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
        (W1 :: W2 :: rest)
```

証明は、既存の `sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlapObstruction` を使い、右 branch で `cons_of_head` するだけのはずじゃ。

## 次の Codex 指示

```text id="mpx9i5"
Checkpoint 165: Main root only — head-pair failure reason for witness lists.

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
Checkpoint 164 added adjacent overlap obstruction for local-island witness lists:

- SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
- SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction_pair_iff
- SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.cons_of_head
- SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.cons_of_tail
- SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction_pair_symm
- SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
- SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction_pair_hasSortedBeforeFailure

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

Main goal:
Add head-pair failure reason API for a witness list whose first two elements
form the failed pair.

Part A: head pair recovered-or-overlap obstruction.

Prove a head-pair theorem by reusing the existing pair theorem:

  theorem sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_overlapObstruction
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      {rest : List (SourcePressureLocalIslandWitness n k r)}
      (h1pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
      (h2pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
      (hfail : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]) :
      (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
        (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          W1 W2 hrev).items).map
          (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
      ∨ SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2

Suggested proof:
- exact sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlapObstruction
    h1pos h2pos hfail
- If `rest` is unused and Lean complains only through linter, either prefix it
  as `_rest` if the style permits, or omit `rest` in this theorem and keep
  Part C for the list embedding theorem.

Part B: explicit head obstruction embedding.

Add an alias around the existing constructor:

  theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_headPairObstruction
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      {rest : List (SourcePressureLocalIslandWitness n k r)}
      (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
        (W1 :: W2 :: rest)

This can reuse `.cons_of_head`.

Part C: head overlap obstruction implies list sorted-before failure.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.of_headPairOverlapObstruction
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      {rest : List (SourcePressureLocalIslandWitness n k r)}
      (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W1 :: W2 :: rest)

Suggested proof:
- use SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
- feed it cons_of_head hobs

Part D: head failure recovered-or-adjacent-obstruction.

Prove the main list-facing split:

  theorem sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_adjacentOverlapObstruction
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      {rest : List (SourcePressureLocalIslandWitness n k r)}
      (h1pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
      (h2pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
      (hfail : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]) :
      (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
        (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          W1 W2 hrev).items).map
          (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
          (W1 :: W2 :: rest)

Suggested proof:
- rcases sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlapObstruction
    h1pos h2pos hfail with hrecovered | hobs
- left: exact hrecovered
- right: exact cons_of_head hobs

Part E: optional theorem with list failure conclusion.

If easy, add:

  theorem sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_listFailure
      ...
      (hfail : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]) :
      (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
        ... sum ≤ -2)
      ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
          (W1 :: W2 :: rest)

This follows from Part D and hasSortedBeforeFailure on the adjacent obstruction
branch.

Do not force this if it becomes verbose.

Part F: no list-wide sorting.

Do not add a sorting algorithm.
Do not classify arbitrary list failures.
Do not add overlap cluster, merge, split, union accounting, coverage,
maximality, uniqueness, prefix behavior, or convergence claims.

Part G: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-165.md

Include:
- head-pair recovered-or-overlap theorem,
- head obstruction embedding theorem,
- head obstruction -> list failure theorem,
- recovered-or-adjacent-obstruction theorem,
- optional recovered-or-list-failure theorem if added,
- explicit note that this is head-pair only,
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

Checkpoint 165 が通ったら、次は **tail failure propagation** じゃ。

今は head pair を扱う。
その次は、

```text id="njt85p"
tail に recovered-or-adjacent-obstruction があるなら、
cons しても recovered-or-adjacent-obstruction が残る
```

という形に進む。

これにより、list の先頭だけでなく、再帰的に後ろ側の failure reason を引き上げられる。

ただし、まだ full algorithm ではない。
まずは constructor と propagation だけ。

候補は、

```lean id="abpmh4"
theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_tail
```

は既に `cons_of_tail` があるので、次は recovered-or-obstruction split の tail 版。

```lean id="d01goz"
theorem sourcePressureLocalIslandWitnessList_tail_failure_recovered_or_adjacentOverlapObstruction_cons
```

のような形じゃ。

## 総評

Checkpoint 164 は良い一手じゃ。
pair obstruction が list の隣接構造へ移った。

これで次は、list の先頭 failure を

```text id="m7n9kx"
budget 回収できる reverse branch
または
adjacent overlap obstruction branch
```

へ分類できる。

ここを閉じれば、list-level failure diagnosis の再帰処理に入れる。
PressureAccounting は、かなり明確に **局所 failure 診断から list 診断へ** 登り始めておるぞ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
index c9116481..04055305 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -2236,6 +2236,119 @@ theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.symm_iff
   ⟨SourcePressureLocalIslandWitnessPairOverlapObstruction.symm,
     SourcePressureLocalIslandWitnessPairOverlapObstruction.symm⟩
 
+/--
+Adjacent overlap obstruction for an explicit local-island witness list.
+
+This predicate intentionally looks only at neighboring witness pairs.  It does
+not quantify over arbitrary pairs in the list, does not construct an overlap
+cluster, and does not merge or split intervals for union accounting.
+-/
+def SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+    {n : OddNat} {k r : ℕ} :
+    List (SourcePressureLocalIslandWitness n k r) → Prop
+  | [] => False
+  | [_] => False
+  | W1 :: W2 :: rest =>
+      SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2 ∨
+        SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+          (W2 :: rest)
+
+/-- A two-witness list has adjacent overlap obstruction exactly at that pair. -/
+theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction_pair_iff
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r} :
+    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction [W1, W2] ↔
+      SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2 := by
+  simp [SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction]
+
+/-- Head constructor for adjacent overlap obstruction. -/
+theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.cons_of_head
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
+    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+      (W1 :: W2 :: rest) :=
+  Or.inl hobs
+
+/-- Tail constructor for adjacent overlap obstruction. -/
+theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.cons_of_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    {rest : List (SourcePressureLocalIslandWitness n k r)}
+    (htail :
+      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+        (W2 :: rest)) :
+    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+      (W1 :: W2 :: rest) :=
+  Or.inr htail
+
+/-- Adjacent overlap obstruction for a pair is symmetric. -/
+theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction_pair_symm
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (h :
+      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+        [W1, W2]) :
+    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+      [W2, W1] := by
+  rw [SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction_pair_iff]
+  exact
+    SourcePressureLocalIslandWitnessPairOverlapObstruction.symm
+      (SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction_pair_iff.1 h)
+
+/--
+Adjacent overlap obstruction implies ordinary adjacent sorted-before failure.
+
+The proof follows the explicit neighboring-pair recursion.  It does not turn
+overlap into a repaired family and does not construct any merged interval.
+-/
+theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hobs :
+      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
+    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L := by
+  induction L with
+  | nil =>
+      exact False.elim hobs
+  | cons W1 L ih =>
+      cases L with
+      | nil =>
+          exact False.elim hobs
+      | cons W2 rest =>
+          rcases hobs with hhead | htail
+          · simpa [SourcePressureLocalIslandWitnessListHasSortedBeforeFailure,
+              sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList,
+              SourcePressureIntervalPulseAddressFamilyHasSortedBeforeFailure,
+              SourcePressureIntervalPulseAddressListHasSortedBeforeFailure,
+              sourcePressureAccountedIntervalList_of_intervalPulseAddressList,
+              SourcePressureAccountedIntervalListHasSortedBeforeFailure] using
+              (Or.inl hhead.not_before)
+          · have htailFailure :
+                SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+                  (W2 :: rest) :=
+              ih htail
+            simpa [SourcePressureLocalIslandWitnessListHasSortedBeforeFailure,
+              sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList,
+              SourcePressureIntervalPulseAddressFamilyHasSortedBeforeFailure,
+              SourcePressureIntervalPulseAddressListHasSortedBeforeFailure,
+              sourcePressureAccountedIntervalList_of_intervalPulseAddressList,
+              SourcePressureAccountedIntervalListHasSortedBeforeFailure] using
+              (Or.inr htailFailure)
+
+/-- Pair specialization of adjacent obstruction implying sorted-before failure. -/
+theorem
+    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction_pair_hasSortedBeforeFailure
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (hobs :
+      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+        [W1, W2]) :
+    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2] :=
+  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
+    hobs
+
 /--
 Reverse-recovery helper for a pair whose failure reason is merely reversed
 order.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-164.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-164.md
new file mode 100644
index 00000000..a5a016a2
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-164.md
@@ -0,0 +1,159 @@
+# Report Petal 164
+
+## Checkpoint
+
+Checkpoint 164 stayed on the main Collatz/PetalBridge root and lifted the
+pair-level overlap obstruction to a minimal adjacent-list API.
+
+Modified implementation file:
+
+- `DkMath/Collatz/PetalBridge/PressureAccounting.lean`
+
+No `OneCycle`, `ValuationFlowBridge`, `ABC`, or `NumberTheory` files were
+modified.
+
+## Adjacent Overlap Obstruction
+
+The adjacent-list predicate was added:
+
+```lean
+def SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+```
+
+It is recursive over neighboring witness pairs:
+
+```text
+[]
+  -> false
+[W]
+  -> false
+W1 :: W2 :: rest
+  -> overlap obstruction at W1 W2
+  or adjacent overlap obstruction in W2 :: rest
+```
+
+This is adjacent-only.  It does not quantify over arbitrary pairs in the list
+and does not define an overlap cluster.
+
+## Pair API
+
+The pair equivalence was added:
+
+```lean
+theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction_pair_iff
+```
+
+Constructors were added:
+
+```lean
+theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.cons_of_head
+theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.cons_of_tail
+```
+
+Pair symmetry through the adjacent predicate was added:
+
+```lean
+theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction_pair_symm
+```
+
+This reuses the pair obstruction symmetry from checkpoint 163.
+
+## Sorted-Before Failure
+
+The full-list implication was proved:
+
+```lean
+theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
+```
+
+This means:
+
+```text
+adjacent overlap obstruction in an explicit witness list
+  -> ordinary adjacent sorted-before failure for that same explicit list
+```
+
+The pair specialization was also added:
+
+```lean
+theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction_pair_hasSortedBeforeFailure
+```
+
+The full-list version was not deferred; the existing recursive sorted-before
+failure predicate was compatible with the adjacent obstruction recursion.
+
+## Boundary Notes
+
+Overlap remains unmerged and unhandled.
+
+This checkpoint does not:
+
+- merge intervals,
+- split intervals,
+- construct merged interval families,
+- define overlap clusters,
+- quantify over arbitrary non-adjacent list pairs,
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
+The next safe target is a head-pair failure reason theorem:
+
+```text
+head pair sorted-before failure
+  -> reverse-recovered budget
+  or overlap obstruction
+```
+
+This should still stay at the head-pair level before any attempt at list-wide
+algorithmic processing.  It can reuse:
+
+```lean
+sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlapObstruction
+```
+
+The expected next theorem can package the first adjacent failure in a list
+without merging intervals or asserting coverage.
````
`````
