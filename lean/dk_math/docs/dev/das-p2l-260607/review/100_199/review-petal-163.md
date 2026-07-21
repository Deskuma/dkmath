# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAccounting

gch: 275cd24eb45dc47bdc82411d5e3a130e9a986f87

## Report

cp162 完了です。

[PressureAccounting.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean) に、overlap の対称性、before 排除補題、`SourcePressureLocalIslandWitnessPairOverlapObstruction`、swap では復旧不能である定理、そして recovered-or-overlapObstruction 分岐を追加しました。overlap は明確に「未回収の障害」として分離し、merge / split / union accounting には踏み込んでいません。

レポートも作成済みです: [report-petal-162.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-162.md)

検証結果:

```text
PASS lake build DkMath.Collatz.PetalBridge.PressureAccounting
PASS lake build DkMath.Collatz.PetalBridge.PressureFrontier
PASS lake build DkMath.Collatz.PetalBridge
PASS no sorry in PressureAccounting.lean
PASS no sorry in PressureFrontier.lean
PASS git diff --check
```

`PetalBridge` build 中に既存の `ZsigmondyCyclotomicResearch.lean` の unrelated `sorry` warning は出ていますが、今回の対象ファイルには `sorry` なしです。

## Review

## 結論

うむ、Checkpoint 162 は **採用** じゃ 👍️
今回で、overlap branch が単なる右分岐ではなく、明確な **未回収 obstruction** として名前を持った。

中心はこれじゃ。

```text id="tmcjya"
pair failure
  -> recovered reversed accounting
  or overlap obstruction
```

特に、

```lean id="xqv8cz"
SourcePressureLocalIslandWitnessPairOverlapObstruction
```

が入ったことで、overlap は「まだ merge していない未処理 Gap」として first-class になった。さらに `not_recoverable_by_swap` まで通っており、reverse branch との違いが Lean で明確になった。

## 状況分析

## 1. pair failure の二分構造が完成に近い

ここまでの流れは、かなり綺麗じゃ。

```text id="kysqzr"
sorted:
  そのまま accounting

failure:
  reverse branch:
    swap して accounting 回収

  overlap branch:
    swap しても回復不能な obstruction
```

Checkpoint 161 で reverse branch は `sum ≤ -2` まで回収された。
今回の Checkpoint 162 で overlap branch は、

```text id="tn1nnp"
failure かつ overlap
```

として名前を持ち、さらに

```text id="9tqnkj"
overlap -> not before
overlap -> not reverse-before
```

が入った。

つまり、overlap は「どちら向きにも sorted に戻せない pair obstruction」として固定された。

## 2. overlap の対称性が入ったのが良い

今回、

```lean id="lsg7eq"
NatIntervalsOverlap.symm
SourcePressureIntervalPulseAddressOverlap.symm
SourcePressureLocalIslandWitnessOverlap.symm
```

が追加された。

これは小さいが重要じゃ。
overlap は順序依存ではなく、区間関係そのものだからの。

これにより、

```text id="6grm6s"
W1 overlaps W2
```

と

```text id="u5d6iz"
W2 overlaps W1
```

を同じ obstruction として扱いやすくなった。

## 3. `not_recoverable_by_swap` が核心

今回の中で一番良い theorem はこれじゃ。

```lean id="pw2kjg"
SourcePressureLocalIslandWitnessPairOverlapObstruction.not_recoverable_by_swap
```

意味は、

```text id="pl6orr"
overlap obstruction があるなら、
[W2, W1] に swap しても sorted にはならない
```

じゃ。

これで failure branch は完全に性格が分かれた。

```text id="kbnqmv"
reverse failure:
  swap で回復できる

overlap failure:
  swap では回復できない
```

これは Core / Gap の切り分けとしてかなり強い。

## レビュー

## 採用理由

今回の採用理由は明確じゃ。

第一に、overlap branch が named obstruction になった。

```lean id="9dfpqm"
def SourcePressureLocalIslandWitnessPairOverlapObstruction
```

中身は、

```text id="o9s9qr"
[W1, W2] has sorted-before failure
and
W1 overlaps W2
```

という最小構造。余計な merge や union accounting を含めていない。

第二に、constructor / projection が揃っている。

```lean id="0fhkb9"
mk_of_failure_overlap
failure
overlap
```

これは後続で扱いやすい。

第三に、diagnostic が揃っている。

```lean id="4gkcqm"
not_before
not_reverseBefore
not_recoverable_by_swap
```

これで obstruction の性質が明確になった。

第四に、recovered-or-obstruction split が入った。

```lean id="i65t9h"
sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlapObstruction
```

これで、pair failure を見たとき、

```text id="t5np41"
回収可能な reverse branch
または
未回収 overlap obstruction
```

として使える。

これはかなり実用的じゃ。

## 注意点

## 1. overlap obstruction はまだ処理していない

これは正しい。
今回の checkpoint は、overlap を「未処理」として分離する段階じゃ。

まだ次は言っていない。

```text id="o2obp5"
overlap を merge する
overlap を split する
union accounting を作る
coverage を出す
maximal family を作る
```

ここへはまだ進まない方がよい。

## 2. pair 限定である

今回も二点 pair の話じゃ。

まだ任意 list ではない。

```text id="e2rohp"
[W1, W2]
```

についてはかなり閉じたが、

```text id="qsryuz"
[W1, W2, W3, ...]
```

の sorting / obstruction classification はまだ先。

この境界は維持するべし。

## 解説

今回の theorem 群を一言で言うと、

```text id="b6v9vj"
overlap は、逆順とは違う本物の局所障害である
```

を Lean に入れた、ということじゃ。

逆順なら、ただ順番を変えればよい。

```text id="0jujzs"
[W1, W2] failed
but W2 before W1
  -> [W2, W1] sorted
  -> budget recovered
```

しかし overlap なら、順番を変えても直らない。

```text id="nnwr9m"
[W1, W2] overlaps
[W2, W1] also overlaps
neither order is before
```

だから、overlap branch は accounting 上の本物の Gap になる。

ここでようやく、DkMath 的な構図が実装上も見えてきた。

```text id="wqi3rw"
Core:
  sorted accounting
  reverse-recovered accounting

Gap:
  overlap obstruction
```

これはよい進展じゃ。

## 一歩先ゆく推論

次は、report の Next Inference にもあるように、obstruction から **両方向の list failure** を取り出す小 API がよい。

今あるのは、

```lean id="xo79np"
not_before
not_reverseBefore
not_recoverable_by_swap
```

じゃ。

次に欲しいのは、

```text id="u0gnni"
[W1, W2] has sorted-before failure
[W2, W1] has sorted-before failure
```

を直接出す theorem じゃ。

前者は obstruction の `failure` projection で出る。
後者は overlap の `not_reverseBefore` と pair failure iff から出せる。

これがあると、overlap obstruction は「どちら向きの pair list でも failure」として、さらに扱いやすくなる。

## さらなる次の一手

Checkpoint 163 が通ったら、その次は obstruction の **symmetry** を考えるとよい。

今の obstruction は、

```text id="cqnni8"
failure [W1, W2] ∧ overlap W1 W2
```

なので、順序つき obstruction じゃ。

しかし overlap 自体は対称。
さらに `[W2, W1]` も failure であることが出れば、

```text id="y1rhh6"
obstruction W1 W2
  -> obstruction W2 W1
```

が言える可能性がある。

これはかなり良い。
なぜなら、overlap obstruction が順序に依存しない「本物の重なり障害」として扱えるからじゃ。

候補は次の checkpoint のさらに次。

```lean id="ib2gqv"
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.symm
```

ただし、まずは両方向 failure projection を作ってからの方が安全じゃ。

## 賢狼が試して欲しい実験補題

## 実験補題 A: obstruction gives original list failure

これは projection でもうあるが、名前を少し実用寄りにしてもよい。

```lean id="udg99v"
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.hasFailure
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2] :=
  hobs.failure
```

既存の `failure` projection で足りるなら不要。

## 実験補題 B: obstruction gives swapped list failure

これが本命じゃ。

```lean id="wp0jsq"
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.swap_failure
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W2, W1] := by
  exact
    sourcePressureLocalIslandWitnessListHasSortedBeforeFailure_pair_iff.2
      hobs.not_reverseBefore
```

通るはずじゃ。

## 実験補題 C: obstruction gives not sorted original

```lean id="gbypfg"
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.not_sorted
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
    ¬ SourcePressureLocalIslandWitnessListSortedBefore [W1, W2] := by
  intro hsorted
  have hbefore : SourcePressureLocalIslandWitnessBefore W1 W2 :=
    sourcePressureLocalIslandWitnessListSortedBefore_pair_iff.1 hsorted
  exact hobs.not_before hbefore
```

## 実験補題 D: obstruction gives not sorted swapped

これは既に `not_recoverable_by_swap` と同じ意味じゃが、名前の用途で alias を置いてもよい。

```lean id="jbohmk"
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.not_sorted_swap
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
    ¬ SourcePressureLocalIslandWitnessListSortedBefore [W2, W1] :=
  hobs.not_recoverable_by_swap
```

## 実験補題 E: obstruction symmetry

両方向 failure が取れれば、これも試せる。

```lean id="6jy6pt"
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.symm
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
    SourcePressureLocalIslandWitnessPairOverlapObstruction W2 W1 :=
  ⟨
    SourcePressureLocalIslandWitnessPairOverlapObstruction.swap_failure hobs,
    SourcePressureLocalIslandWitnessOverlap.symm hobs.overlap
  ⟩
```

これは通る可能性が高い。

## 次の Codex 指示

```text id="m5dxx9"
Checkpoint 163: Main root only — overlap obstruction projections and symmetry.

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
Checkpoint 162 added overlap obstruction API:

- NatIntervalsOverlap.symm
- SourcePressureIntervalPulseAddressOverlap.symm
- SourcePressureLocalIslandWitnessOverlap.symm
- SourcePressureIntervalPulseAddressOverlap.not_before
- SourcePressureIntervalPulseAddressOverlap.not_reverseBefore
- SourcePressureLocalIslandWitnessOverlap.not_before
- SourcePressureLocalIslandWitnessOverlap.not_reverseBefore
- SourcePressureLocalIslandWitnessPairOverlapObstruction
- SourcePressureLocalIslandWitnessPairOverlapObstruction.mk_of_failure_overlap
- SourcePressureLocalIslandWitnessPairOverlapObstruction.failure
- SourcePressureLocalIslandWitnessPairOverlapObstruction.overlap
- SourcePressureLocalIslandWitnessPairOverlapObstruction.not_before
- SourcePressureLocalIslandWitnessPairOverlapObstruction.not_reverseBefore
- SourcePressureLocalIslandWitnessPairOverlapObstruction.not_recoverable_by_swap
- sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlapObstruction

Global rules:
- Do not claim maximality.
- Do not claim uniqueness of pressure families.
- Do not claim coverage.
- Do not claim prefix behavior.
- Do not claim union accounting.
- Do not claim Collatz convergence.
- Keep all statements local to explicitly supplied witness pairs.
- Reverse branch is already recovered by swapped sorted accounting.
- Overlap branch remains an obstruction.
- Do not merge intervals or prove union accounting in this checkpoint.

Main goal:
Make the overlap obstruction easier to consume by exposing both-direction
failure/not-sorted diagnostics and symmetry.

Part A: swapped-list failure from overlap obstruction.

Prove:

  theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.swap_failure
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W2, W1]

Suggested proof:
- use sourcePressureLocalIslandWitnessListHasSortedBeforeFailure_pair_iff.2
- use hobs.not_reverseBefore

Part B: not-sorted diagnostics.

Prove:

  theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.not_sorted
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
      ¬ SourcePressureLocalIslandWitnessListSortedBefore [W1, W2]

Suggested proof:
- intro hsorted
- convert hsorted to before using sourcePressureLocalIslandWitnessListSortedBefore_pair_iff.1
- contradict with hobs.not_before

Prove:

  theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.not_sorted_swap
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
      ¬ SourcePressureLocalIslandWitnessListSortedBefore [W2, W1]

This can be an alias of:
  SourcePressureLocalIslandWitnessPairOverlapObstruction.not_recoverable_by_swap

Part C: obstruction symmetry.

Prove:

  theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.symm
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
      SourcePressureLocalIslandWitnessPairOverlapObstruction W2 W1

Suggested proof:
- constructor
- first field: use swap_failure hobs
- second field: use SourcePressureLocalIslandWitnessOverlap.symm hobs.overlap

Part D: optional iff-style symmetry.

Only if easy, prove:

  theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.symm_iff
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r} :
      SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2 ↔
        SourcePressureLocalIslandWitnessPairOverlapObstruction W2 W1

Use `.symm` both ways.

Part E: do not handle overlap merge.

Do not add merge/split/union accounting.
Do not construct merged intervals or families.
Do not claim coverage, maximality, or convergence.

Part F: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-163.md

Include:
- swapped-list failure theorem,
- not-sorted diagnostics,
- obstruction symmetry theorem,
- optional iff theorem if added,
- explicit note that overlap obstruction is order-independent after symmetry,
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

Checkpoint 163 が通ったら、次は **obstruction cluster の最小入口** じゃ。

今は pair obstruction。
次は list の中に overlap obstruction pair があることを表す。

候補は、

```lean id="2xdpiv"
def SourcePressureLocalIslandWitnessListHasOverlapObstruction
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
  ∃ W1 ∈ L, ∃ W2 ∈ L,
    W1 ≠ W2 ∧
      SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2
```

ただし、`W1 ≠ W2` は subtype equality がやや重いかもしれぬ。
最初は adjacent pair だけに限定した方が安全じゃ。

```lean id="1fycde"
def SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
```

既存の sorted-before failure は adjacent pair ベースなので、こちらの方が自然。

次の山は、

```text id="l3aw7d"
list failure
  -> adjacent reverse recoverable
  or adjacent overlap obstruction
```

じゃ。

これが通ると、pair から list へ一段上がる。

## 総評

Checkpoint 162 は、pair failure の局所診断としてかなり強い。

```text id="h6zc6j"
reverse:
  recovered

overlap:
  obstruction
  symmetric
  not recoverable by swap
```

ここまで来れば、pair failure の Core 分解はほぼ完成じゃ。

次は obstruction の両方向性を整えて、その次に list-level obstruction へ上げる。
これで PressureAccounting は、単なる budget theorem 群から **局所 failure 診断エンジン** に進化してきておる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
index 1f11e802..e685bab1 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -717,6 +717,13 @@ proved only after both ordered directions are ruled out.
 def NatIntervalsOverlap (a lenA b lenB : ℕ) : Prop :=
   a < b + lenB ∧ b < a + lenA

+/-- Natural interval overlap is symmetric. -/
+theorem NatIntervalsOverlap.symm
+    {a lenA b lenB : ℕ}
+    (h : NatIntervalsOverlap a lenA b lenB) :
+    NatIntervalsOverlap b lenB a lenA :=
+  ⟨h.2, h.1⟩
+
 /-- Ordered non-overlap implies ordinary interval disjointness. -/
 theorem NatIntervalsDisjoint.of_before
     {a len b len' : ℕ}
@@ -850,6 +857,14 @@ def SourcePressureIntervalPulseAddressOverlap
     (A B : SourcePressureIntervalPulseAddress n k r) : Prop :=
   NatIntervalsOverlap A.start A.len B.start B.len

+/-- Address-level overlap is symmetric. -/
+theorem SourcePressureIntervalPulseAddressOverlap.symm
+    {n : OddNat} {k r : ℕ}
+    {A B : SourcePressureIntervalPulseAddress n k r}
+    (h : SourcePressureIntervalPulseAddressOverlap A B) :
+    SourcePressureIntervalPulseAddressOverlap B A :=
+  NatIntervalsOverlap.symm h
+
 /-- A before relation between pulse addresses excludes address overlap. -/
 theorem SourcePressureIntervalPulseAddressOverlap.not_of_before
     {n : OddNat} {k r : ℕ}
@@ -866,6 +881,24 @@ theorem SourcePressureIntervalPulseAddressOverlap.not_of_reverseBefore
     ¬ SourcePressureIntervalPulseAddressOverlap A B :=
   NatIntervalsOverlap.not_of_reverseBefore hbefore

+/-- Address overlap excludes the forward before relation. -/
+theorem SourcePressureIntervalPulseAddressOverlap.not_before
+    {n : OddNat} {k r : ℕ}
+    {A B : SourcePressureIntervalPulseAddress n k r}
+    (h : SourcePressureIntervalPulseAddressOverlap A B) :
+    ¬ SourcePressureIntervalPulseAddressBefore A B := by
+  intro hbefore
+  exact SourcePressureIntervalPulseAddressOverlap.not_of_before hbefore h
+
+/-- Address overlap excludes the reverse before relation. -/
+theorem SourcePressureIntervalPulseAddressOverlap.not_reverseBefore
+    {n : OddNat} {k r : ℕ}
+    {A B : SourcePressureIntervalPulseAddress n k r}
+    (h : SourcePressureIntervalPulseAddressOverlap A B) :
+    ¬ SourcePressureIntervalPulseAddressBefore B A := by
+  intro hbefore
+  exact SourcePressureIntervalPulseAddressOverlap.not_of_reverseBefore hbefore h
+
 /--
 If neither pulse address is before the other, then their explicit half-open
 address intervals overlap.
@@ -1868,6 +1901,14 @@ def SourcePressureLocalIslandWitnessOverlap
     (sourcePressureIntervalPulseAddress_of_localIslandWitness W1)
     (sourcePressureIntervalPulseAddress_of_localIslandWitness W2)

+/-- Witness-level overlap is symmetric. -/
+theorem SourcePressureLocalIslandWitnessOverlap.symm
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureLocalIslandWitnessOverlap W1 W2) :
+    SourcePressureLocalIslandWitnessOverlap W2 W1 :=
+  SourcePressureIntervalPulseAddressOverlap.symm h
+
 /-- A witness-level before relation excludes witness-level overlap. -/
 theorem SourcePressureLocalIslandWitnessOverlap.not_of_before
     {n : OddNat} {k r : ℕ}
@@ -1884,6 +1925,24 @@ theorem SourcePressureLocalIslandWitnessOverlap.not_of_reverseBefore
     ¬ SourcePressureLocalIslandWitnessOverlap W1 W2 :=
   SourcePressureIntervalPulseAddressOverlap.not_of_reverseBefore hbefore

+/-- Witness overlap excludes the forward before relation. -/
+theorem SourcePressureLocalIslandWitnessOverlap.not_before
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureLocalIslandWitnessOverlap W1 W2) :
+    ¬ SourcePressureLocalIslandWitnessBefore W1 W2 := by
+  intro hbefore
+  exact SourcePressureLocalIslandWitnessOverlap.not_of_before hbefore h
+
+/-- Witness overlap excludes the reverse before relation. -/
+theorem SourcePressureLocalIslandWitnessOverlap.not_reverseBefore
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureLocalIslandWitnessOverlap W1 W2) :
+    ¬ SourcePressureLocalIslandWitnessBefore W2 W1 := by
+  intro hbefore
+  exact SourcePressureLocalIslandWitnessOverlap.not_of_reverseBefore hbefore h
+
 /--
 Two local-island witness intervals overlap once both ordered directions are
 ruled out.
@@ -2050,6 +2109,77 @@ theorem sourcePressureLocalIslandWitnessPair_failure_reverseBefore_or_overlap
     SourcePressureLocalIslandWitnessOverlap.reverseBefore_or_overlap_of_not_before
       h1pos h2pos hnot12

+/--
+First-class obstruction predicate for the overlap branch of a failed witness
+pair.
+
+This packages exactly two local facts: `[W1, W2]` has sorted-before failure and
+the converted witness intervals overlap.  It does not merge intervals, produce
+coverage, or recover a union-accounting family.
+-/
+def SourcePressureLocalIslandWitnessPairOverlapObstruction
+    {n : OddNat} {k r : ℕ}
+    (W1 W2 : SourcePressureLocalIslandWitness n k r) : Prop :=
+  SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2] ∧
+    SourcePressureLocalIslandWitnessOverlap W1 W2
+
+/-- Constructor for the explicit overlap-obstruction predicate. -/
+theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.mk_of_failure_overlap
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (hfail : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2])
+    (hoverlap : SourcePressureLocalIslandWitnessOverlap W1 W2) :
+    SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2 :=
+  ⟨hfail, hoverlap⟩
+
+/-- Extract the sorted-before failure from an overlap obstruction. -/
+theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.failure
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
+    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2] :=
+  h.1
+
+/-- Extract the witness overlap from an overlap obstruction. -/
+theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.overlap
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
+    SourcePressureLocalIslandWitnessOverlap W1 W2 :=
+  h.2
+
+/-- An overlap obstruction still blocks the original order. -/
+theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.not_before
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
+    ¬ SourcePressureLocalIslandWitnessBefore W1 W2 :=
+  SourcePressureLocalIslandWitnessOverlap.not_before h.overlap
+
+/-- An overlap obstruction also blocks the swapped order. -/
+theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.not_reverseBefore
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
+    ¬ SourcePressureLocalIslandWitnessBefore W2 W1 :=
+  SourcePressureLocalIslandWitnessOverlap.not_reverseBefore h.overlap
+
+/--
+An overlap obstruction cannot be repaired merely by swapping the two witnesses.
+
+This is the key diagnostic distinction from the reverse branch: reverse order
+is recoverable by swapping, but overlap is not.
+-/
+theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.not_recoverable_by_swap
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
+    ¬ SourcePressureLocalIslandWitnessListSortedBefore [W2, W1] := by
+  intro hsorted
+  have hrev : SourcePressureLocalIslandWitnessBefore W2 W1 :=
+    sourcePressureLocalIslandWitnessListSortedBefore_pair_iff.1 hsorted
+  exact SourcePressureLocalIslandWitnessOverlap.not_reverseBefore hobs.overlap hrev
+
 /--
 Reverse-recovery helper for a pair whose failure reason is merely reversed
 order.
@@ -2294,6 +2424,33 @@ theorem sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlap
           W1 W2 hrev⟩
   · exact Or.inr hoverlap

+/--
+Recovered-or-obstruction split for a failed two-witness order.
+
+The left branch is the recovered reversed-order budget.  The right branch is a
+first-class overlap obstruction, keeping the overlap branch explicit and
+unmerged.
+-/
+theorem sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlapObstruction
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
+    ∨ SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2 := by
+  rcases sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlap
+      h1pos h2pos hfail with hrecovered | hoverlap
+  · exact Or.inl hrecovered
+  · exact Or.inr
+      (SourcePressureLocalIslandWitnessPairOverlapObstruction.mk_of_failure_overlap
+        hfail hoverlap)
+
 /--
 Raw-argument version of the sorted pair budget.
 -/
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-162.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-162.md
new file mode 100644
index 00000000..2927d9a6
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-162.md
@@ -0,0 +1,186 @@
+# Report Petal 162
+
+## Checkpoint
+
+Checkpoint 162 stayed on the main Collatz/PetalBridge root and gave the
+overlap branch a first-class obstruction predicate.
+
+Modified implementation file:
+
+- `DkMath/Collatz/PetalBridge/PressureAccounting.lean`
+
+No `OneCycle`, `ValuationFlowBridge`, `ABC`, or `NumberTheory` files were
+modified.
+
+## Overlap Symmetry
+
+Overlap symmetry was added at all three intended layers.
+
+```lean
+theorem NatIntervalsOverlap.symm
+theorem SourcePressureIntervalPulseAddressOverlap.symm
+theorem SourcePressureLocalIslandWitnessOverlap.symm
+```
+
+These are purely local symmetry facts for two supplied intervals, addresses,
+or witnesses.
+
+## Before-Exclusion Diagnostics
+
+Address-level diagnostics were added:
+
+```lean
+theorem SourcePressureIntervalPulseAddressOverlap.not_before
+theorem SourcePressureIntervalPulseAddressOverlap.not_reverseBefore
+```
+
+Witness-level diagnostics were added:
+
+```lean
+theorem SourcePressureLocalIslandWitnessOverlap.not_before
+theorem SourcePressureLocalIslandWitnessOverlap.not_reverseBefore
+```
+
+These make the intended obstruction reading explicit:
+
+```text
+overlap
+  -> not forward before
+  -> not reverse before
+```
+
+Therefore overlap cannot be repaired by simply swapping the pair.
+
+## Overlap Obstruction Predicate
+
+The first-class pair obstruction predicate was added.
+
+```lean
+def SourcePressureLocalIslandWitnessPairOverlapObstruction
+```
+
+It packages exactly:
+
+```text
+SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]
+and
+SourcePressureLocalIslandWitnessOverlap W1 W2
+```
+
+Constructor and projections:
+
+```lean
+theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.mk_of_failure_overlap
+theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.failure
+theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.overlap
+```
+
+Additional diagnostics:
+
+```lean
+theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.not_before
+theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.not_reverseBefore
+theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.not_recoverable_by_swap
+```
+
+The last theorem is the important distinction from the reverse branch:
+
+```text
+reverse branch:
+  swapping recovers sorted accounting
+
+overlap branch:
+  swapping cannot recover sortedness
+```
+
+## Recovered-or-Obstruction Split
+
+The recovered-or-obstruction theorem was added.
+
+```lean
+theorem sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlapObstruction
+```
+
+It refines the previous recovered-or-overlap split by wrapping the overlap
+branch as a named obstruction:
+
+```text
+pair failure
+  -> reversed recovered accounting with sum <= -2
+  or overlap obstruction
+```
+
+## Boundary Notes
+
+Overlap remains unmerged and unhandled.
+
+This checkpoint does not:
+
+- merge intervals,
+- split intervals,
+- construct a merged family,
+- prove union accounting,
+- prove coverage,
+- assert maximality,
+- assert uniqueness,
+- assert prefix behavior,
+- assert Collatz convergence.
+
+All statements remain local to explicitly supplied witness pairs.
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
+The pair failure split is now structurally clear:
+
+```text
+recoverable reversed branch
+unrecoverable overlap obstruction branch
+```
+
+The next safe direction is not union accounting.  A better next step is to add
+small API around the obstruction branch, such as projections from obstruction
+to both list failures:
+
+```text
+[W1, W2] not sorted
+[W2, W1] not sorted
+```
+
+This would keep overlap obstruction isolated while making it easier for later
+merge/split experiments to consume.
````
`````
