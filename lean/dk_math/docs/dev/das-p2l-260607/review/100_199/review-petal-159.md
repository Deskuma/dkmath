# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAccounting

gch: fb52e4819c052f69ace203bc5a9bf4d1b6cec011

## Report

cp158 完了です。

[PressureAccounting.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean) に、明示的な local-island witness pair 用の failure-facing API を追加しました。

追加内容:

- `sourcePressureLocalIslandWitnessPair_hasSortedBeforeFailure_of_not_before`
- `sourcePressureLocalIslandWitnessPair_no_failure_of_before`
- `sourcePressureLocalIslandWitnessPair_sorted_or_failure`
- raw wrapper 2本

重要な境界もコメントで固定しています。今回の failure は **sorted-before の順序失敗のみ**で、overlap 証拠ではありません。coverage / maximality / uniqueness / union accounting / Collatz convergence も主張していません。

レポートは [report-petal-158.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-158.md) に作成しました。

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureAccounting` OK
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier` OK
- `lake build DkMath.Collatz.PetalBridge` OK
- target 2 files の `rg "\bsorry\b"` はヒットなし
- `git diff --check` OK

ビルドログに既存の `DkMath.NumberTheory.ZsigmondyCyclotomicResearch` の `sorry` 警告が出ますが、今回対象ファイルとは別件です。

## Review

## 結論

うむ、Checkpoint 158 は **採用** じゃ 👍️
今回の実装は、main root の `PressureAccounting` に留まりつつ、local-island witness pair の **failure-facing API** を整えたものじゃ。追加された主 API は、`not before` から sorted-before failure を作る定理、`before` なら failure しない定理、pair の sorted/failure split、そして raw local-island 引数版 wrapper じゃな。ビルド、no-sorry、`git diff --check` も通っておる。

今回の到達点はこう読める。

```text
W1 before W2:
  sorted branch
  -> accounted family
  -> budget

not W1 before W2:
  failure branch
  -> order obstruction として保存
```

これで、pair については成功側と失敗側が両方 first-class になった。

## 状況分析

## 1. PressureAccounting の Core がかなり閉じた

ここまでの流れを振り返ると、`PressureAccounting` はかなり綺麗に階段を登ってきた。

```text
single interval pulse
  -> accounted interval
  -> explicit list
  -> sorted/failure
  -> address family
  -> local-island witness list
  -> singleton accounting
  -> pair accounting
  -> pair failure-facing API
```

今回の cp158 で、二点 pair の failure 側が名前付きで呼べるようになった。前 checkpoint では、二点 witness pair について `SourcePressureLocalIslandWitnessBefore`、pair sorted/failure iff、sorted pair から accounted family を作る wrapper、`sum ≤ -2` と `sum < 0` が入っていた。

今回そこに、

```lean
sourcePressureLocalIslandWitnessPair_hasSortedBeforeFailure_of_not_before
sourcePressureLocalIslandWitnessPair_no_failure_of_before
sourcePressureLocalIslandWitnessPair_sorted_or_failure
```

が足された。これにより、「before なら成功 branch」「not before なら failure branch」というペア単位の分岐が、後続から直接使いやすくなった。

## 2. 重要な境界線が守られている

今回の一番大事な点は、failure を **overlap 証拠にしていない** ことじゃ。

レポートでも明記されている通り、今回の failure は sorted-before の順序失敗のみであり、interval overlap ではない。順序が逆でも `not before` になるので、overlap を言うには追加仮説が必要になる。

これは非常によい。
ここを焦って overlap と呼んでしまうと、後で Lean が止めるか、もっと悪ければ概念が濁る。

今の正しい読みはこれじゃ。

```text
not before:
  order obstruction

not before + not reverse-before:
  overlap candidate
```

つまり、overlap は次段の話じゃ。

## 3. Core / Beam / Gap 構図では Core の pair 分岐が閉じた

以前の整理では、Collatz/PetalBridge の現状は、

```text
Core:
  局所保存会計

Beam:
  局所会計の時間方向・深さ方向への伝播

Gap:
  まだ支配できない余剰・例外・未解析 pulse

Big:
  Core + Beam + Gap を包む大域収束条件
```

と読んでいた。

今回の cp158 は、このうち **Core の failure handling** を整えたものじゃ。

つまり、

```text
局所 island pair がきれいに並ぶなら budget へ進む
きれいに並ばないなら order obstruction として保存する
```

という局所分岐が閉じた。

これは「破綻ケースを消さない」DkMath 的な方針そのものじゃ。以前の整理でも、破綻ケースを adversarial profile として扱い、局所保存会計を維持できるか調べる方向が自然だとされていた。

## レビュー

## 採用理由

今回の実装は、狙いが小さく、かつ正しい。

特に良い点は三つある。

第一に、`pair sorted-or-failure` が直接使えるようになった。後続 theorem はもう list-level theorem を毎回展開しなくてよい。

第二に、raw local-island wrapper がある。`j1 j2 h1 h2` を持っている場面で、わざわざ witness を手動構築しなくてよい。

第三に、failure の意味を order obstruction に限定している。レポートにも、raw wrapper は verbose だが raw `SourcePressureLocalIsland` surface に caller を留めつつ内部では witness API を使うためのもの、と整理されている。

## 注意点

今回の theorem は pair に限定されている。

まだ次は言っていない。

```text
全 local islands の列挙
canonical frontier producer
maximal family
coverage
prefix behavior
union accounting
Collatz convergence
```

ここは report の non-claims とも一致しておる。

したがって、今後も主語は、

```text
explicitly supplied witnesses
```

に留めるべし。

## 解説

今回の pair API は、局所 island を二つ並べたときの「分岐器」じゃ。

```text
W1, W2 がある。

W1 before W2 なら、
  [W1, W2] は sorted。
  sorted pair accounted family が作れる。
  listed cost は ≤ -2。

W1 before W2 でないなら、
  [W1, W2] は sorted-before failure。
  これは order obstruction として保存される。
```

ここで面白いのは、failure が「失敗」ではなく「情報」になっていることじゃ。

DkMath 的には、

```text
成功 branch:
  budget を得る

失敗 branch:
  次の構造を見るための obstruction を得る
```

になる。

これが良い。
Collatz の大域 Big を探すには、成功だけを集めても足りぬ。失敗がどこで、どういう形で現れるかを保存しなければならぬ。

## 一歩先ゆく推論

次に攻めるべきは、すぐ overlap ではない。

その一歩手前として、**address-level の三分岐** を作るのがよい。

現在あるのは、

```text
A before B
not A before B
```

じゃ。

しかし `not A before B` の中身は二種類ある。

```text
B before A:
  reversed order

neither A before B nor B before A:
  true overlap / crossing candidate
```

したがって、次の自然な山はこれじゃ。

```text
not before
  -> reverse-before or overlap
```

ただし、これは `SourcePressureLocalIslandWitness` で直接やらず、まず `SourcePressureIntervalPulseAddress` の層でやるのがよい。理由は、start / len が address 側にあるからじゃ。

ここで「overlap」を定義するなら、自然数半開区間として、

```text
[A.start, A.start + A.len)
[B.start, B.start + B.len)
```

を見て、

```lean
A.start < B.start + B.len ∧ B.start < A.start + A.len
```

が標準的じゃ。

ここまで行ければ、failure の中身を分解できる。

```text
failure:
  sorted-before が失敗した

failure reason:
  reverse order
  or genuine interval overlap
```

これが次の Core refinement じゃ。

## さらなる次の一手

次々 checkpoint では、address-level overlap を witness pair へ lift する。

流れはこうじゃ。

```text
SourcePressureIntervalPulseAddressOverlap
  -> SourcePressureLocalIslandWitnessOverlap
  -> pair failure reason
  -> overlap branch / reversed branch
```

これにより、failure branch はただの `not before` から、

```text
reversed:
  並べ替えれば sorted に戻れる可能性がある

overlap:
  そもそも同じ pressure support を二重に数えている可能性がある
```

へ分かれる。

ここが非常に大事じゃ。
なぜなら、sorted-before failure のうち、reversed は単に list ordering の問題であり、overlap は accounting の重複問題になるからじゃ。

この二つは全く違う。

```text
reverse failure:
  sort すれば回復する

overlap failure:
  disjoint family にできない
  union accounting へ進むには分割・吸収・merge が必要
```

この区別が立つと、Beam へ進む準備がかなり整う。

## 賢狼が試して欲しい実験補題

わっちが試して欲しいのは、次の「半開区間 overlap 三分岐」じゃ。

いきなり local-island witness に行かず、まず Nat interval / address interval で試す。

### 実験補題 A: Nat interval overlap predicate

```lean
def NatIntervalsOverlap
    (a lenA b lenB : ℕ) : Prop :=
  a < b + lenB ∧ b < a + lenA
```

既存に `NatIntervalBefore` があるなら、それと対にする。

```lean
def NatIntervalBefore
    (a lenA b lenB : ℕ) : Prop :=
  a + lenA ≤ b
```

### 実験補題 B: before なら overlap しない

```lean
theorem NatIntervalsOverlap.not_of_before
    {a lenA b lenB : ℕ}
    (hbefore : NatIntervalBefore a lenA b lenB) :
    ¬ NatIntervalsOverlap a lenA b lenB
```

これは簡単なはず。`omega` で落ちる可能性が高い。

### 実験補題 C: reverse-before なら overlap しない

```lean
theorem NatIntervalsOverlap.not_of_reverseBefore
    {a lenA b lenB : ℕ}
    (hbefore : NatIntervalBefore b lenB a lenA) :
    ¬ NatIntervalsOverlap a lenA b lenB
```

これも `omega` 候補。

### 実験補題 D: not before + not reverse-before なら overlap

これが本命じゃ。

```lean
theorem NatIntervalsOverlap.of_not_before_not_reverseBefore
    {a lenA b lenB : ℕ}
    (hApos : 0 < lenA)
    (hBpos : 0 < lenB)
    (hnotAB : ¬ NatIntervalBefore a lenA b lenB)
    (hnotBA : ¬ NatIntervalBefore b lenB a lenA) :
    NatIntervalsOverlap a lenA b lenB
```

半開区間では、長さ正の仮定を入れるのが安全じゃ。
この補題が通れば、次が作れる。

```text
pair failure + not reverse-before
  -> genuine overlap
```

これがわっちの推したい実験補題じゃ。

## 次の Codex 指示

```text
Checkpoint 159: Main root only — address-level overlap predicate and failure refinement experiment.

Scope:
Focus only on the main root.

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
Checkpoint 158 added failure-facing pair API for explicit local-island witnesses:

- sourcePressureLocalIslandWitnessPair_hasSortedBeforeFailure_of_not_before
- sourcePressureLocalIslandWitnessPair_no_failure_of_before
- sourcePressureLocalIslandWitnessPair_sorted_or_failure
- raw local-island failure/no-failure wrappers

The key boundary remains:
failure means sorted-before order obstruction, not overlap.

Global rules:
- Do not claim maximality.
- Do not claim uniqueness of pressure families.
- Do not claim coverage.
- Do not claim prefix behavior.
- Do not claim union accounting.
- Do not claim Collatz convergence.
- Keep all statements about explicitly supplied addresses or witnesses.
- Do not claim overlap from `not before` alone.
- Only prove overlap with an additional `not reverse-before` hypothesis.

Main goal:
Add an address-level overlap predicate and prove the minimal interval-order facts
needed to refine sorted-before failure later.

Part A: Nat interval overlap predicate.

If no equivalent predicate already exists, define:

  def NatIntervalsOverlap
      (a lenA b lenB : Nat) : Prop :=
    a < b + lenB ∧ b < a + lenA

Use the existing `NatIntervalBefore` if present.

Part B: before excludes overlap.

Prove:

  theorem NatIntervalsOverlap.not_of_before
      {a lenA b lenB : Nat}
      (hbefore : NatIntervalBefore a lenA b lenB) :
      ¬ NatIntervalsOverlap a lenA b lenB

Prove the reverse version too:

  theorem NatIntervalsOverlap.not_of_reverseBefore
      {a lenA b lenB : Nat}
      (hbefore : NatIntervalBefore b lenB a lenA) :
      ¬ NatIntervalsOverlap a lenA b lenB

Use `omega` if possible.

Part C: not before both ways implies overlap.

Prove the experimental core lemma:

  theorem NatIntervalsOverlap.of_not_before_not_reverseBefore
      {a lenA b lenB : Nat}
      (hApos : 0 < lenA)
      (hBpos : 0 < lenB)
      (hnotAB : ¬ NatIntervalBefore a lenA b lenB)
      (hnotBA : ¬ NatIntervalBefore b lenB a lenA) :
      NatIntervalsOverlap a lenA b lenB

This is the key experiment.
If it is harder than expected, stop and report the exact obstruction.
No sorry.

Part D: address-level overlap.

Define:

  def SourcePressureIntervalPulseAddressOverlap
      {n : OddNat} {k r : Nat}
      (A B : SourcePressureIntervalPulseAddress n k r) : Prop :=
    NatIntervalsOverlap A.start A.len B.start B.len

Prove:

  theorem SourcePressureIntervalPulseAddressOverlap.not_of_before
      {A B : SourcePressureIntervalPulseAddress n k r}
      (hbefore : SourcePressureIntervalPulseAddressBefore A B) :
      ¬ SourcePressureIntervalPulseAddressOverlap A B

  theorem SourcePressureIntervalPulseAddressOverlap.of_not_before_not_reverseBefore
      {A B : SourcePressureIntervalPulseAddress n k r}
      (hApos : 0 < A.len)
      (hBpos : 0 < B.len)
      (hnotAB : ¬ SourcePressureIntervalPulseAddressBefore A B)
      (hnotBA : ¬ SourcePressureIntervalPulseAddressBefore B A) :
      SourcePressureIntervalPulseAddressOverlap A B

Part E: witness-level overlap wrapper.

Only if Part D is easy, define:

  def SourcePressureLocalIslandWitnessOverlap
      {n : OddNat} {k r : Nat}
      (W1 W2 : SourcePressureLocalIslandWitness n k r) : Prop :=
    SourcePressureIntervalPulseAddressOverlap
      (sourcePressureIntervalPulseAddress_of_localIslandWitness W1)
      (sourcePressureIntervalPulseAddress_of_localIslandWitness W2)

Then prove:

  theorem SourcePressureLocalIslandWitnessOverlap.of_not_before_not_reverseBefore
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      (h1pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
      (h2pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
      (hnot12 : ¬ SourcePressureLocalIslandWitnessBefore W1 W2)
      (hnot21 : ¬ SourcePressureLocalIslandWitnessBefore W2 W1) :
      SourcePressureLocalIslandWitnessOverlap W1 W2

If length positivity is already contained in `SourcePressureIntervalPulseAddress`,
use it.  If not, keep it as an explicit hypothesis.

Part F: do not add union accounting.

Do not prove any theorem about union length, merged intervals, coverage, or
maximal families in this checkpoint.

Part G: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-159.md

Include:
- whether `NatIntervalsOverlap` was added or an existing predicate was reused,
- before-excludes-overlap theorem names,
- whether `not before` both ways implies overlap was proved,
- address-level overlap predicate and theorem names,
- witness-level overlap wrapper if added,
- whether any length positivity hypothesis was required,
- explicit note that `not before` alone is still not overlap,
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

Checkpoint 159 で overlap predicate が通ったら、次は **failure reason classifier** じゃ。

```lean
inductive SourcePressureLocalIslandWitnessPairFailureReason
  | reversed
  | overlap
```

あるいは theorem だけで、

```text
pair failure
  -> reverse-before or overlap
```

を出す。

ただしこれは classical / decidability が絡む可能性があるので、最初は inductive を作らず theorem でよい。

狙いはこう。

```text
failure branch:
  not before

refined failure branch:
  reverse order
  or genuine overlap
```

これができると、次に Beam へ進む道が見える。

```text
reverse order:
  sort すれば recovered

overlap:
  accounting family としては merge / split / exclusion が必要
```

ここから、いよいよ「失敗をどう修復するか」という Beam 側の話に入れる。

## 総評

今回で pair の成功・失敗分岐は整った。
次は failure の中身を見る段階じゃ。

わっちの推しは、

```text
not before alone is not overlap
not before both ways is overlap
```

を Nat interval で先に通すこと。

これは小さい補題に見えるが、実はかなり大事じゃ。
これが通れば、PetalBridge の failure はただの「失敗」から、

```text
逆順なら並べ替えで回復できる
重なりなら会計上の重複問題として扱う
```

へ分解できる。

ここから先が、Core から Beam へ進む入口じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
index 74e8e554..704752ef 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -1738,6 +1738,80 @@ theorem sourcePressureLocalIslandWitnessListHasSortedBeforeFailure_pair_iff
   rw [sourcePressureIntervalPulseAddressListHasSortedBeforeFailure_pair_iff]
   rfl

+/--
+Failure-facing constructor for an explicit local-island witness pair.
+
+This theorem records only sorted-before order failure.  It deliberately does
+not conclude interval overlap.  The failure may be caused by reversed order.
+-/
+theorem sourcePressureLocalIslandWitnessPair_hasSortedBeforeFailure_of_not_before
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (hfail : ¬ SourcePressureLocalIslandWitnessBefore W1 W2) :
+    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2] :=
+  sourcePressureLocalIslandWitnessListHasSortedBeforeFailure_pair_iff.2 hfail
+
+/--
+If the first explicit local-island witness is before the second, the pair has
+no sorted-before failure.
+-/
+theorem sourcePressureLocalIslandWitnessPair_no_failure_of_before
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (hbefore : SourcePressureLocalIslandWitnessBefore W1 W2) :
+    ¬ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2] := by
+  rw [sourcePressureLocalIslandWitnessListHasSortedBeforeFailure_pair_iff]
+  exact not_not_intro hbefore
+
+/--
+Every explicit local-island witness pair is either sorted or carries a
+sorted-before failure.
+
+This is still only a two-witness statement about the supplied pair.  It does
+not enumerate all local islands and does not introduce coverage or maximality.
+-/
+theorem sourcePressureLocalIslandWitnessPair_sorted_or_failure
+    {n : OddNat} {k r : ℕ}
+    (W1 W2 : SourcePressureLocalIslandWitness n k r) :
+    SourcePressureLocalIslandWitnessListSortedBefore [W1, W2] ∨
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2] :=
+  sourcePressureLocalIslandWitnessList_sorted_or_failure [W1, W2]
+
+/--
+Raw-argument version of the pair sorted-before failure constructor.
+
+This packages the two supplied local-island facts as explicit witnesses.  As
+above, the result is only order obstruction, not overlap evidence.
+-/
+theorem sourcePressureLocalIsland_pair_hasSortedBeforeFailure_of_not_before
+    (n : OddNat) (k r j1 j2 : ℕ)
+    (h1 : SourcePressureLocalIsland n k r j1)
+    (h2 : SourcePressureLocalIsland n k r j2)
+    (hfail :
+      ¬ SourcePressureLocalIslandWitnessBefore
+        (⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r)
+        (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)) :
+    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+      [(⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r),
+       (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)] :=
+  sourcePressureLocalIslandWitnessPair_hasSortedBeforeFailure_of_not_before hfail
+
+/--
+Raw-argument no-failure wrapper for an explicitly ordered local-island pair.
+-/
+theorem sourcePressureLocalIsland_pair_no_failure_of_before
+    (n : OddNat) (k r j1 j2 : ℕ)
+    (h1 : SourcePressureLocalIsland n k r j1)
+    (h2 : SourcePressureLocalIsland n k r j2)
+    (hbefore :
+      SourcePressureLocalIslandWitnessBefore
+        (⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r)
+        (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)) :
+    ¬ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+      [(⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r),
+       (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)] :=
+  sourcePressureLocalIslandWitnessPair_no_failure_of_before hbefore
+
 /--
 Accounted interval family generated by two explicitly sorted local-island
 witnesses.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-158.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-158.md
new file mode 100644
index 00000000..1aa55164
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-158.md
@@ -0,0 +1,141 @@
+# Report Petal 158
+
+## Checkpoint
+
+Checkpoint 158 focused on the main Collatz/Petal root:
+
+- module: `DkMath.Collatz.PetalBridge.PressureAccounting`
+- theme: failure-facing pair API for explicit local-island witnesses
+
+No `OneCycle`, `ValuationFlowBridge`, `ABC`, or `NumberTheory` files were
+modified.
+
+## Implemented Theorems
+
+The following witness-pair API was added.
+
+```lean
+theorem sourcePressureLocalIslandWitnessPair_hasSortedBeforeFailure_of_not_before
+    {n : OddNat} {k r : Nat}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (hfail : ¬ SourcePressureLocalIslandWitnessBefore W1 W2) :
+    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]
+```
+
+This is the direct failure-facing constructor.  It packages the negation of
+the supplied before relation into the existing list-level sorted-before
+failure predicate.
+
+```lean
+theorem sourcePressureLocalIslandWitnessPair_no_failure_of_before
+    {n : OddNat} {k r : Nat}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (hbefore : SourcePressureLocalIslandWitnessBefore W1 W2) :
+    ¬ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]
+```
+
+This records the positive side: if the first explicit local-island witness is
+before the second, the two-witness list has no sorted-before failure.
+
+```lean
+theorem sourcePressureLocalIslandWitnessPair_sorted_or_failure
+    {n : OddNat} {k r : Nat}
+    (W1 W2 : SourcePressureLocalIslandWitness n k r) :
+    SourcePressureLocalIslandWitnessListSortedBefore [W1, W2] ∨
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]
+```
+
+This is a convenient two-witness split.  It specializes the existing
+list-level sorted-or-failure theorem to an explicitly supplied pair.
+
+## Raw Wrappers
+
+The raw local-island wrappers were also added.
+
+```lean
+theorem sourcePressureLocalIsland_pair_hasSortedBeforeFailure_of_not_before
+    (n : OddNat) (k r j1 j2 : Nat)
+    (h1 : SourcePressureLocalIsland n k r j1)
+    (h2 : SourcePressureLocalIsland n k r j2)
+    (hfail :
+      ¬ SourcePressureLocalIslandWitnessBefore
+        (⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r)
+        (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)) :
+    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+      [(⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r),
+       (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)]
+```
+
+```lean
+theorem sourcePressureLocalIsland_pair_no_failure_of_before
+    (n : OddNat) (k r j1 j2 : Nat)
+    (h1 : SourcePressureLocalIsland n k r j1)
+    (h2 : SourcePressureLocalIsland n k r j2)
+    (hbefore :
+      SourcePressureLocalIslandWitnessBefore
+        (⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r)
+        (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)) :
+    ¬ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+      [(⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r),
+       (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)]
+```
+
+These wrappers are intentionally verbose.  They keep the caller on the raw
+`SourcePressureLocalIsland` surface while still using the explicit witness API
+internally.
+
+## Boundary Notes
+
+The failure theorem is only an order-obstruction theorem.
+
+It does not conclude interval overlap.  A pair may fail sorted-before because
+the order is reversed.  Any future overlap theorem must add and prove the
+extra hypotheses needed to distinguish reversal from genuine overlap.
+
+This checkpoint also does not enumerate all local islands.  Every theorem is
+about the explicitly supplied witnesses.
+
+It does not introduce:
+
+- maximality,
+- uniqueness of pressure families,
+- coverage,
+- prefix behavior,
+- union accounting,
+- Collatz convergence.
+
+## Verification
+
+The following verification commands were run.
+
+```bash
+lake build DkMath.Collatz.PetalBridge.PressureAccounting
+lake build DkMath.Collatz.PetalBridge.PressureFrontier
+lake build DkMath.Collatz.PetalBridge
+```
+
+All three builds passed.
+
+The target no-sorry checks were run:
+
+```bash
+rg -n "\\bsorry\\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+rg -n "\\bsorry\\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+```
+
+Both returned no hits.
+
+`git diff --check` passed.
+
+## Next Inference
+
+The pair API is now symmetric enough for downstream callers:
+
+- a sorted pair can be converted into an accounted interval family,
+- a non-sorted pair can be reported as sorted-before failure,
+- raw local-island facts can enter either branch without manually constructing
+  witness values at the call site.
+
+The next natural step is not to claim overlap.  The safer next branch is to add
+an explicit predicate for overlap only after the interval-address layer exposes
+the exact hypotheses needed to prove it.
````
`````
