# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAccounting

gch: 2d3e75d792b292d2e69f9772b360713dcc4f4a6b

## Report

cp160 完了です。

[PressureAccounting.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean) に、interval / address / witness の三分岐と failure-reason split を追加しました。

追加した主な定理:

- `NatIntervalsOverlap.before_or_reverseBefore_or_overlap`
- `NatIntervalsOverlap.reverseBefore_or_overlap_of_not_before`
- `SourcePressureIntervalPulseAddressOverlap.before_or_reverseBefore_or_overlap`
- `SourcePressureIntervalPulseAddressOverlap.reverseBefore_or_overlap_of_not_before`
- `SourcePressureLocalIslandWitnessOverlap.before_or_reverseBefore_or_overlap`
- `SourcePressureLocalIslandWitnessOverlap.reverseBefore_or_overlap_of_not_before`
- `sourcePressureLocalIslandWitnessPair_failure_reverseBefore_or_overlap`

おまけで reverse recovery も追加しました:

- `sourcePressureLocalIslandWitnessPair_sorted_swap_of_reverseBefore`

これで pair failure は「逆順なら回復可能」「overlap ならまだ別処理が必要」という分岐まで Lean で固定できました。もちろん `not before` 単独から overlap は出していません。coverage / maximality / union accounting / Collatz convergence にも踏み込んでいません。

レポートは [report-petal-160.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-160.md) に作成済みです。

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureAccounting` OK
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier` OK
- `lake build DkMath.Collatz.PetalBridge` OK
- target 2 files の `rg "\bsorry\b"` はヒットなし
- `git diff --check` OK

## Review

## 結論

うむ、Checkpoint 160 は **採用** じゃ 👍️
今回で、pair failure の診断がかなり明確になった。

今回の到達点はこうじゃ。

```text id="koglfa"
pair failure
  -> reverse-before
  or overlap
```

さらに、おまけとして reverse branch から swapped sorted list へ戻す補題も入っておる。

```lean id="h6zp1n"
sourcePressureLocalIslandWitnessPair_sorted_swap_of_reverseBefore
```

これは良い。
これで failure branch の一部は、もはや失敗ではなく **並べ替えで回復可能な branch** として扱えるようになった。レポートでも「逆順なら回復可能」「overlap ならまだ別処理」と明確に整理されている。

## 状況分析

## 1. Core の failure diagnosis が一段閉じた

これまでの流れは、

```text id="1dy16t"
sorted:
  accounted family を作れる

failure:
  sorted-before が壊れた
```

だった。

Checkpoint 159 で overlap vocabulary が入り、Checkpoint 160 で trichotomy と failure-reason split が入ったことで、今はこうなった。

```text id="7a9e5x"
sorted:
  accounted family を作れる

failure:
  reverse-before なら swapped sorted へ回復できる
  overlap なら別処理が必要
```

これはかなり大きい。
`failure` が単なる否定命題ではなく、**処理方針を持つ診断結果**になった。

## 2. interval / address / witness の三層が揃った

追加された層はきれいじゃ。

```text id="pphehs"
Nat interval:
  before / reverse-before / overlap

address:
  SourcePressureIntervalPulseAddressBefore
  SourcePressureIntervalPulseAddressOverlap

witness:
  SourcePressureLocalIslandWitnessBefore
  SourcePressureLocalIslandWitnessOverlap
```

この三層を順に持ち上げたことで、後続では witness-level の theorem を呼びつつ、必要なら address-level の `start` / `len` へ戻れる。

この構造は安全じゃ。
直接 witness で overlap を定義せず、変換後 address の半開区間 overlap として読むのが正しい。

## 3. reverse recovery が Beam への入口になった

今回の追加で一番おいしいのは、実は trichotomy そのものより、

```lean id="yzz5gr"
sourcePressureLocalIslandWitnessPair_sorted_swap_of_reverseBefore
```

じゃ。

これにより、

```text id="n1owcu"
[W1, W2] は failure
しかし reason が W2 before W1
なら [W2, W1] は sorted
```

が言える。

これは **Core から Beam への橋** じゃ。
なぜなら、Beam では「局所構造をどう伝播・修復するか」が主題になるからじゃ。

逆順 failure は、壊れたのではなく、向きが違っただけ。
したがって sorted accounting へ戻せる。

一方、overlap branch は戻せない。そこには merge / split / exclusion が必要になる。

## レビュー

## 採用理由

今回の実装は、前 checkpoint の狙いをきれいに閉じている。

主な採用理由は三つ。

第一に、三分岐が Nat interval から witness まで上がっている。

```lean id="w3mq9n"
NatIntervalsOverlap.before_or_reverseBefore_or_overlap
SourcePressureIntervalPulseAddressOverlap.before_or_reverseBefore_or_overlap
SourcePressureLocalIslandWitnessOverlap.before_or_reverseBefore_or_overlap
```

第二に、failure-reason split が明示された。

```lean id="ant6om"
NatIntervalsOverlap.reverseBefore_or_overlap_of_not_before
SourcePressureIntervalPulseAddressOverlap.reverseBefore_or_overlap_of_not_before
SourcePressureLocalIslandWitnessOverlap.reverseBefore_or_overlap_of_not_before
sourcePressureLocalIslandWitnessPair_failure_reverseBefore_or_overlap
```

第三に、reverse recovery が入った。

```lean id="duhbi0"
sourcePressureLocalIslandWitnessPair_sorted_swap_of_reverseBefore
```

これらにより、pair failure は「逆順」か「overlap」へ分解され、逆順なら sorted list へ戻せるようになった。これは checkpoint として非常に良い閉じ方じゃ。

## 注意点

## 1. まだ global sorting ではない

今回の reverse recovery は、あくまで二要素 list の話じゃ。

まだ次は言っていない。

```text id="qn1pmb"
任意 list を sort できる
sorted family を canonical に作れる
全 local islands を並べられる
```

これはまだ先。

## 2. overlap branch はまだ未処理

今回 overlap は分類されたが、処理はしていない。

まだ次は言っていない。

```text id="l4wf61"
overlap interval を merge する
union length を出す
overlap を除いた budget を作る
重複なし family へ変換する
```

ここは次々以降の山じゃ。

今は overlap を **real obstruction** として保存する段階。

## 3. positivity 仮定は維持する

witness-level の theorem は、変換後 address の len positivity を明示している。

```lean id="h8edkg"
0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len
0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len
```

これは継続した方がよい。
address の実体が空でないことを、caller に明示させるのは安全じゃ。

## 解説

今回できたことを直感でいうと、二つの pressure island witness について、次の診断器ができた。

```text id="8g1eqb"
W1 before W2:
  そのまま sorted accounting へ進める

W2 before W1:
  [W1, W2] は failure だが、swap すれば sorted accounting へ進める

overlap:
  swap では解決しない
  重複 accounting の問題として残す
```

つまり、failure branch が二つに割れた。

```text id="6am52s"
repairable failure:
  reversed

nontrivial obstruction:
  overlap
```

これはかなり良い。
数学的にも実装的にも、次に何をすべきかが明確になる。

## 一歩先ゆく推論

次は、**reverse branch から実際に budget まで回収する theorem** が自然じゃ。

今あるのは、

```lean id="n915i2"
sourcePressureLocalIslandWitnessPair_sorted_swap_of_reverseBefore
```

つまり `[W2, W1]` が sorted になる、まで。

次はこれを、

```lean id="t3qqyu"
sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair W2 W1 hrev
```

へ接続し、逆順 failure だった pair からも budget を回収する。

狙いはこう。

```text id="7p38my"
[W1, W2] failure
reason = W2 before W1
  -> [W2, W1] sorted
  -> accounted family
  -> length = 2
  -> sum ≤ -2
  -> sum < 0
```

これが通ると、failure branch のうち reverse branch は完全に回収済みになる。

すると残る Gap は overlap branch だけになる。

```text id="us7a2f"
failure =
  reverse branch: recovered into Core budget
  overlap branch: still Gap
```

これは Core / Beam / Gap の整理として美しい。

## さらなる次の一手

Checkpoint 161 で reverse branch budget recovery が通ったら、次は **failure recovery theorem** を disjunction で作る。

例えば、

```text id="xqv8uz"
pair failure
  -> recovered sorted accounting family
  or overlap obstruction
```

を theorem として出す。

Lean では dependent pair を避けるなら、最初は theorem を二段に分けるのが安全じゃ。

第一段。

```lean id="l83ptw"
theorem sourcePressureLocalIslandWitnessPair_failure_recover_or_overlap
    ...
    (hfail : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]) :
    SourcePressureLocalIslandWitnessBefore W2 W1 ∨
      SourcePressureLocalIslandWitnessOverlap W1 W2
```

これは既に今回の

```lean id="k062xx"
sourcePressureLocalIslandWitnessPair_failure_reverseBefore_or_overlap
```

がある。

第二段。

```text id="wczkun"
left branch の hrev から
swapped accounted family の budget を得る
```

つまり次は theorem 名を明確にして、reverse branch を「回復済み」として閉じる。

さらにその次に、overlap branch へ進む。
overlap は merge ではなく、まず **overlap obstruction record** にするのが安全じゃ。

```lean id="js26i1"
structure SourcePressureLocalIslandWitnessPairOverlapObstruction ... where
  hfail : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]
  hoverlap : SourcePressureLocalIslandWitnessOverlap W1 W2
```

ただし structure 化は少し早いかもしれぬ。まず theorem で十分じゃ。

## 賢狼が試して欲しい実験補題

今回わっちが試して欲しいのは、**reverse recovery budget** の最短補題群じゃ。

## 実験補題 A: swapped pair accounted family constructor

```lean id="q0rxqk"
def sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
    {n : OddNat} {k r : Nat}
    (W1 W2 : SourcePressureLocalIslandWitness n k r)
    (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
    SourcePressureAccountedIntervalFamily n k r :=
  sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair
    W2 W1 hrev
```

これはただの alias だが、意味が大きい。
「reversed pair を swap して accounting へ戻す」という名前を持たせる。

## 実験補題 B: reversed pair length

```lean id="cgr2ao"
theorem sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length
    {n : OddNat} {k r : Nat}
    (W1 W2 : SourcePressureLocalIslandWitness n k r)
    (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
    (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
      W1 W2 hrev).items.length = 2
```

既存の sorted pair length で通るはずじゃ。

## 実験補題 C: reversed pair budget

```lean id="m4xf1o"
theorem sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two
    {n : OddNat} {k r : Nat}
    (W1 W2 : SourcePressureLocalIslandWitness n k r)
    (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
    (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
      W1 W2 hrev).items).map
      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2
```

## 実験補題 D: reversed pair strict negative

```lean id="6bvbe5"
theorem sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
    {n : OddNat} {k r : Nat}
    (W1 W2 : SourcePressureLocalIslandWitness n k r)
    (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
    (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
      W1 W2 hrev).items).map
      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0
```

## 実験補題 E: reversed pair items

```lean id="uz742g"
theorem sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_items
    {n : OddNat} {k r : Nat}
    (W1 W2 : SourcePressureLocalIslandWitness n k r)
    (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
    (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
      W1 W2 hrev).items =
      [ sourcePressureAccountedInterval_of_intervalPulseAddress
          (sourcePressureIntervalPulseAddress_of_localIslandWitness W2),
        sourcePressureAccountedInterval_of_intervalPulseAddress
          (sourcePressureIntervalPulseAddress_of_localIslandWitness W1) ]
```

これは `rfl` で落ちる可能性が高い。

## 実験補題 F: pair failure + reverse reason gives recovered budget

```lean id="7hkzv8"
theorem sourcePressureLocalIslandWitnessPair_failure_reversed_sum_le_neg_two
    {n : OddNat} {k r : Nat}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (hfail : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2])
    (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
    (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
      W1 W2 hrev).items).map
      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2
```

`hfail` は論理的には不要じゃが、名前の意味として「failure だったが reversed だから回復した」を残せる。Lean 的には未使用引数になるなら `_hfail` でよい。

## 次の Codex 指示

```text id="jsycxd"
Checkpoint 161: Main root only — reverse-branch recovery into sorted pair accounting.

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
Checkpoint 160 added local trichotomy and pair failure-reason split:

- NatIntervalsOverlap.before_or_reverseBefore_or_overlap
- NatIntervalsOverlap.reverseBefore_or_overlap_of_not_before
- SourcePressureIntervalPulseAddressOverlap.before_or_reverseBefore_or_overlap
- SourcePressureIntervalPulseAddressOverlap.reverseBefore_or_overlap_of_not_before
- SourcePressureLocalIslandWitnessOverlap.before_or_reverseBefore_or_overlap
- SourcePressureLocalIslandWitnessOverlap.reverseBefore_or_overlap_of_not_before
- sourcePressureLocalIslandWitnessPair_failure_reverseBefore_or_overlap
- sourcePressureLocalIslandWitnessPair_sorted_swap_of_reverseBefore

Global rules:
- Do not claim maximality.
- Do not claim uniqueness of pressure families.
- Do not claim coverage.
- Do not claim prefix behavior.
- Do not claim union accounting.
- Do not claim Collatz convergence.
- Keep all statements local to explicitly supplied witness pairs.
- Reverse branch may recover sorted accounting by swapping the pair.
- Overlap branch remains a separate obstruction.
- Do not merge intervals or prove union accounting in this checkpoint.

Main goal:
Turn the reverse-before branch of a pair failure into an explicit recovered
sorted pair accounting family and budget.

Part A: reversed pair accounted-family alias.

Define:

  def sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
      {n : OddNat} {k r : Nat}
      (W1 W2 : SourcePressureLocalIslandWitness n k r)
      (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
      SourcePressureAccountedIntervalFamily n k r :=
    sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair
      W2 W1 hrev

Comment:
This is only a two-witness local recovery by swapping.  It is not a global
sorting algorithm.

Part B: length and items.

Prove:

  theorem sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length
      {n : OddNat} {k r : Nat}
      (W1 W2 : SourcePressureLocalIslandWitness n k r)
      (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
      (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W1 W2 hrev).items.length = 2

If easy, also prove:

  theorem sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_items
      {n : OddNat} {k r : Nat}
      (W1 W2 : SourcePressureLocalIslandWitness n k r)
      (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
      (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W1 W2 hrev).items =
        [ sourcePressureAccountedInterval_of_intervalPulseAddress
            (sourcePressureIntervalPulseAddress_of_localIslandWitness W2),
          sourcePressureAccountedInterval_of_intervalPulseAddress
            (sourcePressureIntervalPulseAddress_of_localIslandWitness W1) ]

Part C: recovered budget.

Prove:

  theorem sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two
      {n : OddNat} {k r : Nat}
      (W1 W2 : SourcePressureLocalIslandWitness n k r)
      (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W1 W2 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2

Prove strict negativity:

  theorem sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
      {n : OddNat} {k r : Nat}
      (W1 W2 : SourcePressureLocalIslandWitness n k r)
      (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W1 W2 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0

Part D: explicit failure-recovery wrappers.

Add theorem wrappers where a pair failure is present but the reason is known to
be reverse order:

  theorem sourcePressureLocalIslandWitnessPair_failure_reversed_sum_le_neg_two
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      (_hfail : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2])
      (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W1 W2 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2

  theorem sourcePressureLocalIslandWitnessPair_failure_reversed_sum_neg
      ...

It is okay if `_hfail` is unused; it documents the intended use case.

Part E: do not handle overlap yet.

Do not add merge/split/union accounting.
Do not claim overlap can be recovered by swapping.
The overlap branch should remain an obstruction for a later checkpoint.

Part F: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-161.md

Include:
- reversed pair accounted-family alias,
- length theorem,
- items theorem if added,
- budget ≤ -2 theorem,
- strict negative theorem,
- failure-reversed budget wrappers,
- explicit note that reverse recovery is only two-witness local swapping,
- explicit note that overlap remains unhandled,
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

Checkpoint 161 が通ったら、次は **recovered-or-overlap split** を作るとよい。

つまり、

```text id="f6uozu"
pair failure
  -> reversed recovered accounting
  or overlap obstruction
```

を一つの theorem として出す。

Lean で dependent pair が重くなるなら、最初はこういう形が安全じゃ。

```lean id="dm96k5"
theorem sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlap
    {n : OddNat} {k r : Nat}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (h1pos : ...)
    (h2pos : ...)
    (hfail : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]) :
    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W1 W2 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
    ∨ SourcePressureLocalIslandWitnessOverlap W1 W2
```

これは少し依存型が絡むが、通ればかなり強い。

意味は、

```text id="tp8rrp"
failure しても、
逆順なら budget は回収できる。
回収できない場合は overlap obstruction として残る。
```

これで Core の pair failure 処理は一段閉じる。

## 総評

Checkpoint 160 は良い進展じゃ。
pair failure が、

```text id="nd4yds"
逆順なら回復
overlap なら未処理
```

へ分かれた。

次は逆順回復を budget まで閉じる。
それが通れば、pair failure のうち「ただの順序ミス」は Core へ戻せる。

残る overlap が、本当の Gap になる。
ここまで来ると、Core / Beam / Gap の分解がかなり実装上の形を持ちはじめるぞ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
index de00185e..f95fa9e7 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -764,6 +764,48 @@ theorem NatIntervalsOverlap.of_not_before_not_reverseBefore
   change a < b + lenB ∧ b < a + lenA
   omega
 
+/--
+Local trichotomy for two half-open natural intervals.
+
+The conclusion is intentionally local: the two supplied intervals are either
+ordered one way, ordered the other way, or overlap.  It does not say anything
+about a family of intervals, coverage, maximality, or union accounting.
+-/
+theorem NatIntervalsOverlap.before_or_reverseBefore_or_overlap
+    {a lenA b lenB : ℕ}
+    (hApos : 0 < lenA)
+    (hBpos : 0 < lenB) :
+    NatIntervalBefore a lenA b lenB ∨
+      NatIntervalBefore b lenB a lenA ∨
+        NatIntervalsOverlap a lenA b lenB := by
+  by_cases hAB : NatIntervalBefore a lenA b lenB
+  · exact Or.inl hAB
+  · by_cases hBA : NatIntervalBefore b lenB a lenA
+    · exact Or.inr (Or.inl hBA)
+    · exact Or.inr (Or.inr
+        (NatIntervalsOverlap.of_not_before_not_reverseBefore
+          hApos hBpos hAB hBA))
+
+/--
+Reason split for a failed ordered interval relation.
+
+If `a` is not before `b`, the failure is either explained by the reverse order
+or by genuine overlap.  This is the safe form of failure refinement: a single
+failed `before` is still not overlap evidence by itself.
+-/
+theorem NatIntervalsOverlap.reverseBefore_or_overlap_of_not_before
+    {a lenA b lenB : ℕ}
+    (hApos : 0 < lenA)
+    (hBpos : 0 < lenB)
+    (hnotAB : ¬ NatIntervalBefore a lenA b lenB) :
+    NatIntervalBefore b lenB a lenA ∨
+      NatIntervalsOverlap a lenA b lenB := by
+  by_cases hBA : NatIntervalBefore b lenB a lenA
+  · exact Or.inl hBA
+  · exact Or.inr
+      (NatIntervalsOverlap.of_not_before_not_reverseBefore
+        hApos hBpos hnotAB hBA)
+
 /--
 Transitive-like composition for ordered non-overlap.
 
@@ -838,6 +880,33 @@ theorem SourcePressureIntervalPulseAddressOverlap.of_not_before_not_reverseBefor
     SourcePressureIntervalPulseAddressOverlap A B :=
   NatIntervalsOverlap.of_not_before_not_reverseBefore hApos hBpos hnotAB hnotBA
 
+/-- Local trichotomy for two interval-pulse addresses. -/
+theorem SourcePressureIntervalPulseAddressOverlap.before_or_reverseBefore_or_overlap
+    {n : OddNat} {k r : ℕ}
+    {A B : SourcePressureIntervalPulseAddress n k r}
+    (hApos : 0 < A.len)
+    (hBpos : 0 < B.len) :
+    SourcePressureIntervalPulseAddressBefore A B ∨
+      SourcePressureIntervalPulseAddressBefore B A ∨
+        SourcePressureIntervalPulseAddressOverlap A B :=
+  NatIntervalsOverlap.before_or_reverseBefore_or_overlap hApos hBpos
+
+/--
+Failure-reason split for a failed address-level before relation.
+
+The failed order is either reversed, or the two supplied address intervals
+overlap.
+-/
+theorem SourcePressureIntervalPulseAddressOverlap.reverseBefore_or_overlap_of_not_before
+    {n : OddNat} {k r : ℕ}
+    {A B : SourcePressureIntervalPulseAddress n k r}
+    (hApos : 0 < A.len)
+    (hBpos : 0 < B.len)
+    (hnotAB : ¬ SourcePressureIntervalPulseAddressBefore A B) :
+    SourcePressureIntervalPulseAddressBefore B A ∨
+      SourcePressureIntervalPulseAddressOverlap A B :=
+  NatIntervalsOverlap.reverseBefore_or_overlap_of_not_before hApos hBpos hnotAB
+
 theorem sourcePressureIntervalPulseAddressBefore_iff_accountedBefore
     {n : OddNat} {k r : ℕ}
     {A B : SourcePressureIntervalPulseAddress n k r} :
@@ -1836,6 +1905,40 @@ theorem SourcePressureLocalIslandWitnessOverlap.of_not_before_not_reverseBefore
   SourcePressureIntervalPulseAddressOverlap.of_not_before_not_reverseBefore
     h1pos h2pos hnot12 hnot21
 
+/-- Local trichotomy for two explicit local-island witnesses. -/
+theorem SourcePressureLocalIslandWitnessOverlap.before_or_reverseBefore_or_overlap
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (h1pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
+    (h2pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len) :
+    SourcePressureLocalIslandWitnessBefore W1 W2 ∨
+      SourcePressureLocalIslandWitnessBefore W2 W1 ∨
+        SourcePressureLocalIslandWitnessOverlap W1 W2 :=
+  SourcePressureIntervalPulseAddressOverlap.before_or_reverseBefore_or_overlap
+    h1pos h2pos
+
+/--
+Failure-reason split for a failed witness-level before relation.
+
+This is the local diagnostic form: the failed pair order is either explained by
+the reverse order, or the converted witness intervals overlap.  It still does
+not enumerate all local islands or create a union-accounting statement.
+-/
+theorem SourcePressureLocalIslandWitnessOverlap.reverseBefore_or_overlap_of_not_before
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (h1pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
+    (h2pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
+    (hnot12 : ¬ SourcePressureLocalIslandWitnessBefore W1 W2) :
+    SourcePressureLocalIslandWitnessBefore W2 W1 ∨
+      SourcePressureLocalIslandWitnessOverlap W1 W2 :=
+  SourcePressureIntervalPulseAddressOverlap.reverseBefore_or_overlap_of_not_before
+    h1pos h2pos hnot12
+
 theorem sourcePressureLocalIslandWitnessBefore_iff_addressBefore
     {n : OddNat} {k r : ℕ}
     {W1 W2 : SourcePressureLocalIslandWitness n k r} :
@@ -1921,6 +2024,47 @@ theorem sourcePressureLocalIslandWitnessPair_sorted_or_failure
       SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2] :=
   sourcePressureLocalIslandWitnessList_sorted_or_failure [W1, W2]
 
+/--
+Refine a two-witness sorted-before failure into its local reason.
+
+For a pair, failure of `[W1, W2]` means `W1` is not before `W2`.  With positive
+converted lengths, the reason is either that the pair is reversed, or that the
+two converted witness intervals overlap.  This theorem deliberately stops
+there: it does not merge intervals or create a union-accounting family.
+-/
+theorem sourcePressureLocalIslandWitnessPair_failure_reverseBefore_or_overlap
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (h1pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
+    (h2pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
+    (hfail :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]) :
+    SourcePressureLocalIslandWitnessBefore W2 W1 ∨
+      SourcePressureLocalIslandWitnessOverlap W1 W2 := by
+  have hnot12 :
+      ¬ SourcePressureLocalIslandWitnessBefore W1 W2 :=
+    sourcePressureLocalIslandWitnessListHasSortedBeforeFailure_pair_iff.1 hfail
+  exact
+    SourcePressureLocalIslandWitnessOverlap.reverseBefore_or_overlap_of_not_before
+      h1pos h2pos hnot12
+
+/--
+Reverse-recovery helper for a pair whose failure reason is merely reversed
+order.
+
+If `W2` is before `W1`, then the swapped two-witness list is sorted.  This is
+not an overlap theorem and not a global reordering theorem; it only recovers
+the explicit two-element list.
+-/
+theorem sourcePressureLocalIslandWitnessPair_sorted_swap_of_reverseBefore
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
+    SourcePressureLocalIslandWitnessListSortedBefore [W2, W1] :=
+  sourcePressureLocalIslandWitnessListSortedBefore_pair_iff.2 hrev
+
 /--
 Raw-argument version of the pair sorted-before failure constructor.
 
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-160.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-160.md
new file mode 100644
index 00000000..9fc4f147
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-160.md
@@ -0,0 +1,196 @@
+# Report Petal 160
+
+## Checkpoint
+
+Checkpoint 160 stayed on the main Collatz/PetalBridge root and added local
+trichotomy plus failure-reason split theorems for explicit intervals,
+addresses, and local-island witnesses.
+
+Modified implementation file:
+
+- `DkMath/Collatz/PetalBridge/PressureAccounting.lean`
+
+No `OneCycle`, `ValuationFlowBridge`, `ABC`, or `NumberTheory` files were
+modified.
+
+## Nat Interval Layer
+
+The interval trichotomy theorem was added.
+
+```lean
+theorem NatIntervalsOverlap.before_or_reverseBefore_or_overlap
+```
+
+For two supplied half-open intervals, it returns:
+
+```text
+before A B
+or before B A
+or overlap A B
+```
+
+The failure-reason split was also added.
+
+```lean
+theorem NatIntervalsOverlap.reverseBefore_or_overlap_of_not_before
+```
+
+This theorem is the safe refinement of a failed ordered relation.  If `A` is
+not before `B`, the reason is either reverse order or overlap.  A single failed
+`before` relation is still not overlap evidence by itself.
+
+## Address Layer
+
+The address-level trichotomy theorem was added.
+
+```lean
+theorem SourcePressureIntervalPulseAddressOverlap.before_or_reverseBefore_or_overlap
+```
+
+The address-level failure-reason split was added.
+
+```lean
+theorem SourcePressureIntervalPulseAddressOverlap.reverseBefore_or_overlap_of_not_before
+```
+
+These theorems read only the explicit `start` and `len` fields of the supplied
+`SourcePressureIntervalPulseAddress` values.
+
+## Witness Layer
+
+The witness-level trichotomy theorem was added.
+
+```lean
+theorem SourcePressureLocalIslandWitnessOverlap.before_or_reverseBefore_or_overlap
+```
+
+The witness-level failure-reason split was added.
+
+```lean
+theorem SourcePressureLocalIslandWitnessOverlap.reverseBefore_or_overlap_of_not_before
+```
+
+These wrappers operate through the converted interval-pulse addresses:
+
+```lean
+sourcePressureIntervalPulseAddress_of_localIslandWitness W
+```
+
+The length-positivity hypotheses remain explicit:
+
+```lean
+0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len
+0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len
+```
+
+## Pair Failure Refinement
+
+The pair failure theorem was refined into a local reason split.
+
+```lean
+theorem sourcePressureLocalIslandWitnessPair_failure_reverseBefore_or_overlap
+```
+
+If `[W1, W2]` has a sorted-before failure, then with positive converted
+lengths the failure is either:
+
+```text
+W2 before W1
+or W1 overlaps W2
+```
+
+This is the desired diagnostic split:
+
+- reverse order can be handled by reordering,
+- overlap remains a real obstruction and is not solved here.
+
+## Extra Reverse Recovery
+
+The suggested next-step helper was also added because it closed cleanly.
+
+```lean
+theorem sourcePressureLocalIslandWitnessPair_sorted_swap_of_reverseBefore
+```
+
+If the pair failure is explained by reverse order, then the swapped list is
+sorted:
+
+```text
+W2 before W1
+----------------
+[W2, W1] sorted
+```
+
+This is still only a two-witness local recovery theorem.  It does not create a
+global sorting algorithm or a union-accounting family.
+
+## Boundary Notes
+
+`not before` alone is still not overlap evidence.
+
+The safe failure interpretation is:
+
+```text
+not before
+-------------------------
+reverse before or overlap
+```
+
+with explicit positivity hypotheses for the interval lengths.
+
+This checkpoint does not introduce:
+
+- maximality,
+- uniqueness of pressure families,
+- coverage,
+- prefix behavior,
+- union accounting,
+- Collatz convergence.
+
+All statements remain local to explicitly supplied intervals, addresses, or
+witnesses.
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
+See the final Codex response for the pass/fail status of the final gate.
+
+## Next Inference
+
+The next safe direction is to expose a recovery constructor:
+
+```text
+pair failure
+reverse-before branch
+--------------------------------
+build the swapped sorted pair accounting family
+```
+
+The theorem already added in this checkpoint proves the sorted swapped list.
+The next checkpoint can connect it to:
+
+```lean
+sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair W2 W1 hrev
+```
+
+and recover the existing two-interval budget for the reversed pair.  The
+overlap branch should remain separate and should not be converted into union
+accounting without new interval-merge hypotheses.
````
`````
