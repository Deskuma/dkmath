# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAccounting

gch: 9b32ffbcaea44db76eefcac23800753cfd1ba75a

## Report

cp161 完了です。

[PressureAccounting.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean) に reverse branch の回収 API を追加しました。

追加した主な定理・定義:

- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair`
- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length`
- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_items`
- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two`
- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg`
- `sourcePressureLocalIslandWitnessPair_failure_reversed_sum_le_neg_two`
- `sourcePressureLocalIslandWitnessPair_failure_reversed_sum_neg`

おまけで、次 checkpoint 候補だった recovered-or-overlap split も通ったので追加しました:

- `sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlap`

これで pair failure は「逆順なら swapped sorted accounting と `≤ -2` budget を回収」「そうでなければ overlap obstruction」として使える形になりました。overlap の merge/split/union accounting には踏み込んでいません。

レポートは [report-petal-161.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-161.md) に作成済みです。

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureAccounting` OK
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier` OK
- `lake build DkMath.Collatz.PetalBridge` OK
- target 2 files の `rg "\bsorry\b"` はヒットなし
- `git diff --check` OK

## Review

## 結論

うむ、Checkpoint 161 は **採用** じゃ 👍️
今回で、pair failure のうち **逆順 branch は budget まで回収済み** になった。

今回の主成果はこれじゃ。

```text id="o9f5sy"
pair failure
  -> reverse branch:
       swap して sorted accounting に戻す
       sum ≤ -2 を回収
  -> overlap branch:
       obstruction として残す
```

`sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlap` まで通ったのは大きい。これで、二点 local-island witness pair については、failure が単なる否定ではなく、**回収可能 branch と未処理 obstruction branch** に分かれるところまで Lean で固定できた。

## 状況分析

## 1. reverse branch は Core に戻った

前回までは、

```text id="5no0f6"
failure
  -> reversed
  or overlap
```

までだった。

今回で reversed 側が、

```text id="vdu03w"
reversed
  -> swapped sorted pair
  -> accounted family
  -> length = 2
  -> sum ≤ -2
  -> sum < 0
```

まで進んだ。

つまり、逆順 failure はもう Gap ではない。
これは **修復可能な Core branch** になった。

DkMath 的に言えば、

```text id="k17jv8"
順序が壊れただけなら、向きを直せば会計保存核に戻せる
```

ということじゃ。

## 2. overlap branch だけが本物の未処理 Gap として残った

今回の split はこうじゃ。

```lean id="rxdr8a"
theorem sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlap
```

意味は、

```text id="cyg6x1"
[W1, W2] が failure なら、
  swapped sorted accounting で budget 回収できる
または
  overlap obstruction である
```

じゃ。

これはかなり良い。
これで pair failure の未処理部分は、ほぼ overlap に圧縮された。

つまり現状の分解はこうなる。

```text id="m6c2jj"
Core:
  sorted pair accounting
  reversed pair recovered accounting

Gap:
  overlap obstruction
```

この「Gap の局所化」は大きな前進じゃ。

## 3. まだ union accounting へは踏み込んでいない

重要なのは、今回も overlap の merge / split / union accounting へは進んでいないことじゃ。レポートでも、overlap branch は未処理のまま残し、merge・split・coverage・union accounting は導入していないと明記されている。

これは正しい。
overlap は会計上の重複候補なので、いきなり budget に混ぜてはいけない。

## レビュー

## 採用理由

今回の採用理由は明確じゃ。

まず、reverse branch の alias が良い。

```lean id="h9zipc"
sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
```

これは中身としては sorted pair constructor に `W2 W1 hrev` を渡すだけだが、名前が重要じゃ。

```text id="n8noev"
reversed pair を swap して accounting に戻す
```

という意味を API 名で持てる。

次に、length / items / budget / strict negative が揃っている。

```lean id="ibkxm8"
sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length
sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_items
sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two
sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
```

ここまで揃うと、後続からは reversed pair を普通の recovered family として使える。

さらに、failure-use wrapper がある。

```lean id="ha1wjr"
sourcePressureLocalIslandWitnessPair_failure_reversed_sum_le_neg_two
sourcePressureLocalIslandWitnessPair_failure_reversed_sum_neg
```

`_hfail` が証明に使われないのは問題ではない。
むしろ「この theorem は failure branch で使う」という意味を theorem statement 側に残せている。

最後に recovered-or-overlap split が入った。
これは次 checkpoint 候補だったが、通ったなら入れて正解じゃ。

## 注意点

## 1. 二点 local recovery に限定される

今回の recovery は、

```text id="nadzvo"
[W1, W2] を [W2, W1] に swap する
```

だけじゃ。

まだ次は言っていない。

```text id="gfodsy"
任意 list を sort できる
任意 family の reversed failures を全部回収できる
canonical sorted family を生成できる
```

これはまだ先じゃ。

## 2. overlap branch はまだ危険領域

overlap branch は、まだ budget 回収していない。
これは意図通りじゃ。

overlap は、

```text id="wpiux0"
同じ interval support を二重に数えている可能性
```

なので、次に必要なのは merge ではなく、まず **obstruction として名前を与えること** じゃ。

## 3. recovered-or-overlap の存在証明は強いが、使い方に注意

`sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlap` は、

```lean id="i2t0kc"
(∃ hrev, recovered budget) ∨ overlap
```

の形じゃ。

これはかなり使いやすいが、左 branch の witness `hrev` を取り出して使う場面では、依存型の扱いが少し重くなるかもしれぬ。
後続では、必要なら左 branch 専用 theorem を増やす方が扱いやすい。

## 解説

今回の実装を一言で言えば、

```text id="lt5hds"
pair failure のうち、順序ミスだけは会計可能な形に戻した
```

じゃ。

具体的には、

```text id="5dwevd"
[W1, W2] が sorted-before failure

理由が W2 before W1 なら、
  [W2, W1] は sorted
  accounted family を作れる
  listed net drop sum ≤ -2

理由が overlap なら、
  swap では直らない
  obstruction として残す
```

これで、failure は次の二種類に分かれた。

```text id="wgi87l"
repairable failure:
  reversed

structural obstruction:
  overlap
```

これはかなり綺麗な Core 分解じゃ。

## 一歩先ゆく推論

次は、**overlap obstruction を first-class にする** のが自然じゃ。

今は recovered-or-overlap theorem の右 branch として、

```lean id="pawes0"
SourcePressureLocalIslandWitnessOverlap W1 W2
```

が出る。

しかし、これは単なる overlap であって、

```text id="4vf2as"
pair failure から残った未回収 overlap
```

という意味までは型に残っていない。

次はそこを包む。

候補は theorem でもよいが、わっちならまず軽い structure を試す。

```lean id="kylmns"
structure SourcePressureLocalIslandWitnessPairOverlapObstruction
    {n : OddNat} {k r : ℕ}
    (W1 W2 : SourcePressureLocalIslandWitness n k r) : Prop where
  fail :
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]
  overlap :
    SourcePressureLocalIslandWitnessOverlap W1 W2
```

ただし `Prop` structure にするか、通常 `structure` にするかは Lean の扱いやすさ次第じゃ。
最初は `def` で Prop にしてもよい。

```lean id="6bx5df"
def SourcePressureLocalIslandWitnessPairOverlapObstruction
    {n : OddNat} {k r : ℕ}
    (W1 W2 : SourcePressureLocalIslandWitness n k r) : Prop :=
  SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2] ∧
    SourcePressureLocalIslandWitnessOverlap W1 W2
```

これで、

```text id="za4v6m"
failure かつ overlap
```

が名前を持つ。

これが次の Gap の器になる。

## さらなる次の一手

Overlap obstruction に名前を付けたら、その次は **overlap から何が言えるか** を調べる。

ただし、まだ union accounting ではない。

最初に欲しいのは、overlap の symmetric 性じゃ。

```lean id="394xoy"
SourcePressureLocalIslandWitnessOverlap W1 W2
  -> SourcePressureLocalIslandWitnessOverlap W2 W1
```

Nat interval の overlap は対称なはずじゃ。

まず Nat で、

```lean id="pyo4lf"
theorem NatIntervalsOverlap.symm :
    NatIntervalsOverlap a lenA b lenB ->
      NatIntervalsOverlap b lenB a lenA
```

これを address / witness に lift する。

これにより、overlap obstruction は順序に依存しない「本物の重なり」として扱える。

そのあとで、overlap branch に対して、

```text id="0itzk7"
swap しても recovered しない
```

という診断補題を作れる。

例えば、

```lean id="p5jtyx"
theorem SourcePressureLocalIslandWitnessOverlap.not_before_either
```

のような方向は慎重に扱うべきじゃが、既に overlap から not before は出せる可能性がある。前 checkpoint で `not_of_before` があるので、overlap と before は矛盾する。

つまり、

```text id="2n6wtc"
overlap -> not W1 before W2
overlap -> not W2 before W1
```

が出せる。

これが通ると、overlap branch は「どちらに並べ替えても sorted にならない」ことを示せる。

これは非常に重要じゃ。

## 賢狼が試して欲しい実験補題

## 実験補題 A: Nat overlap symmetry

```lean id="vrmgpy"
theorem NatIntervalsOverlap.symm
    {a lenA b lenB : ℕ}
    (h : NatIntervalsOverlap a lenA b lenB) :
    NatIntervalsOverlap b lenB a lenA := by
  exact ⟨h.2, h.1⟩
```

これは即通るはずじゃ。

## 実験補題 B: address overlap symmetry

```lean id="hvry6p"
theorem SourcePressureIntervalPulseAddressOverlap.symm
    {n : OddNat} {k r : ℕ}
    {A B : SourcePressureIntervalPulseAddress n k r}
    (h : SourcePressureIntervalPulseAddressOverlap A B) :
    SourcePressureIntervalPulseAddressOverlap B A :=
  NatIntervalsOverlap.symm h
```

## 実験補題 C: witness overlap symmetry

```lean id="b4rlgv"
theorem SourcePressureLocalIslandWitnessOverlap.symm
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureLocalIslandWitnessOverlap W1 W2) :
    SourcePressureLocalIslandWitnessOverlap W2 W1 :=
  SourcePressureIntervalPulseAddressOverlap.symm h
```

## 実験補題 D: overlap excludes before in both directions

address-level ではすでに `not_of_before` があるので、向きを変えて使える。

```lean id="qv0j3s"
theorem SourcePressureLocalIslandWitnessOverlap.not_before
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureLocalIslandWitnessOverlap W1 W2) :
    ¬ SourcePressureLocalIslandWitnessBefore W1 W2 :=
  fun hbefore => SourcePressureLocalIslandWitnessOverlap.not_of_before hbefore h
```

reverse も。

```lean id="az5gyf"
theorem SourcePressureLocalIslandWitnessOverlap.not_reverseBefore
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureLocalIslandWitnessOverlap W1 W2) :
    ¬ SourcePressureLocalIslandWitnessBefore W2 W1 :=
  fun hbefore => SourcePressureLocalIslandWitnessOverlap.not_of_reverseBefore hbefore h
```

これで overlap branch は、どちらの順序にも回復できないことが言える。

## 実験補題 E: overlap obstruction predicate

```lean id="j8ren2"
def SourcePressureLocalIslandWitnessPairOverlapObstruction
    {n : OddNat} {k r : ℕ}
    (W1 W2 : SourcePressureLocalIslandWitness n k r) : Prop :=
  SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2] ∧
    SourcePressureLocalIslandWitnessOverlap W1 W2
```

constructor:

```lean id="d1lp9x"
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.mk_of_failure_overlap
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (hfail : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2])
    (hoverlap : SourcePressureLocalIslandWitnessOverlap W1 W2) :
    SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2 :=
  ⟨hfail, hoverlap⟩
```

## 実験補題 F: recovered-or-obstruction split

現在の theorem は右 branch が raw overlap。
次は右 branch を obstruction に包む。

```lean id="5gpry4"
theorem sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlapObstruction
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (h1pos : ...)
    (h2pos : ...)
    (hfail : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]) :
    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W1 W2 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
    ∨ SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2
```

これは既存の `sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlap` から右 branch に `⟨hfail, hoverlap⟩` を作るだけじゃ。

## 次の Codex 指示

```text id="c7n3fp"
Checkpoint 162: Main root only — overlap obstruction predicate and overlap symmetry diagnostics.

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
Checkpoint 161 added reverse-branch recovery:

- sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
- sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length
- sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_items
- sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two
- sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
- sourcePressureLocalIslandWitnessPair_failure_reversed_sum_le_neg_two
- sourcePressureLocalIslandWitnessPair_failure_reversed_sum_neg
- sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlap

Global rules:
- Do not claim maximality.
- Do not claim uniqueness of pressure families.
- Do not claim coverage.
- Do not claim prefix behavior.
- Do not claim union accounting.
- Do not claim Collatz convergence.
- Keep all statements local to explicitly supplied witness pairs.
- Reverse branch is recovered by swapped sorted accounting.
- Overlap branch remains an obstruction.
- Do not merge intervals or prove union accounting in this checkpoint.

Main goal:
Give the overlap branch a first-class obstruction predicate and add small
diagnostic facts showing that overlap is symmetric and cannot be repaired by
swapping.

Part A: overlap symmetry at Nat interval layer.

Prove:

  theorem NatIntervalsOverlap.symm
      {a lenA b lenB : Nat}
      (h : NatIntervalsOverlap a lenA b lenB) :
      NatIntervalsOverlap b lenB a lenA

Expected proof:
  exact ⟨h.2, h.1⟩

Part B: overlap symmetry at address layer.

Prove:

  theorem SourcePressureIntervalPulseAddressOverlap.symm
      {n : OddNat} {k r : Nat}
      {A B : SourcePressureIntervalPulseAddress n k r}
      (h : SourcePressureIntervalPulseAddressOverlap A B) :
      SourcePressureIntervalPulseAddressOverlap B A

Part C: overlap symmetry at witness layer.

Prove:

  theorem SourcePressureLocalIslandWitnessOverlap.symm
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureLocalIslandWitnessOverlap W1 W2) :
      SourcePressureLocalIslandWitnessOverlap W2 W1

Part D: overlap excludes before in both directions.

Prove witness-level diagnostics:

  theorem SourcePressureLocalIslandWitnessOverlap.not_before
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureLocalIslandWitnessOverlap W1 W2) :
      ¬ SourcePressureLocalIslandWitnessBefore W1 W2

  theorem SourcePressureLocalIslandWitnessOverlap.not_reverseBefore
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureLocalIslandWitnessOverlap W1 W2) :
      ¬ SourcePressureLocalIslandWitnessBefore W2 W1

Use the existing not_of_before and not_of_reverseBefore theorems.
If address-level analogues are useful, add them too.

Part E: overlap obstruction predicate.

Define:

  def SourcePressureLocalIslandWitnessPairOverlapObstruction
      {n : OddNat} {k r : Nat}
      (W1 W2 : SourcePressureLocalIslandWitness n k r) : Prop :=
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2] ∧
      SourcePressureLocalIslandWitnessOverlap W1 W2

Add projections or constructor wrappers if useful:

  theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.mk_of_failure_overlap
      ...
      (hfail : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2])
      (hoverlap : SourcePressureLocalIslandWitnessOverlap W1 W2) :
      SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2

  theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.overlap
      ...
      (h : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
      SourcePressureLocalIslandWitnessOverlap W1 W2

  theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.failure
      ...
      (h : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]

Part F: recovered-or-obstruction split.

Prove:

  theorem sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlapObstruction
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
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
- use sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlap
- left branch unchanged
- right branch wrap as ⟨hfail, hoverlap⟩

Part G: do not handle overlap merge.

Do not add merge/split/union accounting.
Do not claim coverage or maximality.
Do not construct a merged family.

Part H: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-162.md

Include:
- Nat/address/witness overlap symmetry theorem names,
- before-exclusion diagnostics,
- overlap obstruction predicate name,
- constructor/projection theorem names,
- recovered-or-obstruction split theorem,
- explicit note that overlap cannot be recovered by swapping,
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

Checkpoint 162 が通ったら、次は **overlap obstruction is unrecoverable by pair swap** を明示するとよい。

つまり、

```text id="kqqw4h"
overlap obstruction
  -> not W1 before W2
  -> not W2 before W1
```

は出る。

これにより、

```text id="p70n1r"
swapping cannot recover sortedness
```

が言える。

候補 theorem:

```lean id="39emhq"
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.not_recoverable_by_swap
    {n : OddNat} {k r : Nat}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
    ¬ SourcePressureLocalIslandWitnessListSortedBefore [W2, W1]
```

これは、

```lean id="h2dcpk"
SourcePressureLocalIslandWitnessListSortedBefore_pair_iff
```

で `[W2, W1]` sorted を `W2 before W1` に変換し、overlap の `not_reverseBefore` あるいは `symm` + `not_before` で矛盾を出せるはずじゃ。

これが通れば、

```text id="h9uahy"
reverse branch:
  swap で回復可能

overlap branch:
  swap では回復不能
```

が Lean で固定できる。

ここまで行けば、pair failure は完全に二分される。

```text id="b1q1ii"
recoverable failure
unrecoverable overlap obstruction
```

その次にようやく、overlap obstruction の処理、つまり merge / split / exclusion の検討へ進める。

## 総評

Checkpoint 161 はかなり良い。
reverse branch が budget まで閉じたことで、pair failure の半分は Core に戻った。

次は overlap branch に名前を与え、対称性と unrecoverable 性を固定する。
これで、局所 pair failure の診断はかなり完成に近づくぞ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
index f95fa9e7..1f11e802 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -2171,6 +2171,129 @@ theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_su
         (sourcePressureLocalIslandWitnessListSortedBefore_pair_iff.2 hbefore)
         (by simp)
 
+/--
+Recovered accounted interval family for a reversed local-island witness pair.
+
+This is only a two-witness local recovery by swapping the supplied pair.  It is
+not a global sorting algorithm, not a maximal family construction, and not a
+union-accounting theorem.
+-/
+def sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+    {n : OddNat} {k r : ℕ}
+    (W1 W2 : SourcePressureLocalIslandWitness n k r)
+    (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
+    SourcePressureAccountedIntervalFamily n k r :=
+  sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair
+    W2 W1 hrev
+
+@[simp]
+theorem sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length
+    {n : OddNat} {k r : ℕ}
+    (W1 W2 : SourcePressureLocalIslandWitness n k r)
+    (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
+    (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+      W1 W2 hrev).items.length = 2 := by
+  simp [sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair]
+
+/--
+The recovered reversed pair lists the converted intervals in swapped order.
+-/
+theorem sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_items
+    {n : OddNat} {k r : ℕ}
+    (W1 W2 : SourcePressureLocalIslandWitness n k r)
+    (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
+    (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+      W1 W2 hrev).items =
+      [sourcePressureAccountedInterval_of_intervalPulseAddress
+        (sourcePressureIntervalPulseAddress_of_localIslandWitness W2),
+       sourcePressureAccountedInterval_of_intervalPulseAddress
+        (sourcePressureIntervalPulseAddress_of_localIslandWitness W1)] := by
+  rfl
+
+/- The recovered reversed-pair budget is just the sorted pair budget after swap. -/
+theorem sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two
+    {n : OddNat} {k r : ℕ}
+    (W1 W2 : SourcePressureLocalIslandWitness n k r)
+    (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
+    (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+      W1 W2 hrev).items).map
+      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2 :=
+  sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_sum_le_neg_two
+    W2 W1 hrev
+
+/-- The recovered reversed-pair family has strictly negative listed cost. -/
+theorem sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
+    {n : OddNat} {k r : ℕ}
+    (W1 W2 : SourcePressureLocalIslandWitness n k r)
+    (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
+    (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+      W1 W2 hrev).items).map
+      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0 :=
+  sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_sum_neg
+    W2 W1 hrev
+
+/--
+Failure-use wrapper: if `[W1, W2]` failed because the witnesses are reversed,
+the swapped recovered family still has the two-interval `≤ -2` budget.
+
+The failure hypothesis is intentionally not used by the proof.  It documents
+the branch in which this theorem is meant to be applied.
+-/
+theorem sourcePressureLocalIslandWitnessPair_failure_reversed_sum_le_neg_two
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (_hfail : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2])
+    (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
+    (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+      W1 W2 hrev).items).map
+      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2 :=
+  sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two
+    W1 W2 hrev
+
+/--
+Failure-use wrapper: the reversed recovered family has strictly negative
+listed cost.
+-/
+theorem sourcePressureLocalIslandWitnessPair_failure_reversed_sum_neg
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (_hfail : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2])
+    (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
+    (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+      W1 W2 hrev).items).map
+      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0 :=
+  sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
+    W1 W2 hrev
+
+/--
+Recovered-or-overlap split for a failed two-witness order.
+
+If the pair failure is a reversed-order failure, the swapped recovered family
+has the two-interval budget.  Otherwise the obstruction is overlap.  This is
+still a local two-witness theorem: it does not merge overlapping intervals and
+does not produce union accounting.
+-/
+theorem sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlap
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
+    ∨ SourcePressureLocalIslandWitnessOverlap W1 W2 := by
+  rcases sourcePressureLocalIslandWitnessPair_failure_reverseBefore_or_overlap
+      h1pos h2pos hfail with hrev | hoverlap
+  · exact Or.inl
+      ⟨hrev,
+        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two
+          W1 W2 hrev⟩
+  · exact Or.inr hoverlap
+
 /--
 Raw-argument version of the sorted pair budget.
 -/
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-161.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-161.md
new file mode 100644
index 00000000..ca42aaea
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-161.md
@@ -0,0 +1,169 @@
+# Report Petal 161
+
+## Checkpoint
+
+Checkpoint 161 stayed on the main Collatz/PetalBridge root and implemented
+reverse-branch recovery for a failed explicit local-island witness pair.
+
+Modified implementation file:
+
+- `DkMath/Collatz/PetalBridge/PressureAccounting.lean`
+
+No `OneCycle`, `ValuationFlowBridge`, `ABC`, or `NumberTheory` files were
+modified.
+
+## Reversed Pair Accounting Family
+
+The recovered reversed-pair family alias was added.
+
+```lean
+def sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+```
+
+It is defined by swapping the supplied pair and reusing the sorted pair
+constructor:
+
+```lean
+sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair W2 W1 hrev
+```
+
+This is only a two-witness local recovery.  It is not a global sorting
+algorithm, not a maximal-family construction, and not union accounting.
+
+## Structure Theorems
+
+The length theorem was added.
+
+```lean
+theorem sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length
+```
+
+The items theorem was also added.
+
+```lean
+theorem sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_items
+```
+
+The recovered family lists the converted intervals in swapped order:
+
+```text
+W2 interval, then W1 interval
+```
+
+## Recovered Budget
+
+The recovered two-witness budget theorem was added.
+
+```lean
+theorem sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two
+```
+
+The strict negative theorem was also added.
+
+```lean
+theorem sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
+```
+
+Both are direct consequences of the existing sorted pair budget applied to the
+swapped pair.
+
+## Failure-Reversed Wrappers
+
+The failure-use wrappers were added.
+
+```lean
+theorem sourcePressureLocalIslandWitnessPair_failure_reversed_sum_le_neg_two
+theorem sourcePressureLocalIslandWitnessPair_failure_reversed_sum_neg
+```
+
+The failure hypothesis is intentionally unused in the proof.  It documents the
+intended use case:
+
+```text
+[W1, W2] failed as ordered,
+but the reason is W2 before W1,
+so the swapped pair recovers the sorted two-interval budget.
+```
+
+## Extra: Recovered-or-Overlap Split
+
+The suggested next-step theorem also closed cleanly, so it was added.
+
+```lean
+theorem sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlap
+```
+
+It states that a failed pair, with positive converted lengths, is either:
+
+```text
+recoverable by a reversed sorted accounting family with sum ≤ -2
+```
+
+or:
+
+```text
+an overlap obstruction
+```
+
+This is the useful Core split:
+
+```text
+failure
+  -> reverse branch: recover budget
+  -> overlap branch: leave as obstruction
+```
+
+## Boundary Notes
+
+The overlap branch remains unhandled.
+
+This checkpoint does not merge intervals, split intervals, prove coverage, or
+construct union accounting.  It only recovers the reversed two-witness branch.
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
+See the final Codex response for the pass/fail status of the final gate.
+
+## Next Inference
+
+The reverse branch is now operationally closed at the two-witness level.
+
+The next safe direction is to isolate the overlap branch further, for example
+with a named obstruction predicate for:
+
+```text
+pair failure whose reason is overlap
+```
+
+That should still avoid merge/split or union accounting until the exact
+interval hypotheses are available.
````
`````
