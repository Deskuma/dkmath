# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAccounting

gch: 6c77e97adf4df86ac07d678153b8002267957295

## Report

cp159 完了です。

[PressureAccounting.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean) に overlap 層を追加しました。`not before` 単独では overlap とせず、両方向の `not before` と長さ正値を仮定して overlap を出す形に固定しています。

追加した主なもの:

- `NatIntervalsOverlap`
- `NatIntervalsOverlap.not_of_before`
- `NatIntervalsOverlap.not_of_reverseBefore`
- `NatIntervalsOverlap.of_not_before_not_reverseBefore`
- `SourcePressureIntervalPulseAddressOverlap`
- address-level の `not_of_before` / `not_of_reverseBefore` / `of_not_before_not_reverseBefore`
- `SourcePressureLocalIslandWitnessOverlap`
- witness-level の対応 wrapper

おまけとして、before がある場合に overlap を否定する reverse 方向 wrapper も address/witness 両方に足しました。主張は明示 supplied interval/address/witness に限定し、coverage / maximality / union accounting / Collatz convergence には踏み込んでいません。

レポートは [report-petal-159.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-159.md) に作成済みです。

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureAccounting` OK
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier` OK
- `lake build DkMath.Collatz.PetalBridge` OK
- target 2 files の `rg "\bsorry\b"` はヒットなし
- `git diff --check` OK

## Review

## 結論

うむ、Checkpoint 159 は **採用** じゃ 👍️
今回の実装はかなり重要じゃ。これまで「sorted-before failure は overlap ではない」と言葉で守っていた境界を、Lean 側で実際に **overlap 層** として切り出した。

今回追加された中心は、

```text id="zf8fgp"
NatIntervalBefore
NatIntervalsOverlap

SourcePressureIntervalPulseAddressBefore
SourcePressureIntervalPulseAddressOverlap

SourcePressureLocalIslandWitnessBefore
SourcePressureLocalIslandWitnessOverlap
```

の三段構えじゃな。

特に良いのは、`not before` 単独では overlap とせず、

```text id="n20hjk"
not A before B
not B before A
positive lengths
```

を仮定して初めて overlap を出す形に固定したことじゃ。レポートでも、この checkpoint は overlap vocabulary を追加しつつ、coverage / maximality / union accounting / Collatz convergence には踏み込んでいないと明記されておる。

## 状況分析

## 1. failure が「失敗」から「分類可能な情報」になった

これまでの failure は、

```text id="yi6kpq"
not A before B
```

という順序失敗だった。

しかし、これは二種類を混ぜていた。

```text id="eburaj"
B before A:
  逆順なだけ

neither A before B nor B before A:
  overlap
```

今回の `NatIntervalsOverlap` により、この二つを分けるための準備が整った。

これはかなり大きい。
なぜなら、failure branch がただの袋ではなく、

```text id="khcnby"
reversed order
genuine overlap
```

へ分解できるようになったからじゃ。

## 2. Core の failure handling が一段深くなった

DkMath Collatz/PetalBridge の今の山は、まだ大域収束ではなく、局所 pressure profile の会計である。

これまでの Core は、

```text id="xmrlgd"
sorted:
  budget を足せる

failure:
  sorted-before が壊れた
```

までだった。

今回で Core は、

```text id="p2f56x"
sorted:
  budget を足せる

failure:
  reversed なら並べ替え可能
  overlap なら会計重複候補
```

へ進む入口を得た。

これは Core から Beam へ進む前に必要な整理じゃ。
Beam とは「局所会計が時間方向・深さ方向へどう伝播するか」なので、局所 failure が単なる逆順なのか、本当に区間重複しているのかを分けないといけない。

## 3. `NatIntervalsOverlap.of_not_before_not_reverseBefore` が良い実験核

今回の一番の実験成功はこれじゃ。

```lean id="j62uxv"
theorem NatIntervalsOverlap.of_not_before_not_reverseBefore
```

この補題は、半開区間について、

```text id="da3w4q"
A before B ではない
B before A でもない
```

なら overlap だ、と言っている。

半開区間ではこれは標準的な三分岐構造じゃ。

```text id="nrnnxt"
A before B
B before A
A overlaps B
```

今回、その最小核が Lean で通った。これは今後かなり効く。

## レビュー

## 良い点

## 1. 層の順番が正しい

いきなり witness overlap に行かず、

```text id="iog4oq"
Nat interval
  -> address interval
  -> local-island witness
```

の順で上げている。

これは正しい。
start / len を直接持つのは address なので、まず address-level で overlap を定義するのが筋じゃ。

## 2. `not before` 単独を overlap にしていない

ここは非常に大事じゃ。

今回の report でも、

```text id="hz25lt"
not before alone is still not overlap evidence
```

と明記されている。

この境界が守られているので、後続で安全に failure reason classifier を作れる。

## 3. 長さ正値を explicit に残したのが良い

`NatIntervalsOverlap.of_not_before_not_reverseBefore` では、算術的には両方向 not-before だけで overlap が出るような形だが、API 境界には length positivity を残している。

これは良い判断じゃ。
pressure address の世界では、長さ 0 の空区間を future caller がどう読むかが事故になりやすい。明示的に

```lean id="epmyn7"
0 < A.len
0 < B.len
```

を要求することで、overlap を「実体ある区間の重なり」として読める。

## 注意点

## 1. まだ union accounting ではない

今回の overlap は、あくまで二つの explicit interval/address/witness の関係じゃ。

まだ次は言っていない。

```text id="amgvjc"
overlap した区間を merge する
union length を計算する
重複を除いた budget を出す
family の coverage を言う
```

これはまだ先じゃ。

## 2. overlap は「会計危険信号」であって、即破綻ではない

overlap が出たからといって、ただちに悪いわけではない。

意味は、

```text id="vzzh4g"
同じ pressure support を二重に数えている可能性がある
```

ということじゃ。

したがって、次の処理は二択になる。

```text id="qxlaz1"
overlap を避けるために並べ替える・選別する
または
overlap を merge / split して union accounting へ進む
```

今はまだ前者、つまり分類と診断に留めるのが安全じゃ。

## 解説

今回の補題群を直感的に言うと、半開区間の世界でこういう診断器を作った。

```text id="7h3erx"
A が B より完全に左:
  A before B

B が A より完全に左:
  B before A

どちらでもない:
  overlap
```

図式にするとこうじゃ。

```text id="qp1e3y"
A before B:
  [AAAA) [BBBB)

B before A:
  [BBBB) [AAAA)

overlap:
  [AAAA)
     [BBBB)
```

この三分岐があると、pair failure の意味が明確になる。

今までは、

```text id="5b8zjw"
not A before B
```

しか見ていなかった。
これは「B が前にある」場合も、「重なっている」場合も含む。

今回の overlap 層により、次は、

```text id="r9hmix"
not A before B
  -> B before A or overlap
```

へ分解できる。

これが次 checkpoint の主眼じゃ。

## 一歩先ゆく推論

次に作るべきは、**trichotomy** じゃ。

つまり、

```text id="z3a5mz"
A before B
or B before A
or A overlaps B
```

を Nat interval / address / witness の各層で作る。

これができると、failure branch はこうなる。

```text id="k344s1"
failure:
  not A before B

trichotomy により:
  B before A
  or A overlaps B
```

つまり、

```text id="meouoy"
failure reason:
  reversed
  overlap
```

が定理として出る。

これは次に Beam へ進むための入口じゃ。
なぜなら reversed は「ソートすれば回復可能」だが、overlap は「会計 family として重複処理が必要」だからじゃ。

ここを分けないと、後で sorted family producer を作るときに failure の扱いが曖昧になる。

## さらなる次の一手

Checkpoint 160 で trichotomy が通ったら、次々 checkpoint では **failure reason classifier** を作るのがよい。

最初は inductive を作らず、theorem だけで十分じゃ。

```lean id="gykvdu"
theorem SourcePressureLocalIslandWitnessPair_failure_reason
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (hfail : ¬ SourcePressureLocalIslandWitnessBefore W1 W2)
    (h1pos : ...)
    (h2pos : ...) :
    SourcePressureLocalIslandWitnessBefore W2 W1 ∨
      SourcePressureLocalIslandWitnessOverlap W1 W2
```

これが通れば、

```text id="lc4xsr"
pair failure
  -> reversed or overlap
```

が出る。

その次に初めて、

```text id="48b6wn"
reversed branch:
  swap して sorted pair accounting に戻す

overlap branch:
  merge / split / exclusion の検討へ進む
```

となる。

## 賢狼が試して欲しい実験補題

わっちが次に試して欲しいのは、まず Nat interval の三分岐じゃ。

## 実験補題 A: Nat interval trichotomy

```lean id="mk09xm"
theorem NatIntervalsOverlap.before_or_reverseBefore_or_overlap
    {a lenA b lenB : ℕ}
    (hApos : 0 < lenA)
    (hBpos : 0 < lenB) :
    NatIntervalBefore a lenA b lenB ∨
      NatIntervalBefore b lenB a lenA ∨
        NatIntervalsOverlap a lenA b lenB
```

これは `by_cases hAB : NatIntervalBefore a lenA b lenB`、次に `by_cases hBA : NatIntervalBefore b lenB a lenA`、両方否定されたら今回の

```lean id="r7y5j8"
NatIntervalsOverlap.of_not_before_not_reverseBefore
```

を使えば通るはずじゃ。

## 実験補題 B: failure reason from not-before

```lean id="h3iqi5"
theorem NatIntervalsOverlap.reverseBefore_or_overlap_of_not_before
    {a lenA b lenB : ℕ}
    (hApos : 0 < lenA)
    (hBpos : 0 < lenB)
    (hnotAB : ¬ NatIntervalBefore a lenA b lenB) :
    NatIntervalBefore b lenB a lenA ∨
      NatIntervalsOverlap a lenA b lenB
```

これが今回の一番実用的な補題じゃ。

なぜなら、pair failure は `not A before B` なので、その中身を

```text id="4hq6lc"
reverse-before
or overlap
```

へ分けられる。

## 実験補題 C: address-level failure reason

```lean id="i5qrvp"
theorem SourcePressureIntervalPulseAddressOverlap.reverseBefore_or_overlap_of_not_before
    {n : OddNat} {k r : ℕ}
    {A B : SourcePressureIntervalPulseAddress n k r}
    (hApos : 0 < A.len)
    (hBpos : 0 < B.len)
    (hnotAB : ¬ SourcePressureIntervalPulseAddressBefore A B) :
    SourcePressureIntervalPulseAddressBefore B A ∨
      SourcePressureIntervalPulseAddressOverlap A B
```

## 実験補題 D: witness-level failure reason

```lean id="sdbi6v"
theorem SourcePressureLocalIslandWitnessOverlap.reverseBefore_or_overlap_of_not_before
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (hnot12 : ¬ SourcePressureLocalIslandWitnessBefore W1 W2) :
    SourcePressureLocalIslandWitnessBefore W2 W1 ∨
      SourcePressureLocalIslandWitnessOverlap W1 W2
```

これは次の実装の中核になるはずじゃ。

## 次の Codex 指示

```text id="nxceie"
Checkpoint 160: Main root only — interval trichotomy and pair failure-reason split.

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
Checkpoint 159 added overlap vocabulary:

- NatIntervalsOverlap
- NatIntervalsOverlap.not_of_before
- NatIntervalsOverlap.not_of_reverseBefore
- NatIntervalsOverlap.of_not_before_not_reverseBefore
- SourcePressureIntervalPulseAddressOverlap
- SourcePressureIntervalPulseAddressOverlap.not_of_before
- SourcePressureIntervalPulseAddressOverlap.not_of_reverseBefore
- SourcePressureIntervalPulseAddressOverlap.of_not_before_not_reverseBefore
- SourcePressureLocalIslandWitnessOverlap
- SourcePressureLocalIslandWitnessOverlap.not_of_before
- SourcePressureLocalIslandWitnessOverlap.not_of_reverseBefore
- SourcePressureLocalIslandWitnessOverlap.of_not_before_not_reverseBefore

Global rules:
- Do not claim maximality.
- Do not claim uniqueness of pressure families.
- Do not claim coverage.
- Do not claim prefix behavior.
- Do not claim union accounting.
- Do not claim Collatz convergence.
- Keep all statements local to explicitly supplied intervals, addresses, or witnesses.
- Do not claim overlap from one failed `before`.
- Overlap is allowed only with both directions ruled out, or through the
  trichotomy/failure-reason lemmas that carry positivity hypotheses.

Main goal:
Add local trichotomy and failure-reason split theorems.

Part A: Nat interval trichotomy.

Prove:

  theorem NatIntervalsOverlap.before_or_reverseBefore_or_overlap
      {a lenA b lenB : Nat}
      (hApos : 0 < lenA)
      (hBpos : 0 < lenB) :
      NatIntervalBefore a lenA b lenB ∨
        NatIntervalBefore b lenB a lenA ∨
          NatIntervalsOverlap a lenA b lenB

Suggested proof:
- by_cases hAB : NatIntervalBefore a lenA b lenB
- if yes, exact Or.inl hAB
- else by_cases hBA : NatIntervalBefore b lenB a lenA
- if yes, exact Or.inr (Or.inl hBA)
- else use NatIntervalsOverlap.of_not_before_not_reverseBefore hApos hBpos hAB hBA

Part B: Nat interval failure-reason split.

Prove:

  theorem NatIntervalsOverlap.reverseBefore_or_overlap_of_not_before
      {a lenA b lenB : Nat}
      (hApos : 0 < lenA)
      (hBpos : 0 < lenB)
      (hnotAB : ¬ NatIntervalBefore a lenA b lenB) :
      NatIntervalBefore b lenB a lenA ∨
        NatIntervalsOverlap a lenA b lenB

Suggested proof:
- by_cases hBA : NatIntervalBefore b lenB a lenA
- if yes, left
- if no, right using NatIntervalsOverlap.of_not_before_not_reverseBefore

Part C: address-level trichotomy.

Prove:

  theorem SourcePressureIntervalPulseAddressOverlap.before_or_reverseBefore_or_overlap
      {n : OddNat} {k r : Nat}
      {A B : SourcePressureIntervalPulseAddress n k r}
      (hApos : 0 < A.len)
      (hBpos : 0 < B.len) :
      SourcePressureIntervalPulseAddressBefore A B ∨
        SourcePressureIntervalPulseAddressBefore B A ∨
          SourcePressureIntervalPulseAddressOverlap A B

Part D: address-level failure-reason split.

Prove:

  theorem SourcePressureIntervalPulseAddressOverlap.reverseBefore_or_overlap_of_not_before
      {n : OddNat} {k r : Nat}
      {A B : SourcePressureIntervalPulseAddress n k r}
      (hApos : 0 < A.len)
      (hBpos : 0 < B.len)
      (hnotAB : ¬ SourcePressureIntervalPulseAddressBefore A B) :
      SourcePressureIntervalPulseAddressBefore B A ∨
        SourcePressureIntervalPulseAddressOverlap A B

Part E: witness-level trichotomy.

Prove:

  theorem SourcePressureLocalIslandWitnessOverlap.before_or_reverseBefore_or_overlap
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      (h1pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
      (h2pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len) :
      SourcePressureLocalIslandWitnessBefore W1 W2 ∨
        SourcePressureLocalIslandWitnessBefore W2 W1 ∨
          SourcePressureLocalIslandWitnessOverlap W1 W2

Part F: witness-level failure-reason split.

Prove:

  theorem SourcePressureLocalIslandWitnessOverlap.reverseBefore_or_overlap_of_not_before
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      (h1pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
      (h2pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
      (hnot12 : ¬ SourcePressureLocalIslandWitnessBefore W1 W2) :
      SourcePressureLocalIslandWitnessBefore W2 W1 ∨
        SourcePressureLocalIslandWitnessOverlap W1 W2

Part G: connect to pair sorted-before failure.

If easy, add a theorem that refines pair failure:

  theorem sourcePressureLocalIslandWitnessPair_failure_reverseBefore_or_overlap
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      (h1pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
      (h2pos :
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
      (hfail :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]) :
      SourcePressureLocalIslandWitnessBefore W2 W1 ∨
        SourcePressureLocalIslandWitnessOverlap W1 W2

Suggested proof:
- get hnot12 from sourcePressureLocalIslandWitnessListHasSortedBeforeFailure_pair_iff.mp hfail
- apply witness-level reverseBefore_or_overlap_of_not_before

Part H: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-160.md

Include:
- Nat interval trichotomy theorem name,
- Nat interval failure-reason theorem name,
- address-level trichotomy theorem names,
- witness-level trichotomy theorem names,
- whether pair failure was refined into reverse-before or overlap,
- whether positivity hypotheses were required,
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

Checkpoint 160 が通ったら、次は **reverse recovery** じゃ。

つまり、failure が reversed だった場合、

```text id="0dhvhd"
[W1, W2] は failure
だが [W2, W1] は sorted
```

を出す。

候補はこれ。

```lean id="poeboc"
theorem sourcePressureLocalIslandWitnessPair_sorted_swap_of_reverseBefore
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
    SourcePressureLocalIslandWitnessListSortedBefore [W2, W1]
```

これは既存の pair sorted iff で即座に通るはずじゃ。

その次に、

```lean id="gym1so"
sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair W2 W1 hrev
```

を使って、逆順 failure だったものを sorted accounting に回復する。

この瞬間に、failure branch の一部は「失敗」ではなくなる。

```text id="q0eh7s"
failure because reversed:
  reorder and recover budget

failure because overlap:
  cannot reorder away
  must handle merge/split/exclusion
```

ここまで来ると、Beam の入口がはっきり見える。

## 総評

今回で overlap の最小核は通った。
これは地味に見えて、実は重要な節目じゃ。

これまでの failure は、

```text id="i4p9gp"
何かが壊れた
```

だった。

今後の failure は、

```text id="d7fv9i"
逆順だから壊れた
または
重なっているから壊れた
```

へ進む。

この分類が立てば、次にやるべきことが自然に決まる。

```text id="f87w0f"
逆順:
  sort / swap で回復

overlap:
  accounting の重複問題として別処理
```

つまり、Core の failure diagnosis が Beam の処理方針へ変わり始めた。
よい進展じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
index 704752ef..de00185e 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -706,6 +706,17 @@ This is a direction-sensitive helper for future sorted-family work.
 def NatIntervalBefore (a len b _len' : ℕ) : Prop :=
   a + len ≤ b

+/--
+Overlap vocabulary for two natural-number half-open intervals.
+
+This is the positive counterpart to ordered non-overlap.  The theorem API below
+is deliberately conservative: one failed `before` relation is not overlap
+evidence, because the intervals may simply be in reverse order.  Overlap is
+proved only after both ordered directions are ruled out.
+-/
+def NatIntervalsOverlap (a lenA b lenB : ℕ) : Prop :=
+  a < b + lenB ∧ b < a + lenA
+
 /-- Ordered non-overlap implies ordinary interval disjointness. -/
 theorem NatIntervalsDisjoint.of_before
     {a len b len' : ℕ}
@@ -713,6 +724,46 @@ theorem NatIntervalsDisjoint.of_before
     NatIntervalsDisjoint a len b len' :=
   Or.inl h

+/-- Ordered non-overlap in one direction excludes overlap. -/
+theorem NatIntervalsOverlap.not_of_before
+    {a lenA b lenB : ℕ}
+    (hbefore : NatIntervalBefore a lenA b lenB) :
+    ¬ NatIntervalsOverlap a lenA b lenB := by
+  change ¬ (a < b + lenB ∧ b < a + lenA)
+  change a + lenA ≤ b at hbefore
+  intro hoverlap
+  omega
+
+/-- Ordered non-overlap in the reverse direction also excludes overlap. -/
+theorem NatIntervalsOverlap.not_of_reverseBefore
+    {a lenA b lenB : ℕ}
+    (hbefore : NatIntervalBefore b lenB a lenA) :
+    ¬ NatIntervalsOverlap a lenA b lenB := by
+  change ¬ (a < b + lenB ∧ b < a + lenA)
+  change b + lenB ≤ a at hbefore
+  intro hoverlap
+  omega
+
+/--
+If neither ordered direction is available, the two half-open intervals overlap.
+
+The length-positivity hypotheses are kept at this API boundary for the pressure
+address use case, even though the arithmetic core is already forced by the two
+negated `before` inequalities.  Keeping them explicit prevents future callers
+from reading a single failed order test as overlap evidence.
+-/
+theorem NatIntervalsOverlap.of_not_before_not_reverseBefore
+    {a lenA b lenB : ℕ}
+    (_hApos : 0 < lenA)
+    (_hBpos : 0 < lenB)
+    (hnotAB : ¬ NatIntervalBefore a lenA b lenB)
+    (hnotBA : ¬ NatIntervalBefore b lenB a lenA) :
+    NatIntervalsOverlap a lenA b lenB := by
+  change ¬ a + lenA ≤ b at hnotAB
+  change ¬ b + lenB ≤ a at hnotBA
+  change a < b + lenB ∧ b < a + lenA
+  omega
+
 /--
 Transitive-like composition for ordered non-overlap.

@@ -745,6 +796,48 @@ def SourcePressureIntervalPulseAddressBefore
     (A B : SourcePressureIntervalPulseAddress n k r) : Prop :=
   A.start + A.len ≤ B.start

+/--
+Overlap predicate for two interval-pulse addresses.
+
+This only compares the explicit half-open address intervals.  It does not
+merge intervals, prove union accounting, or infer coverage of a pressure
+region.
+-/
+def SourcePressureIntervalPulseAddressOverlap
+    {n : OddNat} {k r : ℕ}
+    (A B : SourcePressureIntervalPulseAddress n k r) : Prop :=
+  NatIntervalsOverlap A.start A.len B.start B.len
+
+/-- A before relation between pulse addresses excludes address overlap. -/
+theorem SourcePressureIntervalPulseAddressOverlap.not_of_before
+    {n : OddNat} {k r : ℕ}
+    {A B : SourcePressureIntervalPulseAddress n k r}
+    (hbefore : SourcePressureIntervalPulseAddressBefore A B) :
+    ¬ SourcePressureIntervalPulseAddressOverlap A B :=
+  NatIntervalsOverlap.not_of_before hbefore
+
+/-- A reverse before relation between pulse addresses also excludes overlap. -/
+theorem SourcePressureIntervalPulseAddressOverlap.not_of_reverseBefore
+    {n : OddNat} {k r : ℕ}
+    {A B : SourcePressureIntervalPulseAddress n k r}
+    (hbefore : SourcePressureIntervalPulseAddressBefore B A) :
+    ¬ SourcePressureIntervalPulseAddressOverlap A B :=
+  NatIntervalsOverlap.not_of_reverseBefore hbefore
+
+/--
+If neither pulse address is before the other, then their explicit half-open
+address intervals overlap.
+-/
+theorem SourcePressureIntervalPulseAddressOverlap.of_not_before_not_reverseBefore
+    {n : OddNat} {k r : ℕ}
+    {A B : SourcePressureIntervalPulseAddress n k r}
+    (hApos : 0 < A.len)
+    (hBpos : 0 < B.len)
+    (hnotAB : ¬ SourcePressureIntervalPulseAddressBefore A B)
+    (hnotBA : ¬ SourcePressureIntervalPulseAddressBefore B A) :
+    SourcePressureIntervalPulseAddressOverlap A B :=
+  NatIntervalsOverlap.of_not_before_not_reverseBefore hApos hBpos hnotAB hnotBA
+
 theorem sourcePressureIntervalPulseAddressBefore_iff_accountedBefore
     {n : OddNat} {k r : ℕ}
     {A B : SourcePressureIntervalPulseAddress n k r} :
@@ -1692,6 +1785,57 @@ def SourcePressureLocalIslandWitnessBefore
     (sourcePressureIntervalPulseAddress_of_localIslandWitness W1)
     (sourcePressureIntervalPulseAddress_of_localIslandWitness W2)

+/--
+Overlap predicate for two explicit local-island witnesses.
+
+This is only the address-level overlap of the intervals obtained from the
+supplied witnesses.  It is not a coverage, maximality, or union-accounting
+claim, and it is not derivable from one failed `before` relation alone.
+-/
+def SourcePressureLocalIslandWitnessOverlap
+    {n : OddNat} {k r : ℕ}
+    (W1 W2 : SourcePressureLocalIslandWitness n k r) : Prop :=
+  SourcePressureIntervalPulseAddressOverlap
+    (sourcePressureIntervalPulseAddress_of_localIslandWitness W1)
+    (sourcePressureIntervalPulseAddress_of_localIslandWitness W2)
+
+/-- A witness-level before relation excludes witness-level overlap. -/
+theorem SourcePressureLocalIslandWitnessOverlap.not_of_before
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (hbefore : SourcePressureLocalIslandWitnessBefore W1 W2) :
+    ¬ SourcePressureLocalIslandWitnessOverlap W1 W2 :=
+  SourcePressureIntervalPulseAddressOverlap.not_of_before hbefore
+
+/-- A reverse witness-level before relation also excludes witness-level overlap. -/
+theorem SourcePressureLocalIslandWitnessOverlap.not_of_reverseBefore
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (hbefore : SourcePressureLocalIslandWitnessBefore W2 W1) :
+    ¬ SourcePressureLocalIslandWitnessOverlap W1 W2 :=
+  SourcePressureIntervalPulseAddressOverlap.not_of_reverseBefore hbefore
+
+/--
+Two local-island witness intervals overlap once both ordered directions are
+ruled out.
+
+The length-positivity hypotheses are kept explicit because this wrapper only
+uses the converted address intervals.  The theorem remains local to the two
+supplied witnesses.
+-/
+theorem SourcePressureLocalIslandWitnessOverlap.of_not_before_not_reverseBefore
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (h1pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
+    (h2pos :
+      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
+    (hnot12 : ¬ SourcePressureLocalIslandWitnessBefore W1 W2)
+    (hnot21 : ¬ SourcePressureLocalIslandWitnessBefore W2 W1) :
+    SourcePressureLocalIslandWitnessOverlap W1 W2 :=
+  SourcePressureIntervalPulseAddressOverlap.of_not_before_not_reverseBefore
+    h1pos h2pos hnot12 hnot21
+
 theorem sourcePressureLocalIslandWitnessBefore_iff_addressBefore
     {n : OddNat} {k r : ℕ}
     {W1 W2 : SourcePressureLocalIslandWitness n k r} :
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-159.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-159.md
new file mode 100644
index 00000000..381fd8bd
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-159.md
@@ -0,0 +1,165 @@
+# Report Petal 159
+
+## Checkpoint
+
+Checkpoint 159 stayed on the main Collatz/Petal root and added the first
+overlap vocabulary for pressure-accounting addresses.
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
+A new half-open interval overlap predicate was added.
+
+```lean
+def NatIntervalsOverlap (a lenA b lenB : Nat) : Prop :=
+  a < b + lenB ∧ b < a + lenA
+```
+
+This is paired with the existing ordered non-overlap predicate:
+
+```lean
+def NatIntervalBefore (a len b _len' : Nat) : Prop :=
+  a + len ≤ b
+```
+
+The following exclusion facts were proved:
+
+```lean
+theorem NatIntervalsOverlap.not_of_before
+theorem NatIntervalsOverlap.not_of_reverseBefore
+```
+
+The core experimental lemma was also proved:
+
+```lean
+theorem NatIntervalsOverlap.of_not_before_not_reverseBefore
+```
+
+This says that if neither ordered direction is available, the two half-open
+intervals overlap.  The theorem keeps explicit length-positivity hypotheses at
+the API boundary, even though the arithmetic proof itself is forced by the two
+negated `before` inequalities.
+
+## Address Layer
+
+The address-level overlap predicate was added.
+
+```lean
+def SourcePressureIntervalPulseAddressOverlap
+    {n : OddNat} {k r : Nat}
+    (A B : SourcePressureIntervalPulseAddress n k r) : Prop :=
+  NatIntervalsOverlap A.start A.len B.start B.len
+```
+
+The following address-level theorems were proved:
+
+```lean
+theorem SourcePressureIntervalPulseAddressOverlap.not_of_before
+theorem SourcePressureIntervalPulseAddressOverlap.not_of_reverseBefore
+theorem SourcePressureIntervalPulseAddressOverlap.of_not_before_not_reverseBefore
+```
+
+These theorems read only the explicit `start` and `len` fields of supplied
+addresses.  They do not merge intervals or introduce union accounting.
+
+## Witness Layer
+
+The witness-level wrapper was added.
+
+```lean
+def SourcePressureLocalIslandWitnessOverlap
+    {n : OddNat} {k r : Nat}
+    (W1 W2 : SourcePressureLocalIslandWitness n k r) : Prop :=
+  SourcePressureIntervalPulseAddressOverlap
+    (sourcePressureIntervalPulseAddress_of_localIslandWitness W1)
+    (sourcePressureIntervalPulseAddress_of_localIslandWitness W2)
+```
+
+The following witness-level theorems were proved:
+
+```lean
+theorem SourcePressureLocalIslandWitnessOverlap.not_of_before
+theorem SourcePressureLocalIslandWitnessOverlap.not_of_reverseBefore
+theorem SourcePressureLocalIslandWitnessOverlap.of_not_before_not_reverseBefore
+```
+
+The overlap constructor keeps explicit length-positivity hypotheses:
+
+```lean
+0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len
+0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len
+```
+
+This keeps the theorem local to converted address intervals and avoids hiding
+any positivity requirement in the witness layer.
+
+## Boundary Notes
+
+`not before` alone is still not overlap evidence.
+
+The valid refinement is:
+
+```text
+not A before B
+not B before A
+positive lengths
+--------------------------------
+A overlaps B
+```
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
+The following build gate was run during implementation:
+
+```bash
+lake build DkMath.Collatz.PetalBridge.PressureAccounting
+```
+
+It passed after replacing a fragile `unfold` proof with explicit `change`
+normal forms around the `NatIntervalsOverlap.*` theorem namespace.
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
+The safe next theorem shape is not a union theorem.  The next useful layer is a
+small classification lemma for explicit pairs:
+
+```text
+before A B
+or before B A
+or overlap A B
+```
+
+with explicit positive lengths for the overlap branch.  This would give callers
+a trichotomy-style local diagnostic without claiming maximal families,
+coverage, or Collatz convergence.
````
`````
