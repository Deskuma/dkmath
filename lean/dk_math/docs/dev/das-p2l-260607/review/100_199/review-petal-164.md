# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAccounting

gch: 8abd5f5de4fac8f74e2f55d5754fe87681aba1fb

## Report

cp163 完了です。

[PressureAccounting.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean) に、overlap obstruction の消費用 API を追加しました。

追加内容:

- `SourcePressureLocalIslandWitnessPairOverlapObstruction.swap_failure`
- `not_sorted`
- `not_sorted_swap`
- `symm`
- `symm_iff`

これで overlap obstruction は `[W1, W2]` と `[W2, W1]` のどちら向きでも同じ障害として扱えます。今回も merge / split / union accounting / coverage / convergence には踏み込んでいません。

レポート作成済みです: [report-petal-163.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-163.md)

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

うむ、Checkpoint 163 は **採用** じゃ 👍️
今回で、overlap obstruction が **順序に依存しない pair-level 障害** としてかなり扱いやすくなった。

追加された主 API は、

```lean id="n8twor"
SourcePressureLocalIslandWitnessPairOverlapObstruction.swap_failure
SourcePressureLocalIslandWitnessPairOverlapObstruction.not_sorted
SourcePressureLocalIslandWitnessPairOverlapObstruction.not_sorted_swap
SourcePressureLocalIslandWitnessPairOverlapObstruction.symm
SourcePressureLocalIslandWitnessPairOverlapObstruction.symm_iff
```

じゃな。これにより、`[W1, W2]` でも `[W2, W1]` でも同じ overlap obstruction として扱えるようになった。今回も merge / split / union accounting / coverage / convergence へ踏み込んでいない。これは正しい。

## 状況分析

## 1. pair failure の局所診断はかなり完成した

ここまでの pair failure は、ほぼ次の形に整理された。

```text id="beewfm"
[W1, W2] sorted:
  normal accounting

[W1, W2] failure:
  reverse branch:
    swap して recovered accounting

  overlap branch:
    swap しても sorted にならない obstruction
```

Checkpoint 161 で reverse branch は `sum ≤ -2` まで回収された。
Checkpoint 162 で overlap obstruction が first-class になった。
今回の Checkpoint 163 で、その obstruction が対称化され、両方向の failure / not-sorted を取り出せるようになった。

つまり pair-level では、

```text id="vnou1o"
recoverable failure
unrecoverable obstruction
```

の分解がかなり安定した。

## 2. `symm_iff` が地味に強い

`SourcePressureLocalIslandWitnessPairOverlapObstruction.symm` だけでも十分だが、`symm_iff` まで入ったのは良い。

これにより、

```text id="7p5wz3"
Obstruction W1 W2
  ↔
Obstruction W2 W1
```

として rewrite しやすくなる。

後で list-level や adjacent-pair-level に上げるとき、pair の向きが邪魔になることがある。`symm_iff` は、その邪魔を減らす。

## 3. overlap obstruction は「順序問題ではない」と固定された

今回の追加で、

```lean id="m73gcn"
not_sorted
not_sorted_swap
```

が入った。

これは意味が大きい。

```text id="qt2xvi"
reverse branch:
  swapped list は sorted

overlap obstruction:
  original list も sorted でない
  swapped list も sorted でない
```

つまり overlap は、順番を入れ替えて済む問題ではない。

ここで初めて、

```text id="fdv5x4"
逆順は Core に戻せる
overlap は Gap として残る
```

が Lean API の形になった。

## レビュー

## 採用理由

今回の checkpoint は、前回までの設計を過不足なく閉じている。

特に良い点は三つある。

第一に、`swap_failure` が入ったこと。

```lean id="gfdbo8"
SourcePressureLocalIslandWitnessPairOverlapObstruction.swap_failure
```

これで overlap obstruction は、元の pair だけでなく swapped pair でも sorted-before failure を持つと分かる。

第二に、not-sorted 診断が入ったこと。

```lean id="l7jdcl"
SourcePressureLocalIslandWitnessPairOverlapObstruction.not_sorted
SourcePressureLocalIslandWitnessPairOverlapObstruction.not_sorted_swap
```

これは後続の contradiction proof でかなり使いやすい。

第三に、対称性が定理化されたこと。

```lean id="h3k4jp"
SourcePressureLocalIslandWitnessPairOverlapObstruction.symm
SourcePressureLocalIslandWitnessPairOverlapObstruction.symm_iff
```

これで overlap obstruction が、pair の向きに依存しない本物の区間重複障害として扱える。

## 注意点

## 1. まだ pair-level である

今回の完成度は高いが、対象はあくまで二要素 pair じゃ。

まだ次は言っていない。

```text id="9hhm7d"
任意 list の failure を全部分類する
任意 list を sort して recover する
overlap obstruction cluster を構成する
```

ここは次の段階。

## 2. overlap obstruction はまだ解消していない

これは大事じゃ。

今回の theorem は、

```text id="c6r4pu"
overlap は本当に obstruction である
```

を強くした。

しかし、

```text id="8th7o8"
overlap を merge する
overlap を split する
overlap の union budget を作る
```

はまだやっていない。

この境界は守るべきじゃ。

## 解説

今回の実装を直感的に言えば、

```text id="kw9rzk"
overlap obstruction は左右をひっくり返しても overlap obstruction である
```

ということじゃ。

普通の逆順 failure はこう。

```text id="djd69y"
[W1, W2] failed
because W2 before W1

swap:
  [W2, W1] sorted
```

しかし overlap obstruction はこう。

```text id="gdmu6q"
[W1, W2] failed
because intervals overlap

swap:
  [W2, W1] still failed
```

したがって、pair failure は完全に性格が分かれた。

```text id="wklo7l"
reverse:
  repairable by swap

overlap:
  not repairable by swap
```

この差が Lean 定理として定着したのが今回の意味じゃ。

## 一歩先ゆく推論

次は、pair から **list の adjacent obstruction** に上げるのが自然じゃ。

なぜ adjacent かというと、既存の sorted-before failure は list の隣接順序に関係する形で育っているからじゃ。いきなり任意二点の obstruction に飛ぶと、membership / equality / duplicate の扱いが重くなる。

したがって次は、

```text id="6f3cb1"
list の中に、
隣接する overlap obstruction pair がある
```

を定義するのがよい。

これは、pair-level obstruction を list-level failure diagnosis へ持ち上げる最初の橋になる。

## さらなる次の一手

Checkpoint 164 で adjacent overlap obstruction が入ったら、その次は、

```text id="eu97j6"
list failure
  -> adjacent reverse-recoverable
  or adjacent overlap obstruction
```

を狙う。

ただし、ここでも list 全体の sorting algorithm はまだ作らない。

最初はあくまで、

```text id="x72ajc"
一つの隣接 failure を取り出す
その failure の理由を分類する
```

まででよい。

これが通れば、list-level の failure も pair-level と同じく、

```text id="tg7n4c"
回復可能な局所逆順
未回収の局所 overlap
```

に分解できる。

## 賢狼が試して欲しい実験補題

## 実験補題 A: adjacent overlap obstruction predicate

まずは recursive な定義が安全じゃ。

```lean id="mvp9rb"
def SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
    {n : OddNat} {k r : ℕ}
    : List (SourcePressureLocalIslandWitness n k r) → Prop
  | [] => False
  | [_] => False
  | W1 :: W2 :: rest =>
      SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2 ∨
        SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction (W2 :: rest)
```

これは membership を避けられるので軽い。

## 実験補題 B: pair case

```lean id="wkt9dl"
theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction_pair_iff
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r} :
    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction [W1, W2] ↔
      SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2
```

これは `simp` で落ちる可能性が高い。

## 実験補題 C: cons-left constructor

```lean id="2uwz19"
theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.cons_of_head
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction (W1 :: W2 :: rest)
```

## 実験補題 D: cons-tail constructor

```lean id="6k8gnz"
theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.cons_of_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (htail :
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction (W2 :: rest)) :
    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction (W1 :: W2 :: rest)
```

## 実験補題 E: adjacent obstruction implies list failure

これはすぐ欲しい。

```lean id="vppkei"
theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hobs : SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L
```

ただし既存の `SourcePressureLocalIslandWitnessListHasSortedBeforeFailure` の定義が recursive なら通しやすい。
もし定義が pair-specific / mapped family-specific なら、ここは難しいかもしれぬ。難しければ checkpoint では pair/pair-cons までに留める。

## 実験補題 F: adjacent obstruction symmetry for pair only

list 全体では順序が絡むので、まず pair だけで十分。

```lean id="pc8n3j"
theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction_pair_symm
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (h :
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction [W1, W2]) :
    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction [W2, W1]
```

これは obstruction の `symm` で通るはずじゃ。

## 次の Codex 指示

```text id="ni0gga"
Checkpoint 164: Main root only — adjacent overlap obstruction for local-island witness lists.

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
Checkpoint 163 added overlap obstruction consumption API:

- SourcePressureLocalIslandWitnessPairOverlapObstruction.swap_failure
- SourcePressureLocalIslandWitnessPairOverlapObstruction.not_sorted
- SourcePressureLocalIslandWitnessPairOverlapObstruction.not_sorted_swap
- SourcePressureLocalIslandWitnessPairOverlapObstruction.symm
- SourcePressureLocalIslandWitnessPairOverlapObstruction.symm_iff

Global rules:
- Do not claim maximality.
- Do not claim uniqueness of pressure families.
- Do not claim coverage.
- Do not claim prefix behavior.
- Do not claim union accounting.
- Do not claim Collatz convergence.
- Keep all statements local to explicitly supplied witness lists.
- Reverse branch is already recovered at the pair level.
- Overlap branch remains an obstruction.
- Do not merge intervals or prove union accounting in this checkpoint.

Main goal:
Lift pair-level overlap obstruction to a minimal adjacent-list obstruction API.

Part A: define adjacent overlap obstruction for witness lists.

Add a recursive predicate:

  def SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
      {n : OddNat} {k r : Nat}
      : List (SourcePressureLocalIslandWitness n k r) -> Prop
    | [] => False
    | [_] => False
    | W1 :: W2 :: rest =>
        SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2 ∨
          SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction (W2 :: rest)

Comment:
This is adjacent only.  It does not quantify over arbitrary pairs and does not
construct a cluster, merge, or union family.

Part B: pair iff.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction_pair_iff
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r} :
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction [W1, W2] ↔
        SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2

Part C: constructors.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.cons_of_head
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      {rest : List (SourcePressureLocalIslandWitness n k r)}
      (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction (W1 :: W2 :: rest)

  theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.cons_of_tail
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      {rest : List (SourcePressureLocalIslandWitness n k r)}
      (htail :
        SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction (W2 :: rest)) :
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction (W1 :: W2 :: rest)

Part D: pair symmetry through adjacent predicate.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction_pair_symm
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      (h :
        SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction [W1, W2]) :
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction [W2, W1]

Use pair iff and SourcePressureLocalIslandWitnessPairOverlapObstruction.symm.

Part E: adjacent obstruction implies sorted-before failure.

Try to prove:

  theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (hobs :
        SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L

If the existing list failure predicate is not recursive enough to make this
clean, do not force it.  Instead, prove only the pair-level version:

  theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction_pair_hasSortedBeforeFailure
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      (hobs :
        SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction [W1, W2]) :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]

and report why the full-list version was deferred.

Part F: no merge/split/union accounting.

Do not add interval merge.
Do not add overlap cluster.
Do not add arbitrary-pair list obstruction yet.
Do not prove coverage, maximality, or convergence.

Part G: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-164.md

Include:
- adjacent overlap obstruction predicate,
- pair iff theorem,
- constructors,
- pair symmetry theorem,
- whether full-list obstruction -> sorted-before failure was proved or deferred,
- explicit note that this is adjacent-only,
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

Checkpoint 164 が通ったら、次は **adjacent failure reason** じゃ。

すなわち list の先頭隣接 pair について、

```text id="kfzukt"
head pair failure
  -> reverse-recovered budget
  or overlap obstruction
```

を作る。

ただし list 全体ではなく、まずは head pair だけ。

候補は、

```lean id="f2194g"
theorem sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_overlapObstruction
```

のような形じゃ。

これが通れば、list-level の最初の failure を一つずつ処理する algorithmic skeleton が見えてくる。

## 総評

Checkpoint 163 は、pair-level obstruction の消費 API としてよく閉じておる。

これで pair failure の分解は、

```text id="q9v4s6"
sorted
reverse recoverable
overlap obstruction
```

の三層になった。

次は adjacent list へ上げる。
ただし、まだ任意 pair / cluster / merge へ進まない。
まずは隣接 obstruction を安全に持ち上げる。これが次の堅い一手じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
index e685bab1..c9116481 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -2180,6 +2180,62 @@ theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.not_recoverable_b
     sourcePressureLocalIslandWitnessListSortedBefore_pair_iff.1 hsorted
   exact SourcePressureLocalIslandWitnessOverlap.not_reverseBefore hobs.overlap hrev

+/--
+The swapped two-witness list also has a sorted-before failure under overlap.
+
+Overlap blocks both directions, so the obstruction is independent of which
+side of the pair is inspected first.  This is still only a two-witness local
+diagnostic and does not merge the overlapping intervals.
+-/
+theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.swap_failure
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
+    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W2, W1] :=
+  sourcePressureLocalIslandWitnessListHasSortedBeforeFailure_pair_iff.2
+    hobs.not_reverseBefore
+
+/-- An overlap obstruction makes the original pair list not sorted. -/
+theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.not_sorted
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
+    ¬ SourcePressureLocalIslandWitnessListSortedBefore [W1, W2] := by
+  intro hsorted
+  have hbefore : SourcePressureLocalIslandWitnessBefore W1 W2 :=
+    sourcePressureLocalIslandWitnessListSortedBefore_pair_iff.1 hsorted
+  exact hobs.not_before hbefore
+
+/-- An overlap obstruction makes the swapped pair list not sorted. -/
+theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.not_sorted_swap
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
+    ¬ SourcePressureLocalIslandWitnessListSortedBefore [W2, W1] :=
+  hobs.not_recoverable_by_swap
+
+/--
+Overlap obstruction is symmetric in the two supplied witnesses.
+
+This packages the swapped failure together with symmetric overlap.  It still
+does not choose a repaired order, merged interval, or union-accounting family.
+-/
+theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.symm
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
+    SourcePressureLocalIslandWitnessPairOverlapObstruction W2 W1 :=
+  ⟨hobs.swap_failure, SourcePressureLocalIslandWitnessOverlap.symm hobs.overlap⟩
+
+/-- Symmetric iff form for the local overlap-obstruction predicate. -/
+theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.symm_iff
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r} :
+    SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2 ↔
+      SourcePressureLocalIslandWitnessPairOverlapObstruction W2 W1 :=
+  ⟨SourcePressureLocalIslandWitnessPairOverlapObstruction.symm,
+    SourcePressureLocalIslandWitnessPairOverlapObstruction.symm⟩
+
 /--
 Reverse-recovery helper for a pair whose failure reason is merely reversed
 order.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-163.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-163.md
new file mode 100644
index 00000000..628c1d33
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-163.md
@@ -0,0 +1,146 @@
+# Report Petal 163
+
+## Checkpoint
+
+Checkpoint 163 stayed on the main Collatz/PetalBridge root and strengthened the
+pair overlap-obstruction API.
+
+Modified implementation file:
+
+- `DkMath/Collatz/PetalBridge/PressureAccounting.lean`
+
+No `OneCycle`, `ValuationFlowBridge`, `ABC`, or `NumberTheory` files were
+modified.
+
+## Swapped-List Failure
+
+The swapped failure projection was added:
+
+```lean
+theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.swap_failure
+```
+
+Meaning:
+
+```text
+overlap obstruction for [W1, W2]
+  -> sorted-before failure for [W2, W1]
+```
+
+This fixes the expected diagnostic: overlap blocks both directions, unlike the
+reverse-order branch which can be recovered by swapping.
+
+## Not-Sorted Diagnostics
+
+The direct not-sorted diagnostics were added:
+
+```lean
+theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.not_sorted
+theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.not_sorted_swap
+```
+
+These are consumer-facing wrappers:
+
+```text
+obstruction -> not sorted [W1, W2]
+obstruction -> not sorted [W2, W1]
+```
+
+The swapped version aliases the existing `not_recoverable_by_swap` theorem.
+
+## Obstruction Symmetry
+
+The obstruction predicate is now symmetric:
+
+```lean
+theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.symm
+theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.symm_iff
+```
+
+This makes the overlap-obstruction reading order-independent:
+
+```text
+OverlapObstruction W1 W2
+  iff
+OverlapObstruction W2 W1
+```
+
+The proof uses:
+
+- swapped sorted-before failure,
+- symmetric witness overlap.
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
+The pair obstruction API is now stable enough for a list-level entrance.
+
+The next safe target is an adjacent-pair predicate, not a global pair search:
+
+```lean
+def SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
+```
+
+The intended next theorem shape is:
+
+```text
+list sorted-before failure
+  -> adjacent reverse recoverable
+  or adjacent overlap obstruction
+```
+
+This would lift the pair obstruction one level upward while still avoiding
+merge/split/union accounting.
````
`````
