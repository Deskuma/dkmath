# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis

gch: 7d318a7b597b1c7dacd1f870fb441f6841cc9d7c

## Report

実装完了しました。cp178 は cp177 の一般定理を consumer-facing API に射影する薄い corollary です。

追加:

- [PressureAdjacentDiagnosis.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean)
  - `sourcePressureLocalIslandWitnessList_failure_exists_recovered_or_overlap`
  - `sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_no_overlap`
- [report-petal-178.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-178.md)

意味は、

```text
explicit-list sorted-before failure
  -> recovered adjacent pair
     or adjacent overlap obstruction
```

さらに no-overlap 仮定のもとで、

```text
explicit-list sorted-before failure
  -> recovered adjacent pair
```

です。pair-local recovered budget と adjacent overlap obstruction の分離が使いやすくなりました。

検証:

```bash
lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
git diff --check
```

対象3ファイルの `sorry` 検索も no hits です。既存の無関係 warning として `ZsigmondyCyclotomicResearch.lean:152` の `sorry` は引き続き表示されています。

## Review

## 結論

うむ、Checkpoint 178 は **採用** じゃ 👍️
cp177 で得た一般定理を、consumer がそのまま使いやすい形へ射影する、よい薄い checkpoint になっている。

追加された主定理はこの 2 本じゃ。

```lean
sourcePressureLocalIslandWitnessList_failure_exists_recovered_or_overlap
sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_no_overlap
```

意味は明快で、

```text
explicit-list sorted-before failure
  -> recovered adjacent pair
     or adjacent overlap obstruction
```

さらに no-overlap 仮定のもとで、

```text
explicit-list sorted-before failure
  -> recovered adjacent pair
```

じゃ。pair-local recovered budget と adjacent overlap obstruction の分離が、外部 API として使いやすくなった。

## 実装レビュー

## 1. かなり良い「薄い corollary」

今回の実装は、厚い新理論を足していない。

```lean
sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis
```

で得た list-level adjacent diagnosis を、

```lean
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_overlap
```

へ通しただけじゃ。

この薄さがよい。
既存 API の意味が自然に外向き定理へ流れている。

## 2. overlap を obstruction として分離できた

今回の主価値はここじゃ。

これまで、

```text
failure L
```

から、

```text
has adjacent diagnosis L
```

までは言えた。

今回からは、

```text
failure L
  -> recovered adjacent pair
  or overlap obstruction L
```

まで言える。

つまり、failure の処理方針が二分された。

```text
recovered branch:
  pair-local budget ≤ -2 がある

overlap branch:
  adjacent overlap obstruction が残る
```

この切り分けにより、次からは overlap-free な場合に recovered branch を直接使える。

## 3. no-overlap corollary は実用面で重要

```lean
sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_no_overlap
```

は、今後かなり使いやすいはずじゃ。

形としては、

```text
failure L
no adjacent overlap obstruction L
  -> exists recovered adjacent pair
```

である。

これは「overlap だけが obstruction」と読むための入口になる。
もちろん、これは overlap-free list が大域的に存在するという主張ではない。
あくまで、明示 list `L` に対して no-overlap を仮定した場合の局所分岐じゃ。

## 数学的意味

今回の到達点は、かなり綺麗に言える。

```text
明示 witness list の sorted-before failure は、
隣接 pair の recovered budget へ落ちるか、
隣接 overlap obstruction として残る。
```

つまり failure は、もはや曖昧な「失敗」ではなく、

```text
回収可能な逆順 pair
または
overlap obstruction
```

に分類される。

これは DkMath 的には、Gap をかなり明確にした段階じゃ。

```text
Core:
  pair-local recovered budget

Gap:
  adjacent overlap obstruction
```

まだ overlap repair はしていない。
まだ union accounting もない。
しかし、どこが未処理 Gap なのかは見えた。

## 注意点

## 1. recovered は pair-local

今回の recovered branch は、

```lean
∃ A B,
  SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
    ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
      ...
```

という形じゃ。

つまり、budget は `A,B` の adjacent pair に属する。
list 全体の合計 budget ではない。

ここは引き続き重要じゃ。

## 2. no-overlap は仮定であって構成ではない

今回の theorem は、

```lean
¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
```

を仮定する。

つまり、

```text
overlap-free list を構成できる
canonical に overlap-free な list がある
```

とは言っていない。

次 checkpoint でもこの境界を守るべきじゃ。

## 3. canonical first diagnosis ではない

`exists` なので、どの adjacent pair が選ばれるかは指定しない。

```text
最初の failure
最左の failure
最小 start の pair
```

などはまだ未定義。
現段階では、存在だけで十分じゃ。

## 次の実装方針

次は report の Next Candidate 通り、**overlap-free predicate** を名前として立てるのが自然じゃ。

今は theorem の引数に直接、

```lean
¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
```

と書いている。

これを、

```lean
def SourcePressureLocalIslandWitnessListOverlapFree ...
```

あるいはより明確に、

```lean
def SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction ...
```

として包む。

わっちとしては、否定述語であることを隠さない名前がよい。

```lean
def SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
```

が安全じゃ。

短い `OverlapFree` でもよいが、後で「どの overlap が free なのか」が曖昧になる可能性がある。

## 次の Codex 指示

```text
Checkpoint 179: Main root only — named no-adjacent-overlap predicate for explicit witness lists.

Scope:
Focus on the refactored Collatz/PetalBridge pressure modules.

Primary target file:
- DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean

Allowed supporting file, only if needed:
- DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean

Do not modify:
- PressureAccounting.lean unless import/order forces a tiny fix
- OneCycle.lean
- ValuationFlowBridge.lean
- ABC files
- NumberTheory files

Do not rename or rewrite previous theorem statements.

Context:
Checkpoint 178 added consumer-facing corollaries:

- sourcePressureLocalIslandWitnessList_failure_exists_recovered_or_overlap
- sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_no_overlap

The second theorem currently takes:

  ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L

as a raw hypothesis.

Global guardrails:
- Do not claim global local-island coverage.
- Do not claim maximality.
- Do not claim uniqueness.
- Do not claim prefix behavior.
- Do not claim arbitrary list sorting.
- Do not claim canonical first diagnosis.
- Do not enumerate all diagnoses.
- Do not claim union accounting.
- Do not claim overlap repair.
- Do not claim Collatz convergence.
- Keep all statements local to explicitly supplied witness lists.
- Recovered budgets remain pair-local.
- Overlap remains an adjacent obstruction on the enclosing explicit list.
- Do not prove that any canonical overlap-free list exists.

Main goal:
Introduce a small named predicate for explicit witness lists with no adjacent
overlap obstruction, then restate the no-overlap recovered theorem using that
predicate.

Part A: define a named no-overlap predicate.

Prefer the explicit name:

  def SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
      {n : OddNat} {k r : Nat}
      (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
    ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L

Alternative shorter alias is acceptable only if comments make the meaning clear:

  def SourcePressureLocalIslandWitnessListOverlapFree ...

Do not define a broader overlap-free concept.  This predicate is only about
the existing adjacent-overlap obstruction predicate.

Part B: basic projection theorem.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.not_obstruction
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (hno :
        SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L) :
      ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L

Expected proof:
- exact hno

Part C: constructor from raw negation.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.of_not
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (hno :
        ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L

Expected proof:
- exact hno

Part D: consumer-facing recovered theorem using named predicate.

Prove:

  theorem sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_noAdjacentOverlap
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
      (hno :
        SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L) :
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
            (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
              A B hrev).items).map
              (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2

Suggested proof:
- exact sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_no_overlap
    h hno.not_obstruction
  or unfold the predicate if namespace projection is not convenient.

Part E: optional short-list facts.

Only if easy, prove that nil and singleton lists satisfy the named no-overlap
predicate:

  theorem SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.nil
  theorem SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.singleton

These should follow from existing no-adjacent-diagnosis or adjacent-overlap
short-list facts if available.  Do not force this if it requires new machinery.

Part F: optional naming alias.

If the long predicate name becomes too verbose, add a short abbreviation:

  abbrev SourcePressureLocalIslandWitnessListOverlapFree := ...

Only if it does not create confusing theorem names.  Prefer clarity.

Part G: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-179.md

Include:
- the named no-adjacent-overlap predicate;
- the raw-negation constructor/projection;
- the named no-overlap recovered theorem;
- optional short-list facts if added;
- explicit note that this is only a readability wrapper around an existing
  obstruction negation;
- explicit note that it does not assert existence of canonical overlap-free
  lists;
- explicit note that no coverage, maximality, uniqueness, sorting,
  canonical first diagnosis, enumeration, union accounting, overlap repair,
  or Collatz convergence was introduced;
- verification results.

Verification:

  lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
  lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
  lake build DkMath.Collatz.PetalBridge.PressureAccounting
  lake build DkMath.Collatz.PetalBridge.PressureFrontier
  lake build DkMath.Collatz.PetalBridge

Run no-sorry checks:

  rg -n "\\bsorry\\b" \
    DkMath/Collatz/PetalBridge/PressureAccounting.lean \
    DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
    DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean

Also run:

  git diff --check
```

## さらに一歩先の提案

Checkpoint 179 が通ったら、次は **overlap-free list の recovered branch を accounting family へ接続する薄い theorem** が候補じゃ。

ただし、まだ union accounting ではない。

狙う形は、

```text
failure L
no-adjacent-overlap L
  -> exists adjacent pair A B in L
     with pair-local recovered budget ≤ -2
```

までは cp179 で名前付きになる。

その次に、

```text
その recovered pair を、既存の accounted interval family API に渡す
```

という bridge を作る。
まだ list 全体の budget は言わない。
pair 一つだけを accounted family として再包装するだけじゃ。

## 総評

cp178 は地味に見えて、かなり使いやすさを上げた checkpoint じゃ。

これで consumer は、

```text
failure L
```

を見たら、まず

```text
recovered pair
or
overlap obstruction
```

へ分けられる。

次は no-overlap を名前にする。
そのあと、overlap-free branch を pair-local accounting へ接続する。
これで「overlap が唯一の未処理 Gap」として、だいぶ輪郭が締まってくるぞ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
index 9f78672c..ce2e4107 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
@@ -520,6 +520,56 @@ theorem sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis
       exact sourcePressureIntervalPulseAddress_of_localIslandWitness_len_pos W)
     h

+/--
+Project an explicit-list sorted-before failure to the two consumer-facing
+branches: either some adjacent pair has a pair-local recovered budget, or the
+enclosing explicit list has an adjacent overlap obstruction.
+
+This is the sharp projection of the general adjacent-diagnosis theorem.  It
+does not select a canonical first diagnosis, enumerate all diagnosed pairs,
+repair overlap, or perform any union accounting.
+-/
+theorem sourcePressureLocalIslandWitnessList_failure_exists_recovered_or_overlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L) :
+    (∃ A B,
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
+          (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+            A B hrev).items).map
+            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2)
+    ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L :=
+  SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_overlap
+    (sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis h)
+
+/--
+If a failed explicit witness list has no adjacent overlap obstruction, then
+some adjacent pair in that same list carries a pair-local recovered budget.
+
+The conclusion remains pair-local.  The theorem only removes the overlap branch
+from `sourcePressureLocalIslandWitnessList_failure_exists_recovered_or_overlap`;
+it does not sort the list or claim that all failures are recovered globally.
+-/
+theorem sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_no_overlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
+    (hno :
+      ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
+    ∃ A B,
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
+          (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+            A B hrev).items).map
+            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2 := by
+  rcases sourcePressureLocalIslandWitnessList_failure_exists_recovered_or_overlap h
+      with hrec | hobs
+  · exact hrec
+  · exact False.elim (hno hobs)
+
 /--
 Length-three sorted-before failure yields a list-level adjacent diagnosis.

diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-178.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-178.md
new file mode 100644
index 00000000..09c85797
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-178.md
@@ -0,0 +1,154 @@
+# Report Petal 178
+
+## Scope
+
+Checkpoint 178 added consumer-facing corollaries on top of the checkpoint 177
+explicit-list adjacent diagnosis theorem.
+
+Primary file:
+
+```text
+DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+```
+
+No supporting file changes were needed.
+
+## Implemented Corollaries
+
+### Failure implies recovered-or-overlap
+
+Added:
+
+```lean
+theorem sourcePressureLocalIslandWitnessList_failure_exists_recovered_or_overlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L) :
+    (∃ A B,
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
+          (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+            A B hrev).items).map
+            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2)
+    ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
+```
+
+This combines:
+
+```lean
+sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis
+SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_overlap
+```
+
+### No-overlap failure gives a recovered pair
+
+Added:
+
+```lean
+theorem sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_no_overlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
+    (hno :
+      ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
+    ∃ A B,
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
+          (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+            A B hrev).items).map
+            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2
+```
+
+This eliminates the overlap branch from the recovered-or-overlap corollary.
+
+## Proof Strategy
+
+The first theorem is a direct projection from the list-level adjacent diagnosis
+provided by checkpoint 177.
+
+The second theorem case-splits the first theorem:
+
+```text
+recovered branch:
+  return the recovered adjacent pair
+
+overlap branch:
+  contradict the supplied no-overlap hypothesis
+```
+
+## Meaning
+
+The new API is consumer-facing:
+
+```text
+explicit-list sorted-before failure
+  -> recovered adjacent pair
+     or adjacent overlap obstruction
+```
+
+and under an overlap-free hypothesis:
+
+```text
+explicit-list sorted-before failure
+  -> recovered adjacent pair
+```
+
+## Non-Claims
+
+This checkpoint does not introduce:
+
+```text
+global local-island coverage
+maximality
+uniqueness
+prefix behavior
+arbitrary list sorting
+canonical first diagnosis
+enumeration of all diagnoses
+union accounting
+overlap repair
+Collatz convergence
+```
+
+Recovered budgets remain pair-local.
+Overlap remains an adjacent obstruction on the enclosing explicit list.
+
+## Verification
+
+Passed:
+
+```bash
+lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
+lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
+lake build DkMath.Collatz.PetalBridge.PressureAccounting
+lake build DkMath.Collatz.PetalBridge.PressureFrontier
+lake build DkMath.Collatz.PetalBridge
+git diff --check
+```
+
+No-sorry check:
+
+```bash
+rg -n "\bsorry\b" \
+  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
+  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
+  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+```
+
+Result: no hits.
+
+Known unrelated build warning still appears:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+## Next Candidate
+
+The next natural step is to introduce a small named overlap-free predicate for
+explicit witness lists, then restate the no-overlap recovered theorem against
+that predicate.  This would keep the consumer surface readable while avoiding
+any claim that an overlap-free list exists canonically or globally.
````
`````
