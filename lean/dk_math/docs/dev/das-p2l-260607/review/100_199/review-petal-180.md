# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis

gch: a1f96d2d0c10ca6d5ae9fa034420ce5bff04518d

## Report

cp179 実装完了です。

[PressureAdjacentDiagnosis.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean) に、明示 witness list 用の名前付き predicate `SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction` を追加しました。これは既存の `¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L` の可読性 wrapper だけです。projection / constructor / nil / singleton と、名前付き仮定版の `sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_noAdjacentOverlap` も追加済みです。

レポートも追加しました:
[report-petal-179.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-179.md)

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis` pass
- `lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction` pass
- `lake build DkMath.Collatz.PetalBridge.PressureAccounting` pass
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier` pass
- `lake build DkMath.Collatz.PetalBridge` pass
- 指定 3 pressure files の `rg -n "\bsorry\b"` は no hit
- `git diff --check` pass

既知の unrelated warning として `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` warning は引き続き出ています。今回の変更対象外です。

## Review

## 結論

うむ、Checkpoint 179 は **採用** じゃ 👍️
これは cp178 の no-overlap 仮定を、可読性の高い名前付き predicate に包んだ良い薄層じゃ。

追加された中心は、

```lean id="t9aq75"
SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.not_obstruction
SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.of_not
SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.nil
SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.singleton
sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_noAdjacentOverlap
```

じゃな。新 predicate は既存の `¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L` の可読性 wrapper であり、canonical overlap-free list の存在や coverage を主張していない。境界がきれいに守られている。

## 実装レビュー

## 1. 名前付き no-overlap predicate は良い

```lean id="fur686"
def SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
  ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
```

これは長い名前じゃが、意味が曖昧にならないのが良い。

`OverlapFree` だけだと、

```text id="82g42e"
何の overlap がないのか
global なのか adjacent なのか
canonical list なのか
```

が曖昧になる。

今回の名前は「既存の adjacent-overlap obstruction がない」だけを正確に言っている。

## 2. projection / constructor が最小でよい

```lean id="yuoeh4"
.not_obstruction
.of_not
```

は `exact hno` の薄い theorem じゃが、consumer 側ではかなり効く。

今後 theorem の仮定に、

```lean id="dgg8kz"
hno : SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L
```

と書けるので、raw negation より読みやすい。

## 3. nil / singleton も安全

```lean id="iotqcm"
SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.nil
SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.singleton
```

も良い。

空 list / singleton list には adjacent obstruction はない。
これは後で list induction や短い境界処理に使いやすい。

## 4. named-hypothesis theorem が本命

```lean id="n56fyc"
sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_noAdjacentOverlap
```

により、

```text id="40nppu"
sorted-before failure L
no-adjacent-overlap L
  -> recovered adjacent pair exists
```

が名前付き仮定で読めるようになった。

これは今後の downstream theorem の前提として使いやすい。

## 数学的意味

今回の意味は、こうじゃ。

```text id="3ajq01"
overlap obstruction がない明示 witness list では、
sorted-before failure は必ず pair-local recovered budget を持つ隣接 pair へ落ちる。
```

つまり failure の分岐は、

```text id="u5k32x"
recovered branch
or
overlap obstruction branch
```

であり、今回その overlap branch を名前付き仮定で潰せるようになった。

DkMath 的には、

```text id="fmqen2"
overlap が未処理 Gap
recovered pair が Core 側の回収可能取引
```

として、かなり見通しがよくなった。

## 注意点

## 1. no-overlap は存在定理ではない

今回の predicate は、あくまで与えられた list `L` に対する条件じゃ。

まだ次は言っていない。

```text id="3h5acm"
任意の状況で no-overlap list を構成できる
canonical な overlap-free list がある
global family が overlap-free になる
```

これは未到達。

## 2. recovered は pair-local のまま

今回の conclusion は、隣接 pair `A,B` に紐づく recovered budget じゃ。

list 全体の budget ではない。
union accounting ではない。
全 failure の合算でもない。

この境界は次 checkpoint でも守るべきじゃ。

## 次の一手

次は report の候補通り、**recovered adjacent pair を既存の pair-local accounted interval family API に包み直す薄い bridge** がよい。

狙いは、

```text id="1egzwh"
failure L
noAdjacentOverlap L
  -> exists adjacent pair A B in L
  -> its reversed recovered pair produces an accounted interval family
  -> that family has pair-local budget ≤ -2
```

じゃ。

まだ union accounting はしない。
list 全体の family にもしない。
あくまで、**一つの recovered adjacent pair** を accounted family として再公開する。

## 次の Codex 指示

```text id="c0evwl"
Checkpoint 180: Main root only — package no-overlap recovered adjacent pair as pair-local accounted family.

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
Checkpoint 179 added:

- SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
- SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.not_obstruction
- SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.of_not
- SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.nil
- SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.singleton
- sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_noAdjacentOverlap

The current recovered theorem gives:

  ∃ A B,
    SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
      ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
        (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          A B hrev).items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2

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
- Do not aggregate multiple recovered pairs.

Main goal:
Add a small named predicate/carrier that says an explicit witness list contains
one adjacent pair whose reversed recovered pair yields a pair-local accounted
interval family with budget ≤ -2.  Then prove it from sorted-before failure plus
named no-adjacent-overlap.

Part A: define a pair-local recovered accounted-family carrier.

Suggested name:

  def SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily
      {n : OddNat} {k r : Nat}
      (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
    ∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
          (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
            A B hrev).items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2

Notes:
- This is intentionally just a named carrier for the existing recovered branch.
- The accounted family is the existing
  sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair A B hrev.
- Do not add list-level union accounting.
- Do not aggregate multiple families.

Part B: constructor from explicit pair evidence.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.of_pair
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {A B : SourcePressureLocalIslandWitness n k r}
      (hin :
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B)
      (hrev : SourcePressureLocalIslandWitnessBefore B A)
      (hbudget :
        (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          A B hrev).items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L

Expected proof:
- exact ⟨A, B, hin, hrev, hbudget⟩

Part C: projection back to recovered pair.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_pair
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h :
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L) :
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
            (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
              A B hrev).items).map
              (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2

Expected proof:
- exact h

Part D: theorem from failure and named no-overlap.

Prove:

  theorem sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_noAdjacentOverlap
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
      (hno :
        SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L) :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L

Suggested proof:
- rcases sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_noAdjacentOverlap
    h hno with ⟨A, B, hin, hrev, hbudget⟩
- exact SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.of_pair
    hin hrev hbudget

Part E: optional ordinary raw-negation wrapper.

Only if useful, also prove:

  theorem sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_no_overlap
      ...
      (hno : ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L

by using
  SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.of_not hno

Do not force this if it duplicates too much API.

Part F: optional empty/singleton impossibility.

Do not force this.
If easy, prove that empty/singleton lists do not have recovered adjacent accounted family, using existing adjacent-pair nil/singleton false lemmas.

Part G: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-180.md

Include:
- the recovered-adjacent-accounted-family carrier;
- constructor/projection theorem;
- failure + noAdjacentOverlap theorem;
- optional raw-negation wrapper if added;
- explicit note that this only packages one pair-local recovered family;
- explicit note that no list-level union accounting, aggregation, coverage,
  maximality, uniqueness, sorting, canonical first diagnosis, enumeration,
  overlap repair, or Collatz convergence was introduced;
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

Checkpoint 180 が通ったら、次は **この pair-local recovered family から、既存の pair budget theorem を consumer が使いやすい形で射影する** のが良い。

たとえば、

```text id="iz49hw"
HasRecoveredAdjacentAccountedFamily L
  -> exists accounted family with sum ≤ -2
```

のような theorem じゃ。

ただし、ここでも list 全体の union accounting はしない。
まだ「一つの pair-local recovered family が存在する」だけ。

## 総評

cp179 はとても良い整理じゃ。

raw negation が名前を持ったことで、以後の theorem は読みやすくなる。

次は、その no-overlap branch で得られる recovered pair を、`accounted interval family` として明示的に包む。
ここまで進むと、

```text id="cfto0u"
failure
no-overlap
recovered adjacent pair
pair-local accounted family
budget ≤ -2
```

という一本の導線ができる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
index ce2e4107..f9b27bc2 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
@@ -432,6 +432,55 @@ theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovere
   · exact Or.inl ⟨A, B, hin, hrecovered⟩
   · exact Or.inr hobs
 
+/--
+Named no-adjacent-overlap condition for an explicitly supplied witness list.
+
+This is deliberately only a readability wrapper around the negation of the
+existing adjacent-overlap obstruction predicate.  It does not say that the list
+is globally overlap-free, canonical, maximal, sorted, complete, or repaired; it
+only says that this explicit list has no neighboring overlap obstruction in
+the sense already defined by
+`SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction`.
+-/
+def SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
+  ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
+
+/-- Project the named no-adjacent-overlap wrapper back to the raw negation. -/
+theorem SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.not_obstruction
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hno :
+      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L) :
+    ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L :=
+  hno
+
+/-- Construct the named no-adjacent-overlap wrapper from the raw negation. -/
+theorem SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.of_not
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hno :
+      ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
+    SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L :=
+  hno
+
+/-- Empty explicit witness lists have no adjacent-overlap obstruction. -/
+theorem SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.nil
+    {n : OddNat} {k r : ℕ} :
+    SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
+      ([] : List (SourcePressureLocalIslandWitness n k r)) := by
+  intro h
+  exact h
+
+/-- Singleton explicit witness lists have no adjacent-overlap obstruction. -/
+theorem SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.singleton
+    {n : OddNat} {k r : ℕ}
+    {W : SourcePressureLocalIslandWitness n k r} :
+    SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction [W] := by
+  intro h
+  exact h
+
 /-- The empty witness list cannot carry a list-level adjacent diagnosis. -/
 theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.nil_false
     {n : OddNat} {k r : ℕ} :
@@ -570,6 +619,32 @@ theorem sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_no_over
   · exact hrec
   · exact False.elim (hno hobs)
 
+/--
+Named no-adjacent-overlap version of the recovered-pair projection.
+
+This is the consumer-facing form for callers that track the no-overlap branch
+with the explicit wrapper introduced above.  The conclusion is unchanged from
+`sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_no_overlap`:
+one adjacent pair in the supplied list carries a pair-local recovered budget.
+No global overlap-free construction, list coverage, union accounting, or
+Collatz convergence is introduced here.
+-/
+theorem sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_noAdjacentOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
+    (hno :
+      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L) :
+    ∃ A B,
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
+          (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+            A B hrev).items).map
+            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2 :=
+  sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_no_overlap
+    h hno.not_obstruction
+
 /--
 Length-three sorted-before failure yields a list-level adjacent diagnosis.
 
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-179.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-179.md
new file mode 100644
index 00000000..eecb855c
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-179.md
@@ -0,0 +1,144 @@
+# Report: Petal checkpoint 179
+
+## Summary
+
+Checkpoint 179 added a named no-adjacent-overlap predicate for explicit
+source-pressure local-island witness lists.
+
+The new predicate is intentionally only a readability wrapper around the
+existing adjacent-overlap obstruction negation:
+
+```lean
+def SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
+  ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
+```
+
+This keeps the cp178 theorem surface intact while giving downstream callers a
+named hypothesis instead of a raw negation.
+
+## Implemented Lean Surface
+
+Implemented in:
+
+```text
+DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+```
+
+New API:
+
+```lean
+def SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
+
+theorem
+  SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.not_obstruction
+
+theorem
+  SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.of_not
+
+theorem
+  SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.nil
+
+theorem
+  SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.singleton
+
+theorem
+  sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_noAdjacentOverlap
+```
+
+The consumer theorem is the named-hypothesis version of the cp178 raw-negation
+theorem:
+
+```lean
+sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_no_overlap
+```
+
+Its conclusion is unchanged: from a sorted-before failure and no adjacent
+overlap obstruction, one adjacent pair in the supplied explicit list carries a
+pair-local recovered budget.
+
+## Guardrail Notes
+
+This checkpoint does not introduce a broader overlap-free concept.
+
+In particular, it does not assert:
+
+- existence of a canonical overlap-free list;
+- global local-island coverage;
+- maximality;
+- uniqueness;
+- prefix behavior;
+- arbitrary list sorting;
+- canonical first diagnosis;
+- enumeration of all diagnoses;
+- union accounting;
+- overlap repair;
+- Collatz convergence.
+
+Recovered budgets remain pair-local.  Overlap remains an adjacent obstruction
+on the enclosing explicit list.
+
+## Refactor Check
+
+No split was needed in this checkpoint.
+
+Current relevant file sizes after the change:
+
+```text
+742  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+1391 DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
+```
+
+Both remain below the 2,000-line split threshold.
+
+## Verification
+
+Commands run from `lean/dk_math`:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
+lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
+lake build DkMath.Collatz.PetalBridge.PressureAccounting
+lake build DkMath.Collatz.PetalBridge.PressureFrontier
+lake build DkMath.Collatz.PetalBridge
+```
+
+All builds completed successfully.
+
+No-sorry check:
+
+```text
+rg -n "\bsorry\b" \
+  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
+  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
+  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+```
+
+Result: no output, exit code 1, so no `sorry` was found in the checked pressure
+files.
+
+Whitespace check from repository root:
+
+```text
+git diff --check
+```
+
+Result: pass.
+
+Known unrelated build warning remains:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+This checkpoint did not modify that file.
+
+## Next Candidate
+
+The next thin bridge can use the named no-adjacent-overlap predicate to package
+the recovered adjacent pair into an existing pair-local accounted interval
+family.  That should still avoid union accounting: it should only re-expose the
+one recovered pair already produced by
+`sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_noAdjacentOverlap`.
````
`````
