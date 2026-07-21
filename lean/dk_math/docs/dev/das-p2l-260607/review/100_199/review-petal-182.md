# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis

gch: 1116fd86a470eaf6ce39b86e54e6e0c8071fbc2f

## Report

cp181 実装完了です。

[PressureAdjacentDiagnosis.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean) に、既存 carrier から実際の pair-local accounted family object を取り出す `exists_accountedFamily` projection を追加しました。新 carrier は不要でした。あわせて `failure + noAdjacentOverlap` 版と raw `no_overlap` 版の consumer theorem も追加しています。どちらも一つの recovered adjacent pair から得られる family を露出するだけで、aggregation / union accounting は入れていません。

レポートも追加しました:
[report-petal-181.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-181.md)

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis` pass
- `lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction` pass
- `lake build DkMath.Collatz.PetalBridge.PressureAccounting` pass
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier` pass
- `lake build DkMath.Collatz.PetalBridge` pass
- 指定 3 pressure files の `rg -n "\bsorry\b"` は no hit
- `git diff --check` pass

既知の unrelated warning として `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` warning は残っています。

## Review

## 結論

うむ、Checkpoint 181 は **採用** じゃ 👍️
cp180 の carrier から、実際の pair-local accounted interval family object を consumer-facing に露出する薄い projection が入った。

追加された中心は、

```lean id="tw0d2j"
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_accountedFamily
sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_of_no_overlap
```

じゃな。新 carrier は不要で、既存の `SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily` が持っている pair-local recovered branch を、`let F := sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair A B hrev` の形で下流から見えるようにした checkpoint じゃ。aggregation / union accounting には進んでいない。

## 実装レビュー

## 1. `exists_accountedFamily` は良い projection

今回の theorem は、本質的には `exists_pair` と同じ情報を持っている。

ただし、

```lean id="lqox7i"
let F :=
  sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
    A B hrev
```

という形で family object を明示しているのが良い。

これにより、downstream theorem は `A B hrev` から毎回 family を再構成するのではなく、概念上は `F.items` を主語にできる。

これは API として使いやすい。

## 2. 新 carrier を増やさなかった判断が正しい

report にある通り、新 carrier は不要じゃ。

既存の

```lean id="47m7t1"
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily
```

はすでに、

```text id="1w4n9a"
adjacent pair A,B
reverse-before witness hrev
pair-local family budget ≤ -2
```

を保持している。

ここで似た carrier を増やすと、API が二重化する。
今回は projection theorem だけで済ませたのが正解じゃ。

## 3. noAdjacentOverlap 版と raw no_overlap 版の両方が良い

```lean id="bah96c"
sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_of_no_overlap
```

の両方があるので、新しい名前付き predicate を使う caller と、まだ raw negation を持つ caller の両方を受けられる。

この互換性はよい。

## 数学的意味

今回で導線はこうなった。

```text id="h0a1p7"
sorted-before failure L
no adjacent overlap obstruction L
  -> recovered adjacent pair
  -> pair-local accounted interval family F
  -> F.items の net-drop sum ≤ -2
```

これは、overlap-free な明示 witness list における failure が、**一つの pair-local accounted family** として回収される、という意味じゃ。

重要なのは、まだこれが list 全体の family ではないこと。

```text id="6m67gl"
一つの recovered adjacent pair から生じる family
```

だけを露出している。

この境界が守られているので、安全に次へ進める。

## 注意点

## 1. `F` は pair-local family

今回の `F` は、

```lean id="cnrqxd"
sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair A B hrev
```

そのものじゃ。

したがって、次はまだ言っていない。

```text id="xzn5s7"
list 全体の accounted family
複数 recovered pair の aggregation
union accounting
全 interval の disjoint union
```

ここは未到達。

## 2. budget はすでに見えるが、family facts はまだ直接 consumer-facing ではない

今回の theorem では `F.items` の sum ≤ -2 は見える。
ただし、たとえば

```text id="5009hl"
F.items.length = 2
F.items の具体的構成
F.items の pairwise disjoint
sum < 0
```

などを consumer が使うには、まだ projection theorem が薄い可能性がある。

次はそこを整えるのが自然じゃ。

## 次の checkpoint 方針

次は、report の Next Candidate 通り、**exposed family に関する事実を consumer-facing に射影する** のが良い。

特に候補はこの二つ。

```lean id="as58og"
sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_with_budget_neg_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_with_length_two_of_noAdjacentOverlap
```

ただし、既存 theorem 名を確認してから進めるべきじゃ。
過去の流れでは reversed pair family について length / items / budget の theorem があるはずだが、Codex 側で `rg` して正確な名前を拾うのが安全じゃ。

## 次の Codex 指示

```text id="nog9h2"
Checkpoint 182: Main root only — expose basic facts of the pair-local accounted family.

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
Checkpoint 181 added:

- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_accountedFamily
- sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_of_noAdjacentOverlap
- sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_of_no_overlap

These expose the actual pair-local accounted family object:

  let F :=
    sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
      A B hrev

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
- Do not aggregate multiple recovered pairs.
- Do not create a list-wide accounted interval union.

Main goal:
Add thin consumer-facing projections for basic facts of the exposed pair-local
accounted interval family.  The target should remain one recovered adjacent pair
and its existing family object.

Part A: inspect existing reversed-pair family facts.

Search for the exact existing theorem names:

  rg "sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair.*length" DkMath/Collatz/PetalBridge
  rg "sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair.*items" DkMath/Collatz/PetalBridge
  rg "sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair.*sum" DkMath/Collatz/PetalBridge
  rg "reversedLocalIslandWitnessPair.*sum" DkMath/Collatz/PetalBridge
  rg "reversedLocalIslandWitnessPair.*neg" DkMath/Collatz/PetalBridge

Use the existing names if available.  Do not reprove heavy facts.

Part B: projection from carrier to family with negative budget.

If there is already a theorem proving strict negativity for the reversed pair
family, prove:

  theorem
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_accountedFamily_sum_neg
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h :
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L) :
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
            let F :=
              sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
                A B hrev
            ((F.items).map
              (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0

Suggested proof:
- rcases h.exists_pair with ⟨A, B, hin, hrev, hbudget⟩
- either use the existing reversed-pair `sum_neg` theorem,
  or derive from hbudget by integer arithmetic because hbudget says sum ≤ -2.
- If using integer arithmetic, `linarith` may work after setting the sum expression as an Int term.

If strict negativity becomes annoying, skip this theorem.  The existing ≤ -2
projection is already useful.

Part C: projection from carrier to family length, if existing theorem is available.

If a theorem such as

  sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length

exists, prove:

  theorem
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_accountedFamily_length_two
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h :
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L) :
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
            let F :=
              sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
                A B hrev
            F.items.length = 2

If the existing length theorem states a different exact value or uses a different
shape, adapt the statement to match the existing theorem.  Do not force this if
it requires heavy rewriting.

Part D: consumer theorem from failure + named no-overlap with strict negative budget.

If Part B succeeds, prove:

  theorem
      sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_sum_neg_of_noAdjacentOverlap
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
      (hno :
        SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L) :
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
            let F :=
              sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
                A B hrev
            ((F.items).map
              (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0

Proof:
- apply the carrier theorem:
  sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_noAdjacentOverlap
- then apply the Part B projection.

Part E: optional raw-negation wrapper.

Only if Part D succeeds and the wrapper is useful, add:

  theorem
      sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_sum_neg_of_no_overlap
      ...
      (hno : ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
      ...

Do not force this if it duplicates too much.

Part F: do not introduce aggregation.

Do not prove:
- a list of all recovered families,
- sum over all recovered families,
- disjointness between multiple recovered families,
- union accounting,
- coverage,
- overlap repair.

Part G: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-182.md

Include:
- which existing reversed-pair family facts were found;
- whether strict negative budget projection was added;
- whether length projection was added;
- consumer theorem from failure + noAdjacentOverlap if added;
- optional raw-negation wrapper if added;
- explicit note that the exposed family remains pair-local;
- explicit note that no aggregation, union accounting, coverage, maximality,
  uniqueness, sorting, canonical first diagnosis, enumeration, overlap repair,
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

## 総評

cp181 は、consumer-facing API として良い橋じゃ。

これで、下流は

```text id="c7780t"
failure
noAdjacentOverlap
exists pair-local accounted family F
F.items budget ≤ -2
```

まで直接読める。

次は `F` の基本性質を少しだけ露出する。
ただし、まだ合算しない。まだ全列挙しない。
一つの recovered adjacent pair の family に留めるのが正しいぞ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
index 338bcc7d..051eec79 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
@@ -696,6 +696,32 @@ theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.
             (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2 :=
   h

+/--
+Expose the actual pair-local accounted interval family object stored by the
+recovered adjacent-family carrier.
+
+The `let F := ...` form is deliberately consumer-facing: downstream code can
+see the `SourcePressureAccountedIntervalFamily` object and then use `F.items`.
+This is still definitionally the same pair-local recovered branch as
+`exists_pair`; no new list-wide family or aggregation is introduced.
+-/
+theorem
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_accountedFamily
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L) :
+    ∃ A B,
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
+          let F :=
+            sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+              A B hrev
+          ((F.items).map
+            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2 := by
+  rcases h.exists_pair with ⟨A, B, hin, hrev, hbudget⟩
+  exact ⟨A, B, hin, hrev, hbudget⟩
+
 /--
 Empty explicit witness lists cannot contain a recovered adjacent accounted
 family, because they contain no adjacent pair.
@@ -763,6 +789,60 @@ theorem
     (SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.of_not
       hno)

+set_option linter.style.longLine false in
+/--
+Failure plus named no-adjacent-overlap, projected directly to the pair-local
+accounted interval family object.
+
+This theorem only exposes the same recovered family already provided by the
+carrier theorem.  The family is still produced from one adjacent recovered pair;
+there is no list-wide union family and no aggregation over multiple pairs.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_of_noAdjacentOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
+    (hno :
+      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L) :
+    ∃ A B,
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
+          let F :=
+            sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+              A B hrev
+          ((F.items).map
+            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2 :=
+  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_noAdjacentOverlap
+    h hno).exists_accountedFamily
+
+set_option linter.style.longLine false in
+/--
+Raw-negation version of the direct accounted-family projection.
+
+This is a compatibility wrapper for callers that still store no-overlap as the
+raw negation of the adjacent-overlap obstruction predicate.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_of_no_overlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
+    (hno :
+      ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
+    ∃ A B,
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
+          let F :=
+            sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+              A B hrev
+          ((F.items).map
+            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2 :=
+  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_no_overlap
+    h hno).exists_accountedFamily
+
 /--
 Length-three sorted-before failure yields a list-level adjacent diagnosis.

diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-181.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-181.md
new file mode 100644
index 00000000..4a55547a
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-181.md
@@ -0,0 +1,158 @@
+# Report: Petal checkpoint 181
+
+## Summary
+
+Checkpoint 181 exposed the actual pair-local accounted interval family object
+from the recovered adjacent-family carrier.
+
+No new carrier was necessary.  The existing
+`SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily`
+already stores the recovered adjacent pair and the budget over
+`sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair`.
+The new work is a projection with a consumer-facing `let F := ...` form.
+
+## Existing Family Type
+
+The accounted family object is:
+
+```lean
+structure SourcePressureAccountedIntervalFamily
+    (n : OddNat) (k r : ℕ) where
+  items : List (SourcePressureAccountedInterval n k r)
+  pairwiseDisjoint :
+    SourcePressureAccountedIntervalListPairwiseDisjoint items
+```
+
+The recovered pair-local family constructor is:
+
+```lean
+sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+  A B hrev
+```
+
+It returns `SourcePressureAccountedIntervalFamily n k r`.
+
+## Implemented Lean Surface
+
+Implemented in:
+
+```text
+DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+```
+
+New projection:
+
+```lean
+theorem
+  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_accountedFamily
+```
+
+New consumer theorems:
+
+```lean
+theorem
+  sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_of_noAdjacentOverlap
+
+theorem
+  sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_of_no_overlap
+```
+
+The projection exposes:
+
+```lean
+let F :=
+  sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+    A B hrev
+((F.items).map
+  (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2
+```
+
+This makes the family object visible to downstream users while keeping the
+proof route identical to the pair-local recovered branch.
+
+## Guardrail Notes
+
+The exposed family remains pair-local.  It comes from one adjacent recovered
+pair `A, B` in the explicitly supplied witness list.
+
+This checkpoint does not introduce:
+
+- aggregation of recovered families;
+- a list of all recovered families;
+- a sum over all recovered families;
+- disjointness between multiple recovered families;
+- list-wide union accounting;
+- global local-island coverage;
+- maximality;
+- uniqueness;
+- arbitrary list sorting;
+- canonical first diagnosis;
+- enumeration of all diagnoses;
+- overlap repair;
+- Collatz convergence.
+
+## Refactor Check
+
+No split was needed in this checkpoint.
+
+Current relevant file sizes after the change:
+
+```text
+940  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+1391 DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
+1896 DkMath/Collatz/PetalBridge/PressureAccounting.lean
+```
+
+All are below the 2,000-line split threshold.
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
+The next thin bridge can project facts about the exposed family itself, for
+example its recovered reversed-pair length or its negative budget, while still
+keeping the statement tied to one adjacent recovered pair.
+
+That should remain a local projection from the existing family object, not an
+aggregation theorem.
````
`````
