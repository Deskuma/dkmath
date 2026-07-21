# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis

gch: 98a78d9384e7bedba82324014c26b3251defb697

## Report

cp180 実装完了です。

[PressureAdjacentDiagnosis.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean) に、pair-local recovered branch を包む `SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily` を追加しました。`of_pair` / `exists_pair` / `nil_false` / `singleton_false` と、`noAdjacentOverlap` 版・raw `no_overlap` 版の consumer theorem も追加しています。主張は一つの adjacent pair の accounted family に限定し、union accounting や aggregation は入れていません。

レポートも追加しました:
[report-petal-180.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-180.md)

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

うむ、Checkpoint 180 は **採用** じゃ 👍️
cp179 の no-adjacent-overlap branch から得られる recovered adjacent pair を、さらに **pair-local accounted interval family** として包む carrier が入った。

追加された中心は、

```lean
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.of_pair
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_pair
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.nil_false
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.singleton_false
sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_no_overlap
```

じゃな。主張は一つの adjacent pair の accounted family に限定されており、union accounting や aggregation には踏み込んでいない。境界管理もよい。

## 実装レビュー

## 1. carrier の粒度がちょうどよい

今回の carrier は、

```lean
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L
```

として、明示 list `L` の中に、

```text
隣接 pair A,B があり、
B before A の reversed recovered evidence があり、
その pair-local accounted family の budget が ≤ -2
```

であることを包んでいる。

これは cp178 / cp179 で得た recovered branch の自然な名前付けじゃ。

重要なのは、ここで **list 全体の accounted family** を作っていないこと。
あくまで、

```lean
sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair A B hrev
```

という既存の **pair-local family** を再公開しているだけじゃ。

この控えめさが正しい。

## 2. `of_pair` / `exists_pair` は良い対称 API

```lean
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.of_pair
```

で包み、

```lean
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_pair
```

で戻せる。

この往復 API があるので、consumer は carrier を使っても、必要なときには `A B hrev hbudget` を取り出せる。

これは今後の downstream theorem に効く。

## 3. nil / singleton false も安全

```lean
nil_false
singleton_false
```

もよい。

理由は単純で、空 list / singleton list には adjacent pair が存在しない。
したがって recovered adjacent accounted family も存在しない。

この末端補題は、後で induction や short-list case を潰すのに便利じゃ。

## 4. named no-overlap 版と raw negation 版の両方があるのも良い

```lean
sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_noAdjacentOverlap
```

が本命 API。

さらに互換用として、

```lean
sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_no_overlap
```

もある。

これは downstream がまだ raw negation で持っている場合に使える。
既存 theorem を壊さず、移行しやすい。

## 数学的意味

今回で、次の導線が一本につながった。

```text
sorted-before failure L
no adjacent overlap obstruction L
  -> recovered adjacent pair exists
  -> pair-local accounted interval family exists
  -> its net-drop budget is ≤ -2
```

これはかなり良い。

DkMath 的には、

```text
failure:
  list の局所順序破綻

no-overlap:
  未処理 Gap branch を排除

recovered adjacent accounted family:
  破綻を pair-local accounting に回収
```

と読める。

つまり、overlap-free な明示 list では、failure は単なる破綻ではなく、**回収可能な局所会計単位** として取り出せる。

## 注意点

## 1. まだ list-wide union accounting ではない

今回の carrier は、名前に `List` が入っていても、結論は一つの adjacent pair じゃ。

まだ次は言っていない。

```text
list 全体の recovered pairs を集約する
複数 accounted families を合算する
interval union を取る
全 failure を列挙する
```

ここは未到達。

## 2. no-overlap は仮定

今回も、

```lean
SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L
```

は仮定じゃ。

canonical overlap-free list の存在はまだ主張していない。
global construction でもない。

## 3. theorem 名は長いが、今はこれでよい

`sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_noAdjacentOverlap`

は長い。
だが、証明ルートを隠していないので、今の段階ではむしろ安全じゃ。

短縮名は、意味が安定してから alias として足せばよい。

## 次の一手

次は report の Next Candidate 通り、carrier から **accounted interval family object そのものを existential として取り出す bridge** が自然じゃ。

今の `exists_pair` は、

```text
A, B, hin, hrev, hbudget
```

を返す。

次は consumer が pair を手動で unpack しなくてもよいように、

```text
何らかの accounted interval family F があり、
F.items の net-drop sum ≤ -2
```

という形に射影する。

ただし、この `F` は一つの pair-local family だけ。
list-wide union family ではない。

## 次の Codex 指示

```text
Checkpoint 181: Main root only — project recovered adjacent carrier to explicit pair-local accounted family object.

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
Checkpoint 180 added:

- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.of_pair
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_pair
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.nil_false
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.singleton_false
- sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_noAdjacentOverlap
- sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_no_overlap

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
Add a thin projection from
`SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L`
to an existential that exposes the actual pair-local accounted interval family
object produced by the recovered adjacent pair.

Part A: inspect the exact type of `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair`.

Search its declaration and confirm the family type name and fields.

Likely shape:

  sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
    A B hrev

has fields:
- `.items`
- maybe a sorted/family proof

Do not invent a new family type unless absolutely necessary.

Part B: define an explicit carrier for one accounted family object, only if the type is not too verbose.

If useful, define:

  def SourcePressureLocalIslandWitnessListHasPairLocalAccountedFamily
      {n : OddNat} {k r : Nat}
      (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
    ∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
          let F :=
            sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
              A B hrev
          ((F.items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2

However, if this duplicates the existing
`SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily`, skip
this definition.  The existing carrier may already be enough.

Part C: preferred theorem — expose the family object by existential.

Prove a theorem with a precise name such as:

  theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_accountedFamily
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
              (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2

This may be definitionally identical to `exists_pair`.
If so, prove it as:

  exact h.exists_pair

or simply by unpacking and repacking.

Part D: consumer theorem from failure + named no-overlap.

Prove:

  theorem sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_of_noAdjacentOverlap
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
              (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2

Suggested proof:
- use
  sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_noAdjacentOverlap
- then apply `.exists_accountedFamily` or `.exists_pair`.

Part E: optional raw-negation wrapper.

Only if useful, prove the raw-negation version:

  theorem sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_of_no_overlap
      ...
      (hno : ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
      ...

Do not force this if it duplicates too much.

Part F: do not introduce aggregation.

Do not prove:
- a Finset/List of all recovered families,
- sum over all recovered families,
- disjointness of recovered families,
- union accounting,
- coverage,
- overlap repair.

Part G: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-181.md

Include:
- whether a new carrier was necessary or existing carrier was enough;
- the exists-accounted-family projection theorem;
- consumer theorem from failure + noAdjacentOverlap;
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

cp180 は、ここまでの導線を一段見やすくした checkpoint じゃ。

これで、

```text
failure
noAdjacentOverlap
recovered adjacent pair
pair-local accounted family
budget ≤ -2
```

まで一本で読める。

次は、その accounted family を consumer が直接使いやすい形へ射影する。
ただし、まだ合算しない。まだ union しない。
一つの pair-local family を、ただ取り出すだけじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
index f9b27bc2..338bcc7d 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
@@ -645,6 +645,124 @@ theorem sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_noAdjac
   sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_no_overlap
     h hno.not_obstruction

+/--
+Carrier saying that an explicit witness list contains one adjacent pair whose
+reversed order yields a pair-local accounted interval family with budget
+`≤ -2`.
+
+This is only a named package for the existing recovered branch.  The accounted
+family is exactly
+`sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair A B hrev`
+for one adjacent pair `A, B` already occurring in the supplied list.  It does
+not aggregate multiple recovered pairs, merge intervals, perform union
+accounting, or claim coverage of all local islands.
+-/
+def SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
+  ∃ A B,
+    SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+      ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
+        (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+          A B hrev).items).map
+          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2
+
+/-- Build the recovered accounted-family carrier from explicit adjacent-pair evidence. -/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.of_pair
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {A B : SourcePressureLocalIslandWitness n k r}
+    (hin :
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B)
+    (hrev : SourcePressureLocalIslandWitnessBefore B A)
+    (hbudget :
+      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+        A B hrev).items).map
+        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) :
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L :=
+  ⟨A, B, hin, hrev, hbudget⟩
+
+/-- Project the carrier back to the underlying recovered adjacent pair. -/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_pair
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L) :
+    ∃ A B,
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
+          (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+            A B hrev).items).map
+            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2 :=
+  h
+
+/--
+Empty explicit witness lists cannot contain a recovered adjacent accounted
+family, because they contain no adjacent pair.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.nil_false
+    {n : OddNat} {k r : ℕ} :
+    ¬ SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily
+      ([] : List (SourcePressureLocalIslandWitness n k r)) := by
+  rintro ⟨A, B, hin, _⟩
+  exact SourcePressureLocalIslandWitnessAdjacentPairInList.nil_false hin
+
+/--
+Singleton explicit witness lists cannot contain a recovered adjacent accounted
+family, because they contain no adjacent pair.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.singleton_false
+    {n : OddNat} {k r : ℕ}
+    {W : SourcePressureLocalIslandWitness n k r} :
+    ¬ SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily [W] := by
+  rintro ⟨A, B, hin, _⟩
+  exact SourcePressureLocalIslandWitnessAdjacentPairInList.singleton_false hin
+
+set_option linter.style.longLine false in
+/--
+A failed explicit witness list with no adjacent overlap obstruction contains a
+recovered adjacent pair packaged as one pair-local accounted interval family.
+
+This is still only a one-pair statement.  It reuses the recovered pair obtained
+from the no-adjacent-overlap projection and does not add list-level union
+accounting or aggregation.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_noAdjacentOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
+    (hno :
+      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L) :
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L := by
+  rcases sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_noAdjacentOverlap
+      h hno with ⟨A, B, hin, hrev, hbudget⟩
+  exact
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.of_pair
+      hin hrev hbudget
+
+set_option linter.style.longLine false in
+/--
+Raw-negation version of the recovered accounted-family carrier theorem.
+
+This keeps compatibility with callers that still store the no-overlap branch as
+`¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L`.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_no_overlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
+    (hno :
+      ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L :=
+  sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_noAdjacentOverlap
+    h
+    (SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.of_not
+      hno)
+
 /--
 Length-three sorted-before failure yields a list-level adjacent diagnosis.

diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-180.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-180.md
new file mode 100644
index 00000000..d67bca19
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-180.md
@@ -0,0 +1,174 @@
+# Report: Petal checkpoint 180
+
+## Summary
+
+Checkpoint 180 packaged the no-adjacent-overlap recovered branch as a named
+pair-local accounted-family carrier.
+
+The new carrier says only that the explicit witness list contains one adjacent
+pair `A, B` whose reversed order gives the existing pair-local accounted
+interval family with budget `≤ -2`.
+
+It does not aggregate multiple recovered pairs and does not introduce
+list-level union accounting.
+
+## Implemented Lean Surface
+
+Implemented in:
+
+```text
+DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+```
+
+New carrier:
+
+```lean
+def SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
+  ∃ A B,
+    SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+      ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
+        (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+          A B hrev).items).map
+          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2
+```
+
+New API:
+
+```lean
+theorem
+  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.of_pair
+
+theorem
+  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_pair
+
+theorem
+  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.nil_false
+
+theorem
+  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.singleton_false
+
+theorem
+  sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_noAdjacentOverlap
+
+theorem
+  sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_no_overlap
+```
+
+The raw-negation wrapper was added for callers that still store the no-overlap
+branch as:
+
+```lean
+¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
+```
+
+The named no-overlap theorem uses:
+
+```lean
+SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L
+```
+
+## Guardrail Notes
+
+This checkpoint only packages one recovered adjacent pair and its existing
+pair-local accounted interval family.
+
+It does not assert:
+
+- list-level union accounting;
+- aggregation of multiple recovered pairs;
+- global local-island coverage;
+- maximality;
+- uniqueness;
+- prefix behavior;
+- arbitrary list sorting;
+- canonical first diagnosis;
+- enumeration of all diagnoses;
+- overlap repair;
+- existence of a canonical overlap-free list;
+- Collatz convergence.
+
+Recovered budgets remain pair-local.  Overlap remains an adjacent obstruction
+on the enclosing explicit list.
+
+## Style Note
+
+The two consumer-facing theorem names are long because they intentionally
+encode the whole proof route:
+
+```text
+failure + noAdjacentOverlap -> hasRecoveredAdjacentAccountedFamily
+failure + raw no_overlap    -> hasRecoveredAdjacentAccountedFamily
+```
+
+The declarations use local `set_option linter.style.longLine false in`
+wrappers so the searchable theorem names remain intact without affecting the
+rest of the file.
+
+## Refactor Check
+
+No split was needed in this checkpoint.
+
+Current relevant file sizes after the change:
+
+```text
+860  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
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
+The next thin bridge can project from
+`SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L` to
+an explicit existential over the accounted interval family object itself, so a
+consumer can use the family without unpacking the adjacent pair manually.
+
+That bridge should still remain pair-local and avoid any claim about list-wide
+union accounting or aggregation.
````
`````
