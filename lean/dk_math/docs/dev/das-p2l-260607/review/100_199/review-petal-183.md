# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis

gch: eb0f316d26ca2f38ee6a0b0ffc850966578d2f59

## Report

cp182 を完了しました。

`PressureAdjacentDiagnosis.lean` に、回収された隣接ペア由来の accounted family から次を取り出す補題を追加しました。

- `exists_accountedFamily_sum_neg`
- `exists_accountedFamily_length_two`
- `..._of_noAdjacentOverlap`
- raw negation wrapper `..._of_no_overlap`

内容はすべて pair-local のままです。リスト全体の union accounting や coverage には踏み込んでいません。

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b" ...
git diff --check
```

`rg` は対象 3 ファイルで no match、`git diff --check` も通過です。

レポートも追加しました。

`lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-182.md`

## Review

## 結論

うむ、Checkpoint 182 は **採用** じゃ 👍️
cp181 で露出した pair-local accounted family object について、下流がすぐ使いたい基本事実を追加できている。

追加された中心は、

```lean id="qumtgg"
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_accountedFamily_sum_neg
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_accountedFamily_length_two
sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_sum_neg_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_sum_neg_of_no_overlap
```

じゃな。既存の reversed-pair family 補題 `_sum_neg` と `_length` を再利用し、strict negativity と `items.length = 2` を pair-local のまま consumer-facing に出している。リスト全体の aggregation / union accounting / coverage には進んでいない。よい境界管理じゃ。

## 実装レビュー

## 1. strict negativity の出し方が良い

```lean id="p5dkvf"
exists_accountedFamily_sum_neg
```

は、保存していた `≤ -2` から `linarith` で `< 0` を出すのではなく、既存の

```lean id="ksk66x"
sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
```

を使っている。

これは良い。
既存 API の意味を再利用しており、証明の責任が分散しない。

## 2. length-two projection も自然

```lean id="7q79jh"
exists_accountedFamily_length_two
```

も良い。

reversed adjacent pair から作られる accounted family が `items.length = 2` であることを、下流から直接読めるようになった。

これは後で、

```text id="1ga7zi"
この recovered artifact は二項の局所取引である
```

と見るための足場になる。

## 3. consumer wrapper は薄くて正しい

```lean id="mq9u7s"
sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_sum_neg_of_noAdjacentOverlap
```

は、

```text id="xgqtxw"
failure
noAdjacentOverlap
  -> recovered adjacent accounted family
  -> sum_neg
```

という既存導線をただ合成している。

これも正しい薄層じゃ。
raw negation wrapper も互換性のために有用。

## 数学的意味

今回で、overlap-free な explicit failure list から、次の形が得られるようになった。

```text id="k96o2k"
there exists a recovered adjacent pair,
and its explicit two-item accounted family has negative total net drop.
```

DkMath 的には、これはかなり良い局所診断じゃ。

```text id="gnxw2l"
failure:
  list 内の sorted-before 破綻

noAdjacentOverlap:
  overlap obstruction branch を排除

recovered adjacent accounted family:
  一つの隣接 pair に回収される局所会計

sum_neg:
  その局所会計は正味で下降側

length_two:
  その局所会計は二項構造
```

ここまでで、「overlap がなければ failure は二項の負 budget として回収される」という輪郭がかなり締まった。

## 注意点

## 1. まだ合算ではない

今回も、あくまで **一つの recovered adjacent pair** の話じゃ。

まだ次は言っていない。

```text id="5r9ams"
全 recovered pair の列挙
複数 family の合算
pairwise disjointness between recovered families
list-wide union accounting
```

ここは未到達。

## 2. length-two は enclosing list の長さではない

`F.items.length = 2` は、pair-local accounted family の items が 2 個という意味じゃ。

`L.length = 2` ではない。
ここを混同しないのが大事じゃ。

## 3. 次は bundle record が自然

report の Next Inference にある通り、次は aggregation ではなく、繰り返し destructuring を減らすための **pair-local diagnostic record / carrier** がよい。

今は、

```lean id="94gdtt"
exists_accountedFamily
exists_accountedFamily_sum_neg
exists_accountedFamily_length_two
```

が別々にある。

次はこれらを一つに束ねて、

```text id="k80fle"
one recovered adjacent pair
one pair-local family F
budget ≤ -2
sum < 0
items.length = 2
```

をまとめて取り出せるようにするのが安全じゃ。

## 次の Codex 指示

```text id="eo03ji"
Checkpoint 183: Main root only — bundle recovered adjacent accounted-family facts into one pair-local diagnostic carrier.

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
Checkpoint 182 added:

- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_accountedFamily_sum_neg
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_accountedFamily_length_two
- sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_sum_neg_of_noAdjacentOverlap
- sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_sum_neg_of_no_overlap

The existing carrier already gives the pair-local budget `≤ -2`.
The new cp182 projections expose:
- strict negativity of the same family;
- length-two structure of the same family.

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
- Do not prove disjointness between multiple recovered families.

Main goal:
Create a small bundled consumer-facing carrier for one recovered adjacent
accounted-family diagnostic, combining:
- adjacent pair membership in the explicit list;
- reversed-before witness;
- the pair-local accounted family object;
- budget `≤ -2`;
- strict negative budget `< 0`;
- `items.length = 2`.

This is only a packaging layer for one pair-local recovered family.

Part A: define bundled pair-local diagnostic carrier.

Suggested name:

  def SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
      {n : OddNat} {k r : Nat}
      (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
    ∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
          let F :=
            sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
              A B hrev
          (((F.items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
          (((F.items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
          F.items.length = 2

Notes:
- This carrier is intentionally redundant: `< 0` follows from `≤ -2`, but
  downstream callers may want both facts without reproving them.
- This is still one pair-local family.
- Do not include any list-wide aggregation.

Part B: constructor from explicit pair evidence.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {A B : SourcePressureLocalIslandWitness n k r}
      (hin :
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B)
      (hrev : SourcePressureLocalIslandWitnessBefore B A)
      (hbudget :
        let F :=
          sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
            A B hrev
        ((F.items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2)
      (hneg :
        let F :=
          sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
            A B hrev
        ((F.items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0)
      (hlen :
        let F :=
          sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
            A B hrev
        F.items.length = 2) :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic L

If the repeated `let F := ...` makes the statement hard, use the expanded
expression matching the carrier definition exactly.

Part C: projection from existing recovered carrier.

Prove:

  theorem
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.toDiagnostic
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h :
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L) :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic L

Suggested proof:
- unpack h.exists_pair to get A B hin hrev hbudget;
- use existing reversed-pair facts:
  sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
  sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length
- package all three facts.

Part D: projection back to existing carrier.

Prove:

  theorem
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.toRecoveredAdjacentAccountedFamily
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h :
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic L) :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L

Suggested proof:
- unpack diagnostic;
- use SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.of_pair
  with the `≤ -2` budget.

Part E: consumer theorem from failure + named no-overlap.

Prove:

  theorem
      sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
      (hno :
        SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L) :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic L

Suggested proof:
- use
  sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_noAdjacentOverlap
- then apply `.toDiagnostic`.

Part F: optional raw-negation wrapper.

Only if useful, add:

  theorem
      sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_no_overlap
      ...
      (hno : ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic L

Part G: optional projections from diagnostic.

If easy, add projections:

  theorem ...Diagnostic.exists_accountedFamily_sum_neg
  theorem ...Diagnostic.exists_accountedFamily_length_two
  theorem ...Diagnostic.exists_pair

But avoid excessive duplication.  The main value is the bundled carrier and
conversion theorems.

Part H: do not introduce aggregation.

Do not prove:
- a list of all recovered families,
- sum over all recovered families,
- disjointness between multiple recovered families,
- union accounting,
- coverage,
- overlap repair.

Part I: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-183.md

Include:
- the bundled diagnostic carrier;
- conversion from existing recovered carrier to diagnostic;
- conversion from diagnostic back to existing carrier;
- consumer theorem from failure + noAdjacentOverlap;
- optional raw-negation wrapper if added;
- explicit note that the diagnostic remains one pair-local recovered family;
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

cp182 はかなり良い薄層じゃ。

これで下流は、

```text id="z2w9h"
one recovered adjacent pair
pair-local family F
F.items.length = 2
sum F.items < 0
```

まで直接読める。

次は、それらを一つの diagnostic carrier に束ねる。
まだ合算しない。まだ列挙しない。
「一つの回収可能な二項局所会計」として固定するのが、いま一番安全な前進じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
index 051eec79..cf39fada 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
@@ -722,6 +722,59 @@ theorem
   rcases h.exists_pair with ⟨A, B, hin, hrev, hbudget⟩
   exact ⟨A, B, hin, hrev, hbudget⟩

+set_option linter.style.longLine false in
+/--
+Expose strict negativity for the recovered pair-local accounted family.
+
+This projection uses the existing reversed-pair family theorem rather than
+deriving negativity from the stored `≤ -2` budget.  The result is still about
+one adjacent recovered pair only.
+-/
+theorem
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_accountedFamily_sum_neg
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
+            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0 := by
+  rcases h.exists_pair with ⟨A, B, hin, hrev, _hbudget⟩
+  exact ⟨A, B, hin, hrev,
+    sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
+      A B hrev⟩
+
+set_option linter.style.longLine false in
+/--
+Expose the length of the recovered pair-local accounted family.
+
+The recovered family is built from a reversed adjacent pair, so its explicit
+`items` list has length `2`.  This is a pair-local structural fact, not a
+statement about the length of the enclosing witness list.
+-/
+theorem
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_accountedFamily_length_two
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
+          F.items.length = 2 := by
+  rcases h.exists_pair with ⟨A, B, hin, hrev, _hbudget⟩
+  exact ⟨A, B, hin, hrev,
+    sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length
+      A B hrev⟩
+
 /--
 Empty explicit witness lists cannot contain a recovered adjacent accounted
 family, because they contain no adjacent pair.
@@ -843,6 +896,59 @@ theorem
   (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_no_overlap
     h hno).exists_accountedFamily

+set_option linter.style.longLine false in
+/--
+Failure plus named no-adjacent-overlap, projected to a pair-local recovered
+accounted family with strictly negative listed cost.
+
+This is a direct consumer wrapper over the carrier-level strict-negativity
+projection.  It does not combine multiple families.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_sum_neg_of_noAdjacentOverlap
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
+            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0 :=
+  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_noAdjacentOverlap
+    h hno).exists_accountedFamily_sum_neg
+
+set_option linter.style.longLine false in
+/--
+Raw-negation version of the strict-negative accounted-family projection.
+
+This keeps compatibility with callers that have not yet switched to the named
+no-adjacent-overlap predicate.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_sum_neg_of_no_overlap
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
+            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0 :=
+  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_no_overlap
+    h hno).exists_accountedFamily_sum_neg
+
 /--
 Length-three sorted-before failure yields a list-level adjacent diagnosis.

diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-182.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-182.md
new file mode 100644
index 00000000..12ccdf07
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-182.md
@@ -0,0 +1,144 @@
+# report-petal-182
+
+Date: 2026-07-06
+
+## Scope
+
+This checkpoint continues the pair-local pressure accounting surface in
+`DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis`.
+
+The requested target was to expose two already-known structural facts of the
+recovered adjacent accounted family:
+
+- the listed recovered budget is strictly negative;
+- the accounted interval family built from the recovered pair has length `2`.
+
+No global coverage, maximality, uniqueness, sorting, first-diagnosis,
+enumeration, union accounting, overlap repair, or Collatz convergence claim is
+introduced.
+
+## Existing facts used
+
+The implementation reuses the reversed-pair accounted family facts from
+`PressureLocalWitnessObstruction.lean`:
+
+- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length`
+- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_items`
+- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two`
+- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg`
+
+For this checkpoint, the direct dependencies are:
+
+- `_sum_neg` for strict negativity;
+- `_length` for the length-two projection.
+
+## Implemented theorem surface
+
+Added carrier-level projections:
+
+```lean
+theorem
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_accountedFamily_sum_neg
+```
+
+This exposes an adjacent pair `A B`, the reverse-before witness `hrev`, and the
+associated reversed-pair accounted family whose listed net drop sum is `< 0`.
+
+```lean
+theorem
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_accountedFamily_length_two
+```
+
+This exposes the same pair-local family and records that its explicit
+`items.length = 2`.
+
+Added consumer wrappers:
+
+```lean
+theorem
+    sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_sum_neg_of_noAdjacentOverlap
+```
+
+This combines sorted-before failure with the named no-adjacent-overlap
+predicate and returns a strictly negative recovered accounted family.
+
+```lean
+theorem
+    sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_sum_neg_of_no_overlap
+```
+
+This is the raw-negation compatibility wrapper for callers that still hold
+`¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L`.
+
+## Mathematical reading
+
+The recovered family is still a single adjacent-pair artifact.  The theorem
+surface now lets downstream callers read both:
+
+```text
+there exists a recovered adjacent pair,
+and its explicit two-item accounted family has negative total net drop.
+```
+
+This is intentionally weaker than any list-wide accounting theorem.  The
+result says that one local failure can be converted into one local recovered
+budget witness, not that all local failures have been globally reconciled.
+
+## File-size check
+
+Current line counts:
+
+```text
+1046 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+1391 lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
+1896 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+```
+
+`PressureAdjacentDiagnosis.lean` remains below the 2000-line local watch limit.
+
+## Verification
+
+Targeted builds run before this report:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
+lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
+lake build DkMath.Collatz.PetalBridge.PressureAccounting
+lake build DkMath.Collatz.PetalBridge.PressureFrontier
+lake build DkMath.Collatz.PetalBridge
+```
+
+All completed successfully.
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
+Result: no matches.  `rg` exited with code `1`, which is the expected
+no-match result.
+
+Whitespace check:
+
+```text
+git diff --check
+```
+
+Result: passed.
+
+## Next inference
+
+The next useful step is probably not aggregation yet.  The API now has:
+
+1. existence of a recovered adjacent accounted family;
+2. strict negativity of that family;
+3. length-two structure of that family.
+
+The next safe local theorem would be a named consumer that bundles these as one
+pair-local diagnostic record, if repeated downstream destructuring becomes
+noisy.  That should still avoid list-wide union accounting unless a separate
+disjointness or coverage hypothesis is introduced.
````
`````
