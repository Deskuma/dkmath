# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis

gch: 5d42876648c980fb9994d7fee00144b94792fffa

## Report

cp183 を完了しました。

`PressureAdjacentDiagnosis.lean` に、pair-local の recovered accounted family を束ねる診断 carrier を追加しました。

追加内容:

- `SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic`
- `.of_pair`
- `.toDiagnostic`
- `.toRecoveredAdjacentAccountedFamily`
- `.exists_pair`
- `.exists_accountedFamily_sum_neg`
- `.exists_accountedFamily_length_two`
- failure + noAdjacentOverlap から diagnostic へ上げる theorem
- raw negation wrapper

すべて「1 つの recovered adjacent pair」に限定しています。aggregation、union accounting、coverage、uniqueness、canonical first diagnosis、Collatz convergence には踏み込んでいません。

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

対象 3 ファイルの no-sorry は no match。`git diff --check` も通過です。

レポートも追加しました。

`lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-183.md`

## Review

## 結論

うむ、Checkpoint 183 は **採用** じゃ 👍️
cp182 で分かれていた pair-local family の情報を、ひとつの diagnostic carrier に束ねられた。

追加された中心は、

```lean id="yzp4er"
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.toDiagnostic
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.toRecoveredAdjacentAccountedFamily
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_pair
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_accountedFamily_sum_neg
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_accountedFamily_length_two
sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_no_overlap
```

じゃな。すべて **1 つの recovered adjacent pair** に限定されており、aggregation、union accounting、coverage、canonical first diagnosis、Collatz convergence には踏み込んでいない。境界は守られている。

## 実装レビュー

## 1. diagnostic carrier の設計は良い

今回の carrier は、次を一つに束ねている。

```text id="prv6fd"
adjacent pair A B が explicit list L にある
B before A の reversed witness がある
pair-local accounted family の budget が ≤ -2
同じ family の sum が < 0
同じ family の items.length が 2
```

これは下流でかなり使いやすい。

`≤ -2`、`< 0`、`length = 2` は冗長ではあるが、証明利用上は有益じゃ。毎回 projection を呼んだり、既存 reversed-pair 補題を探したりしなくてよくなる。

## 2. `toDiagnostic` / `toRecoveredAdjacentAccountedFamily` が良い

この双方向変換は重要じゃ。

```lean id="697voe"
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.toDiagnostic
```

で低レベル carrier を diagnostic に上げる。

```lean id="k3yi06"
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.toRecoveredAdjacentAccountedFamily
```

で余分な情報を忘れて、既存 theorem が期待する carrier に戻せる。

この互換性があるので、API が分裂していない。
新しい diagnostic は既存 carrier の上位包装として自然に使える。

## 3. consumer theorem も自然

```lean id="m76qhg"
sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
```

により、

```text id="l2z72t"
failure L
noAdjacentOverlap L
  -> diagnostic L
```

が得られた。

これはいまの到達点を一文で使える、とても良い公開 API じゃ。

raw negation wrapper も移行期には有用。

## 数学的意味

今回の到達点はこう読める。

```text id="rhhb3m"
overlap obstruction がない explicit failure list では、
failure は 1 つの recovered adjacent pair に局所化され、
その pair は 2-item の accounted family として負 budget を持つ。
```

DkMath 的には、かなり綺麗な局所会計になった。

```text id="fy6edh"
failure:
  局所順序の破綻

noAdjacentOverlap:
  overlap Gap branch の排除

diagnostic:
  回収可能な二項局所会計
```

ここで `items.length = 2` が見えるのが良い。
これは「回収された failure は、隣接 pair 由来の二項取引として見える」という読みを支えている。

## 注意点

## 1. diagnostic は一つの pair だけ

今回の diagnostic は、

```text id="ezk3oj"
∃ A B, ...
```

であり、全 pair の列挙ではない。

まだ次は言っていない。

```text id="gj6tvf"
全 recovered pair を集める
複数 family を合算する
pairwise disjointness between families を証明する
list-wide union accounting を作る
```

ここは未到達。

## 2. canonical diagnosis ではない

`exists` なので、どの pair が選ばれるかは指定していない。

```text id="lpjyd3"
最初の pair
最左の pair
最小 start の pair
```

などはまだ導入していない。これも正しい。

## 3. 次は短い list の否定補題か tail propagation

report の Next inference にある通り、次は aggregation ではない。
安全なのは、diagnostic carrier の基本 API をもう少し整えることじゃ。

候補は二つ。

```text id="u4ffuo"
nil / singleton では diagnostic は存在しない

tail に diagnostic があれば、head を足した list にも diagnostic がある
```

この二つは今後の構文的な list induction に効く。

わっちのおすすめは、**短 list 否定 + tail lift** を同じ checkpoint で入れることじゃ。
どちらも薄い補題で、数学的主張を強めない。

## 次の Codex 指示

```text id="gbqa9e"
Checkpoint 184: Main root only — basic structural API for the bundled diagnostic carrier.

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
Checkpoint 183 added:

- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.toDiagnostic
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.toRecoveredAdjacentAccountedFamily
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_pair
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_accountedFamily_sum_neg
- SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_accountedFamily_length_two
- sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
- sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_no_overlap

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
Add small structural helper theorems for the bundled diagnostic carrier:
- empty and singleton lists cannot carry a diagnostic;
- diagnostics in a tail list lift through a new head;
- optionally, a raw projection to show the underlying recovered carrier exists.

Part A: empty and singleton impossibility.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.nil_false
      {n : OddNat} {k r : Nat} :
      ¬ SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
        ([] : List (SourcePressureLocalIslandWitness n k r))

Suggested proof:
- rcases h with ⟨A, B, hin, ...⟩
- exact SourcePressureLocalIslandWitnessAdjacentPairInList.nil_false hin

Prove:

  theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.singleton_false
      {n : OddNat} {k r : Nat}
      {W : SourcePressureLocalIslandWitness n k r} :
      ¬ SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic [W]

Suggested proof:
- rcases h with ⟨A, B, hin, ...⟩
- exact SourcePressureLocalIslandWitnessAdjacentPairInList.singleton_false hin

Part B: tail lifting.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      {rest : List (SourcePressureLocalIslandWitness n k r)}
      (h :
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
          (W2 :: rest)) :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
        (W1 :: W2 :: rest)

Suggested proof:
- unpack h as A B hin hrev hbudget hneg hlen.
- use `SourcePressureLocalIslandWitnessAdjacentPairInList.tail hin`
  to lift the adjacent-pair address into the larger list.
- repackage the same hrev, hbudget, hneg, hlen.
- No family changes; the pair-local family is exactly the same.

Part C: optional two-step and three-step tail lifting.

Only if useful and easy, add:

  theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail_tail
  theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail_tail_tail

These should just compose `.of_tail`, mirroring the older
`SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail_tail`
helpers.

Do not add an arbitrary recursive lift in this checkpoint.

Part D: optional raw recovered-carrier projection alias.

The theorem

  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.toRecoveredAdjacentAccountedFamily

already exists.

If desired, add a naming alias:

  theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_recoveredCarrier
      ...
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L

But avoid duplication if not useful.

Part E: do not introduce aggregation.

Do not prove:
- a list of all recovered diagnostics,
- sum over all recovered diagnostics,
- disjointness between multiple recovered families,
- union accounting,
- coverage,
- overlap repair,
- canonical first diagnosis.

Part F: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-184.md

Include:
- nil/singleton impossibility;
- tail lift theorem;
- optional bounded tail composition helpers if added;
- explicit note that the lifted diagnostic is the same pair-local family with a lifted list address;
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

cp183 は良い足場固めじゃ。

これで下流は、

```text id="6vany2"
failure
noAdjacentOverlap
diagnostic
```

を一発で受け取れる。

しかも diagnostic の中には、

```text id="72qnvw"
pair-local family
budget ≤ -2
sum < 0
length = 2
```

が揃っている。

次はこの diagnostic を list 構造の中で扱いやすくする。
まだ合算しない。まだ列挙しない。
まずは「短い list には無い」「tail から持ち上げられる」という構文補助を固めるのがよい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
index cf39fada..ed8b4519 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
@@ -696,6 +696,190 @@ theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.
             (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2 :=
   h

+set_option linter.style.longLine false in
+/--
+Bundled consumer-facing diagnostic for one recovered adjacent accounted family.
+
+This carrier intentionally stores redundant local facts about the same
+recovered reversed-pair family:
+
+* the pair occurs adjacently in the explicit witness list;
+* the pair is reversed with respect to the `Before` relation;
+* the associated pair-local accounted family has budget `≤ -2`;
+* the same listed budget is strictly negative;
+* the family has exactly two listed accounted intervals.
+
+The redundancy is deliberate.  Downstream callers often need the operational
+`< 0` and `items.length = 2` facts without reproving them from the lower-level
+carrier.  This definition is still a one-pair diagnostic.  It does not list all
+diagnoses, aggregate multiple recovered pairs, form interval unions, claim
+coverage, or repair overlaps.
+-/
+def SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
+  ∃ A B,
+    SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+      ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
+        let F :=
+          sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+            A B hrev
+        (((F.items).map
+          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
+          (((F.items).map
+            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
+          F.items.length = 2
+
+set_option linter.style.longLine false in
+/--
+Build the bundled diagnostic from explicit pair-local evidence.
+
+This constructor only packages one recovered adjacent pair and its associated
+reversed-pair accounted family.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {A B : SourcePressureLocalIslandWitness n k r}
+    (hin :
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B)
+    (hrev : SourcePressureLocalIslandWitnessBefore B A)
+    (hbudget :
+      let F :=
+        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+          A B hrev
+      ((F.items).map
+        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2)
+    (hneg :
+      let F :=
+        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+          A B hrev
+      ((F.items).map
+        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0)
+    (hlen :
+      let F :=
+        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+          A B hrev
+      F.items.length = 2) :
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic L :=
+  ⟨A, B, hin, hrev, hbudget, hneg, hlen⟩
+
+set_option linter.style.longLine false in
+/--
+Upgrade the lower-level recovered accounted-family carrier to the bundled
+diagnostic carrier.
+
+The strict negativity and length-two facts come from the existing reversed-pair
+accounted-family theorems, so no list-wide accounting principle is introduced.
+-/
+theorem
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.toDiagnostic
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L) :
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic L := by
+  rcases h.exists_pair with ⟨A, B, hin, hrev, hbudget⟩
+  exact
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
+      hin hrev hbudget
+      (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
+        A B hrev)
+      (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length
+        A B hrev)
+
+set_option linter.style.longLine false in
+/--
+Forget the extra diagnostic fields and recover the lower-level carrier.
+
+This is useful when a caller has the bundled diagnostic but an older theorem
+expects only the recovered accounted-family carrier.
+-/
+theorem
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.toRecoveredAdjacentAccountedFamily
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic L) :
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L := by
+  rcases h with ⟨A, B, hin, hrev, hbudget, _hneg, _hlen⟩
+  exact
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.of_pair
+      hin hrev hbudget
+
+set_option linter.style.longLine false in
+/--
+Project the underlying adjacent recovered pair from the bundled diagnostic.
+
+This is a convenience projection only; it does not assert uniqueness or
+enumerate every possible diagnostic in the list.
+-/
+theorem
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_pair
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic L) :
+    ∃ A B,
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
+          let F :=
+            sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+              A B hrev
+          (((F.items).map
+            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
+            (((F.items).map
+            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
+            F.items.length = 2 :=
+  h
+
+set_option linter.style.longLine false in
+/--
+Project strict negativity from the bundled diagnostic.
+
+This is the same pair-local family stored in the diagnostic; the theorem only
+forgets the additional `≤ -2` and length fields.
+-/
+theorem
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_accountedFamily_sum_neg
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic L) :
+    ∃ A B,
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
+          let F :=
+            sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+              A B hrev
+          ((F.items).map
+            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0 := by
+  rcases h.exists_pair with ⟨A, B, hin, hrev, _hbudget, hneg, _hlen⟩
+  exact ⟨A, B, hin, hrev, hneg⟩
+
+set_option linter.style.longLine false in
+/--
+Project length-two structure from the bundled diagnostic.
+
+This remains about the explicit accounted family associated with one recovered
+adjacent pair.
+-/
+theorem
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_accountedFamily_length_two
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic L) :
+    ∃ A B,
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
+          let F :=
+            sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+              A B hrev
+          F.items.length = 2 := by
+  rcases h.exists_pair with ⟨A, B, hin, hrev, _hbudget, _hneg, hlen⟩
+  exact ⟨A, B, hin, hrev, hlen⟩
+
 /--
 Expose the actual pair-local accounted interval family object stored by the
 recovered adjacent-family carrier.
@@ -842,6 +1026,46 @@ theorem
     (SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.of_not
       hno)

+set_option linter.style.longLine false in
+/--
+Failure plus named no-adjacent-overlap, packaged as the bundled pair-local
+diagnostic carrier.
+
+This is the consumer-facing form of the recovered branch.  It bundles the
+adjacent pair, reversed-before witness, budget `≤ -2`, strict negativity, and
+length-two structure for one recovered family only.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
+    (hno :
+      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L) :
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic L :=
+  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_noAdjacentOverlap
+    h hno).toDiagnostic
+
+set_option linter.style.longLine false in
+/--
+Raw-negation version of the bundled diagnostic consumer theorem.
+
+This keeps the compatibility path for callers that still represent the
+no-adjacent-overlap branch as a raw negation.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_no_overlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
+    (hno :
+      ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic L :=
+  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_no_overlap
+    h hno).toDiagnostic
+
 set_option linter.style.longLine false in
 /--
 Failure plus named no-adjacent-overlap, projected directly to the pair-local
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-183.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-183.md
new file mode 100644
index 00000000..975d1e0f
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-183.md
@@ -0,0 +1,188 @@
+# report-petal-183
+
+Date: 2026-07-06
+
+## Scope
+
+Checkpoint 183 adds a bundled pair-local diagnostic carrier in
+`DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis`.
+
+The goal was not to strengthen the accounting model globally.  The new surface
+only packages facts already available for one recovered adjacent reversed pair:
+
+- adjacent pair membership in the explicit list;
+- reversed-before witness;
+- the recovered pair-local accounted family;
+- budget `≤ -2`;
+- strict negative budget `< 0`;
+- `items.length = 2`.
+
+## Implemented carrier
+
+Added:
+
+```lean
+def SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+```
+
+This carrier is intentionally redundant.  The lower-level recovered carrier
+already stores `≤ -2`, and cp182 exposed `< 0` and `items.length = 2`.  The new
+diagnostic bundles those facts so downstream callers can destruct one carrier
+instead of repeatedly calling separate projections.
+
+The definition remains one-pair only.  It does not aggregate recovered pairs or
+build a list-wide accounted interval union.
+
+## Constructors and conversions
+
+Added:
+
+```lean
+theorem
+  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
+```
+
+This constructs the diagnostic from explicit adjacent-pair evidence and the
+three pair-local facts.
+
+Added:
+
+```lean
+theorem
+  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.toDiagnostic
+```
+
+This upgrades the existing recovered carrier to the bundled diagnostic.  The
+proof reuses the existing reversed-pair family facts:
+
+- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg`
+- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length`
+
+Added:
+
+```lean
+theorem
+  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.toRecoveredAdjacentAccountedFamily
+```
+
+This forgets the extra diagnostic fields and returns the existing lower-level
+recovered carrier.
+
+## Consumer theorem
+
+Added:
+
+```lean
+theorem
+  sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
+```
+
+This packages the failure + named no-adjacent-overlap branch directly into the
+new diagnostic carrier.
+
+Also added the raw-negation compatibility wrapper:
+
+```lean
+theorem
+  sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_no_overlap
+```
+
+## Additional projections
+
+Added lightweight projections from the diagnostic:
+
+```lean
+theorem
+  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_pair
+
+theorem
+  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_accountedFamily_sum_neg
+
+theorem
+  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_accountedFamily_length_two
+```
+
+These are convenience projections only.  They do not assert uniqueness, choose a
+canonical diagnosis, or enumerate every possible diagnostic.
+
+## Guardrails preserved
+
+This checkpoint did not introduce:
+
+- global local-island coverage;
+- maximality;
+- uniqueness;
+- prefix behavior;
+- arbitrary list sorting;
+- canonical first diagnosis;
+- enumeration of all diagnoses;
+- union accounting;
+- overlap repair;
+- Collatz convergence;
+- aggregation of multiple recovered pairs;
+- disjointness between multiple recovered families.
+
+Recovered budgets remain pair-local.
+
+## File-size check
+
+Current line counts:
+
+```text
+1270 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+1391 lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
+1896 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+```
+
+`PressureAdjacentDiagnosis.lean` remains below the 2000-line split threshold.
+
+## Verification
+
+Builds:
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
+Known unrelated warning:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+This is outside the checkpoint scope and was not modified.
+
+No-sorry check on the targeted pressure files:
+
+```text
+rg -n "\bsorry\b" \
+  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
+  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
+  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+```
+
+Result: no matches.  `rg` exited with code `1`, which is the expected no-match
+result.
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
+The new diagnostic carrier is now the clean consumer surface for one recovered
+adjacent local accounting witness.  The next safe step is to use this carrier
+where repeated destructuring appears, or to add a small negative example showing
+that short lists still cannot produce the diagnostic.  Aggregation should remain
+blocked until an explicit disjointness or coverage hypothesis is available.
````
`````
