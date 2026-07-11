# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition

gch: 83545d95d222e45af87622c045b2640625167cf5

## Report

cp192 を閉じました。

実装済み:

- `three_iff_pairDiagnostic_cases`
- `four_iff_pairDiagnostic_cases`
- 2要素の命名 alias
- 3/4要素の `failure + noAdjacentOverlap` consumer wrappers
- `report-petal-192.md` 新規作成

確認:

- 指定された `lake build ...` 群は通過済み
- 指定4ファイルの no-sorry check は一致なし
- `git diff --check` 通過
- 既知の unrelated warning: `ZsigmondyCyclotomicResearch.lean` の `sorry`

変更ファイル:

- `lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean`
- `lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-192.md`

今回も固定長 API 補完に留めて、任意リスト分解・集約・coverage・Collatz convergence には踏み込んでいません。

## Review

## 結論

うむ、Checkpoint 192 は **採用** じゃ 👍️
これで length 2〜5 の bounded pair-cases API がかなり綺麗に揃った。

追加された中心は、

```lean id="3q9c8k"
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_iff_pairDiagnostic_cases
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_iff_pairDiagnostic_cases
sourcePressureLocalIslandWitnessList_failure_two_pairDiagnostic_cases_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_three_pairDiagnostic_cases_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_four_pairDiagnostic_cases_of_noAdjacentOverlap
```

じゃな。今回も固定長 API 補完に留めており、任意リスト分解、集約、coverage、canonical first diagnosis、Collatz convergence には踏み込んでいない。境界管理は安定している。

## 実装レビュー

## 1. three / four の API 粒度が揃った

cp191 では five だけが fully opened pair-cases の `iff` と consumer theorem を持っていた。
今回で three / four も揃った。

```text id="5rie7e"
2:
  direct pair diagnostic

3:
  pair cases
  iff pair cases
  failure consumer

4:
  pair cases
  iff pair cases
  failure consumer

5:
  pair cases
  iff pair cases
  failure consumer
```

これは良い整理じゃ。
固定長の bounded layer として、かなり一貫性が出た。

## 2. reverse direction の bounded address が明示的

`three_iff_pairDiagnostic_cases` と `four_iff_pairDiagnostic_cases` の逆向きは、選ばれた pair に応じて、

```lean id="u0gx1h"
SourcePressureLocalIslandWitnessAdjacentPairInList.head
SourcePressureLocalIslandWitnessAdjacentPairInList.tail SourcePressureLocalIslandWitnessAdjacentPairInList.head
SourcePressureLocalIslandWitnessAdjacentPairInList.tail
  (SourcePressureLocalIslandWitnessAdjacentPairInList.tail
    SourcePressureLocalIslandWitnessAdjacentPairInList.head)
```

という形で直接 address を組んでいる。

これはよい。
tail lift の合成よりも、「固定長 list の中のこの隣接 pair」という意味が明確じゃ。

## 3. consumer wrappers が実用向き

```lean id="2rf950"
sourcePressureLocalIslandWitnessList_failure_three_pairDiagnostic_cases_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_four_pairDiagnostic_cases_of_noAdjacentOverlap
```

により、

```text id="byx09v"
failure + noAdjacentOverlap
  -> どれかの adjacent pair が pairDiagnostic
```

を length 3 / 4 でも直接使える。

これで downstream theorem は、長い diagnostic carrier を一度経由せずに、固定窓の recovered pair branch へ行ける。

## 数学的意味

今回で、固定小窓については次の形が揃った。

```text id="k4yp3l"
failure + noAdjacentOverlap on fixed window
  -> finite disjunction of pair-local recovered diagnostics
```

つまり、DkMath 的には、

```text id="0svzgg"
局所 failure が overlap branch でなければ、
その固定窓内のどこかの隣接二項が
負会計を持つ recovered pair として観測される。
```

ここまで来ると、「failure を局所二項回収へ落とす」構築がかなり明示的じゃ。

## 注意点

## 1. まだ arbitrary-list ではない

これは重要じゃ。

今回揃ったのは、

```text id="xk04sg"
length 2
length 3
length 4
length 5
```

の固定長 API。

まだ次は言っていない。

```text id="wcv5kz"
任意 list に対する pair cases
任意 list の canonical first diagnostic
全 diagnostics の列挙
coverage
union accounting
```

ここはまだ別設計が必要じゃ。

## 2. 次に length-six へ進む必然性は薄い

length 5 まで揃ったので、同じ型で length 6 を足すことはできる。
だが、いまは増やすより、

```text id="gp9kdv"
この fixed-window API をどこで使うか
```

を探す段階に来ている。

ここで downstream consumer を決めると、次に必要な長さ・形が自然に分かる。

## 次の checkpoint 方針

次は **consumer audit / integration checkpoint** を推す。

新しい数学的主張を足すより、

```text id="pmorrg"
既存 downstream theorem のどこで
pairDiagnostic cases API を使えるか
```

を調べる。

候補は、

```text id="bce8j6"
PressureFrontier
PressureAccounting
PressureLocalWitnessObstruction
PressureAdjacentDiagnosis
```

周辺じゃな。

とくに、既に `failure + noAdjacentOverlap` や `hasAdjacentDiagnosis` を扱っている theorem があれば、今回の compact consumer wrappers に置き換えられる可能性がある。

## 次の Codex 指示

```text id="ko641f"
Checkpoint 193: Consumer audit only — find the first downstream use for bounded pair-cases API.

Scope:
Audit the Collatz/PetalBridge pressure modules and identify whether the new
bounded pair-cases API can simplify an existing downstream theorem or prepare a
small consumer-facing theorem.

Primary files to inspect:
- DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
- DkMath/Collatz/PetalBridge/PressureFrontier.lean
- DkMath/Collatz/PetalBridge/PressureAccounting.lean
- DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
- DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean

Do not modify:
- OneCycle.lean
- ValuationFlowBridge.lean
- ABC files
- NumberTheory files

Context:
Checkpoint 192 completed the fixed bounded pair-cases API for length 2 through
5:

- three_iff_pairDiagnostic_cases
- four_iff_pairDiagnostic_cases
- five_iff_pairDiagnostic_cases
- failure_two_pairDiagnostic_cases_of_noAdjacentOverlap
- failure_three_pairDiagnostic_cases_of_noAdjacentOverlap
- failure_four_pairDiagnostic_cases_of_noAdjacentOverlap
- failure_five_pairDiagnostic_cases_of_noAdjacentOverlap

Main goal:
Do not add length-six yet.
First identify an actual downstream caller or a concrete theorem that benefits
from the fixed pair-cases API.

Part A: audit existing uses.

Search for these patterns:
- SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
- SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
- sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
- sourcePressureLocalIslandWitnessList_failure_three_diagnostic_head_or_tail_of_noAdjacentOverlap
- sourcePressureLocalIslandWitnessList_failure_four_diagnostic_head_or_tail_of_noAdjacentOverlap
- sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_or_tail_of_noAdjacentOverlap
- HasAdjacentDiagnosis
- RecoveredAdjacentAccountedFamilyDiagnostic

Record whether any theorem can be simplified by replacing a diagnostic
intermediate with one of:

- sourcePressureLocalIslandWitnessList_failure_two_pairDiagnostic_cases_of_noAdjacentOverlap
- sourcePressureLocalIslandWitnessList_failure_three_pairDiagnostic_cases_of_noAdjacentOverlap
- sourcePressureLocalIslandWitnessList_failure_four_pairDiagnostic_cases_of_noAdjacentOverlap
- sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_cases_of_noAdjacentOverlap

Part B: if a direct replacement is found.

Make only a small refactor:
- preserve theorem names and statements;
- replace proof internals with the compact pair-cases API;
- do not strengthen or weaken statements;
- do not add new global assumptions.

Part C: if no direct replacement is found.

Add one small downstream-facing wrapper in
`PressureDiagnosticDecomposition.lean` only if it is clearly useful.

Preferred shape:
a theorem that exposes the fixed length-five result from failure and no-overlap
in the most consumer-friendly form already available.

If the existing theorem
`sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_cases_of_noAdjacentOverlap`
is already sufficient, do not add a duplicate theorem.

Part D: report-only is acceptable.

If no safe code change is justified, create only the report and state:
- searched modules;
- no direct downstream replacement found;
- current bounded API is ready for future concrete consumers;
- no Lean source changes beyond report.

Part E: do not introduce new mathematical strength.

Do not add:
- length-six decomposition;
- arbitrary-list decomposition;
- arbitrary-list recursion;
- aggregation over multiple recovered diagnostics;
- list-wide interval union accounting;
- coverage;
- maximality;
- uniqueness for arbitrary lists;
- sorting theorems;
- canonical first diagnosis for arbitrary lists;
- diagnostic enumeration beyond fixed finite disjunctions;
- overlap repair;
- disjointness between multiple recovered families;
- Collatz convergence.

Part F: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-193.md

Include:
- searched files and patterns;
- whether existing downstream code can use the compact pair-cases API;
- any theorem proof refactor performed, if any;
- if no source change was made, explicitly say this was an audit-only checkpoint;
- explicit note that no length-six, arbitrary-list decomposition, aggregation,
  union accounting, coverage, maximality, uniqueness for arbitrary lists,
  sorting, canonical first diagnosis for arbitrary lists, enumeration beyond
  fixed finite disjunctions, overlap repair, or Collatz convergence was introduced;
- verification results.

Verification:

  lake build DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
  lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
  lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
  lake build DkMath.Collatz.PetalBridge.PressureAccounting
  lake build DkMath.Collatz.PetalBridge.PressureFrontier
  lake build DkMath.Collatz.PetalBridge

Run no-sorry checks:

  rg -n "\\bsorry\\b" \
    DkMath/Collatz/PetalBridge/PressureAccounting.lean \
    DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
    DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
    DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean

Also run:

  git diff --check
```

## 総評

cp192 は良い仕上げじゃ。

bounded pair-cases API は length 2〜5 で揃った。
ここからは「さらに長さを増やす」より、「この API をどこで使うか」を見つける方が強い。

固定窓内の failure を pair-local recovered branch に落とす装置は、もう十分に形になってきている。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
index 886d6195..110cce1f 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
@@ -378,6 +378,40 @@ theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyD
       (SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.two_iff_pairDiagnostic.mp
         htail)
 
+set_option linter.style.longLine false in
+/--
+Iff form of the fully bounded three-to-pairs normalization.
+
+The reverse direction builds the diagnostic from the selected bounded
+adjacent-pair address.  This is only a fixed three-element finite disjunction;
+it does not choose or enumerate diagnostics in arbitrary lists.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_iff_pairDiagnostic_cases
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r} :
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+      [W1, W2, W3] ↔
+    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+      W1 W2 ∨
+      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+        W2 W3 := by
+  constructor
+  · exact
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_pairDiagnostic_cases
+  · intro h
+    rcases h with h12 | h23
+    · rcases h12 with ⟨hrev, hbudget, hneg, hlen⟩
+      exact
+        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
+          SourcePressureLocalIslandWitnessAdjacentPairInList.head
+          hrev hbudget hneg hlen
+    · rcases h23 with ⟨hrev, hbudget, hneg, hlen⟩
+      exact
+        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
+          (SourcePressureLocalIslandWitnessAdjacentPairInList.tail
+            SourcePressureLocalIslandWitnessAdjacentPairInList.head)
+          hrev hbudget hneg hlen
+
 set_option linter.style.longLine false in
 /--
 Four-element bounded decomposition for the bundled diagnostic carrier.
@@ -508,6 +542,50 @@ theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyD
     · exact Or.inr (Or.inl h23)
     · exact Or.inr (Or.inr h34)
 
+set_option linter.style.longLine false in
+/--
+Iff form of the fully bounded four-to-pairs normalization.
+
+The reverse direction builds the diagnostic from exactly one selected bounded
+adjacent-pair address.  This is only a fixed four-element finite disjunction;
+it does not choose or enumerate diagnostics in arbitrary lists.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_iff_pairDiagnostic_cases
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r} :
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+      [W1, W2, W3, W4] ↔
+    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+      W1 W2 ∨
+      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+        W2 W3 ∨
+      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+        W3 W4 := by
+  constructor
+  · exact
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_pairDiagnostic_cases
+  · intro h
+    rcases h with h12 | htail
+    · rcases h12 with ⟨hrev, hbudget, hneg, hlen⟩
+      exact
+        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
+          SourcePressureLocalIslandWitnessAdjacentPairInList.head
+          hrev hbudget hneg hlen
+    · rcases htail with h23 | h34
+      · rcases h23 with ⟨hrev, hbudget, hneg, hlen⟩
+        exact
+          SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
+            (SourcePressureLocalIslandWitnessAdjacentPairInList.tail
+              SourcePressureLocalIslandWitnessAdjacentPairInList.head)
+            hrev hbudget hneg hlen
+      · rcases h34 with ⟨hrev, hbudget, hneg, hlen⟩
+        exact
+          SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
+            (SourcePressureLocalIslandWitnessAdjacentPairInList.tail
+              (SourcePressureLocalIslandWitnessAdjacentPairInList.tail
+                SourcePressureLocalIslandWitnessAdjacentPairInList.head))
+            hrev hbudget hneg hlen
+
 set_option linter.style.longLine false in
 /--
 Five-element bounded decomposition for the bundled diagnostic carrier.
@@ -709,6 +787,25 @@ theorem
   sourcePressureLocalIslandWitnessList_failure_two_exists_reversed_of_noAdjacentOverlap
     h hno
 
+set_option linter.style.longLine false in
+/--
+Two-element consumer alias matching the `pairDiagnostic_cases` naming style.
+
+For two witnesses, the finite pair-cases result is just the unique head pair.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_failure_two_pairDiagnostic_cases_of_noAdjacentOverlap
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2])
+    (hno :
+      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction [W1, W2]) :
+    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+      W1 W2 :=
+  sourcePressureLocalIslandWitnessList_failure_two_pairDiagnostic_of_noAdjacentOverlap
+    h hno
+
 set_option linter.style.longLine false in
 /--
 Three-element consumer form: failure plus named no-adjacent-overlap yields
@@ -764,6 +861,30 @@ theorem
   sourcePressureLocalIslandWitnessList_failure_three_diagnostic_head_or_tail_of_noAdjacentOverlap
     h hno
 
+set_option linter.style.longLine false in
+/--
+Three-element consumer form normalized all the way to the fixed finite
+disjunction of adjacent pair diagnostics.
+
+The theorem is bounded to `[W1, W2, W3]`; it does not aggregate branches or
+choose a canonical diagnosis in an arbitrary list.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_failure_three_pairDiagnostic_cases_of_noAdjacentOverlap
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2, W3])
+    (hno :
+      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
+        [W1, W2, W3]) :
+    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+      W1 W2 ∨
+      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+        W2 W3 :=
+  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
+    h hno).three_pairDiagnostic_cases
+
 set_option linter.style.longLine false in
 /--
 Four-element consumer form: failure plus named no-adjacent-overlap yields
@@ -821,6 +942,33 @@ theorem
   sourcePressureLocalIslandWitnessList_failure_four_diagnostic_head_or_tail_of_noAdjacentOverlap
     h hno
 
+set_option linter.style.longLine false in
+/--
+Four-element consumer form normalized all the way to the fixed finite
+disjunction of adjacent pair diagnostics.
+
+The theorem is bounded to `[W1, W2, W3, W4]`; it does not aggregate branches or
+choose a canonical diagnosis in an arbitrary list.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_failure_four_pairDiagnostic_cases_of_noAdjacentOverlap
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        [W1, W2, W3, W4])
+    (hno :
+      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
+        [W1, W2, W3, W4]) :
+    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+      W1 W2 ∨
+      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+        W2 W3 ∨
+      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
+        W3 W4 :=
+  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
+    h hno).four_pairDiagnostic_cases
+
 set_option linter.style.longLine false in
 /--
 Five-element consumer form: failure plus named no-adjacent-overlap yields
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-192.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-192.md
new file mode 100644
index 00000000..9b777c30
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-192.md
@@ -0,0 +1,202 @@
+# Report Petal 192
+
+## Checkpoint
+
+Checkpoint 192 completed the fixed three/four-element pair-cases API for the
+bounded pressure diagnostic decomposition layer.
+
+Primary file:
+
+- `DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean`
+
+No other Lean source file was changed.
+
+## Implemented
+
+### Three-element iff pair-cases theorem
+
+Added:
+
+```lean
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_iff_pairDiagnostic_cases
+```
+
+This gives the fixed three-element equivalence:
+
+```text
+Diagnostic [W1, W2, W3]
+  iff
+PairDiagnostic W1 W2 or PairDiagnostic W2 W3
+```
+
+The forward direction uses the existing three-element finite decomposition.
+The reverse direction builds the list diagnostic directly from the selected
+bounded adjacent-pair address:
+
+- `W1,W2`: head address;
+- `W2,W3`: one tail step then head.
+
+### Four-element iff pair-cases theorem
+
+Added:
+
+```lean
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_iff_pairDiagnostic_cases
+```
+
+This gives the fixed four-element equivalence:
+
+```text
+Diagnostic [W1, W2, W3, W4]
+  iff
+PairDiagnostic W1 W2
+or PairDiagnostic W2 W3
+or PairDiagnostic W3 W4
+```
+
+The reverse direction again uses explicit bounded addresses:
+
+- `W1,W2`: head address;
+- `W2,W3`: one tail step then head;
+- `W3,W4`: two tail steps then head.
+
+### Two-element naming alias
+
+Added:
+
+```lean
+theorem sourcePressureLocalIslandWitnessList_failure_two_pairDiagnostic_cases_of_noAdjacentOverlap
+```
+
+This is a naming-style alias for the existing two-element consumer theorem.
+For two witnesses, the fully opened finite pair-cases result is just the
+unique head pair.
+
+### Three/four consumer wrappers
+
+Added:
+
+```lean
+theorem sourcePressureLocalIslandWitnessList_failure_three_pairDiagnostic_cases_of_noAdjacentOverlap
+theorem sourcePressureLocalIslandWitnessList_failure_four_pairDiagnostic_cases_of_noAdjacentOverlap
+```
+
+These compose the existing failure plus no-adjacent-overlap diagnostic theorem
+with the fixed three/four pair-cases normalizations.
+
+They provide direct consumer-facing results:
+
+```text
+failure + noAdjacentOverlap on [W1, W2, W3]
+  -> PairDiagnostic W1 W2 or PairDiagnostic W2 W3
+
+failure + noAdjacentOverlap on [W1, W2, W3, W4]
+  -> PairDiagnostic W1 W2
+     or PairDiagnostic W2 W3
+     or PairDiagnostic W3 W4
+```
+
+## API Status
+
+The bounded pair-cases API now has matching fixed-length surfaces for
+lengths two through five:
+
+```text
+2: direct pair diagnostic
+3: forward cases, iff cases, failure/noAdjacentOverlap consumer
+4: forward cases, iff cases, failure/noAdjacentOverlap consumer
+5: forward cases, iff cases, failure/noAdjacentOverlap consumer
+```
+
+This closes the intended API completion checkpoint without increasing
+mathematical strength.
+
+## Guardrails
+
+This checkpoint only completed the bounded fixed-length API.
+
+It did not introduce:
+
+- length-six decomposition;
+- arbitrary-list decomposition;
+- arbitrary-list recursion;
+- aggregation over multiple recovered diagnostics;
+- list-wide interval union accounting;
+- coverage;
+- maximality;
+- uniqueness for arbitrary lists;
+- sorting theorems;
+- canonical first diagnosis for arbitrary lists;
+- diagnostic enumeration beyond fixed finite disjunctions;
+- overlap repair;
+- disjointness between multiple recovered families;
+- Collatz convergence.
+
+Recovered budgets remain pair-local.  The new theorems only expose which
+explicit adjacent pair carries the named pair-local diagnostic inside a fixed
+small list.
+
+## File Size Watch
+
+Current line counts after this checkpoint:
+
+```text
+  1027 lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
+  1356 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+  1391 lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
+  1896 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+  5670 total
+```
+
+`PressureDiagnosticDecomposition.lean` remains below the 2,000-line split
+threshold.  No refactor was needed in this checkpoint.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
+lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
+lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
+lake build DkMath.Collatz.PetalBridge.PressureAccounting
+lake build DkMath.Collatz.PetalBridge.PressureFrontier
+lake build DkMath.Collatz.PetalBridge
+git diff --check
+```
+
+No-sorry check over the requested pressure files produced no matches:
+
+```text
+rg -n "\bsorry\b" \
+  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
+  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
+  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
+  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
+```
+
+Known unrelated warning still appears during builds:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+That warning is outside this checkpoint and was not modified.
+
+## Next Inference
+
+The pressure diagnostic decomposition layer now has a coherent bounded
+consumer API for the small explicit list sizes currently used by downstream
+experiments.
+
+The next safe direction is not to generalize automatically to arbitrary lists.
+Instead, the next checkpoint should first identify an actual downstream caller
+that needs either:
+
+- another fixed length;
+- a one-step head-or-tail view;
+- or a carefully designed arbitrary-list policy.
+
+That keeps the API evidence-driven and avoids accidental claims about
+coverage, canonical choice, or global interval accounting.
````
`````
