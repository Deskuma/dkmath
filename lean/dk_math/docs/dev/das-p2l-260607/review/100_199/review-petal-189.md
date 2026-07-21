# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition

gch: 8c3d967b564ce8a57a562905991a44acf521fdcc

## Report

cp188 完了です。refactor-only で、数学的主張は増やしていません。

bounded diagnostic decomposition 群を新規 [PressureDiagnosticDecomposition.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean:1) へ移しました。[PressureAdjacentDiagnosis.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean:1) は core carrier/API 側に戻し、[PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean:23) に新モジュールの public import を追加しました。

レポート: [report-petal-188.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-188.md)

確認済み:
`lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis`
`lake build DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition`
`lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction`
`lake build DkMath.Collatz.PetalBridge.PressureAccounting`
`lake build DkMath.Collatz.PetalBridge.PressureFrontier`
`lake build DkMath.Collatz.PetalBridge`
対象4ファイル no-sorry
`git diff --check`

行数は `PressureAdjacentDiagnosis.lean` が 1356 行、新ファイルが 418 行です。既知の `ZsigmondyCyclotomicResearch.lean` の warning は今回も対象外です。

## Review

## 結論

うむ、Checkpoint 188 は **採用** じゃ 👍️
これはきれいな **refactor-only checkpoint** になっている。

bounded diagnostic decomposition 群を新規 module、

```lean id="j5xz70"
DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
```

へ移し、`PressureAdjacentDiagnosis.lean` は core carrier / API 側へ戻された。さらに public umbrella の `PetalBridge.lean` に新 module の import も追加されている。数学的主張は増やしていない、という境界も守られている。

## 実装レビュー

## 1. 分割タイミングが良い

`PressureAdjacentDiagnosis.lean` が 1750 行まで来ていたので、ここで切ったのは正解じゃ。

分割後は、

```text id="p1qq9d"
PressureAdjacentDiagnosis.lean              1356 lines
PressureDiagnosticDecomposition.lean         418 lines
PressureLocalWitnessObstruction.lean        1391 lines
PressureAccounting.lean                     1896 lines
```

となり、`PressureAdjacentDiagnosis.lean` が watch zone から戻った。

今後 length-five 以降を伸ばすとしても、新 module 側で受けられる。

## 2. module 境界が自然

今回の切り分けはかなり自然じゃ。

`PressureAdjacentDiagnosis.lean` に残したものは、

```text id="qgp6nd"
core carrier
diagnostic definition
constructor / projection
no-overlap predicate
tail lift
failure -> diagnostic
```

一方、新 module に移したものは、

```text id="ejot9q"
length-two normal form
length-three bounded decomposition
length-four bounded decomposition
bounded consumer corollaries
```

つまり、

```text id="9ukrsn"
何であるか
```

と、

```text id="vfcr3v"
明示 list 上でどう分解するか
```

が分かれた。これは良い設計じゃ。

## 3. public import 追加も妥当

`PetalBridge.lean` に、

```lean id="pp23zf"
import DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
```

が追加されているので、umbrella import 利用者には theorem surface が保たれる。

ただし、直接

```lean id="xjjyah"
import DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
```

だけを使う downstream code は、今後 bounded decomposition theorem が見えなくなる。これは refactor として許容範囲じゃが、必要な downstream では新 module を明示 import するのが正しい。

## 数学的意味

今回、数学的前進は意図的にない。

だが、構築上の意味は大きい。

```text id="yms91w"
diagnostic carrier の基礎層
bounded decomposition の展開層
```

が分離された。

これは今後の収束方向の構築で重要じゃ。
なぜなら、bounded decomposition は今後さらに伸びる可能性が高いからじゃ。

```text id="jv23jw"
length 2
length 3
length 4
length 5
...
```

をすべて core carrier file に入れていくと、構造が見えなくなる。
今回の分割で、「伸びる枝」を別 module に逃がせた。

## 注意点

## 1. theorem 名は変えていないが、import boundary は変わった

Lean 的には、同じ theorem 名でも、利用側が直接 import していた module によっては見え方が変わる。

したがって今後は、

```lean id="le3h74"
import DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
```

を bounded decomposition 利用側の明示 import とするのがよい。

## 2. 次に length-five へ行く前に、長い branch を名前にしたい

今の decomposition theorem は、head branch が毎回とても長い。

```lean id="o2apv3"
∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
  let F := ...
  sum ≤ -2 ∧ sum < 0 ∧ F.items.length = 2
```

これを毎回 theorem statement に書くと、length-five 以降でさらに長くなる。

だから次は length-five 追加より先に、**head pair branch に名前を付ける** のが良い。

## 次の checkpoint 方針

次は **API compression checkpoint** を推す。

新しい数学的主張は増やさず、長い pair-local branch を名前付き predicate にする。

たとえば、

```lean id="y7l1ye"
SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W1 W2
```

のような predicate を新 module に置く。

意味は、

```text id="ghzkc3"
W2 before W1 であり、
W1,W2 の reversed pair-local accounted family が
budget ≤ -2, sum < 0, length = 2 を持つ
```

じゃ。

すると今後、

```lean id="g9pw7k"
Diagnostic [W1, W2, W3, W4]
  ↔ PairDiagnostic W1 W2 ∨ Diagnostic [W2, W3, W4]
```

のように theorem statement が短くなる。

## 次の Codex 指示

```text id="eegikt"
Checkpoint 189: API compression only — name the recovered head-pair branch in PressureDiagnosticDecomposition.

Scope:
Work in the refactored diagnostic decomposition layer.

Primary target file:
- DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean

Allowed supporting files:
- DkMath/Collatz/PetalBridge.lean only if import order somehow requires it
- Do not modify PressureAdjacentDiagnosis.lean unless absolutely necessary

Do not modify:
- PressureAccounting.lean
- PressureLocalWitnessObstruction.lean
- PressureFrontier.lean
- OneCycle.lean
- ValuationFlowBridge.lean
- ABC files
- NumberTheory files

Context:
Checkpoint 188 split bounded diagnostic decomposition helpers into:

  DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition

The current length-two/three/four theorem statements repeatedly use a long
head-branch expression:

  ∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
    let F :=
      sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W1 W2 hrev
    (((F.items).map
      (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
      (((F.items).map
        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
      F.items.length = 2

Main goal:
Introduce a named predicate for this pair-local recovered head branch, then add
compact wrapper theorems for the existing length-two, length-three, and
length-four decomposition API.

This is an API-compression checkpoint.  Do not add length-five here.

Part A: define a named pair-local recovered branch predicate.

Suggested name:

  def SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
      {n : OddNat} {k r : Nat}
      (W1 W2 : SourcePressureLocalIslandWitness n k r) : Prop :=
    ∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      let F :=
        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          W1 W2 hrev
      (((F.items).map
        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
        (((F.items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
        F.items.length = 2

Keep the name explicit.  Avoid short names like `PairDiagnostic` unless added as
an abbreviation later.

Part B: constructor from reversed-before witness.

Prove:

  theorem SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic.of_before
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W1 W2

Expected proof:
- use existing reversed-pair facts:
  sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two
  sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
  sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length

Part C: bridge between pair predicate and two-element diagnostic.

Prove compact wrappers:

  theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.two_iff_pairDiagnostic
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r} :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
        [W1, W2] ↔
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W1 W2

Suggested proof:
- exact existing `two_iff`, adjusted by unfolding the new predicate if needed.

Also prove, if convenient:

  theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pairDiagnostic_two
      ...
      (h : SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W1 W2) :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic [W1, W2]

This is just the reverse direction of the iff.

Part D: compact length-three decomposition.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_iff_pairDiagnostic_or_tail
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 : SourcePressureLocalIslandWitness n k r} :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
        [W1, W2, W3] ↔
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W1 W2 ∨
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
          [W2, W3]

Suggested proof:
- use existing `three_iff_head_or_tail`;
- unfold the new predicate, or use theorem extensionality if Lean can infer it.

Part E: compact length-four decomposition.

Prove:

  theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_iff_pairDiagnostic_or_tail
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r} :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
        [W1, W2, W3, W4] ↔
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W1 W2 ∨
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
          [W2, W3, W4]

Suggested proof:
- use existing `four_iff_head_or_tail`;
- unfold the new predicate if needed.

Part F: compact consumer wrappers for failure + noAdjacentOverlap.

Add compact wrappers using the new predicate:

  theorem sourcePressureLocalIslandWitnessList_failure_two_pairDiagnostic_of_noAdjacentOverlap
      {n : OddNat} {k r : Nat}
      {W1 W2 : SourcePressureLocalIslandWitness n k r}
      (h :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2])
      (hno :
        SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction [W1, W2]) :
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W1 W2

  theorem sourcePressureLocalIslandWitnessList_failure_three_pairDiagnostic_or_tail_of_noAdjacentOverlap
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
      (h :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2, W3])
      (hno :
        SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction [W1, W2, W3]) :
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W1 W2 ∨
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic [W2, W3]

  theorem sourcePressureLocalIslandWitnessList_failure_four_pairDiagnostic_or_tail_of_noAdjacentOverlap
      {n : OddNat} {k r : Nat}
      {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r}
      (h :
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2, W3, W4])
      (hno :
        SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction [W1, W2, W3, W4]) :
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W1 W2 ∨
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic [W2, W3, W4]

Suggested proof:
- use the existing non-compact consumer theorem and unfold the new predicate,
  or obtain diagnostic via existing failure theorem and then use compact iff.

Part G: optional abbreviation.

Only if the long predicate name becomes too burdensome, add an abbrev:

  abbrev SourcePressureLocalIslandWitnessPairDiagnostic :=
    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic

Do not use the abbreviation in theorem names yet unless it clearly improves
readability.

Part H: do not introduce new mathematical strength.

Do not add:
- length-five decomposition;
- arbitrary-list decomposition;
- a list of all diagnostics;
- canonical first diagnosis for arbitrary lists;
- sum over all recovered diagnostics;
- disjointness between multiple recovered families;
- union accounting;
- coverage;
- overlap repair;
- Collatz convergence.

Part I: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-189.md

Include:
- this is API-compression only;
- the new pair-local branch predicate;
- constructor from reversed-before witness;
- compact two/three/four iff wrappers;
- compact consumer wrappers if added;
- explicit note that theorem strength is unchanged and the long head branch was only named;
- explicit note that no length-five, arbitrary-list decomposition, aggregation,
  union accounting, coverage, maximality, uniqueness for arbitrary lists,
  sorting, canonical first diagnosis for arbitrary lists, enumeration,
  overlap repair, or Collatz convergence was introduced;
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

cp188 はかなり良い整理じゃ。

これで bounded decomposition の枝を安心して伸ばせる。
ただし、次に length-five へ伸ばす前に、長い head branch を名前付き predicate にしておくと、その後の theorem が一気に読みやすくなる。

今は証明力を増やすより、API の可読性を上げる局面じゃな。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index cad9a911..cf6da7e1 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -21,6 +21,7 @@ import DkMath.Collatz.PetalBridge.PressureFrontier
 import DkMath.Collatz.PetalBridge.PressureAccounting
 import DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
 import DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
+import DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
 import DkMath.Collatz.PetalBridge.OneCycle
 import DkMath.Collatz.PetalBridge.ValuationFlowBridge
 import DkMath.Collatz.PetalBridge.Collision
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
index c5782340..f41c2920 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
@@ -278,65 +278,6 @@ theorem SourcePressureLocalIslandWitnessAdjacentPairInList.singleton_false
   intro h
   exact h

-/--
-In a two-element explicit witness list, the only adjacent-pair address is the
-head pair.
-
-This is a two-element normal form only.  It does not choose a canonical pair in
-longer lists and does not enumerate diagnostics.
--/
-theorem SourcePressureLocalIslandWitnessAdjacentPairInList.two_iff_head
-    {n : OddNat} {k r : ℕ}
-    {W1 W2 A B : SourcePressureLocalIslandWitness n k r} :
-    SourcePressureLocalIslandWitnessAdjacentPairInList [W1, W2] A B ↔
-      A = W1 ∧ B = W2 := by
-  constructor
-  · intro h
-    rcases h with hhead | htail
-    · exact hhead
-    · exact False.elim
-        (SourcePressureLocalIslandWitnessAdjacentPairInList.singleton_false htail)
-  · rintro ⟨rfl, rfl⟩
-    exact SourcePressureLocalIslandWitnessAdjacentPairInList.head
-
-/-- Extract the head-pair equality from a two-element adjacent-pair address. -/
-theorem SourcePressureLocalIslandWitnessAdjacentPairInList.two_eq
-    {n : OddNat} {k r : ℕ}
-    {W1 W2 A B : SourcePressureLocalIslandWitness n k r}
-    (h : SourcePressureLocalIslandWitnessAdjacentPairInList [W1, W2] A B) :
-    A = W1 ∧ B = W2 :=
-  SourcePressureLocalIslandWitnessAdjacentPairInList.two_iff_head.mp h
-
-/--
-In a three-element explicit witness list, an adjacent-pair address is either
-the head pair or an adjacent-pair address in the two-element tail.
-
-This is a bounded three-element decomposition only.  It does not enumerate
-diagnostics in arbitrary lists.
--/
-theorem SourcePressureLocalIslandWitnessAdjacentPairInList.three_head_or_tail
-    {n : OddNat} {k r : ℕ}
-    {W1 W2 W3 A B : SourcePressureLocalIslandWitness n k r}
-    (h : SourcePressureLocalIslandWitnessAdjacentPairInList [W1, W2, W3] A B) :
-    (A = W1 ∧ B = W2) ∨
-      SourcePressureLocalIslandWitnessAdjacentPairInList [W2, W3] A B :=
-  h
-
-/--
-In a four-element explicit witness list, an adjacent-pair address is either
-the head pair or an adjacent-pair address in the three-element tail.
-
-This is a bounded four-element decomposition only.  It does not enumerate
-diagnostics in arbitrary lists.
--/
-theorem SourcePressureLocalIslandWitnessAdjacentPairInList.four_head_or_tail
-    {n : OddNat} {k r : ℕ}
-    {W1 W2 W3 W4 A B : SourcePressureLocalIslandWitness n k r}
-    (h : SourcePressureLocalIslandWitnessAdjacentPairInList [W1, W2, W3, W4] A B) :
-    (A = W1 ∧ B = W2) ∨
-      SourcePressureLocalIslandWitnessAdjacentPairInList [W2, W3, W4] A B :=
-  h
-
 /--
 A list-level carrier for "some adjacent pair in this explicit list has an
 adjacent diagnosis".
@@ -1025,248 +966,6 @@ theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyD
     (SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail_tail
       h)

-set_option linter.style.longLine false in
-/--
-Build the bundled diagnostic directly from a reversed two-witness list.
-
-For `[W1, W2]`, the only adjacent-pair address is the head pair `W1, W2`.
-Thus a witness that `W2` is before `W1` gives the recovered pair-local
-accounted family immediately.
--/
-theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_two_reversed
-    {n : OddNat} {k r : ℕ}
-    {W1 W2 : SourcePressureLocalIslandWitness n k r}
-    (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
-    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
-      [W1, W2] :=
-  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
-    SourcePressureLocalIslandWitnessAdjacentPairInList.head
-    hrev
-    (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two
-      W1 W2 hrev)
-    (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
-      W1 W2 hrev)
-    (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length
-      W1 W2 hrev)
-
-set_option linter.style.longLine false in
-/--
-Extract the reversed-before witness and the bundled pair-local facts from a
-two-element diagnostic.
-
-This is a two-element explicit-list normal form only.  It does not choose a
-canonical diagnostic in longer lists.
--/
-theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_reversed_of_two
-    {n : OddNat} {k r : ℕ}
-    {W1 W2 : SourcePressureLocalIslandWitness n k r}
-    (h :
-      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
-        [W1, W2]) :
-    ∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
-      let F :=
-        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
-          W1 W2 hrev
-      (((F.items).map
-        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
-        (((F.items).map
-          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
-        F.items.length = 2 := by
-  rcases h.exists_pair with ⟨A, B, hin, hrev, hbudget, hneg, hlen⟩
-  rcases SourcePressureLocalIslandWitnessAdjacentPairInList.two_eq hin with
-    ⟨rfl, rfl⟩
-  exact ⟨hrev, hbudget, hneg, hlen⟩
-
-set_option linter.style.longLine false in
-/--
-Two-element normal form for the bundled diagnostic carrier.
-
-The equivalence is only for the explicit two-witness list `[W1, W2]`.  It does
-not assert uniqueness or canonical selection for arbitrary lists.
--/
-theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.two_iff
-    {n : OddNat} {k r : ℕ}
-    {W1 W2 : SourcePressureLocalIslandWitness n k r} :
-    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
-      [W1, W2] ↔
-    ∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
-      let F :=
-        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
-          W1 W2 hrev
-      (((F.items).map
-        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
-        (((F.items).map
-          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
-        F.items.length = 2 := by
-  constructor
-  · exact
-      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_reversed_of_two
-  · rintro ⟨hrev, _hbudget, _hneg, _hlen⟩
-    exact
-      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_two_reversed
-        hrev
-
-set_option linter.style.longLine false in
-/--
-Three-element bounded decomposition for the bundled diagnostic carrier.
-
-A diagnostic on `[W1, W2, W3]` is either carried by the head pair `W1, W2`,
-or it is already a diagnostic on the two-element tail `[W2, W3]`.
-This theorem only decomposes the explicit three-element list; it does not
-enumerate diagnostics in arbitrary lists.
--/
-theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_head_or_tail
-    {n : OddNat} {k r : ℕ}
-    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
-    (h :
-      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
-        [W1, W2, W3]) :
-    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
-      let F :=
-        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
-          W1 W2 hrev
-      (((F.items).map
-        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
-        (((F.items).map
-          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
-        F.items.length = 2)
-    ∨
-      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
-        [W2, W3] := by
-  rcases h.exists_pair with ⟨A, B, hin, hrev, hbudget, hneg, hlen⟩
-  rcases SourcePressureLocalIslandWitnessAdjacentPairInList.three_head_or_tail
-      hin with hhead | htail
-  · rcases hhead with ⟨rfl, rfl⟩
-    exact Or.inl ⟨hrev, hbudget, hneg, hlen⟩
-  · exact Or.inr
-      (SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
-        htail hrev hbudget hneg hlen)
-
-set_option linter.style.longLine false in
-/--
-Iff form of the three-element diagnostic decomposition.
-
-The reverse direction either builds the head-pair diagnostic from the reversed
-witness and lifts it through the tail API, or lifts an existing tail diagnostic.
--/
-theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_iff_head_or_tail
-    {n : OddNat} {k r : ℕ}
-    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r} :
-    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
-      [W1, W2, W3] ↔
-    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
-      let F :=
-        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
-          W1 W2 hrev
-      (((F.items).map
-        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
-        (((F.items).map
-          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
-        F.items.length = 2)
-    ∨
-      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
-        [W2, W3]) := by
-  constructor
-  · exact
-      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_head_or_tail
-  · intro h
-    rcases h with hhead | htail
-    · rcases hhead with ⟨hrev, _hbudget, _hneg, _hlen⟩
-      exact
-        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
-          SourcePressureLocalIslandWitnessAdjacentPairInList.head
-          hrev
-          (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two
-            W1 W2 hrev)
-          (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
-            W1 W2 hrev)
-          (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length
-            W1 W2 hrev)
-    · exact
-        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail
-          htail
-
-set_option linter.style.longLine false in
-/--
-Four-element bounded decomposition for the bundled diagnostic carrier.
-
-A diagnostic on `[W1, W2, W3, W4]` is either carried by the head pair `W1, W2`,
-or it is already a diagnostic on the three-element tail `[W2, W3, W4]`.
-This theorem only decomposes the explicit four-element list; it does not
-enumerate diagnostics in arbitrary lists.
--/
-theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_head_or_tail
-    {n : OddNat} {k r : ℕ}
-    {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r}
-    (h :
-      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
-        [W1, W2, W3, W4]) :
-    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
-      let F :=
-        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
-          W1 W2 hrev
-      (((F.items).map
-        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
-        (((F.items).map
-          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
-        F.items.length = 2)
-    ∨
-      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
-        [W2, W3, W4] := by
-  rcases h.exists_pair with ⟨A, B, hin, hrev, hbudget, hneg, hlen⟩
-  rcases SourcePressureLocalIslandWitnessAdjacentPairInList.four_head_or_tail
-      hin with hhead | htail
-  · rcases hhead with ⟨rfl, rfl⟩
-    exact Or.inl ⟨hrev, hbudget, hneg, hlen⟩
-  · exact Or.inr
-      (SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
-        htail hrev hbudget hneg hlen)
-
-set_option linter.style.longLine false in
-/--
-Iff form of the four-element diagnostic decomposition.
-
-The reverse direction either builds the head-pair diagnostic directly from the
-reversed witness, or lifts an existing tail diagnostic.  This is still bounded
-to `[W1, W2, W3, W4]`.
--/
-theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_iff_head_or_tail
-    {n : OddNat} {k r : ℕ}
-    {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r} :
-    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
-      [W1, W2, W3, W4] ↔
-    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
-      let F :=
-        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
-          W1 W2 hrev
-      (((F.items).map
-        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
-        (((F.items).map
-          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
-        F.items.length = 2)
-    ∨
-      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
-        [W2, W3, W4]) := by
-  constructor
-  · exact
-      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_head_or_tail
-  · intro h
-    rcases h with hhead | htail
-    · rcases hhead with ⟨hrev, _hbudget, _hneg, _hlen⟩
-      exact
-        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
-          SourcePressureLocalIslandWitnessAdjacentPairInList.head
-          hrev
-          (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two
-            W1 W2 hrev)
-          (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
-            W1 W2 hrev)
-          (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length
-            W1 W2 hrev)
-    · exact
-        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail
-          htail
-
 /--
 Expose the actual pair-local accounted interval family object stored by the
 recovered adjacent-family carrier.
@@ -1453,99 +1152,6 @@ theorem
   (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_no_overlap
     h hno).toDiagnostic

-set_option linter.style.longLine false in
-/--
-Two-element consumer form: failure plus named no-adjacent-overlap yields the
-reversed-before witness for the only adjacent pair.
-
-This is only the `[W1, W2]` normal form.  It does not select a canonical pair in
-longer lists.
--/
-theorem
-    sourcePressureLocalIslandWitnessList_failure_two_exists_reversed_of_noAdjacentOverlap
-    {n : OddNat} {k r : ℕ}
-    {W1 W2 : SourcePressureLocalIslandWitness n k r}
-    (h :
-      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2])
-    (hno :
-      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction [W1, W2]) :
-    ∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
-      let F :=
-        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
-          W1 W2 hrev
-      (((F.items).map
-        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
-        (((F.items).map
-          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
-        F.items.length = 2 :=
-  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
-    h hno).exists_reversed_of_two
-
-set_option linter.style.longLine false in
-/--
-Three-element consumer form: failure plus named no-adjacent-overlap yields
-either the head-pair recovered branch or a diagnostic on the two-element tail.
-
-This is still a bounded decomposition for `[W1, W2, W3]`; it does not enumerate
-or aggregate diagnostics in longer lists.
--/
-theorem
-    sourcePressureLocalIslandWitnessList_failure_three_diagnostic_head_or_tail_of_noAdjacentOverlap
-    {n : OddNat} {k r : ℕ}
-    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
-    (h :
-      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2, W3])
-    (hno :
-      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
-        [W1, W2, W3]) :
-    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
-      let F :=
-        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
-          W1 W2 hrev
-      (((F.items).map
-        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
-        (((F.items).map
-          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
-        F.items.length = 2)
-    ∨
-      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
-        [W2, W3] :=
-  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
-    h hno).three_head_or_tail
-
-set_option linter.style.longLine false in
-/--
-Four-element consumer form: failure plus named no-adjacent-overlap yields
-either the head-pair recovered branch or a diagnostic on the three-element tail.
-
-This remains a bounded decomposition for `[W1, W2, W3, W4]`; it does not
-enumerate or aggregate diagnostics in longer lists.
--/
-theorem
-    sourcePressureLocalIslandWitnessList_failure_four_diagnostic_head_or_tail_of_noAdjacentOverlap
-    {n : OddNat} {k r : ℕ}
-    {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r}
-    (h :
-      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
-        [W1, W2, W3, W4])
-    (hno :
-      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
-        [W1, W2, W3, W4]) :
-    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
-      let F :=
-        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
-          W1 W2 hrev
-      (((F.items).map
-        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
-        (((F.items).map
-          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
-        F.items.length = 2)
-    ∨
-      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
-        [W2, W3, W4] :=
-  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
-    h hno).four_head_or_tail
-
 set_option linter.style.longLine false in
 /--
 Failure plus named no-adjacent-overlap, projected directly to the pair-local
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
new file mode 100644
index 00000000..41f16698
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
@@ -0,0 +1,418 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
+
+#print "file: DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition"
+
+namespace DkMath.Collatz
+
+/-
+Bounded diagnostic decomposition helpers for explicit witness lists.
+
+This module is a refactor-only split from `PressureAdjacentDiagnosis`.  It
+keeps the bounded length-two, length-three, and length-four helper theorems
+separate from the core diagnostic carriers and constructors.  Nothing here
+adds arbitrary-list coverage, maximality, uniqueness, canonical selection,
+enumeration, union accounting, overlap repair, aggregation, or Collatz
+convergence.
+-/
+
+/--
+In a two-element explicit witness list, the only adjacent-pair address is the
+head pair.
+
+This is a two-element normal form only.  It does not choose a canonical pair in
+longer lists and does not enumerate diagnostics.
+-/
+theorem SourcePressureLocalIslandWitnessAdjacentPairInList.two_iff_head
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 A B : SourcePressureLocalIslandWitness n k r} :
+    SourcePressureLocalIslandWitnessAdjacentPairInList [W1, W2] A B ↔
+      A = W1 ∧ B = W2 := by
+  constructor
+  · intro h
+    rcases h with hhead | htail
+    · exact hhead
+    · exact False.elim
+        (SourcePressureLocalIslandWitnessAdjacentPairInList.singleton_false htail)
+  · rintro ⟨rfl, rfl⟩
+    exact SourcePressureLocalIslandWitnessAdjacentPairInList.head
+
+/-- Extract the head-pair equality from a two-element adjacent-pair address. -/
+theorem SourcePressureLocalIslandWitnessAdjacentPairInList.two_eq
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 A B : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureLocalIslandWitnessAdjacentPairInList [W1, W2] A B) :
+    A = W1 ∧ B = W2 :=
+  SourcePressureLocalIslandWitnessAdjacentPairInList.two_iff_head.mp h
+
+/--
+In a three-element explicit witness list, an adjacent-pair address is either
+the head pair or an adjacent-pair address in the two-element tail.
+
+This is a bounded three-element decomposition only.  It does not enumerate
+diagnostics in arbitrary lists.
+-/
+theorem SourcePressureLocalIslandWitnessAdjacentPairInList.three_head_or_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 A B : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureLocalIslandWitnessAdjacentPairInList [W1, W2, W3] A B) :
+    (A = W1 ∧ B = W2) ∨
+      SourcePressureLocalIslandWitnessAdjacentPairInList [W2, W3] A B :=
+  h
+
+/--
+In a four-element explicit witness list, an adjacent-pair address is either
+the head pair or an adjacent-pair address in the three-element tail.
+
+This is a bounded four-element decomposition only.  It does not enumerate
+diagnostics in arbitrary lists.
+-/
+theorem SourcePressureLocalIslandWitnessAdjacentPairInList.four_head_or_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 W4 A B : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureLocalIslandWitnessAdjacentPairInList [W1, W2, W3, W4] A B) :
+    (A = W1 ∧ B = W2) ∨
+      SourcePressureLocalIslandWitnessAdjacentPairInList [W2, W3, W4] A B :=
+  h
+
+set_option linter.style.longLine false in
+/--
+Build the bundled diagnostic directly from a reversed two-witness list.
+
+For `[W1, W2]`, the only adjacent-pair address is the head pair `W1, W2`.
+Thus a witness that `W2` is before `W1` gives the recovered pair-local
+accounted family immediately.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_two_reversed
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+      [W1, W2] :=
+  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
+    SourcePressureLocalIslandWitnessAdjacentPairInList.head
+    hrev
+    (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two
+      W1 W2 hrev)
+    (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
+      W1 W2 hrev)
+    (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length
+      W1 W2 hrev)
+
+set_option linter.style.longLine false in
+/--
+Extract the reversed-before witness and the bundled pair-local facts from a
+two-element diagnostic.
+
+This is a two-element explicit-list normal form only.  It does not choose a
+canonical diagnostic in longer lists.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_reversed_of_two
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (h :
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        [W1, W2]) :
+    ∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
+      let F :=
+        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+          W1 W2 hrev
+      (((F.items).map
+        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
+        (((F.items).map
+          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
+        F.items.length = 2 := by
+  rcases h.exists_pair with ⟨A, B, hin, hrev, hbudget, hneg, hlen⟩
+  rcases SourcePressureLocalIslandWitnessAdjacentPairInList.two_eq hin with
+    ⟨rfl, rfl⟩
+  exact ⟨hrev, hbudget, hneg, hlen⟩
+
+set_option linter.style.longLine false in
+/--
+Two-element normal form for the bundled diagnostic carrier.
+
+The equivalence is only for the explicit two-witness list `[W1, W2]`.  It does
+not assert uniqueness or canonical selection for arbitrary lists.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.two_iff
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r} :
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+      [W1, W2] ↔
+    ∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
+      let F :=
+        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+          W1 W2 hrev
+      (((F.items).map
+        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
+        (((F.items).map
+          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
+        F.items.length = 2 := by
+  constructor
+  · exact
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_reversed_of_two
+  · rintro ⟨hrev, _hbudget, _hneg, _hlen⟩
+    exact
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_two_reversed
+        hrev
+
+set_option linter.style.longLine false in
+/--
+Three-element bounded decomposition for the bundled diagnostic carrier.
+
+A diagnostic on `[W1, W2, W3]` is either carried by the head pair `W1, W2`,
+or it is already a diagnostic on the two-element tail `[W2, W3]`.
+This theorem only decomposes the explicit three-element list; it does not
+enumerate diagnostics in arbitrary lists.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_head_or_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
+    (h :
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        [W1, W2, W3]) :
+    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
+      let F :=
+        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+          W1 W2 hrev
+      (((F.items).map
+        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
+        (((F.items).map
+          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
+        F.items.length = 2)
+    ∨
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        [W2, W3] := by
+  rcases h.exists_pair with ⟨A, B, hin, hrev, hbudget, hneg, hlen⟩
+  rcases SourcePressureLocalIslandWitnessAdjacentPairInList.three_head_or_tail
+      hin with hhead | htail
+  · rcases hhead with ⟨rfl, rfl⟩
+    exact Or.inl ⟨hrev, hbudget, hneg, hlen⟩
+  · exact Or.inr
+      (SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
+        htail hrev hbudget hneg hlen)
+
+set_option linter.style.longLine false in
+/--
+Iff form of the three-element diagnostic decomposition.
+
+The reverse direction either builds the head-pair diagnostic from the reversed
+witness and lifts it through the tail API, or lifts an existing tail diagnostic.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_iff_head_or_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r} :
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+      [W1, W2, W3] ↔
+    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
+      let F :=
+        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+          W1 W2 hrev
+      (((F.items).map
+        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
+        (((F.items).map
+          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
+        F.items.length = 2)
+    ∨
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        [W2, W3]) := by
+  constructor
+  · exact
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_head_or_tail
+  · intro h
+    rcases h with hhead | htail
+    · rcases hhead with ⟨hrev, _hbudget, _hneg, _hlen⟩
+      exact
+        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
+          SourcePressureLocalIslandWitnessAdjacentPairInList.head
+          hrev
+          (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two
+            W1 W2 hrev)
+          (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
+            W1 W2 hrev)
+          (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length
+            W1 W2 hrev)
+    · exact
+        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail
+          htail
+
+set_option linter.style.longLine false in
+/--
+Four-element bounded decomposition for the bundled diagnostic carrier.
+
+A diagnostic on `[W1, W2, W3, W4]` is either carried by the head pair `W1, W2`,
+or it is already a diagnostic on the three-element tail `[W2, W3, W4]`.
+This theorem only decomposes the explicit four-element list; it does not
+enumerate diagnostics in arbitrary lists.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_head_or_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r}
+    (h :
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        [W1, W2, W3, W4]) :
+    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
+      let F :=
+        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+          W1 W2 hrev
+      (((F.items).map
+        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
+        (((F.items).map
+          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
+        F.items.length = 2)
+    ∨
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        [W2, W3, W4] := by
+  rcases h.exists_pair with ⟨A, B, hin, hrev, hbudget, hneg, hlen⟩
+  rcases SourcePressureLocalIslandWitnessAdjacentPairInList.four_head_or_tail
+      hin with hhead | htail
+  · rcases hhead with ⟨rfl, rfl⟩
+    exact Or.inl ⟨hrev, hbudget, hneg, hlen⟩
+  · exact Or.inr
+      (SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
+        htail hrev hbudget hneg hlen)
+
+set_option linter.style.longLine false in
+/--
+Iff form of the four-element diagnostic decomposition.
+
+The reverse direction either builds the head-pair diagnostic directly from the
+reversed witness, or lifts an existing tail diagnostic.  This is still bounded
+to `[W1, W2, W3, W4]`.
+-/
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_iff_head_or_tail
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r} :
+    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+      [W1, W2, W3, W4] ↔
+    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
+      let F :=
+        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+          W1 W2 hrev
+      (((F.items).map
+        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
+        (((F.items).map
+          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
+        F.items.length = 2)
+    ∨
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        [W2, W3, W4]) := by
+  constructor
+  · exact
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_head_or_tail
+  · intro h
+    rcases h with hhead | htail
+    · rcases hhead with ⟨hrev, _hbudget, _hneg, _hlen⟩
+      exact
+        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
+          SourcePressureLocalIslandWitnessAdjacentPairInList.head
+          hrev
+          (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two
+            W1 W2 hrev)
+          (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
+            W1 W2 hrev)
+          (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length
+            W1 W2 hrev)
+    · exact
+        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail
+          htail
+
+set_option linter.style.longLine false in
+/--
+Two-element consumer form: failure plus named no-adjacent-overlap yields the
+reversed-before witness for the only adjacent pair.
+
+This is only the `[W1, W2]` normal form.  It does not select a canonical pair in
+longer lists.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_failure_two_exists_reversed_of_noAdjacentOverlap
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 : SourcePressureLocalIslandWitness n k r}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2])
+    (hno :
+      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction [W1, W2]) :
+    ∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
+      let F :=
+        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+          W1 W2 hrev
+      (((F.items).map
+        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
+        (((F.items).map
+          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
+        F.items.length = 2 :=
+  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
+    h hno).exists_reversed_of_two
+
+set_option linter.style.longLine false in
+/--
+Three-element consumer form: failure plus named no-adjacent-overlap yields
+either the head-pair recovered branch or a diagnostic on the two-element tail.
+
+This is still a bounded decomposition for `[W1, W2, W3]`; it does not enumerate
+or aggregate diagnostics in longer lists.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_failure_three_diagnostic_head_or_tail_of_noAdjacentOverlap
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2, W3])
+    (hno :
+      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
+        [W1, W2, W3]) :
+    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
+      let F :=
+        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+          W1 W2 hrev
+      (((F.items).map
+        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
+        (((F.items).map
+          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
+        F.items.length = 2)
+    ∨
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        [W2, W3] :=
+  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
+    h hno).three_head_or_tail
+
+set_option linter.style.longLine false in
+/--
+Four-element consumer form: failure plus named no-adjacent-overlap yields
+either the head-pair recovered branch or a diagnostic on the three-element tail.
+
+This remains a bounded decomposition for `[W1, W2, W3, W4]`; it does not
+enumerate or aggregate diagnostics in longer lists.
+-/
+theorem
+    sourcePressureLocalIslandWitnessList_failure_four_diagnostic_head_or_tail_of_noAdjacentOverlap
+    {n : OddNat} {k r : ℕ}
+    {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r}
+    (h :
+      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+        [W1, W2, W3, W4])
+    (hno :
+      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
+        [W1, W2, W3, W4]) :
+    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
+      let F :=
+        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
+          W1 W2 hrev
+      (((F.items).map
+        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
+        (((F.items).map
+          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
+        F.items.length = 2)
+    ∨
+      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
+        [W2, W3, W4] :=
+  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
+    h hno).four_head_or_tail
+
+end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-188.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-188.md
new file mode 100644
index 00000000..e62dc33e
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-188.md
@@ -0,0 +1,184 @@
+# report-petal-188
+
+Date: 2026-07-06
+
+## Scope
+
+Checkpoint 188 is refactor-only.
+
+The bounded diagnostic decomposition helpers were split out of
+`DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis` into the new module:
+
+```lean
+DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
+```
+
+No theorem statement was intentionally strengthened, weakened, or renamed.
+No length-five theorem and no arbitrary-list decomposition was added.
+
+## New module
+
+Created:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
+```
+
+The new module imports:
+
+```lean
+import DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
+```
+
+It now owns the bounded length-two, length-three, and length-four helper
+surface.  The original `PressureAdjacentDiagnosis` module remains the core
+carrier/API module.
+
+## Public import update
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+Added the public umbrella import:
+
+```lean
+import DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
+```
+
+No downstream pressure module needed an additional explicit import in this
+checkpoint.
+
+## Declarations moved
+
+Address-level bounded decomposition:
+
+```lean
+theorem SourcePressureLocalIslandWitnessAdjacentPairInList.two_iff_head
+theorem SourcePressureLocalIslandWitnessAdjacentPairInList.two_eq
+theorem SourcePressureLocalIslandWitnessAdjacentPairInList.three_head_or_tail
+theorem SourcePressureLocalIslandWitnessAdjacentPairInList.four_head_or_tail
+```
+
+Diagnostic length-two normal form:
+
+```lean
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_two_reversed
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_reversed_of_two
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.two_iff
+theorem sourcePressureLocalIslandWitnessList_failure_two_exists_reversed_of_noAdjacentOverlap
+```
+
+Diagnostic length-three bounded decomposition:
+
+```lean
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_head_or_tail
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_iff_head_or_tail
+theorem sourcePressureLocalIslandWitnessList_failure_three_diagnostic_head_or_tail_of_noAdjacentOverlap
+```
+
+Diagnostic length-four bounded decomposition:
+
+```lean
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_head_or_tail
+theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_iff_head_or_tail
+theorem sourcePressureLocalIslandWitnessList_failure_four_diagnostic_head_or_tail_of_noAdjacentOverlap
+```
+
+These declarations now appear in
+`PressureDiagnosticDecomposition.lean`, and not in `PressureAdjacentDiagnosis.lean`.
+
+## What stayed in PressureAdjacentDiagnosis
+
+`PressureAdjacentDiagnosis.lean` still contains the core adjacent-pair and
+diagnostic infrastructure:
+
+- adjacent-pair-in-list constructors and general API;
+- list-level adjacent diagnosis carrier;
+- no-adjacent-overlap predicate;
+- recovered adjacent accounted-family carrier;
+- diagnostic carrier definition;
+- diagnostic constructors, conversions, and projections;
+- nil/singleton false helpers;
+- tail lift helpers;
+- failure plus no-adjacent-overlap diagnostic carrier theorem;
+- raw no-overlap compatibility wrappers.
+
+## File sizes
+
+After the split:
+
+```text
+  1356 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+   418 lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
+  1391 lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
+  1896 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+  5061 total
+```
+
+The original file is now comfortably below the 1900-2000 line watch zone.
+
+## Guardrails preserved
+
+This checkpoint did not introduce:
+
+- global local-island coverage;
+- maximality;
+- uniqueness for arbitrary lists;
+- prefix behavior;
+- arbitrary list sorting;
+- canonical first diagnosis for arbitrary lists;
+- enumeration of all diagnostics;
+- union accounting;
+- overlap repair;
+- Collatz convergence;
+- aggregation of multiple recovered pairs;
+- a list-wide accounted interval union;
+- disjointness between multiple recovered families.
+
+This was a module-boundary cleanup only.
+
+## Verification
+
+Commands run:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
+lake build DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
+lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
+lake build DkMath.Collatz.PetalBridge.PressureAccounting
+lake build DkMath.Collatz.PetalBridge.PressureFrontier
+lake build DkMath.Collatz.PetalBridge
+rg -n "\bsorry\b" DkMath/Collatz/PetalBridge/PressureAccounting.lean DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
+git diff --check
+```
+
+Results:
+
+- all listed `lake build` commands completed successfully;
+- the targeted `rg` no-sorry check returned no matches;
+- `git diff --check` passed.
+
+Known unrelated warning still appears during builds:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+This checkpoint did not modify that file.
+
+## Next inference
+
+The bounded decomposition layer now has a dedicated module.  The next checkpoint
+can safely continue in one of two directions:
+
+- add a length-five bounded decomposition in
+  `PressureDiagnosticDecomposition.lean`; or
+- add a downstream consumer theorem that imports the new module and uses the
+  length-four decomposition.
+
+The second option is preferable if the next proof needs evidence that the split
+module is the right API boundary.
````
`````
