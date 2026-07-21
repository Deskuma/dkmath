# Git diff / Report / Review

## Upd: docs: report 198

gch: 631e8c52d0371c7cd78925e1955118f1a351c5b6

## Report

改訂版 cp198 を反映しました。今回は指示どおり audit-only で、Lean theorem は追加していません。

更新したレポート:

[report-petal-198.md](/home/deskuma/develop/lean/dkmath/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-198.md)

内容は import direction / API boundary を中心に書き直しています。

確認した import chain:

```text
PressureFrontier
  <- PressureAccounting
    <- PressureLocalWitnessObstruction
      <- PressureAdjacentDiagnosis
        <- PressureDiagnosticDecomposition
```

また、以下 2 theorem が `PressureDiagnosticDecomposition.lean` のみにあることも確認しました。

```lean
sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap
sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
```

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
git diff --check
```

5 pressure files の `sorry` / `admit` チェックは一致なしです。ビルドログ上の既知 unrelated warning `ZsigmondyCyclotomicResearch.lean:152` はそのままです。

## Review

## 大丈夫。状況把握 OK じゃ

うむ、把握しておる。
今の局面はかなり大事じゃ。

今回の snapshot が現在ワークスペースそのもの、かつコードレベルでコミットとの差がないなら、わっちの認識はこうじゃ。

```text
現在地:
  Lean が認めた pressure 会計システムの局所オートマトンは成立している。

次の目的:
  そのオートマトンの状態遷移を、依存方向を壊さずに上位面へ持ち上げる。

まだやらないこと:
  Collatz convergence、global coverage、canonical diagnosis、union accounting。
```

添付の `review-petal-199-r0.md` と `review-petal-199.md` も見た。r0 では `PressureFrontier` / `PressureAccounting` 側の consumer gap 調査だったが、改訂版では import direction / API boundary audit に正しく収束しておる。改訂版 cp198 は audit-only で Lean theorem 追加なし、import chain と API 境界確認に集中している。

## 今の会計スタックの正体

確定した import chain はこれじゃ。

```text
PressureFrontier
  <- PressureAccounting
    <- PressureLocalWitnessObstruction
      <- PressureAdjacentDiagnosis
        <- PressureDiagnosticDecomposition
```

改訂 report でもこの chain が明示され、`PressureFrontier` や `PressureAccounting` が `PressureDiagnosticDecomposition` の theorem 名を consume してはいけない、と整理されておる。これは正しい。

役割としてはこうじゃな。

```text
PressureFrontier:
  pressure depths / local islands / interval pulses / pulse addresses

PressureAccounting:
  explicit witness lists / sorted-before carrier / finite accounting

PressureLocalWitnessObstruction:
  witness-level obstruction vocabulary

PressureAdjacentDiagnosis:
  adjacent pair diagnosis, recovered-or-overlap

PressureDiagnosticDecomposition:
  named pair diagnostic surface, no-overlap consumer, bounded decomposition
```

つまり、これはすでに **Lean が認めた有限会計オートマトン** になっている。

## Lean が認めた遷移

いま見えている主な状態遷移はこれじゃ。

```text
local pressure profile
  -> local island / interval pulse

interval pulse
  -> accounted interval
  -> finite net drop budget

witness list
  -> sorted-before failure

sorted-before failure
  -> adjacent diagnosis

adjacent diagnosis
  -> recovered branch or overlap obstruction

sorted-before failure + no-adjacent-overlap
  -> pair-local recovered accounted-family diagnostic
```

cp198 改訂版では、最後の二段 API が `PressureDiagnosticDecomposition.lean` 側にあることも確認されておる。

```lean
sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap

sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
```

前者は overlap を branch として残す。後者は no-overlap を渡したときだけ recovered diagnostic を抽出する。この分離が大事じゃ。

## 次に収束すべき実装

見えておる。
次は **下位ファイルに theorem を足す段階ではない**。

次にやるべきは、上位に薄い **Pressure Automaton Surface** を置くことじゃ。

候補名は例えばこれ。

```text
DkMath/Collatz/PetalBridge/PressureAutomaton.lean
```

または、より控えめにするなら、

```text
DkMath/Collatz/PetalBridge/PressureDiagnosticSurface.lean
```

ここは `PressureDiagnosticDecomposition` より上に置く。つまり import は一方向だけ。

```lean
import DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
```

この新ファイルでやることは、まだ大定理ではない。
**Lean が認めた局所オートマトンの状態遷移表を theorem / def 名として固定する** ことじゃ。

## 次 checkpoint の最小実装案

わっちの推奨はこれ。

```lean
def SourcePressureFailureResolution
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
  (∃ A B,
    SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic A B) ∨
    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
```

そして wrapper theorem を一本だけ。

```lean
theorem sourcePressureFailureResolution_of_sortedBeforeFailure
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L) :
    SourcePressureFailureResolution L :=
  sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap h
```

さらに no-overlap 版を置くなら、これも許容範囲。

```lean
theorem sourcePressureFailureResolution_recovered_of_noAdjacentOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
    (hno : SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L) :
    ∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic A B :=
  sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap h hno
```

これは新しい証明力ではなく、**オートマトンの公開面** じゃ。

ここが次の収束点として一番よい。

## なぜこれが重要か

いまのコードは、部品としては強い。
しかし「機械語バイナリコードを読む」には、状態遷移名が必要じゃ。

いまは theorem 名が少し実装寄りで、

```text
failure_exists_pairDiagnostic_or_adjacentOverlap
failure_exists_pairDiagnostic_of_noAdjacentOverlap
```

となっている。

これを上位で、

```text
failure resolution
automaton transition
recovered or obstruction
```

として束ねると、次に一般化しやすくなる。

DkMath 語彙で言えば、

```text
Core:
  interval / witness / net-drop 会計

Beam:
  failure resolution automaton

Gap:
  overlap obstruction branch
```

がはっきり見える。

## cp198 / cp199 の判定

今回の `review-petal-199.md` は、内容としては **cp198 改訂版の採用** でよい。

理由は明確じゃ。

```text
採用理由:
  audit-only で止めた
  theorem を増やしていない
  import direction を明文化した
  pairDiagnostic theorem の配置を確認した
  lower module への逆流を防いだ
  build / no-sorry / git diff check が報告されている
```

改訂版 report では、5 pressure files の `sorry` / `admit` チェック一致なし、`lake build` 群と `git diff --check` 通過も報告されておる。既知の `ZsigmondyCyclotomicResearch.lean:152` warning は unrelated として切り分けられている。

## 注意点

ここで焦ってはいけないのは、次の誘惑じゃ。

```text
arbitrary list 全体の canonical diagnosis を作る
all diagnostics を列挙する
複数 recovered family を aggregate する
overlap を repair する
interval union accounting に進む
global coverage を言う
Collatz convergence を言う
```

まだそれは早い。

今は、

```text
Lean が認めた局所会計オートマトンを、
壊さずに名前付き公開面へ持ち上げる
```

ここが次の一手じゃ。

## 次の Codex 指示

```text
Checkpoint: petal-199

Main goal:
  Add a thin upper-level pressure automaton surface above
  `PressureDiagnosticDecomposition`.  This checkpoint should not add new
  mathematical strength.  It should expose the already Lean-proved failure
  resolution as a named automaton-style API.

Primary target file:
  DkMath/Collatz/PetalBridge/PressureAutomaton.lean

Allowed supporting files:
  DkMath/Collatz/PetalBridge.lean
  docs/dev/das-p2l-260607/review/report-petal-199.md

Imports:
  `PressureAutomaton.lean` should import only:
    DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition

Do not modify:
  DkMath/Collatz/PetalBridge/PressureFrontier.lean
  DkMath/Collatz/PetalBridge/PressureAccounting.lean
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
  Any non-Collatz files

Suggested definitions:

  def SourcePressureFailureResolution
      {n : OddNat} {k r : ℕ}
      (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
    (∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
          A B) ∨
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L

Suggested theorems:

  theorem sourcePressureFailureResolution_of_sortedBeforeFailure
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L) :
      SourcePressureFailureResolution L :=
    sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap h

  theorem sourcePressureFailureResolution_recovered_of_noAdjacentOverlap
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
      (hno : SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L) :
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
            A B :=
    sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
      h hno

Optional aggregator:
  Add `import DkMath.Collatz.PetalBridge.PressureAutomaton` to
  `DkMath/Collatz/PetalBridge.lean`, after `PressureDiagnosticDecomposition`.

Guardrails:
  Do not add:
    - arbitrary-list recursive decomposition;
    - canonical first diagnosis;
    - enumeration of all diagnostics;
    - aggregation over multiple recovered diagnostics;
    - interval union accounting;
    - overlap repair;
    - coverage;
    - maximality;
    - uniqueness;
    - sorting theorem;
    - disjointness between multiple recovered families;
    - Collatz convergence.

Report requirements:
  - Explain that this is an upper-level API surface, not new proof strength.
  - Include the pressure import chain.
  - State that lower modules were not modified.
  - State that overlap remains an obstruction branch.
  - State that no global convergence, coverage, aggregation, or repair was added.

Verification commands:
  lake build DkMath.Collatz.PetalBridge.PressureAutomaton
  lake build DkMath.Collatz.PetalBridge

No-sorry check:
  rg -n "\bsorry\b|admit" \
    DkMath/Collatz/PetalBridge/PressureAutomaton.lean \
    DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean \
    DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
    DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
    DkMath/Collatz/PetalBridge/PressureAccounting.lean \
    DkMath/Collatz/PetalBridge/PressureFrontier.lean

Git diff hygiene:
  git diff --check
```

## わっちの見立て

ぬしよ、ここは本当に良い局面じゃ。
「証明できた」と騒ぐ場所ではなく、**Lean が認めた局所機械を読める形に翻訳する場所** じゃ。

コラッツ予想の機械語バイナリコード、という比喩はかなり当たっておる。
今はそのバイナリ列の中に、

```text
failure
diagnosis
recovered
overlap obstruction
no-overlap extraction
negative budget
```

という命令語が見えてきた段階じゃ。

次はそれを **PressureAutomaton** として命令表にする。
ここまで行けば、その次にようやく「この automaton が時間方向にどう伝播するか」、つまり Beam 解析へ入れる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-198.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-198.md
index 5337c1ef..98b0fb22 100644
--- a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-198.md
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-198.md
@@ -2,104 +2,101 @@

 ## Checkpoint

-Checkpoint 198 was audit-only.
+Checkpoint 198 revised was audit-only.

-No Lean theorem was added.  The downstream shape of the arbitrary-list
-diagnostic API is already in the right module layer, and no clear consumer gap
-was found in `PressureFrontier` or `PressureAccounting`.
+No Lean theorem was added.  The purpose of this checkpoint was to confirm the
+import direction and API boundary around the arbitrary-list pressure diagnostic
+surface.

-## Files inspected
+## Import Chain

-Primary file:
+The current pressure stack flows upward as follows:

 ```text
-DkMath/Collatz/PetalBridge/PressureFrontier.lean
+PressureFrontier
+  <- PressureAccounting
+    <- PressureLocalWitnessObstruction
+      <- PressureAdjacentDiagnosis
+        <- PressureDiagnosticDecomposition
 ```

-Supporting files inspected:
-
-```text
-DkMath/Collatz/PetalBridge/PressureAccounting.lean
-DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
-```
+The concrete imports are:

-## Theorems and definitions inspected
+```lean
+-- PressureFrontier.lean
+import DkMath.Collatz.PetalBridge.PressureDecay

-In `PressureFrontier.lean`, the relevant inspected surface was the frontier and
-local-island producer layer:
+-- PressureAccounting.lean
+import DkMath.Collatz.PetalBridge.PressureFrontier

-```lean
-SourcePressureLocalIsland
-sourcePressureLocalIsland_iff_margin
-sourcePressureIntervalPulse_of_localIsland
-sourcePressureIntervalPulseAddress_of_localIsland
-```
+-- PressureLocalWitnessObstruction.lean
+import DkMath.Collatz.PetalBridge.PressureAccounting

-This file imports only:
+-- PressureAdjacentDiagnosis.lean
+import DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction

-```lean
-import DkMath.Collatz.PetalBridge.PressureDecay
+-- PressureDiagnosticDecomposition.lean
+import DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
 ```

-So it is intentionally upstream of accounting witnesses and diagnostic
-decomposition.  Making `PressureFrontier` consume pair diagnostics would invert
-the current dependency direction.
+This means lower modules such as `PressureFrontier` and `PressureAccounting`
+must not consume theorem names from `PressureDiagnosticDecomposition` unless a
+separate refactor-only checkpoint deliberately changes the module structure.

-In `PressureAccounting.lean`, the relevant inspected surface was the explicit
-witness-list and sorted-before carrier layer:
+## Diagnostic Surface Location

-```lean
-SourcePressureLocalIslandWitness
-sourcePressureIntervalPulseAddress_of_localIslandWitness
-sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList
-SourcePressureLocalIslandWitnessListSortedBefore
-SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
-sourcePressureLocalIslandWitnessList_sorted_or_failure
+The branch split theorem lives only in:
+
+```text
+DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
 ```

-This file imports:
+The exact theorem is:

 ```lean
-import DkMath.Collatz.PetalBridge.PressureFrontier
+sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap
 ```

-It defines the explicit witness and sorted-before vocabulary, but it does not
-import adjacent diagnosis or diagnostic decomposition.  Adding the requested
-consumer here would pull a downstream diagnostic layer back into the carrier
-layer.
+The no-overlap consumer theorem also lives only in:
+
+```text
+DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
+```

-In `PressureDiagnosticDecomposition.lean`, the already confirmed two-stage API
-remains:
+The exact theorem is:

 ```lean
-sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap
 sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
 ```

-## Audit result
+Search result:

-No downstream wrapper was added.
+```text
+DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean:806
+DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean:836
+```

-The current layering is:
+No lower pressure module defines or imports these names.

-```text
-PressureFrontier
-  -> pressure depths, local islands, interval pulses, pulse addresses
+## Boundary Interpretation

-PressureAccounting
-  -> explicit local-island witnesses and sorted/failure carrier vocabulary
+`PressureFrontier` is a producer layer.  It talks about pressure depths, local
+islands, interval pulses, and pulse addresses.  It is upstream of explicit
+local-island witness lists and does not know about adjacent diagnostics.

-PressureDiagnosticDecomposition
-  -> named recovered diagnostics and no-overlap consumers
-```
+`PressureAccounting` is a carrier layer.  It introduces explicit witness lists,
+sorted-before predicates, sorted-before failure predicates, and finite
+accounting wrappers.  It should not import diagnostic decomposition, because
+that would pull a downstream consumer layer back into a foundational carrier
+module.

-This is the intended separation.  The no-overlap pair diagnostic API should be
-used from `PressureDiagnosticDecomposition` or later downstream modules, not
-from `PressureFrontier` or `PressureAccounting`.
+`PressureDiagnosticDecomposition` is the correct location for the named
+pair-diagnostic arbitrary-list API, because it already imports the adjacent
+diagnosis layer and sits above the carrier modules.

-## Two-stage API confirmed
+## Two-Stage API Confirmed

-The two-stage arbitrary-list diagnostic API remains:
+The current two-stage API remains:

 ```text
 sorted-before failure
@@ -109,15 +106,23 @@ sorted-before failure + no-adjacent-overlap
   -> exists pairDiagnostic
 ```

-The branch split keeps overlap visible.  The recovered diagnostic extraction is
-only available once the caller supplies no-overlap.
+In theorem names:
+
+```lean
+sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap
+sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
+```
+
+The first theorem keeps overlap visible as a branch.  The second theorem
+extracts a recovered adjacent pair only after the caller supplies no-overlap.

 ## Guardrails

-No theorem was added for:
+No theorem or import was added for:

-- length-six decomposition,
-- arbitrary-list recursion,
+- downstream imports from `PressureFrontier` or `PressureAccounting` to
+  `PressureDiagnosticDecomposition`,
+- arbitrary-list recursive decomposition,
 - canonical first diagnosis,
 - enumeration of all diagnostics,
 - aggregation over multiple recovered diagnostics,
@@ -125,21 +130,23 @@ No theorem was added for:
 - coverage,
 - maximality,
 - uniqueness,
-- sorting,
+- sorting theorem,
 - overlap repair,
 - disjointness between multiple recovered families,
 - Collatz convergence.

-## Line-count status
+## Line-Count Status

 ```text
-  1517 DkMath/Collatz/PetalBridge/PressureFrontier.lean
-  1896 DkMath/Collatz/PetalBridge/PressureAccounting.lean
   1130 DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
-  4543 total
+  1356 DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+  1391 DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
+  1896 DkMath/Collatz/PetalBridge/PressureAccounting.lean
+  1517 DkMath/Collatz/PetalBridge/PressureFrontier.lean
+  7290 total
 ```

-All inspected files remain under the 2,000-line split threshold.
+All five files remain under the 2,000-line split threshold.

 ## Verification

@@ -147,6 +154,8 @@ Commands run from `lean/dk_math`:

 ```text
 lake build DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
+lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
+lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
 lake build DkMath.Collatz.PetalBridge.PressureAccounting
 lake build DkMath.Collatz.PetalBridge.PressureFrontier
 lake build DkMath.Collatz.PetalBridge
@@ -154,11 +163,13 @@ lake build DkMath.Collatz.PetalBridge

 Result: all builds passed.

-No-sorry check over the requested files:
+No-sorry check over the five requested pressure files:

 ```text
 rg -n "\bsorry\b|admit" \
   DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean \
+  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
+  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
   DkMath/Collatz/PetalBridge/PressureAccounting.lean \
   DkMath/Collatz/PetalBridge/PressureFrontier.lean
 ```
@@ -167,7 +178,7 @@ Result: no matches.

 `git diff --check` passed.

-Known unrelated warning:
+Known unrelated warning observed in local build logs:

 ```text
 DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
````
`````
