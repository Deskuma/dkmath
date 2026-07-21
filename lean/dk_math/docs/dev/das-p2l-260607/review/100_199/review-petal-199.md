# Git diff / Report / Review

## Add: docs: report 198

gch: 90e6eb364ffa465e361122bbd1358b84b46ec7e0

## Report

cp198 完了です。今回は audit-only で、Lean theorem は追加していません。

確認結果として、`PressureFrontier` は `PressureDecay` だけを import する上流の producer 層、`PressureAccounting` は explicit witness / sorted-before carrier 層なので、ここへ no-overlap diagnostic consumer を入れると依存方向が不自然になります。既存の二段構えは `PressureDiagnosticDecomposition` 側に置かれており、そのままが適切です。

追加したレポート:

[report-petal-198.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-198.md)

確認済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
git diff --check
```

指定 3 ファイルの `sorry` / `admit` チェックは一致なしです。既知の unrelated warning `ZsigmondyCyclotomicResearch.lean:152` はそのままです。

## Review

## 結論

うむ、snapshot は確認した。
SHA256 は、ぬしの提示した値と一致しておる。

```text
57344b6bc175251a31f555bc2761c515aad54ce1421431399a654a6c9824dbd8  __snapshot-dk_math-lean-code-260706-1126.tar.gz
```

手元で tar を展開し、`DkMath/Collatz/PetalBridge` 周辺を実コードとして見た。`README.md` / `AGENT.md` / `SUMMARY.md` の前提どおり、実装確認は snapshot / all.lean / summary を優先する方針で進める、という理解も改めて固定しておく。`SUMMARY.md` でも `__dkmath-all.lean.txt` は全 Lean コード参照用、`__theorems-heading.txt` や `__sorries.txt` などは補助インデックスとして位置づけられておる。

## 確認した Collatz / PetalBridge の現況

`DkMath/Collatz/PetalBridge` は現在、かなり整理された分割になっておる。

```text
Basic.lean
Residues.lean
Profiles.lean
Counts.lean
Ratios.lean
Mass.lean
PressureCore.lean
PressureCounts.lean
HeightBudget.lean
TailSplits.lean
TailGrammar.lean
DriftBudget.lean
PressureDecay.lean
PressureFrontier.lean
PressureAccounting.lean
PressureLocalWitnessObstruction.lean
PressureAdjacentDiagnosis.lean
PressureDiagnosticDecomposition.lean
OneCycle.lean
ValuationFlowBridge.lean
Collision.lean
```

import の層はこうじゃ。

```text
PressureFrontier
  <- PressureAccounting
    <- PressureLocalWitnessObstruction
      <- PressureAdjacentDiagnosis
        <- PressureDiagnosticDecomposition
```

つまり、`PressureDiagnosticDecomposition.lean` は診断分解の上位面であり、`PressureFrontier.lean` や `PressureAccounting.lean` から直接これを consume する方向ではない。ここは、わっちの次 checkpoint 指示に少し補正が必要じゃな。

## cp196 / cp197 周辺の実コード確認

`PressureDiagnosticDecomposition.lean` では、次の named predicate が定義されておる。

```lean
def SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
```

これは pair-local な recovered accounted family diagnostic で、list-wide aggregation ではない。

さらに cp196 の主 theorem も実体として確認した。

```lean
theorem
    sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap
```

statement は、sorted-before failure から、

```lean
(∃ A B,
  SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic A B)
∨
  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
```

を出す形じゃ。

証明は既存の

```lean
sourcePressureLocalIslandWitnessList_failure_exists_recovered_or_overlap
```

を `rcases` し、recovered branch では

```lean
SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic.of_before hrev
```

で named predicate に包み直している。これはわっちの以前の採用判断どおり、過大主張ではなく **既存 carrier の named-surface projection** じゃ。

cp197 で監査対象だった no-overlap consumer も確認した。

```lean
theorem
    sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
```

これは

```lean
sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
```

から

```lean
.exists_pairDiagnostic
```

で existential projection する形になっておる。つまり report-petal-197 の言う二段構えは、snapshot 上でも実コードとして成立しておる。

## line count / no-sorry 状況

該当 pressure files の行数は次じゃ。

```text
  1130 DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
  1356 DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
  1391 DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
  1896 DkMath/Collatz/PetalBridge/PressureAccounting.lean
  1517 DkMath/Collatz/PetalBridge/PressureFrontier.lean
    93 DkMath/Collatz/PetalBridge.lean
```

指定 pressure files については、

```text
rg -n "\bsorry\b|admit" ...
```

で一致なしだった。ここは report と整合しておる。

ただし、手元コンテナには `lake` / `lean` コマンドが無かったため、わっち自身では `lake build` は実行できておらん。build 成功については、snapshot 内 report の記載と、コード構造の静的確認までじゃ。ここは正直に言っておくぞい。

## 大域判断

現状は、**Collatz convergence へ進んだ段階ではなく、局所 pressure diagnostic API の出口が整った段階** じゃ。

より正確には、

```text
sorted-before failure
  -> pairDiagnostic-or-adjacentOverlap
```

と、

```text
sorted-before failure + no-adjacent-overlap
  -> exists pairDiagnostic
```

が `PressureDiagnosticDecomposition.lean` 上で閉じておる。

これは **Adjacent Diagnosis layer** と **Overlap Obstruction layer** の分離に成功している状態じゃな。
no-overlap を使わず overlap branch を見えるまま残し、no-overlap を供給した後だけ recovered diagnostic へ落とす。層の切り分けは良い。

一方で、重要な補正点がある。

前回わっちが出した「次は `PressureFrontier` / `PressureAccounting` 側の downstream consumer を見る」という方針は、実コードの import 方向を見ると少し危うい。`PressureFrontier` / `PressureAccounting` は `PressureDiagnosticDecomposition` より下位にあるので、そこで `pairDiagnostic` API を直接 consume させると依存方向が逆流しやすい。

したがって、次 checkpoint は `PressureFrontier.lean` を primary target にするより、**import DAG audit / report-only** に寄せる方が安全じゃ。

## 次の checkpoint 方針の補正

次は theorem 追加ではなく、まず **import direction audit** がよい。

見るべきことはこれじゃ。

```text
PressureFrontier
  基礎 pressure predicate / local pressure facts

PressureAccounting
  interval pulse / net drop / finite accounting

PressureLocalWitnessObstruction
  witness-level before / overlap / sorted-before failure

PressureAdjacentDiagnosis
  carrier-level adjacent recovered-or-overlap

PressureDiagnosticDecomposition
  named predicate / fixed finite cases / arbitrary-list existential projection
```

この階層を崩さないこと。
つまり、`PressureFrontier` や `PressureAccounting` に diagnostic decomposition の語彙を戻さない。これは循環依存の匂いがする。

次に足すなら、`PressureDiagnosticDecomposition.lean` 内で薄い整理をするか、docs で「consumer は上位 diagnostic decomposition surface に置く」と明文化するのがよい。

## 次 Codex 指示の修正版

```text
Checkpoint: petal-198-revised

Main goal:
  Perform an import-direction and API-boundary audit for the Collatz PetalBridge
  pressure diagnostic stack.  Do not add new Lean theorems unless a genuinely
  missing wrapper can be added without reversing dependencies.

Primary target file:
  docs/dev/das-p2l-260607/review/report-petal-198.md

Allowed supporting files:
  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean

Do not modify:
  DkMath/Collatz/PetalBridge/PressureFrontier.lean
  DkMath/Collatz/PetalBridge/PressureAccounting.lean
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
  DkMath/Collatz/PetalBridge.lean
  Any non-Collatz files

Context:
  The current import direction is:

    PressureFrontier
      <- PressureAccounting
        <- PressureLocalWitnessObstruction
          <- PressureAdjacentDiagnosis
            <- PressureDiagnosticDecomposition

  Therefore `PressureFrontier` and `PressureAccounting` must not consume
  theorem names defined in `PressureDiagnosticDecomposition`, unless the module
  structure is deliberately refactored in a separate refactor-only checkpoint.

Audit targets:
  - Confirm that `sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap`
    lives only in `PressureDiagnosticDecomposition.lean`.
  - Confirm that
    `sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap`
    is also in `PressureDiagnosticDecomposition.lean`.
  - Confirm that lower modules do not import or depend on the named
    pairDiagnostic decomposition layer.
  - Confirm that the current two-stage API remains:
      sorted-before failure -> pairDiagnostic-or-adjacentOverlap;
      sorted-before failure + no-adjacent-overlap -> exists pairDiagnostic.

Guardrails:
  Do not add:
    - downstream imports from `PressureFrontier` or `PressureAccounting`
      to `PressureDiagnosticDecomposition`;
    - arbitrary-list recursive decomposition;
    - canonical first diagnosis;
    - enumeration of all diagnostics;
    - aggregation over multiple recovered diagnostics;
    - list-wide interval union accounting;
    - coverage;
    - maximality;
    - uniqueness;
    - sorting theorem;
    - overlap repair;
    - disjointness between multiple recovered families;
    - Collatz convergence.

Report requirements:
  - State explicitly whether this is audit-only.
  - Include the pressure module import chain.
  - Explain why lower modules should not consume diagnostic decomposition
    directly.
  - State whether any Lean theorem was added. Prefer no theorem.
  - Include line counts for the five pressure files.
  - Include no-sorry check for the five pressure files.
  - Mention the known unrelated `ZsigmondyCyclotomicResearch.lean` warning
    only if it appears in the local build log.

Verification commands:
  lake build DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
  lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
  lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
  lake build DkMath.Collatz.PetalBridge.PressureAccounting
  lake build DkMath.Collatz.PetalBridge.PressureFrontier
  lake build DkMath.Collatz.PetalBridge

No-sorry check:
  rg -n "\bsorry\b|admit" \
    DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean \
    DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
    DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
    DkMath/Collatz/PetalBridge/PressureAccounting.lean \
    DkMath/Collatz/PetalBridge/PressureFrontier.lean

Git diff hygiene:
  git diff --check
```

## わっちの現時点判断

現在の山は安定しておる。
だが、次に「下流 consumer」を足す方向へ進むと、import 方向を壊す危険がある。

ゆえに次は **新 theorem ではなく import DAG audit** 。
ここを確認してから、必要なら `PressureDiagnosticDecomposition` をさらに分割するか、`PressureDiagnosticSurface.lean` のような上位 consumer 面を新設するかを判断するのが賢い。わっちの耳にも、その方が安全な足音に聞こえるぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-198.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-198.md
new file mode 100644
index 00000000..5337c1ef
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-198.md
@@ -0,0 +1,177 @@
+# report-petal-198
+
+## Checkpoint
+
+Checkpoint 198 was audit-only.
+
+No Lean theorem was added.  The downstream shape of the arbitrary-list
+diagnostic API is already in the right module layer, and no clear consumer gap
+was found in `PressureFrontier` or `PressureAccounting`.
+
+## Files inspected
+
+Primary file:
+
+```text
+DkMath/Collatz/PetalBridge/PressureFrontier.lean
+```
+
+Supporting files inspected:
+
+```text
+DkMath/Collatz/PetalBridge/PressureAccounting.lean
+DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
+```
+
+## Theorems and definitions inspected
+
+In `PressureFrontier.lean`, the relevant inspected surface was the frontier and
+local-island producer layer:
+
+```lean
+SourcePressureLocalIsland
+sourcePressureLocalIsland_iff_margin
+sourcePressureIntervalPulse_of_localIsland
+sourcePressureIntervalPulseAddress_of_localIsland
+```
+
+This file imports only:
+
+```lean
+import DkMath.Collatz.PetalBridge.PressureDecay
+```
+
+So it is intentionally upstream of accounting witnesses and diagnostic
+decomposition.  Making `PressureFrontier` consume pair diagnostics would invert
+the current dependency direction.
+
+In `PressureAccounting.lean`, the relevant inspected surface was the explicit
+witness-list and sorted-before carrier layer:
+
+```lean
+SourcePressureLocalIslandWitness
+sourcePressureIntervalPulseAddress_of_localIslandWitness
+sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList
+SourcePressureLocalIslandWitnessListSortedBefore
+SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
+sourcePressureLocalIslandWitnessList_sorted_or_failure
+```
+
+This file imports:
+
+```lean
+import DkMath.Collatz.PetalBridge.PressureFrontier
+```
+
+It defines the explicit witness and sorted-before vocabulary, but it does not
+import adjacent diagnosis or diagnostic decomposition.  Adding the requested
+consumer here would pull a downstream diagnostic layer back into the carrier
+layer.
+
+In `PressureDiagnosticDecomposition.lean`, the already confirmed two-stage API
+remains:
+
+```lean
+sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap
+sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
+```
+
+## Audit result
+
+No downstream wrapper was added.
+
+The current layering is:
+
+```text
+PressureFrontier
+  -> pressure depths, local islands, interval pulses, pulse addresses
+
+PressureAccounting
+  -> explicit local-island witnesses and sorted/failure carrier vocabulary
+
+PressureDiagnosticDecomposition
+  -> named recovered diagnostics and no-overlap consumers
+```
+
+This is the intended separation.  The no-overlap pair diagnostic API should be
+used from `PressureDiagnosticDecomposition` or later downstream modules, not
+from `PressureFrontier` or `PressureAccounting`.
+
+## Two-stage API confirmed
+
+The two-stage arbitrary-list diagnostic API remains:
+
+```text
+sorted-before failure
+  -> pairDiagnostic-or-adjacentOverlap
+
+sorted-before failure + no-adjacent-overlap
+  -> exists pairDiagnostic
+```
+
+The branch split keeps overlap visible.  The recovered diagnostic extraction is
+only available once the caller supplies no-overlap.
+
+## Guardrails
+
+No theorem was added for:
+
+- length-six decomposition,
+- arbitrary-list recursion,
+- canonical first diagnosis,
+- enumeration of all diagnostics,
+- aggregation over multiple recovered diagnostics,
+- list-wide interval union accounting,
+- coverage,
+- maximality,
+- uniqueness,
+- sorting,
+- overlap repair,
+- disjointness between multiple recovered families,
+- Collatz convergence.
+
+## Line-count status
+
+```text
+  1517 DkMath/Collatz/PetalBridge/PressureFrontier.lean
+  1896 DkMath/Collatz/PetalBridge/PressureAccounting.lean
+  1130 DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
+  4543 total
+```
+
+All inspected files remain under the 2,000-line split threshold.
+
+## Verification
+
+Commands run from `lean/dk_math`:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
+lake build DkMath.Collatz.PetalBridge.PressureAccounting
+lake build DkMath.Collatz.PetalBridge.PressureFrontier
+lake build DkMath.Collatz.PetalBridge
+```
+
+Result: all builds passed.
+
+No-sorry check over the requested files:
+
+```text
+rg -n "\bsorry\b|admit" \
+  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean \
+  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
+  DkMath/Collatz/PetalBridge/PressureFrontier.lean
+```
+
+Result: no matches.
+
+`git diff --check` passed.
+
+Known unrelated warning:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+This checkpoint did not touch that file.
````
`````
