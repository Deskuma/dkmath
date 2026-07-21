# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam.Pulse

gch: 6333d8eb6ee640b11de6c7e40cfbb7cf38c83ae2

## Report

Revised cp227 をやり直しました。

変更点は最小です。既に追加していた seed 経由 theorem を、改訂指示に合わせて **Branch B** として明確化しました。

```lean
exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_seed
```

コードコメントを `cp227-r1 Branch B` に修正し、[report-petal-227.md](/home/deskuma/develop/lean/dkmath/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-227.md) を revised 仕様で全面更新しました。Branch A-F の調査結果、True Beam / Boundary / False Beam / Gap 分類、次に攻める Branch C の条件も記録しています。

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
rg -n "sorry|admit" ...PressureBeam + inspected pressure files
git diff --check
```

すべて通過。既知の unrelated warning として `ZsigmondyCyclotomicResearch.lean` の `sorry` 警告のみ出ています。

## Director

```txt
## Next Branch To Attack

The next useful branch is Branch C, but only if a caller needs to remain at the
automaton/failure-resolution level.

Candidate future theorem:

```text
SourcePressureFailureResolution L
  -> exists W in L
       such that W's singleton pulse has the full local diagnostic
```

This should be added only when it removes real caller noise.  For current Beam
work, the seed theorem is the cleaner public surface.

```

追加続行、これも実装実験してみて

## 実験結果より

次回からは、指定 checkpoint の Goal を満たした後に、Lean が自然に通せる範囲の branch 候補をこちらで判断して追加実装します。

方針はこうします。

- 主 goal を先に閉じる
- その結果から自然な branch 候補を 1-2 個まで選ぶ
- local / existential / wrapper 系の安全な theorem を優先
- coverage、canonical selection、aggregation、propagation、convergence は明示証拠なしに踏み込まない
- 追加した branch はコードコメントと report に「なぜ今足したか」を残す
- 重くなりそうなら TODO/Gap として止める

今回の Branch C のような薄い橋は、今後はこちらで進めます。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
index 1a5a4036..414503d4 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
@@ -213,7 +213,7 @@ theorem sourcePressureBeamPulse_witness_singleton_full_diagnostic
 A Beam seed exposes one witness whose singleton pulse has the full local
 entry-depth-exit diagnostic.

-This is the cp227 higher-level consumer of
+This is the cp227-r1 Branch B higher-level consumer of
 `sourcePressureBeamPulse_witness_singleton_full_diagnostic`.  The seed layer
 already contains an existential witness membership; this theorem only keeps
 that witness explicit and applies the full diagnostic package to it.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-227.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-227.md
index 8d1ff06f..2721b8e5 100644
--- a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-227.md
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-227.md
@@ -2,54 +2,63 @@

 ## Checkpoint

-`petal-227`
+`petal-227-revised`

 ## Goal

-Investigate whether the cp226 Pulse-level full diagnostic theorem has an
-immediate higher-level caller without forcing a broad new API.
-
-The theorem under inspection was:
+Use the Pulse-level full diagnostic theorem as a strategic probe:

 ```lean
 sourcePressureBeamPulse_witness_singleton_full_diagnostic
 ```

-It consumes one explicit witness membership `W ∈ L` and packages:
+The theorem consumes one explicit witness membership:
+
+```lean
+W ∈ L
+```

-- entry mass-balance: `left < right`;
-- list-relative addressed depth at the singleton right edge;
-- exit mass-balance: `right <= left`.
+and packages the local singleton pulse diagnostic:

-## Files Inspected
+- entry: `left < right`;
+- center/right: `SourcePressureBeamAddressedDepthTarget L ...`;
+- exit: `right <= left`.

-Primary:
+## Branch Taken

-- `DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean`
-- `DkMath/Collatz/PetalBridge/PressureBeam.lean`
-- `DkMath/Collatz/PetalBridge/PressureAutomaton.lean`
+Branch B was taken:
+
+```text
+caller exists but only has Beam seed
+```

-Secondary context:
+The smallest available higher-level caller is:

-- `DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean`
-- `DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean`
-- `DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean`
+```lean
+SourcePressureBeamSeed L
+```

-## Finding
+This caller does not itself present a named `W ∈ L` at the surface, and we
+should not invent a canonical witness.  However, the existing seed machinery
+already exposes an existential contained witness through:

-The useful immediate caller is not the lower diagnostic modules.  Those modules
-classify obstruction and adjacent-witness phenomena and should not import the
-Beam layer.
+```lean
+exists_sourcePressureBeamSeedContainsDepth_of_seed
+```

-The clean caller is instead the Beam seed surface:
+That gives:

 ```lean
-SourcePressureBeamSeed L
+∃ j, SourcePressureBeamSeedContainsDepth L j
+```
+
+and `SourcePressureBeamSeedContainsDepth L j` unfolds to:
+
+```lean
+∃ W ∈ L, W.val = j
 ```

-The seed API already exposes an existential contained witness through
-`exists_sourcePressureBeamSeedContainsDepth_of_seed`.  That is enough to obtain
-an explicit `W ∈ L`, so the cp226 full diagnostic can be applied directly.
+So the seed can safely feed the full diagnostic existentially.

## Added Theorem

@@ -68,21 +77,95 @@ SourcePressureBeamSeed L
        diagnostic.

 ```

-This theorem consumes:
+The theorem consumes:

 ```lean
 sourcePressureBeamPulse_witness_singleton_full_diagnostic
 ```

-It does not rebuild the entry/depth/exit facts manually.  It only opens the
-seed existential witness and passes its membership to the cp226 diagnostic
-package.
+It does not rebuild the pulse facts manually.  It opens the seed existential,
+keeps the extracted witness explicit, and applies the full diagnostic package
+to that witness membership.
+
+## Branches Inspected But Not Taken
+
+Branch A:
+
+- No better existing caller with an already surfaced `W ∈ L` was found.
+- The Pulse API itself has explicit-membership theorems, but adding another

+ direct alias there would only duplicate the cp226 theorem.
+

+Branch C:
+
+- `PressureAutomaton` exposes `SourcePressureFailureResolution L`, with either

+ a recovered adjacent pair or an overlap obstruction.
+- The recovered branch gives an adjacent-pair relation, and the overlap branch
+ is list-addressed, but the clean exposed Beam-facing route is already
+ mediated by `SourcePressureBeamSeed`.
+- A direct failure-resolution theorem may be useful later, but it would be a
+ higher duplicate of the seed route unless a caller specifically works before
+ entering Beam seed vocabulary.
+

+Branch D:
+
+- Multiple possible caller surfaces exist, but the seed route is the smallest

+ one with the fewest new assumptions after explicit `W ∈ L`.
+

+Branch E:
+
+- No contradiction or useful local negative theorem was discovered.
+
+Branch F:
+
+- Not applicable.  A valid caller route exists through the Beam seed.

-## Boundary
+## Classification

-This is local explicit-witness API consumption only.
+True Beam:

-It does not claim:
+- `W ∈ L -> full local singleton diagnostic` is already proved by cp226.
+- `SourcePressureBeamSeed L -> ∃ W ∈ L, full local singleton diagnostic` is now

+ proved by cp227-r1.
+

+Boundary:
+
+- The new theorem is existential.  It identifies one witness already contained

+ in the supplied seed list.
+

+False Beam:
+
+- No false/negative theorem was needed here.
+- The failure-resolution overlap branch remains an obstruction branch, not an

+ overlap repair theorem.
+

+Gap:
+
+- A direct automaton-level bridge from

+ `SourcePressureFailureResolution L` to the full diagnostic may be possible,
+ but it is currently unnecessary because `SourcePressureBeamSeed L` is exactly
+ the Beam-facing wrapper of that state.
+- If a future caller must stay at `PressureAutomaton` level, the missing bridge
+ to inspect is:
+

+```text
+failure/obstruction branch -> explicit W ∈ L -> full diagnostic
+```
+
+## Dependency Direction
+
+No dependency inversion was introduced.
+
+The new theorem was placed in:
+
+```text
+DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
+```
+
+No lower diagnostic module imports `PressureBeam`.
+
+## Guardrails
+
+The new theorem does not claim:

+ list-wide coverage;
+ witness-family aggregation;
@@ -93,16 +176,12 @@ It does not claim:
+ propagation;
+ Collatz convergence.

-## Dependency Direction
-

-No dependency inversion was introduced
-

-The new theorem was placed in `PressureBeam/Pulse.lean`, above the diagnostic
-modules.  No lower diagnostic module imports `PressureBeam`.
+It is local explicit-witness API consumption, lifted existentially from the
+Beam seed.

## Verification

-Commands run from `lean/dk_math` unless noted:
+Commands run from `lean/dk_math`:

 ```text
 lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
@@ -129,16 +208,18 @@ DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
 declaration uses `sorry`
 ```

-## Next Inference
+## Next Branch To Attack

-The seed-to-diagnostic path is now explicit:
+The next useful branch is Branch C, but only if a caller needs to remain at the
+automaton/failure-resolution level.
+
+Candidate future theorem:

 ```text
-SourcePressureBeamSeed L
-  -> exists W ∈ L
-  -> full local singleton pulse diagnostic for W
+SourcePressureFailureResolution L
+  -> exists W in L
+       such that W's singleton pulse has the full local diagnostic
 ```

-The next useful question is whether `PressureAutomaton` failure resolution can
-expose a similarly explicit witness membership from its recovered adjacent
-pair, without turning that into coverage or canonical selection.
+This should be added only when it removes real caller noise.  For current Beam
+work, the seed theorem is the cleaner public surface.

````
`````
