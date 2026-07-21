# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam.Pulse

gch: bf3774e98e1aa3bf6c217e4c25266cb179b2ef70

## Report

cp227 完了です。

[Pulse.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean) に、seed から明示 witness を取り出して cp226 の full diagnostic を適用する存在補題を追加しました。

```lean
exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_seed
```

意味は局所的に限定しています。

```text
SourcePressureBeamSeed L
  -> ∃ W ∈ L, W の singleton pulse に entry-depth-exit diagnostic がある
```

list 全体 coverage、canonical selection、aggregation、overlap repair、propagation、Collatz convergence は主張していません。依存方向も clean で、下位 diagnostic module には触れていません。

レポートも追加しました。

[report-petal-227.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-227.md)

確認済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
rg -n "sorry|admit" lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam
git diff --check
```

すべて通過。既知の unrelated warning として `ZsigmondyCyclotomicResearch.lean` の `sorry` 警告だけ出ています。

## Review

```txt
Checkpoint: petal-227-revised

Primary Goal:
  Use the new Pulse-level full diagnostic theorem as a strategic probe.
  Do not merely ask whether a caller exists.  Investigate what kind of next
  bridge is now possible from explicit witness membership, Beam seed, failure
  resolution, or automaton output.

Current key theorem:
  sourcePressureBeamPulse_witness_singleton_full_diagnostic

It gives, from one explicit witness membership:

  W ∈ L

the local diagnostic package:

  entry:
    left < right

  center/right:
    SourcePressureBeamAddressedDepthTarget L ...

  exit:
    right <= left

Branch Goals:

  Branch A: explicit caller exists
    If an existing higher-level theorem already has an explicit witness
    membership `W ∈ L`, add one small theorem that consumes
    `sourcePressureBeamPulse_witness_singleton_full_diagnostic`.

    The theorem should package the caller-facing consequence, not rebuild the
    pulse facts manually.

    Keep it local to one witness and one membership.

  Branch B: caller exists but only has Beam seed
    If the caller has `SourcePressureBeamSeed L` but not an explicit `W ∈ L`,
    do not invent a canonical witness.

    Instead investigate whether the existing seed existential machinery can
    expose:
      ∃ W ∈ L, ...

    If this already exists, add an existential diagnostic theorem:
      seed -> ∃ W, W ∈ L ∧ <full diagnostic for W>

    If it does not exist, report the exact missing relation.

  Branch C: caller exists but only has failure resolution / adjacent obstruction
    If a higher-level automaton/failure-resolution theorem exposes an adjacent
    pair, overlap obstruction, or recovered witness list, inspect whether it
    gives a concrete witness membership.

    If yes:
      add a theorem only for that explicit witness/membership path.

    If no:
      record the missing bridge:
        failure/obstruction -> explicit witness membership

    Do not select arbitrary witnesses.

  Branch D: multiple candidate callers exist
    Choose the smallest local caller with the fewest new assumptions.
    Implement only one theorem.
    Record the other candidates in the report as future routes.

    Priority order:
      1. explicit W ∈ L caller
      2. seed -> existential witness diagnostic
      3. failure resolution -> explicit witness
      4. automaton-level packaging

  Branch E: obstruction found
    If Lean shows a proposed route is impossible or contradicts current
    definitions, add a small negative theorem only if it is useful and local.

    Otherwise record it as False Beam / obstruction in the report.

  Branch F: no caller exists
    Add no Lean code.
    Report:
      - what modules were inspected;
      - which expected caller shape was absent;
      - the exact missing relation;
      - the next viable bridge to try.

Files to inspect:
  DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
  DkMath/Collatz/PetalBridge/PressureBeam/Core.lean
  DkMath/Collatz/PetalBridge/PressureAutomaton.lean
  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean

Implementation rule:
  Codex should use workspace judgment.
  Use `#check`, `#print`, and scratch lemmas.
  Do not write the theorem shape blindly.  Discover which branch the workspace
  supports.

Strict guardrails:
  Do not add:
    - list-wide coverage;
    - witness-family aggregation;
    - arbitrary witness selection;
    - canonical target selection;
    - arbitrary target transport;
    - overlap repair;
    - propagation;
    - Collatz convergence.

Dependency guardrail:
  Do not make lower diagnostic modules import PressureBeam.
  If a bridge is needed, place it in `PressureBeam/Pulse.lean` or another
  Beam-facing upper module.

Report requirements:
  - State which Branch was taken.
  - State which Branches were inspected but not taken.
  - If theorem added, identify the existing theorem it consumes.
  - If no theorem added, identify the precise missing relation.
  - Classify findings as True Beam / Boundary / False Beam / Gap.
  - Predict the next branch to attack.
  - Confirm no dependency inversion.
  - Confirm no coverage or aggregation was introduced.

Verification if code changes:
  lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge
  no-sorry grep over PressureBeam split files and inspected pressure files
  git diff --check
```

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
index e0ae68db..1a5a4036 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
@@ -209,5 +209,43 @@ theorem sourcePressureBeamPulse_witness_singleton_full_diagnostic
     ⟨hdepth, _⟩
   exact ⟨hentry, hdepth, hexitBalance⟩

+/--
+A Beam seed exposes one witness whose singleton pulse has the full local
+entry-depth-exit diagnostic.
+
+This is the cp227 higher-level consumer of
+`sourcePressureBeamPulse_witness_singleton_full_diagnostic`.  The seed layer
+already contains an existential witness membership; this theorem only keeps
+that witness explicit and applies the full diagnostic package to it.
+
+It is intentionally existential and local.  It does not choose a canonical
+witness, cover the whole list, aggregate witness families, repair overlaps,
+propagate the diagnostic, or assert Collatz convergence.
+-/
+theorem exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_seed
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hseed : SourcePressureBeamSeed L) :
+    ∃ W : SourcePressureLocalIslandWitness n k r,
+      W ∈ L ∧
+        SourcePressureBeamMassBalanceLeftInt n k r
+            ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) <
+          SourcePressureBeamMassBalanceRightInt n k r
+            ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) ∧
+          SourcePressureBeamAddressedDepthTarget L
+            ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
+              (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) ∧
+            SourcePressureBeamMassBalanceRightInt n k r
+              ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
+                (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) ≤
+              SourcePressureBeamMassBalanceLeftInt n k r
+                ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
+                  (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) := by
+  rcases exists_sourcePressureBeamSeedContainsDepth_of_seed hseed with
+    ⟨_, W, hmem, _⟩
+  exact
+    ⟨W, hmem,
+      sourcePressureBeamPulse_witness_singleton_full_diagnostic hmem⟩
+

 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-227.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-227.md
new file mode 100644
index 00000000..8d1ff06f
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-227.md
@@ -0,0 +1,144 @@
+# report-petal-227
+
+## Checkpoint
+
+`petal-227`
+
+## Goal
+
+Investigate whether the cp226 Pulse-level full diagnostic theorem has an
+immediate higher-level caller without forcing a broad new API.
+
+The theorem under inspection was:
+
+```lean
+sourcePressureBeamPulse_witness_singleton_full_diagnostic
+```
+
+It consumes one explicit witness membership `W ∈ L` and packages:
+
+- entry mass-balance: `left < right`;
+- list-relative addressed depth at the singleton right edge;
+- exit mass-balance: `right <= left`.
+
+## Files Inspected
+
+Primary:
+
+- `DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean`
+- `DkMath/Collatz/PetalBridge/PressureBeam.lean`
+- `DkMath/Collatz/PetalBridge/PressureAutomaton.lean`
+
+Secondary context:
+
+- `DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean`
+- `DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean`
+- `DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean`
+
+## Finding
+
+The useful immediate caller is not the lower diagnostic modules.  Those modules
+classify obstruction and adjacent-witness phenomena and should not import the
+Beam layer.
+
+The clean caller is instead the Beam seed surface:
+
+```lean
+SourcePressureBeamSeed L
+```
+
+The seed API already exposes an existential contained witness through
+`exists_sourcePressureBeamSeedContainsDepth_of_seed`.  That is enough to obtain
+an explicit `W ∈ L`, so the cp226 full diagnostic can be applied directly.
+
+## Added Theorem
+
+Added in `DkMath.Collatz.PetalBridge.PressureBeam.Pulse`:
+
+```lean
+theorem exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_seed
+```
+
+Meaning:
+
+```text
+SourcePressureBeamSeed L
+  -> exists W in L
+       such that W's singleton pulse has the full local entry-depth-exit
+       diagnostic.
+```
+
+This theorem consumes:
+
+```lean
+sourcePressureBeamPulse_witness_singleton_full_diagnostic
+```
+
+It does not rebuild the entry/depth/exit facts manually.  It only opens the
+seed existential witness and passes its membership to the cp226 diagnostic
+package.
+
+## Boundary
+
+This is local explicit-witness API consumption only.
+
+It does not claim:
+
+- list-wide coverage;
+- witness-family aggregation;
+- arbitrary witness selection;
+- canonical target selection;
+- arbitrary target transport;
+- overlap repair;
+- propagation;
+- Collatz convergence.
+
+## Dependency Direction
+
+No dependency inversion was introduced.
+
+The new theorem was placed in `PressureBeam/Pulse.lean`, above the diagnostic
+modules.  No lower diagnostic module imports `PressureBeam`.
+
+## Verification
+
+Commands run from `lean/dk_math` unless noted:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
+lake build DkMath.Collatz.PetalBridge.PressureBeam
+lake build DkMath.Collatz.PetalBridge
+```
+
+All builds completed successfully.
+
+Additional checks from repository root:
+
+```text
+rg -n "sorry|admit" lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam
+git diff --check
+```
+
+The no-sorry grep found no matches in the PressureBeam split files.
+`git diff --check` passed.
+
+Known unrelated warning observed during builds:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+## Next Inference
+
+The seed-to-diagnostic path is now explicit:
+
+```text
+SourcePressureBeamSeed L
+  -> exists W ∈ L
+  -> full local singleton pulse diagnostic for W
+```
+
+The next useful question is whether `PressureAutomaton` failure resolution can
+expose a similarly explicit witness membership from its recovered adjacent
+pair, without turning that into coverage or canonical selection.
````
`````
