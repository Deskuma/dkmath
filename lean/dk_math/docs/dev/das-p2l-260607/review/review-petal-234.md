# Git diff / Report / Review

## Upd: docs: report 233

gch: 06600db5610f66b4691341c5e731b2a7287f6b82

## Report

cp233 も no-code で閉じました。

`DkMath.Collatz.PetalBridge` 周辺を検索しましたが、現時点で `SourcePressureFailureResolution L` を持っていて Pulse diagnostic を必要としている未接続 caller は見つかりませんでした。したがって、追加 theorem は不要です。

作成した report:

`lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-233.md`

内容は、上位 caller 監査と現在の使い分けです。

- `PressureAutomaton`: branch-kind classifier
- `PressureBeam.Core`: seed / depth target extraction
- `PressureBeam.Pulse`: singleton Beam diagnostic extraction

`git diff --check` は通っています。Lean コード変更はありません。

## Review

## 結論

**cp233 は採用。だが、戦略評価としては「空振り寄りの採用」じゃ。**

no-code で止めた判断そのものは正しい。
報告では、`SourcePressureFailureResolution L` を持ちながら Pulse diagnostic を必要としている未接続 caller は見つからず、追加 theorem は不要と判断している。さらに、`PressureAutomaton` は branch-kind classifier、`PressureBeam.Core` は seed/depth target extraction、`PressureBeam.Pulse` は singleton Beam diagnostic extraction、という役割分担も整理できている。

ただし、ここで終わると二球連続の見送り・空振りになる。
報告自身が次候補として、

```text id="gc8a4a"
target/depth transport from SourcePressureBeamSeed
caller that combines Beam depth target and Pulse diagnostic
```

を挙げている。

ここを狙う。
次は caller 探しではない。**Core の depth axis と Pulse の interval-address axis のズレを撃つ。**

## snapshot から見えた球筋

260707-1927 snapshot を展開して、`PressureBeam.Core` と `PressureBeam.Pulse` を見た。

見えた構造はこれじゃ。

```text id="xcgc0h"
Core:
  W.val を native depth として扱う

Pulse:
  sourcePressureIntervalPulseAddress_of_localIslandWitness W
  の start / len / right edge を使って診断を書く
```

Core 側にはすでに、witness の中心深さ `W.val` と interval pulse の右 edge が一致する事実がある。

```lean id="nwe0dw"
sourcePressureIntervalPulseAddress_of_localIslandWitness_rightEdge_eq
```

さらに、membership から `W.val` の addressed target も取れる。

```lean id="gtakd7"
sourcePressureBeamAddressedDepthTarget_of_localIslandWitness_mem
```

一方、Pulse 側の full diagnostic はまだこういう形で出ている。

```text id="h83d81"
entry:
  (sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1

center/right:
  (sourcePressureIntervalPulseAddress_of_localIslandWitness W).start
    + (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1
```

これは数学的には `W.val - 1` と `W.val` じゃ。
つまり次の一手は、

```text id="ye5gpf"
Pulse diagnostic を W.val 座標へ正規化する
```

これが狙い球じゃ。

## 今回のレビュー

## True Beam

cp233 の True Beam は、API の役割分担が確定したこと。

```text id="eo4m0p"
PressureAutomaton:
  branch-kind classifier

PressureBeam.Core:
  seed / depth target extraction

PressureBeam.Pulse:
  singleton Beam diagnostic extraction
```

これは正しい整理じゃ。

## Boundary

no-code で止めたのは妥当。
右 endpoint wrapper や branch-kind wrapper を対称性だけで増やさなかった点は良い。

## Gap

今回、次の Gap がはっきりした。

```text id="ejas3l"
Core は W.val を見ている。
Pulse は interval-address expression を見ている。
両者を同じ座標に正規化する theorem surface が足りない。
```

これが次の攻め目標。

## 次の checkpoint 方針

次は **center-coordinate diagnostic** を作る。

名前の方向はこう。

```lean id="jj6ovx"
sourcePressureBeamPulse_witness_singleton_full_diagnostic_at_center
```

意味はこれ。

```text id="eh1xmw"
W ∈ L
  -> entry comparison at W.val - 1
  -> addressed depth target at W.val
  -> exit comparison at W.val
```

さらに seed からの存在版も狙える。

```lean id="x61di6"
exists_sourcePressureBeamPulse_witness_center_full_diagnostic_of_seed
```

これは、cp233 report が挙げた

```text id="rqgpat"
seed/depth target extraction
+
full singleton diagnostic
```

を実際に結合する一手じゃ。

## 次の Codex 指示

```text id="w2xseh"
Checkpoint: petal-234

Primary Goal:
  Stop searching for abstract callers.  Use the current snapshot to connect
  `PressureBeam.Core` depth-target vocabulary and `PressureBeam.Pulse`
  singleton diagnostic vocabulary on the same native witness depth `W.val`.

Context:
  cp232 and cp233 were no-code audits.  They showed that the Pulse API is
  broadly sufficient and that no higher caller currently needs extra symmetric
  wrappers.

  The real next target is not another caller search.

  The real target is the coordinate mismatch:

    Core speaks in native depth:
      W.val

    Pulse full diagnostics speak in interval-pulse coordinates:
      (sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1
      (sourcePressureIntervalPulseAddress_of_localIslandWitness W).start
        + (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1

  For a singleton local-island witness, these should normalize to:

    entry edge:
      W.val - 1

    center/right edge:
      W.val

Known existing Core facts to inspect:
  - sourcePressureBeamAddressedDepthTarget_of_localIslandWitness_mem
  - sourcePressureIntervalPulseAddress_of_localIslandWitness_rightEdge_eq
  - sourcePressureBeamAddressedDepthTarget_of_localIslandWitness_intervalPulse_right

Known existing Pulse fact to consume:
  - sourcePressureBeamPulse_witness_singleton_full_diagnostic

Strategic Branch Goals:

  Branch A: direct center-coordinate full diagnostic is easy
    If Lean can rewrite the singleton pulse address with existing simp facts,
    add a theorem in `PressureBeam/Pulse.lean`:

      theorem sourcePressureBeamPulse_witness_singleton_full_diagnostic_at_center
          {n : OddNat} {k r : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          {W : SourcePressureLocalIslandWitness n k r}
          (hmem : W ∈ L) :
          SourcePressureBeamMassBalanceLeftInt n k r (W.val - 1) <
            SourcePressureBeamMassBalanceRightInt n k r (W.val - 1) ∧
          SourcePressureBeamAddressedDepthTarget L W.val ∧
            SourcePressureBeamMassBalanceRightInt n k r W.val ≤
              SourcePressureBeamMassBalanceLeftInt n k r W.val

    This theorem should consume the existing full diagnostic, or the existing
    singleton mass-balance and addressed-depth facts.  Do not rebuild low-level
    edge proofs.

  Branch B: start/len helper lemmas are missing
    If the theorem in Branch A is blocked because Lean lacks simple projection
    lemmas for the witness-generated singleton address, add tiny helper lemmas
    in the smallest appropriate lower module, likely `PressureBeam/Core.lean`
    or the module that defines the conversion:

      sourcePressureIntervalPulseAddress_of_localIslandWitness_start_eq
      sourcePressureIntervalPulseAddress_of_localIslandWitness_len_eq

    Expected meanings:

      (sourcePressureIntervalPulseAddress_of_localIslandWitness W).start = W.val
      (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len = 1

    These helpers must be pure coordinate projections.  They must not mention
    Beam diagnostics, coverage, propagation, or global Collatz behavior.

    After adding helpers, retry Branch A.

  Branch C: seed-level centered full diagnostic
    If Branch A succeeds, add at most one seed-level theorem:

      theorem exists_sourcePressureBeamPulse_witness_center_full_diagnostic_of_seed
          {n : OddNat} {k r : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (hseed : SourcePressureBeamSeed L) :
          ∃ W : SourcePressureLocalIslandWitness n k r,
            W ∈ L ∧
              SourcePressureBeamMassBalanceLeftInt n k r (W.val - 1) <
                SourcePressureBeamMassBalanceRightInt n k r (W.val - 1) ∧
              SourcePressureBeamAddressedDepthTarget L W.val ∧
                SourcePressureBeamMassBalanceRightInt n k r W.val ≤
                  SourcePressureBeamMassBalanceLeftInt n k r W.val

    This is the concrete combined bridge that cp233 identified as a future
    possible need:
      seed/depth target extraction + full Pulse diagnostic.

    It should consume:
      exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_seed
      or
      exists_sourcePressureBeamSeedContainsDepth_of_seed
      plus Branch A.

    Do not choose a canonical witness.  Keep it existential.

  Branch D: failure-resolution wrapper
    Add a failure-resolution version only if it is one line and clearly useful:

      SourcePressureFailureResolution L
        -> ∃ W ∈ L, centered full diagnostic for W

    If it is merely an alias of the seed theorem and no caller needs it, do not
    add it.  Report it as optional.

  Branch E: theorem duplicates existing API too much
    If Branch A turns out to be entirely redundant because existing theorem
    statements already simplify to the centered form by `simpa`, add no large
    theorem.

    Instead add only the coordinate helper lemmas or write a report explaining
    the simplification route.

Implementation rules:
  - Use #check, #print, and scratch lemmas.
  - Inspect the actual definitions of:
      sourcePressureIntervalPulseAddress_of_localIslandWitness
      sourcePressureIntervalPulseAddress_of_localIsland
  - Do not search for more abstract callers in this checkpoint.
  - Add no more than three tiny theorems total.
  - Prefer:
      coordinate helper(s)
      one witness-level centered theorem
      one seed-level centered theorem

Guardrails:
  Do not add:
    - arbitrary target transport;
    - list-wide coverage;
    - witness-family aggregation;
    - canonical witness selection;
    - overlap repair;
    - disjointness;
    - propagation;
    - Collatz convergence;
    - right/both endpoint wrappers by symmetry.

Dependency guardrail:
  Lower coordinate helpers must not import Beam/Pulse if they belong below it.
  Beam-facing centered diagnostics belong in `PressureBeam/Pulse.lean`.

Verification:
  lake build DkMath.Collatz.PetalBridge.PressureBeam.Core
  lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge
  no-sorry grep over inspected pressure files
  git diff --check

Report requirements:
  - State which Branch was taken.
  - If helper lemmas were added, show their exact statements.
  - If the centered witness theorem was added, explain how it normalizes
    interval-pulse coordinates to `W.val`.
  - If the seed theorem was added, explain that it combines Core depth extraction
    and Pulse diagnostic extraction without canonical selection.
  - If no theorem was added, explain the exact simplification route.
  - Classify findings as True Beam / Boundary / False Beam / Gap.
  - Predict the next branch to attack.
```

## 待ち構え

次の戻りで期待するのは、これ。

```text id="qwd2dn"
Branch A + C:
  witness-level centered diagnostic
  seed-level centered diagnostic
```

これが通れば、次はようやく

```text id="ih6hkm"
seed
  -> centered diagnostic
  -> margin transition / local Big estimate
```

に入れる。

もし Branch B になったら、それも当たりじゃ。
なぜなら `start = W.val`, `len = 1` を明示補題として持つと、今後の theorem statement が一気に読みやすくなる。

## 総合判断

cp233 は採用。
しかし次は no-code audit ではない。

次の球はこれじゃ。

```text id="km6cn9"
Pulse diagnostic を W.val 座標へ正規化する。
Core depth extraction と Pulse diagnostic extraction を同じ座標で結ぶ。
```

球は見えた。
次は振る。

## Diff

`````md
````diff
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-233.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-233.md
new file mode 100644
index 00000000..49724897
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-233.md
@@ -0,0 +1,212 @@
+# report-petal-233
+
+## Checkpoint
+
+`petal-233`
+
+## Goal
+
+Move upward from the completed Pulse diagnostic API and inspect whether a
+concrete higher-level caller now needs those diagnostics.
+
+## Branch Taken
+
+Branch D was taken: current API is sufficient and no concrete higher-level
+caller exists.
+
+No Lean theorem was added in this checkpoint.
+
+## Modules Inspected
+
+Inspected caller and boundary modules:
+
+```text
+DkMath/Collatz/PetalBridge/PressureAutomaton.lean
+DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
+DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
+DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
+DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
+DkMath/Collatz/PetalBridge/PressureBeam/Core.lean
+```
+
+Also searched the wider `DkMath.Collatz.PetalBridge` tree for current uses of:
+
+```text
+SourcePressureFailureResolution
+SourcePressureBeamSeed
+exists_sourcePressureBeamPulse...
+AdjacentPairInList
+AdjacentOverlapObstruction
+PairOverlapObstruction
+```
+
+## Finding
+
+No caller currently has:
+
+```text
+SourcePressureFailureResolution L
+```
+
+and then struggles to obtain an anonymous Pulse diagnostic.  The existing
+theorem is already available:
+
+```lean
+exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_failureResolution
+```
+
+No caller currently needs branch-kind-preserving Beam diagnostics either.
+`SourcePressureFailureResolution` itself is the branch-kind classifier, and the
+recommended use remains:
+
+```text
+SourcePressureFailureResolution:
+  inspect recovered vs overlap branch
+
+PressureBeam.Pulse:
+  extract singleton Beam diagnostics after a branch or anonymous witness is
+  chosen
+```
+
+## Current Use Paths
+
+Anonymous path:
+
+```text
+SourcePressureFailureResolution L
+  -> ∃ W, W ∈ L ∧ full singleton diagnostic for W
+```
+
+Recovered pair path:
+
+```text
+AdjacentPairInList L A B
+  -> full diagnostic for A
+  -> full diagnostic for B
+```
+
+Overlap precise path:
+
+```text
+overlap obstruction
+  -> ∃ A B,
+       AdjacentPairInList L A B
+       ∧ PairOverlapObstruction A B
+       ∧ full diagnostic for A
+```
+
+Overlap anonymous path:
+
+```text
+overlap obstruction
+  -> ∃ W, W ∈ L ∧ full singleton diagnostic for W
+```
+
+Seed/depth path in `PressureBeam.Core`:
+
+```text
+SourcePressureBeamSeed L
+  -> ∃ j, SourcePressureBeamSeedContainsDepth L j
+  -> ∃ j, SourcePressureBeamDepthTarget n k r j
+```
+
+This is a depth/target path, not a Pulse diagnostic path.  It should not force
+a new theorem unless a caller needs to combine target extraction and full
+singleton diagnostic in one statement.
+
+## Branches Inspected But Not Taken
+
+Branch A:
+
+- Not taken.
+- The anonymous failure-resolution diagnostic theorem already exists.
+- No higher caller was found that would become simpler from another wrapper.
+
+Branch B:
+
+- Not taken.
+- Branch-kind preservation remains available at `SourcePressureFailureResolution`.
+- No caller currently needs a larger Beam theorem that mirrors both branches.
+
+Branch C:
+
+- Not taken.
+- No concrete caller needs overlap right endpoint or both-endpoint diagnostics.
+
+Branch E:
+
+- Not taken.
+- No missing relation was found in current callers.
+
+## Classification
+
+True Beam:
+
+- No new theorem added.
+- Existing Pulse diagnostic surfaces are sufficient for visible callers.
+
+Boundary:
+
+- `PressureAutomaton` owns branch-kind classification.
+- `PressureBeam.Core` owns seed/depth target extraction.
+- `PressureBeam.Pulse` owns singleton Beam diagnostics.
+
+False Beam:
+
+- None added.
+
+Gap:
+
+- If a future theorem needs a single bundled theorem combining seed/depth
+  target and full Pulse diagnostic, that will be a new caller-driven bridge.
+- If a future theorem needs branch-kind-preserving Beam diagnostics, it should
+  be designed from that caller, not added generically now.
+
+## Dependency Direction
+
+No dependency inversion was introduced.
+
+No Lean code changed in this checkpoint.  Lower diagnostic modules still do not
+import Beam.
+
+## Guardrails
+
+No theorem claims:
+
+- list-wide coverage;
+- witness-family aggregation;
+- arbitrary witness selection;
+- canonical target selection;
+- arbitrary target transport;
+- overlap repair;
+- disjointness;
+- propagation;
+- Collatz convergence.
+
+## Verification
+
+No Lean code changed for cp233.
+
+Workspace hygiene check:
+
+```text
+git diff --check
+```
+
+completed successfully.
+
+## Next Branch To Attack
+
+The Pulse diagnostic API can remain closed for now.
+
+The next useful work should move to a concrete upstream or downstream caller,
+most likely one of:
+
+```text
+1. target/depth transport from SourcePressureBeamSeed;
+2. a caller that combines Beam depth target and Pulse diagnostic;
+3. a branch-kind-preserving theorem only after a caller demands it.
+```
+
+Until then, avoid adding right-endpoint, both-endpoint, or branch-kind Beam
+wrappers for symmetry alone.
````
`````
