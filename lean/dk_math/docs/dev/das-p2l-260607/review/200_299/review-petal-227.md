# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam.Pulse

gch: 78d6f363926c336970e6f26fbdb3a559d4e965de

## Report

cp226 完了です。

分割後の小さな [Pulse.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean) に、明示的な `W ∈ L` から entry / center-right / exit をまとめて返す caller-facing theorem を追加しました。

```lean
sourcePressureBeamPulse_witness_singleton_full_diagnostic
```

これは既存の次の 2 本を消費して束ねるだけです。

```lean
sourcePressureBeamPulse_witness_singleton_massBalance_edges
sourcePressureBeamPulse_witness_singleton_depth_and_exit_massBalance
```

したがって、list coverage / family aggregation / canonical target selection / overlap repair / propagation / convergence は追加していません。あくまで「1 witness + 1 membership」の local diagnostic package です。

レポートも追加済みです。

- [report-petal-226.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-226.md)

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
rg no-sorry/admit over PressureBeam split files
git diff --check
```

`Pulse.lean` は 213 行です。既知の unrelated warning として `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` 警告だけ残っています。

## Review

## 結論

**採用** じゃ。
cp226 は、分割後の `PressureBeam.Pulse` に対する小さな数学作業として、ちょうどよい。

追加された theorem はこれ。

```lean id="ephlu5"
sourcePressureBeamPulse_witness_singleton_full_diagnostic
```

これは新しい大きな主張ではなく、既存の 2 本を束ねる caller-facing package じゃ。

```lean id="smk4h1"
sourcePressureBeamPulse_witness_singleton_massBalance_edges
sourcePressureBeamPulse_witness_singleton_depth_and_exit_massBalance
```

この 2 本を消費して、

```text id="kj8n9m"
entry:
  left < right

center/right:
  SourcePressureBeamAddressedDepthTarget L ...

exit:
  right <= left
```

を `W ∈ L` から一度に返す。あくまで「1 witness + 1 membership」の local diagnostic package で、coverage / aggregation / canonical selection / propagation / convergence には踏み込んでいない。

## 実装レビュー

実装は素直で良い。

```lean id="w9i8k1"
rcases sourcePressureBeamPulse_witness_singleton_massBalance_edges W with
  ⟨hentry, hexitBalance⟩
rcases sourcePressureBeamPulse_witness_singleton_depth_and_exit_massBalance hmem with
  ⟨hdepth, _⟩
exact ⟨hentry, hdepth, hexitBalance⟩
```

ここで `sourcePressureBeamPulse_witness_singleton_depth_and_exit_massBalance hmem` から得た exit balance を捨てて、`sourcePressureBeamPulse_witness_singleton_massBalance_edges W` 側の `hexitBalance` を使っている。

これは問題ない。
ただ、exit balance は両方から取れるので、証明としてはやや重複している。とはいえ theorem の目的が「既存 projection を束ねる」ことなので許容範囲じゃ。

より最小にするなら、

```lean id="ytl929"
rcases sourcePressureBeamPulse_witness_singleton_depth_and_exit_massBalance hmem with
  ⟨hdepth, hexitBalance⟩
```

を使って exit を取り、entry だけ別 theorem から取る形でもよい。
ただし現状で build が通っており、意味も明確なので差し戻す必要はない。

## 数学的意味

これで、明示的 witness に対して、局所 pulse の三点構造が一発で読める。

```text id="eww272"
W ∈ L
  -> entry true comparison
  -> center/right addressed target
  -> exit false-or-boundary comparison
```

これは downstream caller に優しい。

以前は caller が、

```text id="cbs8rr"
entry / exit mass-balance theorem
```

と、

```text id="0jl6vc"
depth / exit theorem
```

を別々に呼び、手で結合する必要があった。
今回の theorem により、明示的 witness を持っている場面では、その proof noise が減る。

## True Beam / DepthTarget / False-or-Boundary / Gap

## True Beam

entry 側。

```text id="6rmb5o"
left < right
```

これは singleton pulse の入口で True Beam 比較を返す。

## DepthTarget

center/right 側。

```text id="1b635c"
SourcePressureBeamAddressedDepthTarget L ...
```

ここだけ `W ∈ L` が必要。
list-relative carrier だからじゃ。

## False-or-Boundary

exit 側。

```text id="9kxbxd"
right <= left
```

non-strict なので、境界 `right = left` と strict false `right < left` の両方を含む。

## Gap

残る Gap はこれまで通り。

```text id="xquupi"
list-wide coverage
family aggregation
canonical target selection
overlap repair
propagation
Collatz convergence
```

今回の theorem は、explicit membership の一点だけを扱う。
この限定が守られているのは良い。

## 評価

cp225 の分割が効いている。
`Pulse.lean` は 213 行で、まだかなり小さい。

分割前なら、この小さな theorem でも 1900 行級の巨大ファイル末尾に積むことになった。
今は `Pulse.lean` に閉じているので、レビューしやすく、Codex の対象も小さい。

これはよい流れじゃ。

## 次の checkpoint 方針

次は、無理に `Pulse` に theorem を足し続けるより、**実際にこの full diagnostic をどこで使うか**を見る段階じゃ。

候補は上位の automaton / failure resolution 側。

ただし、下流モジュールに Beam を逆 import させてはいけない。
やるなら `PressureBeam.Pulse` より上、または新しい上位 bridge 層が安全。

## 次の Codex 指示

```text id="ki4gpr"
Checkpoint: petal-227

Goal:
  Investigate whether the new Pulse-level full diagnostic theorem has an
  immediate higher-level caller, without forcing new API.

Primary files to inspect:
  DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
  DkMath/Collatz/PetalBridge/PressureBeam.lean
  DkMath/Collatz/PetalBridge/PressureAutomaton.lean

Secondary files, inspect only as needed:
  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean

Context:
  cp226 added:

    sourcePressureBeamPulse_witness_singleton_full_diagnostic

  From one explicit witness membership:

    W ∈ L

  it packages:

    entry:
      left < right

    center/right:
      SourcePressureBeamAddressedDepthTarget L ...

    exit:
      right <= left

  This remains local to one witness and one list membership.

Main question:
  Is there already a higher-level Beam / Automaton theorem where this bundled
  entry-depth-exit diagnostic reduces proof noise?

Codex should use workspace judgment:
  - inspect whether an existing theorem manually combines entry / addressed
    depth / exit facts;
  - inspect whether SourcePressureBeamSeed or failure-resolution witnesses can
    expose an explicit W ∈ L;
  - use #check, #print, and scratch lemmas;
  - decide whether a small theorem should be added or whether this is
    report-only.

Allowed outcomes:
  1. Add one small higher-level theorem that consumes
       sourcePressureBeamPulse_witness_singleton_full_diagnostic
     for an explicit witness membership.
  2. Add no Lean code and report that no caller currently needs it.
  3. If the real missing relation is explicit witness membership from a seed or
     failure resolution, report that exact Gap.

Guardrails:
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
  Keep dependency direction clean.  If a caller bridge is needed, place it in
  PressureBeam/Pulse.lean or a higher Beam-facing module.

Verification if code changes:
  lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge
  no-sorry grep over PressureBeam split files
  git diff --check

Report requirements:
  - Explain what Codex inspected.
  - State whether a higher-level consumer theorem was added or skipped.
  - If added, say exactly how it consumes the full diagnostic.
  - If skipped, identify the missing caller or missing relation.
  - Confirm no dependency inversion was introduced.
  - Make clear this is local explicit-witness API consumption, not coverage or
    aggregation.
```

## 一歩先ゆく推論

いまの `Pulse` はかなり caller-friendly になった。

```text id="ycgo2o"
one witness + membership
  -> full local pulse diagnostic
```

次に見るべきは、

```text id="35va6n"
seed / failure resolution から explicit W ∈ L が取れるか
```

じゃ。

もし取れるなら、Beam seed から local pulse diagnostic を得る道が開く。
ただし、これは **存在する witness を一つ取り出す** 話であって、list 全体の coverage ではない。そこを守れば安全に進める。

## 総合判断

cp226 は成功。
分割後の `Pulse.lean` で、小さく、明確で、使いやすい theorem が追加された。

次は「この theorem の caller はどこか」を探す段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
index f0bc855d..e0ae68db 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
@@ -171,5 +171,43 @@ theorem sourcePressureBeamPulse_witness_singleton_depth_and_exit_massBalance
     ⟨hdepth,
       sourcePressureBeamMassBalanceRight_le_left_of_fallingEdgeTarget hexit⟩

+/--
+Caller-facing full diagnostic for one explicitly contained witness singleton.
+
+This is only a convenience package for one witness `W` with `W ∈ L`.  It
+combines the existing singleton edge comparisons with the list-relative
+addressed-depth fact:
+
+* entry edge: True Beam comparison `left < right`;
+* center/right edge: `SourcePressureBeamAddressedDepthTarget L ...`;
+* exit edge: False/Boundary comparison `right <= left`.
+
+No list coverage, witness-family aggregation, canonical target selection,
+overlap repair, propagation, or convergence is claimed.
+-/
+theorem sourcePressureBeamPulse_witness_singleton_full_diagnostic
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W : SourcePressureLocalIslandWitness n k r}
+    (hmem : W ∈ L) :
+    SourcePressureBeamMassBalanceLeftInt n k r
+        ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) <
+      SourcePressureBeamMassBalanceRightInt n k r
+        ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) ∧
+      SourcePressureBeamAddressedDepthTarget L
+        ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
+          (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) ∧
+        SourcePressureBeamMassBalanceRightInt n k r
+          ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
+            (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) ≤
+          SourcePressureBeamMassBalanceLeftInt n k r
+            ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
+              (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) := by
+  rcases sourcePressureBeamPulse_witness_singleton_massBalance_edges W with
+    ⟨hentry, hexitBalance⟩
+  rcases sourcePressureBeamPulse_witness_singleton_depth_and_exit_massBalance hmem with
+    ⟨hdepth, _⟩
+  exact ⟨hentry, hdepth, hexitBalance⟩
+

 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-226.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-226.md
new file mode 100644
index 00000000..ecb817ab
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-226.md
@@ -0,0 +1,118 @@
+# Report: petal-226
+
+## Checkpoint
+
+`petal-226` resumed mathematical work after the mechanical split and targeted
+`DkMath.Collatz.PetalBridge.PressureBeam.Pulse`.
+
+The goal was to decide whether an explicitly contained witness can expose a
+single caller-facing local diagnostic package.
+
+## Implemented Theorem
+
+Added in `PressureBeam/Pulse.lean`:
+
+```lean
+sourcePressureBeamPulse_witness_singleton_full_diagnostic
+```
+
+The theorem starts from one explicit list membership:
+
+```lean
+W ∈ L
+```
+
+and packages the three local facts:
+
+```text
+entry:
+  left < right
+
+center/right:
+  SourcePressureBeamAddressedDepthTarget L ...
+
+exit:
+  right <= left
+```
+
+This remains one witness / one explicit list membership.  It does not claim
+coverage of a list, family aggregation, canonical target selection, overlap
+repair, propagation, or convergence.
+
+## Existing API Consumed
+
+The new theorem consumes existing `Pulse` API:
+
+```lean
+sourcePressureBeamPulse_witness_singleton_massBalance_edges
+sourcePressureBeamPulse_witness_singleton_depth_and_exit_massBalance
+```
+
+The proof deliberately avoids rebuilding the edge facts directly.  It only
+bundles the caller-facing pieces already proved by the smaller projections.
+
+## Why Add It?
+
+The existing API was mathematically sufficient, but a downstream caller would
+otherwise need to call two separate theorems and manually combine:
+
+- entry mass-balance;
+- addressed depth;
+- exit mass-balance.
+
+The new theorem reduces that proof noise while preserving the local-only
+contract.
+
+## cp225 Compatibility
+
+No public names from cp225 were renamed or removed.
+
+The post-split module layout remains:
+
+```text
+PressureBeam.Core
+  -> PressureBeam.Edge
+  -> PressureBeam.Pulse
+  -> PressureBeam
+```
+
+## Line Counts
+
+Touched file:
+
+```text
+213  DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
+```
+
+The small `Pulse` file remains well below the refactor threshold.
+
+## Verification
+
+Completed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
+lake build DkMath.Collatz.PetalBridge.PressureBeam
+lake build DkMath.Collatz.PetalBridge
+rg -n "\bsorry\b|admit" over PressureBeam split files
+git diff --check
+```
+
+The inspected pressure files have no new `sorry` / `admit` matches.
+
+Known unrelated project warning remains:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses 'sorry'
+```
+
+## Next Inference
+
+The Pulse-level witness singleton diagnostic is now caller-friendly.  The next
+safe step is to use it from a higher diagnostic/automaton layer only when a
+concrete caller needs the bundled entry-depth-exit shape.
+
+Avoid turning this into list-wide coverage or witness-family aggregation until
+exact list membership, non-overlap, and coverage hypotheses are explicitly
+available.
````
`````
