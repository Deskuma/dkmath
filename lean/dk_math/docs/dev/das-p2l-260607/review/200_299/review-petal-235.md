# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam.Pulse, Core

gch: 6bd74e4fe52863b60a2e721b47bffb1d5e2f7b01

## Report

cp234 実装完了です。

追加したのは3本です。

- `sourcePressureIntervalPulseAddress_of_localIslandWitness_start_eq`
- `sourcePressureBeamPulse_witness_singleton_full_diagnostic_at_center`
- `exists_sourcePressureBeamPulse_witness_center_full_diagnostic_of_seed`

これで singleton witness の interval-pulse 座標を `W.val` 中心の native depth 表現に正規化して読めます。既存の edge/mass-balance 証明は作り直さず、既存 diagnostic を座標補題で薄く投影しています。

検証も通過しました。

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam.Core
lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
git diff --check
```

対象 pressure 範囲の `sorry/admit` grep も該当なしです。レポートは `lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-234.md` に作成しました。

## Review

## 結論

**採用。これは当たった。**
cp234 は、前回狙った球をきちんと捉えている。

追加された 3 本は、まさに狙い通りじゃ。

```lean id="luzbki"
sourcePressureIntervalPulseAddress_of_localIslandWitness_start_eq
```

```lean id="sxpo4r"
sourcePressureBeamPulse_witness_singleton_full_diagnostic_at_center
```

```lean id="w1znf5"
exists_sourcePressureBeamPulse_witness_center_full_diagnostic_of_seed
```

これで、singleton witness の Pulse 診断を interval-pulse 座標ではなく、native witness depth `W.val` で読めるようになった。前回の「Core は `W.val`、Pulse は interval address」という座標ズレを、きれいに閉じている。

## 実装レビュー

今回の Branch は、予定通りに進んでいる。

```text id="pglfmm"
Branch B:
  start = W.val の coordinate helper

Branch A:
  W ∈ L -> centered full diagnostic

Branch C:
  SourcePressureBeamSeed L -> ∃ W ∈ L, centered full diagnostic
```

`start_eq` は下層 `Core.lean` に置かれており、Beam diagnostic を含まない純粋な座標補題になっている。これは配置が正しい。

中心 theorem は、既存の interval-coordinate full diagnostic を開いて、

```lean id="p8brr4"
sourcePressureIntervalPulseAddress_of_localIslandWitness_start_eq
sourcePressureIntervalPulseAddress_of_localIslandWitness_rightEdge_eq
```

で書き換えるだけ。
edge / mass-balance の低層証明を作り直していない。これも良い。

seed 版も、

```lean id="rveqxs"
exists_sourcePressureBeamSeedContainsDepth_of_seed
```

で witness を取り出し、centered diagnostic に渡しているだけ。canonical witness は選んでいない。

## 数学的意味

今回、ようやくこの形が native depth で読めるようになった。

```text id="9xfdq9"
entry:
  W.val - 1 で left < right

center/right:
  W.val で SourcePressureBeamAddressedDepthTarget L W.val

exit:
  W.val で right <= left
```

これは大きい。
今までは同じ内容が、

```text id="c0g5n8"
(sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1
(sourcePressureIntervalPulseAddress_of_localIslandWitness W).start
  + (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1
```

という長い座標で出ていた。
数学的には同じでも、次の推論ではこれが邪魔になる。

今回の定理で、

```text id="m5s43j"
local pulse = W.val - 1 から W.val への crossing/falling
```

として読める。
つまり、局所 pulse が native depth 上の 1-step pressure event として見えるようになった。

## True Beam / Boundary / False Beam / Gap

## True Beam

entry edge が明確になった。

```text id="pxe5ep"
W.val - 1:
  left < right
```

これは True Beam 側。
圧力が正側へ入る入口じゃ。

## Boundary / False Beam

center/right edge も明確になった。

```text id="yztw43"
W.val:
  right <= left
```

これは boundary または falling 側。
`=` なら境界、`<` なら strict falling。

## Core

`SourcePressureBeamAddressedDepthTarget L W.val` が、同じ theorem の中に入った。
これが今回の最大の命中点じゃ。

```text id="c3n9ma"
Core depth target
+
Pulse mass-balance diagnostic
```

が同じ `W.val` 座標にそろった。

## Gap

まだ言っていないことは明確。

```text id="jrjzxf"
list-wide coverage はない
propagation はない
local Big 上界はまだない
Collatz convergence はない
```

今回閉じたのは、あくまで座標正規化と seed-level centered diagnostic じゃ。

## 戦略評価

これは、前回の「空振り後の狙い直し」が成功している。

cp232 / cp233 は caller 監査で no-code だった。
それ自体は悪くないが、攻撃としては浅かった。

今回はこちらで snapshot から、

```text id="q1kssi"
Core と Pulse の座標系がズレている
```

と見抜き、そこを刺した。

Codex もその通りに、

```text id="1f25bw"
start = W.val
right edge = W.val
```

を使って、centered diagnostic を作った。
これは良い連携じゃ。

## 注意点

report の Next Branch では、centered versions を adjacent-pair / overlap wrappers にも作るかが候補として挙がっている。

ただし、ここで機械的に centered wrapper を増やすのは危険じゃ。
今は wrapper API を太らせるより、**centered seed theorem を使って次の数学へ進む**べき。

次の主戦場はこれ。

```text id="cmdr42"
centered diagnostic
  -> margin sign
  -> local pulse height / local Big estimate
```

つまり、今度こそ local Big へ踏み込む。

## 次の checkpoint 方針

次は、centered mass-balance inequalities を **margin sign / transition** に戻す。

いま得たものは、

```text id="he4b7m"
W.val - 1:
  left < right

W.val:
  right <= left
```

既存には、mass-balance と next margin をつなぐ定理群があるはずじゃ。

狙いは、

```text id="e57azc"
seed
  -> ∃ W ∈ L,
       next margin at W.val - 1 is positive
       and next margin at W.val is nonpositive
```

または native に読むなら、

```text id="idyc2f"
entry:
  M(W.val) > 0

exit:
  M(W.val + 1) <= 0
```

のような shape じゃ。
正確な index は既存定理に合わせて Codex に確認させる。

ここで local pulse が「質量比較」から「margin sign event」へ戻る。
その次に、height / width / Big estimate へ進める。

## 次の Codex 指示

```text id="pkhmep"
Checkpoint: petal-235

Primary Goal:
  Use the new centered seed diagnostic from cp234 to move from centered
  mass-balance comparisons to centered margin-sign / transition facts.

Context:
  cp234 added:

    sourcePressureIntervalPulseAddress_of_localIslandWitness_start_eq

    sourcePressureBeamPulse_witness_singleton_full_diagnostic_at_center

    exists_sourcePressureBeamPulse_witness_center_full_diagnostic_of_seed

  The seed theorem now gives:

    ∃ W ∈ L,
      MassBalanceLeft (W.val - 1) < MassBalanceRight (W.val - 1)
      ∧ SourcePressureBeamAddressedDepthTarget L W.val
      ∧ MassBalanceRight W.val ≤ MassBalanceLeft W.val

  This is the first clean native-depth surface:
    entry edge  = W.val - 1
    center/exit = W.val

Strategic Branch Goals:

  Branch A: convert centered mass-balance to margin signs
    Inspect existing mass-balance/sign theorems in `PressureBeam/Core.lean`
    and `PressureBeam/Pulse.lean`.

    Look especially for theorems relating:
      SourcePressureBeamMassBalanceLeftInt < RightInt
      SourcePressureBeamMassBalanceRightInt ≤ LeftInt
    to:
      SourcePressureMarginInt ... > 0
      SourcePressureMarginInt ... ≤ 0
      next margin positivity/nonpositivity

    If direct theorems exist, add a thin centered theorem:

      theorem exists_sourcePressureBeamPulse_witness_center_margin_signs_of_seed
          {n : OddNat} {k r : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (hseed : SourcePressureBeamSeed L) :
          ∃ W : SourcePressureLocalIslandWitness n k r,
            W ∈ L ∧
              <entry margin sign at W.val - 1 or W.val> ∧
              SourcePressureBeamAddressedDepthTarget L W.val ∧
              <exit margin sign at W.val or W.val + 1>

    Codex must discover the exact index convention from existing theorems.
    Do not guess whether the sign belongs to `j`, `j+1`, or `r+j+1`.

  Branch B: only one side converts directly
    If entry converts but exit does not, or exit converts but entry does not,
    add only the directly supported one-sided theorem if useful.

    Otherwise report the missing sign bridge.

  Branch C: existing sign theorems require CrossingEdgeTarget/FallingEdgeTarget
    If mass-balance-to-sign conversion is mediated by:

      SourcePressureBeamCrossingEdgeTarget
      SourcePressureBeamFallingEdgeTarget

    then inspect whether the centered witness theorem can expose those targets
    at:
      W.val - 1
      W.val

    Add a theorem only if it is a thin wrapper over existing edge-target API.

  Branch D: centered mass-balance is already sufficient
    If converting to margin signs would duplicate existing API or produce an
    unclear theorem statement, add no Lean code.

    Report the exact existing theorem chain a caller should use.

  Branch E: local Big estimate is immediately available
    If existing API already has upper bounds for:
      SourcePressureMarginInt
      SourcePressureNetDropInt
      retention mass
      continuation mass

    and the centered diagnostic can feed them directly, do not prove a large
    theorem.  Report the exact next theorem shape for a later checkpoint.

Implementation rules:
  - Use #check, #print, and scratch lemmas.
  - Inspect exact definitions of:
      SourcePressureMarginInt
      SourcePressureBeamMassBalanceLeftInt
      SourcePressureBeamMassBalanceRightInt
      sourcePressureMargin_next_eq_massBalanceRight_sub_left
      sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right
      sourcePressureMargin_next_nonpos_iff_massBalanceRight_le_left
      any edge-target sign theorem
  - Do not add centered adjacent-pair / overlap wrappers in this checkpoint.
  - Add no more than one new theorem unless a tiny helper is strictly necessary.
  - Prefer native-depth theorem statements.

Guardrails:
  Do not add:
    - arbitrary target transport;
    - list-wide coverage;
    - witness-family aggregation;
    - canonical witness selection;
    - overlap repair;
    - disjointness;
    - propagation;
    - local Big upper bound unless already directly supported;
    - Collatz convergence.

Dependency guardrail:
  Keep lower modules free of Beam/Pulse imports.
  Beam-facing sign wrappers belong in `PressureBeam/Pulse.lean` or another
  Beam-facing module.

Verification:
  lake build DkMath.Collatz.PetalBridge.PressureBeam.Core
  lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge
  no-sorry grep over inspected pressure files
  git diff --check

Report requirements:
  - State which Branch was taken.
  - State the exact margin index convention discovered.
  - If theorem added, show how it consumes cp234 centered diagnostic.
  - If no theorem added, show the exact existing theorem chain.
  - Classify findings as True Beam / Boundary / False Beam / Gap.
  - Predict whether the next branch should attack local Big bounds or more
    sign normalization.
```

## 待ち構え

次の返りは、このどれかじゃ。

```text id="qrdabj"
A:
  centered diagnostic -> centered margin signs が通る
```

この場合、次は local Big estimate へ行く。

```text id="e3y73a"
B:
  index convention が複雑で、直接 theorem が大きくなる
```

この場合は sign theorem chain を report に固定して、次に薄い helper を設計する。

```text id="xlmqql"
C:
  CrossingEdgeTarget / FallingEdgeTarget 経由が正道
```

この場合、edge target の centered API を作る。

## 総合判断

cp234 は成功。
前回の狙いは当たった。

次は、centered diagnostic をさらに一段進めて、

```text id="e81y8e"
mass-balance comparison
  -> margin sign / transition
```

へ戻す。

その先に、ようやく局所 Big の上界が見えてくる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Core.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Core.lean
index 3e1d5db3..10334ec3 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Core.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Core.lean
@@ -1333,6 +1333,21 @@ theorem sourcePressureBeamAddressedDepthTarget_of_localIslandWitness_mem
     sourcePressureBeamAddressedDepthTarget_mk hcontains
       (sourcePressureBeamDepthTarget_of_seedContainsDepth hcontains)

+/--
+The singleton interval-pulse address generated by a local-island witness starts
+at the witness center.
+
+This is a pure coordinate projection.  It exists so Beam-facing pulse
+diagnostics can be rewritten from interval-pulse coordinates back to the native
+witness depth `W.val` without rebuilding any edge or mass-balance proof.
+-/
+theorem sourcePressureIntervalPulseAddress_of_localIslandWitness_start_eq
+    {n : OddNat} {k r : ℕ}
+    (W : SourcePressureLocalIslandWitness n k r) :
+    (sourcePressureIntervalPulseAddress_of_localIslandWitness W).start = W.val := by
+  simp [sourcePressureIntervalPulseAddress_of_localIslandWitness,
+    sourcePressureIntervalPulseAddress_of_localIsland]
+
 /--
 The singleton interval-pulse address generated by a local-island witness has
 right edge equal to the witness center.
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
index 2e9ebeee..ed40e1d1 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
@@ -209,6 +209,41 @@ theorem sourcePressureBeamPulse_witness_singleton_full_diagnostic
     ⟨hdepth, _⟩
   exact ⟨hentry, hdepth, hexitBalance⟩

+/--
+Centered full diagnostic for one explicitly contained witness singleton.
+
+This is the cp234 native-depth surface over the interval-pulse diagnostic
+above.  A witness-generated pulse is a singleton address:
+
+* its entry edge is `W.val - 1`;
+* its center/right edge is `W.val`.
+
+The proof only normalizes coordinates using the Core alignment lemmas.  It
+does not rebuild low-level edge proofs, transport diagnostics to arbitrary
+targets, select a canonical witness, or claim coverage beyond the supplied
+membership `W ∈ L`.
+-/
+theorem sourcePressureBeamPulse_witness_singleton_full_diagnostic_at_center
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W : SourcePressureLocalIslandWitness n k r}
+    (hmem : W ∈ L) :
+    SourcePressureBeamMassBalanceLeftInt n k r (W.val - 1) <
+      SourcePressureBeamMassBalanceRightInt n k r (W.val - 1) ∧
+      SourcePressureBeamAddressedDepthTarget L W.val ∧
+        SourcePressureBeamMassBalanceRightInt n k r W.val ≤
+          SourcePressureBeamMassBalanceLeftInt n k r W.val := by
+  rcases sourcePressureBeamPulse_witness_singleton_full_diagnostic hmem with
+    ⟨hentry, hdepth, hexit⟩
+  have hstart :=
+    sourcePressureIntervalPulseAddress_of_localIslandWitness_start_eq W
+  have hright :=
+    sourcePressureIntervalPulseAddress_of_localIslandWitness_rightEdge_eq W
+  exact
+    ⟨by simpa [hstart] using hentry,
+      by simpa [hright] using hdepth,
+      by simpa [hright] using hexit⟩
+
 /--
 A Beam seed exposes one witness whose singleton pulse has the full local
 entry-depth-exit diagnostic.
@@ -247,6 +282,33 @@ theorem exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_seed
     ⟨W, hmem,
       sourcePressureBeamPulse_witness_singleton_full_diagnostic hmem⟩

+/--
+A Beam seed exposes one witness whose singleton pulse has the centered full
+local diagnostic at native depth `W.val`.
+
+This is the cp234 seed bridge.  It combines the existing seed witness
+extraction with the centered singleton diagnostic above.  The witness remains
+existential: the theorem does not choose a canonical witness, cover the list,
+aggregate witnesses, repair overlap, propagate diagnostics, or assert Collatz
+convergence.
+-/
+theorem exists_sourcePressureBeamPulse_witness_center_full_diagnostic_of_seed
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hseed : SourcePressureBeamSeed L) :
+    ∃ W : SourcePressureLocalIslandWitness n k r,
+      W ∈ L ∧
+        SourcePressureBeamMassBalanceLeftInt n k r (W.val - 1) <
+          SourcePressureBeamMassBalanceRightInt n k r (W.val - 1) ∧
+          SourcePressureBeamAddressedDepthTarget L W.val ∧
+            SourcePressureBeamMassBalanceRightInt n k r W.val ≤
+              SourcePressureBeamMassBalanceLeftInt n k r W.val := by
+  rcases exists_sourcePressureBeamSeedContainsDepth_of_seed hseed with
+    ⟨_, W, hmem, _⟩
+  exact
+    ⟨W, hmem,
+      sourcePressureBeamPulse_witness_singleton_full_diagnostic_at_center hmem⟩
+
 /--
 Failure resolution also exposes one witness whose singleton pulse has the full
 local entry-depth-exit diagnostic.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-234.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-234.md
new file mode 100644
index 00000000..db252b85
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-234.md
@@ -0,0 +1,117 @@
+# report-petal-234
+
+## Checkpoint
+
+`petal-234`
+
+## Result
+
+Implemented Branch B + Branch A + Branch C in the requested three-theorem
+limit.
+
+The checkpoint target was the coordinate mismatch between:
+
+- Core depth-target vocabulary at native witness depth `W.val`;
+- Pulse singleton diagnostics stated in interval-pulse coordinates.
+
+For a witness-generated singleton pulse, the interval address has
+`start = W.val` and right edge `start + len - 1 = W.val`.  The right-edge
+alignment already existed, so this checkpoint only added the missing `start`
+projection and then exposed centered Pulse diagnostics.
+
+## Added Theorems
+
+### Branch B: coordinate helper
+
+```lean
+theorem sourcePressureIntervalPulseAddress_of_localIslandWitness_start_eq
+    {n : OddNat} {k r : ℕ}
+    (W : SourcePressureLocalIslandWitness n k r) :
+    (sourcePressureIntervalPulseAddress_of_localIslandWitness W).start = W.val
+```
+
+This is a pure coordinate projection.  It does not mention Beam diagnostics,
+coverage, propagation, or global Collatz behavior.
+
+### Branch A: witness centered diagnostic
+
+```lean
+theorem sourcePressureBeamPulse_witness_singleton_full_diagnostic_at_center
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W : SourcePressureLocalIslandWitness n k r}
+    (hmem : W ∈ L) :
+    SourcePressureBeamMassBalanceLeftInt n k r (W.val - 1) <
+      SourcePressureBeamMassBalanceRightInt n k r (W.val - 1) ∧
+      SourcePressureBeamAddressedDepthTarget L W.val ∧
+        SourcePressureBeamMassBalanceRightInt n k r W.val ≤
+          SourcePressureBeamMassBalanceLeftInt n k r W.val
+```
+
+This consumes the existing interval-coordinate full diagnostic and rewrites:
+
+- entry edge by `sourcePressureIntervalPulseAddress_of_localIslandWitness_start_eq`;
+- center/right edge by `sourcePressureIntervalPulseAddress_of_localIslandWitness_rightEdge_eq`.
+
+No low-level edge proof was rebuilt.
+
+### Branch C: seed centered diagnostic
+
+```lean
+theorem exists_sourcePressureBeamPulse_witness_center_full_diagnostic_of_seed
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hseed : SourcePressureBeamSeed L) :
+    ∃ W : SourcePressureLocalIslandWitness n k r,
+      W ∈ L ∧
+        SourcePressureBeamMassBalanceLeftInt n k r (W.val - 1) <
+          SourcePressureBeamMassBalanceRightInt n k r (W.val - 1) ∧
+          SourcePressureBeamAddressedDepthTarget L W.val ∧
+            SourcePressureBeamMassBalanceRightInt n k r W.val ≤
+              SourcePressureBeamMassBalanceLeftInt n k r W.val
+```
+
+This combines seed witness extraction with the centered singleton diagnostic.
+The witness remains existential.  No canonical witness, coverage, aggregation,
+overlap repair, propagation, or convergence is claimed.
+
+## Beam Classification
+
+- True Beam: the entry edge `W.val - 1` has `left < right`.
+- Boundary / False Beam: the center/right edge `W.val` has `right <= left`.
+- Core: `SourcePressureBeamAddressedDepthTarget L W.val` is now visible in the
+  same centered theorem as the Beam comparisons.
+- Gap: no list-wide coverage or propagation theorem is added.  This checkpoint
+  only fixes local coordinate readability.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureBeam.Core
+lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
+lake build DkMath.Collatz.PetalBridge.PressureBeam
+lake build DkMath.Collatz.PetalBridge
+git diff --check
+```
+
+No `sorry` or `admit` was found in the requested pressure-file grep scope.
+
+Known unrelated warning still appears during builds:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+## Next Branch
+
+The next useful branch is to decide whether centered versions are needed for
+existing adjacent-pair / overlap wrappers.
+
+Do not add them automatically unless caller noise appears.  The current
+centered seed theorem is the clean public surface for seed-level use.  If a
+future caller remains at the adjacent-overlap layer and repeatedly rewrites
+interval coordinates, add a pair-preserving centered wrapper for that caller
+only.
````
`````
