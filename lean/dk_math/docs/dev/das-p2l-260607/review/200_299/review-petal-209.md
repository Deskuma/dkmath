# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam

gch: 362a899d84426b81fe279d0fab01adad0082c73a

## Report

cp208 完了です。

[PressureBeam.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean) に、Beam-facing な margin transition wrapper を追加しました。

追加 theorem:

- `sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget`
- `exists_sourcePressureMargin_transition_of_beamSeed`

`PressureDecay` 側の実際の式は `r + j + 1` 形だったので、その形をそのまま使っています。これは局所 transition equation の読み替えで、time/orbit propagation ではありません。

レポート:
[report-petal-208.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-208.md)

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureBeam` passed
- `lake build DkMath.Collatz.PetalBridge` passed
- 指定 pressure files の `sorry/admit` check: no matches
- `git diff --check` passed

補足として、transition equation 自体は `PressureDecay` のグローバルな局所代数恒等式なので、任意 `j` でも成り立ちます。ただし seed が任意 `j` を addressed target として選ぶわけではない、という Gap は残しています。

## Review

## 結論

**採用** じゃ。
cp208 はかなり良い。

今回、Beam はついに

```text
Seed
  -> exists addressed target
  -> exists positive margin
  -> local margin transition equation
```

まで到達した。

追加された theorem は次の 2 本。

```lean
sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget

exists_sourcePressureMargin_transition_of_beamSeed
```

これは **time/orbit propagation ではなく、既存 `PressureDecay` の局所代数恒等式を Beam-facing に読んだもの** じゃ。report でも、実際の式形が `r + j + 1` であることを確認し、その形を無理に `r + (j + 1)` へ書き換えずに採用している。これは正しい。

## 実装レビュー

実装は安全じゃ。

```lean
theorem sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (_h : SourcePressureBeamAddressedDepthTarget L j) :
    SourcePressureMarginInt n k (r + j + 1) =
      SourcePressureMarginInt n k (r + j) +
        SourcePressureNetDropInt n k r j :=
  sourcePressureMargin_next_eq_current_add_netDrop n k r j
```

ここで `_h` が未使用なのは悪くない。
むしろ意味がある。

代数恒等式そのものは任意 `j` で成り立つ。
だが Beam API としては、**その `j` が witness list に address された depth である**という文脈を持たせたい。だから `_h` は「証明に必要な仮定」ではなく、「この式を Beam-selected depth として読むためのタグ」じゃ。

次の existential wrapper も良い。

```lean
theorem exists_sourcePressureMargin_transition_of_beamSeed
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hseed : SourcePressureBeamSeed L) :
    ∃ j,
      SourcePressureBeamAddressedDepthTarget L j ∧
        SourcePressureMarginInt n k (r + j + 1) =
          SourcePressureMarginInt n k (r + j) +
            SourcePressureNetDropInt n k r j
```

これは、

```text
seed が選ぶ存在的 addressed depth において、
margin transition equation が読める
```

という形に閉じている。
任意外部 `j` への seed-address claim はしていない。

## 数学的意味

今回で Beam は「点」から「局所線分」へ進み始めた。

cp207 までは、

```text
BeamSeed
  -> ∃ j, margin_pos at r+j
```

だった。

cp208 で、

```text
BeamSeed
  -> ∃ j, margin_next(j) = margin_current(j) + netDrop(j)
```

が得られた。

より正確には、同じ `j` について

```text
AddressedDepthTarget L j
  and
SourcePressureMarginInt n k (r + j + 1)
  =
SourcePressureMarginInt n k (r + j)
  +
SourcePressureNetDropInt n k r j
```

が取れる。

これはまだ propagation ではない。
しかし、**Beam-selected point に隣接差分の式が刺さった**。
ここから初めて、True / False Beams が符号で割れる。

## True Beam / False Beam / Gap

## True Beam

今回の True Beam はこれ。

```text
AddressedDepthTarget at j
  -> local margin transition equation at j
```

```text
BeamSeed
  -> exists addressed j with local margin transition equation
```

これは強い。
なぜなら、Beam seed が持つ正圧点に対して、次点との差分 `netDrop` を読めるようになったからじゃ。

## False Beam

新しい negated theorem はなし。
ここはまだ無理に作らなくてよい。

## Gap

今回 report が整理している通り、注意すべき Gap は少し精密化された。

遷移式そのものは `PressureDecay` のグローバル局所代数恒等式なので、任意 `j` で成り立つ。
だから、

```text
transition equation at arbitrary j
```

は偽ではない。

本当の Gap はこれじゃ。

```text
SourcePressureBeamSeed L
  -> SourcePressureBeamAddressedDepthTarget L j
```

任意外部 `j` が seed に address されるわけではない。
seed が選べるのは、存在的に抽出された `j` だけじゃ。

## 注意点

今回も境界は守られている。

```text
time/orbit propagation ではない。
```

```text
arbitrary target transport ではない。
```

```text
arbitrary margin positivity ではない。
```

```text
canonical target selection ではない。
```

```text
coverage / aggregation / overlap repair ではない。
```

```text
Collatz convergence ではない。
```

これは **local transition reading** じゃ。

## 次の checkpoint 方針

次は、report の一歩先推論どおり、**sign reading** に入るのがよい。

今ある Core はこれ。

```text
AddressedDepthTarget
  -> margin_pos at j

AddressedDepthTarget
  -> margin_next(j) = margin_current(j) + netDrop(j)
```

次に Lean に聞くべきは、

```text
netDrop が十分なら next margin remains positive
```

と、

```text
netDrop が十分に負なら next margin becomes nonpositive
```

の二方向じゃ。

ここで DkMath の Beam x2 が初めて本格的に出る。

```text
True Beam:
  next margin が正に残る条件

False Beam:
  next margin が非正へ落ちる条件
```

ただし、まだ大域伝播ではない。
局所の `j -> j+1` 符号読みだけじゃ。

## 次の Codex 指示

```text
Checkpoint: petal-209

Main goal:
  Start the sign-reading layer for the Beam-facing local margin transition.
  Ask Lean for small True/False Beam facts around:
    current margin > 0
    next margin = current margin + netDrop
    next margin > 0 or next margin <= 0
  Do not prove time/orbit propagation, coverage, aggregation, or convergence.

Primary target file:
  DkMath/Collatz/PetalBridge/PressureBeam.lean

Allowed supporting files:
  docs/dev/das-p2l-260607/review/report-petal-209.md

Do not modify:
  DkMath/Collatz/PetalBridge/PressureDecay.lean
  DkMath/Collatz/PetalBridge/PressureFrontier.lean
  DkMath/Collatz/PetalBridge/PressureAccounting.lean
  DkMath/Collatz/PetalBridge/PressureAutomaton.lean
  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
  Any non-Collatz files

DkMath philosophy:
  Beams means Beam x2.

  Core:
    facts accepted by Lean.

  True Beam:
    facts Lean proves from the current Core.

  False Beam:
    negated facts, obstruction facts, or explicit rejected overclaims.

  Gap:
    under-specified statements where a relation is missing.

  The goal is to grow Core by fixing both True and False observations.
  Do not merely inspect code.  Ask Lean small questions.

Current Core:
  SourcePressureBeamSeed
  SourcePressureBeamAddressedDepthTarget
  exists_sourcePressureBeamAddressedDepthTarget_of_seed
  sourcePressureMargin_pos_of_addressedDepthTarget
  sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget
  exists_sourcePressureMargin_transition_of_beamSeed

Known Gap:
  SourcePressureBeamSeed L -> SourcePressureBeamAddressedDepthTarget L j
  for arbitrary external `j`.

Required Lean exploration:

  Step 1:
    Use `#check` or scratch wrappers to inspect whether existing integer-order
    lemmas are already available for:
      a > 0
      a + b > 0
      a + b <= 0
      b >= 0
      b <= -a
    over `Int`.

    Do not guess exact lemma names.  Use Lean.

  Experiment T1:
    Prove a local True Beam sign-preservation condition from an addressed
    target.

    Candidate theorem shape:

      theorem sourcePressureMargin_next_pos_of_addressedDepthTarget_of_netDrop_nonneg
          {n : OddNat} {k r j : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (haddr : SourcePressureBeamAddressedDepthTarget L j)
          (hdrop : 0 <= SourcePressureNetDropInt n k r j) :
          0 < SourcePressureMarginInt n k (r + j + 1)

    Proof idea:
      - get current positivity from
          `sourcePressureMargin_pos_of_addressedDepthTarget haddr`;
      - get transition equation from
          `sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget haddr`;
      - use integer arithmetic / linarith if available.

  Experiment T2:
    Prove the existential seed version if T1 passes.

      theorem exists_sourcePressureMargin_next_pos_of_beamSeed_of_netDrop_nonneg_at_addressed
          {n : OddNat} {k r : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (hseed : SourcePressureBeamSeed L)
          (hdrop :
            ∀ j,
              SourcePressureBeamAddressedDepthTarget L j ->
                0 <= SourcePressureNetDropInt n k r j) :
          ∃ j,
            SourcePressureBeamAddressedDepthTarget L j ∧
              0 < SourcePressureMarginInt n k (r + j + 1)

    This is still existential and addressed.  It is not global propagation.

  Experiment F1:
    Try a local False Beam drop condition.

    Candidate theorem shape:

      theorem sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_netDrop_le_neg_current
          {n : OddNat} {k r j : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (haddr : SourcePressureBeamAddressedDepthTarget L j)
          (hdrop :
            SourcePressureNetDropInt n k r j
              <= - SourcePressureMarginInt n k (r + j)) :
          SourcePressureMarginInt n k (r + j + 1) <= 0

    This should follow from the same transition equation and integer arithmetic.
    If Lean proves it, this is a genuine local False Beam condition:
      the next margin falls out of the positive region.

  Experiment G1:
    In scratch only, try to prove next positivity from `haddr` alone:

      SourcePressureBeamAddressedDepthTarget L j
        -> 0 < SourcePressureMarginInt n k (r + j + 1)

    Do not commit unless Lean unexpectedly proves it.  It should remain Gap,
    because the sign of `netDrop` is not constrained by the addressed target.

  Experiment G2:
    In scratch only, try to prove next nonpositivity from `haddr` alone:

      SourcePressureBeamAddressedDepthTarget L j
        -> SourcePressureMarginInt n k (r + j + 1) <= 0

    Do not commit unless Lean unexpectedly proves it.  It should remain Gap for
    the same reason.

Guardrails:
  Do not add:
    - time/orbit propagation;
    - arbitrary target transport;
    - arbitrary margin positivity;
    - canonical target selection;
    - global coverage;
    - convergence theorem;
    - arbitrary-list recursive decomposition;
    - enumeration of all diagnostics;
    - aggregation over multiple recovered diagnostics;
    - interval union accounting;
    - overlap repair;
    - maximality;
    - uniqueness;
    - sorting theorem;
    - disjointness between multiple recovered families.

Report requirements:
  The report must contain:
    1. Situation analysis.
    2. Exact arithmetic / order lemmas used, or that `linarith` closed them.
    3. True Beam facts that passed.
    4. False Beam facts that passed, if any.
    5. Gap observations for sign claims without netDrop hypotheses.
    6. Confirmation that this is local sign reading, not propagation.
    7. One-step-ahead Wise Wolf inference.
    8. Experimental lemma table with passed / failed / under-specified.
    9. Explicit statement that no time/orbit propagation, arbitrary transport,
       arbitrary positivity, convergence, coverage, aggregation, or overlap
       repair theorem was added.

Verification commands:
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge

No-sorry check:
  rg -n "\bsorry\b|admit" \
    DkMath/Collatz/PetalBridge/PressureBeam.lean \
    DkMath/Collatz/PetalBridge/PressureAutomaton.lean \
    DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean \
    DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
    DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
    DkMath/Collatz/PetalBridge/PressureAccounting.lean \
    DkMath/Collatz/PetalBridge/PressureFrontier.lean \
    DkMath/Collatz/PetalBridge/PressureDecay.lean \
    DkMath/Collatz/PetalBridge/DriftBudget.lean

Git diff hygiene:
  git diff --check
```

## 一歩先ゆく推論

T1 / F1 が通れば、次はこう分かれる。

```text
True Beam:
  current positive + nonnegative netDrop
    -> next positive
```

```text
False Beam:
  current positive + sufficiently negative netDrop
    -> next nonpositive
```

この二本が通ると、DkMath Beams の哲学が Lean 上でかなり見える。

```text
Core:
  margin transition equation

True Beam:
  next positive condition

False Beam:
  next nonpositive condition

Gap:
  netDrop 条件なしでは次符号は未決定
```

ここまで来ると、次は netDrop 自体の分類へ入れる。
つまり Beam が「線分」から「符号分岐する線分」になる。

## 総合判断

cp208 で、Beam は

```text
positive point
  -> local transition equation
```

まで来た。

次は

```text
transition equation
  -> sign split
```

じゃ。

ここで初めて True Beam / False Beam が数学的に二股に割れる。
良い局面じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
index 11b06f41..03d2f250 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
@@ -408,4 +408,46 @@ theorem exists_sourcePressureBeamDepthTarget_and_margin_pos_of_seed
       sourcePressureBeamDepthTarget_of_addressedDepthTarget haddressed,
       sourcePressureMargin_pos_of_addressedDepthTarget haddressed⟩
 
+/--
+An addressed Beam depth target opens the local source-pressure margin
+transition equation at the same depth.
+
+This is only the Beam-facing spelling of the local `PressureDecay` transition
+identity.  The addressed target hypothesis is intentionally unused by the
+algebraic equation; it documents that the equation is being read at a depth
+selected by the supplied witness list.  No time/orbit propagation is asserted.
+-/
+theorem sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (_h : SourcePressureBeamAddressedDepthTarget L j) :
+    SourcePressureMarginInt n k (r + j + 1) =
+      SourcePressureMarginInt n k (r + j) +
+        SourcePressureNetDropInt n k r j :=
+  sourcePressureMargin_next_eq_current_add_netDrop n k r j
+
+/--
+A raw Beam seed existentially exposes an addressed target together with the
+local margin transition equation at that same selected depth.
+
+The selected depth is existential.  This is not a statement that the transition
+at an arbitrary external depth belongs to the seed.
+-/
+theorem exists_sourcePressureMargin_transition_of_beamSeed
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hseed : SourcePressureBeamSeed L) :
+    ∃ j,
+      SourcePressureBeamAddressedDepthTarget L j ∧
+        SourcePressureMarginInt n k (r + j + 1) =
+          SourcePressureMarginInt n k (r + j) +
+            SourcePressureNetDropInt n k r j := by
+  rcases exists_sourcePressureBeamAddressedDepthTarget_of_seed hseed with
+    ⟨j, haddressed⟩
+  exact
+    ⟨j,
+      haddressed,
+      sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget
+        haddressed⟩
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-208.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-208.md
new file mode 100644
index 00000000..25f76f79
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-208.md
@@ -0,0 +1,190 @@
+# report-petal-208
+
+## Situation
+
+Checkpoint `petal-208` starts the Beam-facing margin transition layer.
+
+The current Beam surface before this checkpoint was:
+
+```text
+BeamSeed
+  -> exists addressed target
+  -> exists positive pressure margin
+```
+
+This checkpoint asks whether that addressed positive-margin point can be read
+through the existing local `PressureDecay` transition equations.  The answer is
+yes, but only as a local equation at the selected addressed depth.
+
+## Exact Transition Shapes Found
+
+The relevant existing local transition theorems in `PressureDecay` have these
+shapes:
+
+```lean
+theorem sourcePressureMarginStepDiff_eq
+    (n : OddNat) (k r j : ℕ) :
+    SourcePressureMarginInt n k (r + j + 1) -
+        SourcePressureMarginInt n k (r + j) =
+      SourcePressureNetDropInt n k r j
+```
+
+```lean
+theorem sourcePressureMargin_next_eq_current_add_netDrop
+    (n : OddNat) (k r j : ℕ) :
+    SourcePressureMarginInt n k (r + j + 1) =
+      SourcePressureMarginInt n k (r + j) +
+        SourcePressureNetDropInt n k r j
+```
+
+The actual index shape is:
+
+```text
+r + j + 1
+```
+
+not the alternative spelling:
+
+```text
+r + (j + 1)
+```
+
+The Beam-facing wrapper therefore preserves the exact existing local theorem
+shape instead of forcing an index rewrite.
+
+## True Beam Facts
+
+Implemented:
+
+```lean
+theorem sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget
+```
+
+This reads the local transition equation at a depth already selected by an
+addressed Beam target.
+
+Implemented:
+
+```lean
+theorem exists_sourcePressureMargin_transition_of_beamSeed
+```
+
+This proves:
+
+```text
+SourcePressureBeamSeed L
+  -> exists j,
+       SourcePressureBeamAddressedDepthTarget L j
+       and
+       local margin transition equation at j
+```
+
+## Experimental Lemma Table
+
+| experiment | theorem | status | note |
+| --- | --- | --- | --- |
+| Step 1 | `sourcePressureMarginStepDiff_eq` shape | inspected | uses `r + j + 1` |
+| Step 1 | `sourcePressureMargin_next_eq_current_add_netDrop` shape | inspected | uses `SourcePressureNetDropInt n k r j` |
+| T1 | `sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget` | passed | addressed local transition wrapper |
+| T2 | `exists_sourcePressureMargin_transition_of_beamSeed` | passed | seed gives existential addressed transition |
+| G1 | `SourcePressureBeamSeed L -> transition equation at arbitrary j` | nuanced | equation is globally algebraic, but not seed-addressed |
+
+## False Beam / Gap
+
+The transition equation itself is a global local algebra identity from
+`PressureDecay`; it does not need a seed.  Therefore the overclaim is not false
+as a raw equation.
+
+The actual Gap is more precise:
+
+```text
+SourcePressureBeamSeed L
+  -> SourcePressureBeamAddressedDepthTarget L j
+```
+
+for arbitrary external `j`.
+
+The seed does not select arbitrary external depths.  It selects only an
+existential addressed depth from its witness list.
+
+No negated theorem was added in this checkpoint.
+
+## Local Reading, Not Propagation
+
+The new wrapper is only a local transition reading:
+
+```text
+AddressedDepthTarget at j
+  -> margin_next(j) = margin_current(j) + netDrop(j)
+```
+
+The addressed target hypothesis is not needed for the algebraic identity
+itself.  It is included to keep the API tied to the Beam-selected depth.
+
+No theorem was added for:
+
+- time/orbit propagation;
+- arbitrary target transport;
+- arbitrary margin positivity;
+- canonical target selection;
+- convergence;
+- global coverage;
+- arbitrary-list recursive decomposition;
+- enumeration of all diagnostics;
+- aggregation over multiple recovered diagnostics;
+- interval union accounting;
+- overlap repair;
+- maximality;
+- uniqueness;
+- sorting;
+- disjointness between multiple recovered families.
+
+## One-Step-Ahead Inference
+
+The next safe surface is sign reading at the addressed transition:
+
+```text
+AddressedDepthTarget
+  -> margin_pos at j
+  -> margin_next = margin_current + netDrop
+```
+
+From here, the natural split is:
+
+```text
+True Beam:
+  conditions under which next margin remains positive
+
+False Beam:
+  conditions under which next margin is nonpositive
+```
+
+That should still be stated locally at the addressed depth.  It should not be
+promoted to time/orbit propagation until there is a separate theorem connecting
+adjacent pressure-depth edges into a valid Beam path.
+
+## Verification
+
+Commands run:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureBeam
+lake build DkMath.Collatz.PetalBridge
+rg -n "\bsorry\b|admit" DkMath/Collatz/PetalBridge/PressureBeam.lean ...
+git diff --check
+```
+
+Results:
+
+- `lake build DkMath.Collatz.PetalBridge.PressureBeam`: passed.
+- `lake build DkMath.Collatz.PetalBridge`: passed.
+- no-sorry check over the requested pressure files: no matches.
+- `git diff --check`: passed.
+
+Known unrelated warning remains:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
````
`````
