# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam

gch: 2fb242e1a8ba74228712892b158d9f7506f78f25

## Report

cp207 完了です。

[PressureBeam.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean) に、raw Beam seed から存在的な positive margin を取り出す補題を追加しました。

追加 theorem:

- `exists_sourcePressureMargin_pos_of_beamSeed`
- `exists_sourcePressureBeamAddressedDepthTarget_and_margin_pos_of_seed`
- `exists_sourcePressureBeamDepthTarget_and_margin_pos_of_seed`

すべて `∃ j` の形に閉じています。任意の外部 `j` への margin positivity や target transport は追加していません。

レポート:
[report-petal-207.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-207.md)

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureBeam` passed
- `lake build DkMath.Collatz.PetalBridge` passed
- 指定 pressure files の `sorry/admit` check: no matches
- `git diff --check` passed

既知の unrelated warning として `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` warning は残っています。

## Review

## 結論

**採用** じゃ。

cp207 は、Beam seed から **存在的 positive margin** まできれいに到達した checkpoint じゃ。

今回追加された theorem は次の 3 本。

```lean id="l73l3r"
exists_sourcePressureMargin_pos_of_beamSeed

exists_sourcePressureBeamAddressedDepthTarget_and_margin_pos_of_seed

exists_sourcePressureBeamDepthTarget_and_margin_pos_of_seed
```

すべて `∃ j` に閉じており、任意の外部 `j` への positivity や target transport は追加していない。これは正しい。report でも、任意 `j` への主張は under-specified な Gap として残されている。

## 実装レビュー

今回の流れは非常に良い。

まず、raw seed から addressed carrier を取り出す。

```text id="rq9yvb"
SourcePressureBeamSeed L
  -> ∃ j, SourcePressureBeamAddressedDepthTarget L j
```

そこから margin positivity に降りる。

```text id="cdsmad"
SourcePressureBeamAddressedDepthTarget L j
  -> 0 < SourcePressureMarginInt n k (r + j)
```

そして合成として、

```text id="8g5rym"
SourcePressureBeamSeed L
  -> ∃ j, 0 < SourcePressureMarginInt n k (r + j)
```

が Core に入った。

これは Beam の「点」が、単なる witness address ではなく、**正の pressure margin を持つ観測点**であることを Lean が認めた、という意味じゃ。

## 数学的意味

ここで Beam の入口はかなり明確になった。

現在の構造はこうじゃ。

```text id="olggoy"
Seed
  -> exists AddressedDepthTarget
  -> exists positive source-pressure margin
```

これはまだ伝播ではない。
だが、伝播を始めるための **初期点** は得た。

DkMath 哲学で言えば、

```text id="n0e1ur"
Core:
  raw Beam seed は positive margin depth を存在的に持つ

True Beam:
  seed -> ∃ addressed target
  seed -> ∃ positive margin

Gap:
  任意外部 j への target / margin positivity
```

この整理はかなり強い。
「Beam は空ではない」「Beam は少なくとも一つの正圧点を持つ」という観測事実が Core 化されたからじゃ。

## True Beam / False Beam / Gap

## True Beam

今回の True Beam はこれ。

```text id="iydrqw"
SourcePressureBeamSeed L
  -> ∃ j, 0 < SourcePressureMarginInt n k (r + j)
```

```text id="raef42"
SourcePressureBeamSeed L
  -> ∃ j,
       SourcePressureBeamAddressedDepthTarget L j
       ∧ 0 < SourcePressureMarginInt n k (r + j)
```

```text id="9zksfh"
SourcePressureBeamSeed L
  -> ∃ j,
       SourcePressureBeamDepthTarget n k r j
       ∧ 0 < SourcePressureMarginInt n k (r + j)
```

全部、存在的で安全じゃ。

## False Beam

新しい negated theorem はなし。
ここも無理に作らなくてよい。

## Gap

残る Gap は report 通り。

```text id="hugm5i"
SourcePressureBeamSeed L
  -> SourcePressureBeamDepthTarget n k r j
```

```text id="tmx93k"
SourcePressureBeamSeed L
  -> SourcePressureBeamAddressedDepthTarget L j
```

```text id="4ewqnn"
SourcePressureBeamSeed L
  -> 0 < SourcePressureMarginInt n k (r + j)
```

いずれも **任意の外部 `j`** についてはまだ言えない。
これは正しい Gap のままじゃ。

## 注意点

今回も境界は守られている。

```text id="vj6avz"
arbitrary target transport ではない。
```

```text id="8jp144"
arbitrary margin positivity ではない。
```

```text id="1s2ods"
canonical target selection ではない。
```

```text id="2cq91m"
time/orbit propagation ではない。
```

```text id="55v4mt"
coverage / aggregation / overlap repair ではない。
```

```text id="clzo0t"
Collatz convergence ではない。
```

これはあくまで、**存在的 projection** じゃ。

## 次の checkpoint 方針

次は report の一歩先推論どおり、**margin transition layer** に入るのがよい。

ただし、いきなり「`j` から `j+1` へ進む」とは言わない。
まずは `PressureDecay` にある既存の margin transition 事実を、Beam-facing に薄く読む。

狙いはこれ。

```text id="yy1zse"
AddressedDepthTarget
  -> margin_pos
  -> local transition equation at the same addressed depth
```

次の実験で Lean に聞くべきは、

```text id="x9f2pk"
positive margin at r + j
  と
next margin / netDrop
  の既存関係を Beam 側で開けるか
```

じゃ。

候補 theorem は、既存 theorem の実際の型を `#check` してから決めるべき。
ここは推測しない。Lean に聞く。

## 次の Codex 指示

```text id="k5wa77"
Checkpoint: petal-208

Main goal:
  Start the Beam-facing margin transition layer by asking Lean how the
  addressed positive-margin point connects to existing `PressureDecay`
  transition facts.  Do not prove time/orbit propagation yet.  This checkpoint
  should wrap existing local transition equations only if Lean confirms their
  exact statement.

Primary target file:
  DkMath/Collatz/PetalBridge/PressureBeam.lean

Allowed supporting files:
  docs/dev/das-p2l-260607/review/report-petal-208.md

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

  Grow Core by fixing both True and False observations.  Do not merely inspect
  code; ask Lean small questions.

Current Core:
  SourcePressureBeamSeed
  SourcePressureBeamAddressedDepthTarget
  exists_sourcePressureBeamAddressedDepthTarget_of_seed
  sourcePressureMargin_pos_of_addressedDepthTarget
  exists_sourcePressureMargin_pos_of_beamSeed
  exists_sourcePressureBeamAddressedDepthTarget_and_margin_pos_of_seed
  exists_sourcePressureBeamDepthTarget_and_margin_pos_of_seed

Current known Gap:
  SourcePressureBeamSeed L -> 0 < SourcePressureMarginInt n k (r + j)
  for arbitrary external `j`.
  The current theorem is only existential in `j`.

Required Lean exploration:

  Step 1:
    Use `#check` or small scratch wrappers to inspect the exact types of the
    existing local transition facts in `PressureDecay`, especially:

      sourcePressureMarginStepDiff_eq
      sourcePressureMargin_next_eq_current_add_netDrop

    Do not guess their statement.  Let Lean reveal the exact shape.

  Experiment T1:
    If the existing transition theorem has the expected shape, add a
    Beam-facing wrapper from an addressed target at depth `j` to the local
    margin transition equation at that same addressed depth.

    Candidate shape, adjust to the actual theorem type Lean reports:

      theorem sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget
          {n : OddNat} {k r j : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (h : SourcePressureBeamAddressedDepthTarget L j) :
          SourcePressureMarginInt n k (r + (j + 1))
            =
          SourcePressureMarginInt n k (r + j)
            + SourcePressureNetDropInt n k r j

    Commit only if this follows directly from the existing `PressureDecay`
    theorem without adding new assumptions or changing lower modules.

  Experiment T2:
    If T1 passes, try the paired existential version from a raw seed:

      theorem exists_sourcePressureMargin_transition_of_beamSeed
          {n : OddNat} {k r : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (hseed : SourcePressureBeamSeed L) :
          ∃ j,
            SourcePressureBeamAddressedDepthTarget L j ∧
              <the local margin transition equation at j>

    The exact equation must match the theorem Lean confirmed in T1.

  Experiment G1:
    In scratch only, try the overclaim:

      SourcePressureBeamSeed L -> <transition equation at arbitrary j>

    Do not commit it.  Record as Gap unless Lean unexpectedly proves it.

  Experiment F1:
    If the expected transition theorem cannot be wrapped because the index shape
    differs, record the exact mismatch:
      - `(r + j + 1)` versus `(r + (j + 1))`;
      - net-drop index uses `r + j` instead of `r j`;
      - theorem requires additional hypotheses;
      - theorem name or orientation differs.

    Record this as Gap unless Lean proves an actual negated obstruction theorem.

Guardrails:
  Do not add:
    - time/orbit propagation;
    - arbitrary target transport;
    - arbitrary margin positivity;
    - canonical target selection;
    - convergence theorem;
    - global coverage;
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
    2. Exact `#check` results or exact theorem shapes discovered.
    3. True Beam facts that passed.
    4. False Beam / Gap observations.
    5. Whether a Beam-facing margin transition wrapper was added.
    6. Confirmation that this is local transition reading, not propagation.
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

この次に見たいのは、こうじゃ。

```text id="jhi2v8"
AddressedDepthTarget
  -> margin transition equation
  -> sign / pulse / net-drop reading
```

つまり、Beam が「正の一点」から「隣接差分を持つ一点」へ進む。

この transition equation が Beam 側で開ければ、次は True / False Beams が二方向に割れる可能性がある。

```text id="xdah54"
True Beam:
  next margin がまだ正である条件

False Beam:
  next margin が非正に落ちる条件
```

ここで初めて、Beam x2 の意味がかなり数学的に出てくるはずじゃ。

## 総合判断

cp207 で、Beam は

```text id="x2ar7d"
seed
  -> exists positive margin
```

まで来た。

次は

```text id="y3jfgs"
positive margin
  -> local transition equation
```

を Beam 側に読む。

ここから、点の抽出から線分の解析へ移る。
いよいよ Beam が「伸びる」直前じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
index 70cbc51f..11b06f41 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
@@ -353,4 +353,59 @@ theorem sourcePressureMargin_pos_of_addressedDepthTarget
   sourcePressureMargin_pos_of_beamDepthTarget n k r j
     (sourcePressureBeamDepthTarget_of_addressedDepthTarget h)

+/--
+A raw Beam seed existentially exposes a positive source-pressure margin.
+
+The depth is selected through the addressed carrier extracted from the seed.
+This is not arbitrary margin positivity and does not propagate the Beam to a
+new depth.
+-/
+theorem exists_sourcePressureMargin_pos_of_beamSeed
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hseed : SourcePressureBeamSeed L) :
+    ∃ j, 0 < SourcePressureMarginInt n k (r + j) := by
+  rcases exists_sourcePressureBeamAddressedDepthTarget_of_seed hseed with
+    ⟨j, haddressed⟩
+  exact ⟨j, sourcePressureMargin_pos_of_addressedDepthTarget haddressed⟩
+
+/--
+A raw Beam seed produces an addressed target together with positive margin at
+the same extracted depth.
+
+This keeps the address and the margin proof paired.  It is still an
+existential projection from the supplied seed data, not a canonical choice.
+-/
+theorem exists_sourcePressureBeamAddressedDepthTarget_and_margin_pos_of_seed
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hseed : SourcePressureBeamSeed L) :
+    ∃ j,
+      SourcePressureBeamAddressedDepthTarget L j ∧
+        0 < SourcePressureMarginInt n k (r + j) := by
+  rcases exists_sourcePressureBeamAddressedDepthTarget_of_seed hseed with
+    ⟨j, haddressed⟩
+  exact ⟨j, haddressed, sourcePressureMargin_pos_of_addressedDepthTarget haddressed⟩
+
+/--
+A raw Beam seed produces a Beam depth target together with positive margin at
+the same extracted depth.
+
+This is a thinner package for callers that do not need the list-address
+component.  It does not state positivity for arbitrary external depths.
+-/
+theorem exists_sourcePressureBeamDepthTarget_and_margin_pos_of_seed
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hseed : SourcePressureBeamSeed L) :
+    ∃ j,
+      SourcePressureBeamDepthTarget n k r j ∧
+        0 < SourcePressureMarginInt n k (r + j) := by
+  rcases exists_sourcePressureBeamAddressedDepthTarget_of_seed hseed with
+    ⟨j, haddressed⟩
+  exact
+    ⟨j,
+      sourcePressureBeamDepthTarget_of_addressedDepthTarget haddressed,
+      sourcePressureMargin_pos_of_addressedDepthTarget haddressed⟩
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-207.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-207.md
new file mode 100644
index 00000000..89b12feb
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-207.md
@@ -0,0 +1,148 @@
+# report-petal-207
+
+## Situation
+
+Checkpoint `petal-207` asks for the next True Beam projection from a raw Beam
+seed:
+
+```text
+SourcePressureBeamSeed L
+  -> exists addressed target
+  -> exists positive source-pressure margin
+```
+
+The goal is still existential.  The seed selects a depth through the explicit
+witness list, and the margin positivity is read at that same selected depth.
+
+## True Beam Facts
+
+Implemented:
+
+```lean
+theorem exists_sourcePressureMargin_pos_of_beamSeed
+```
+
+This proves:
+
+```text
+SourcePressureBeamSeed L
+  -> ∃ j, 0 < SourcePressureMarginInt n k (r + j)
+```
+
+Implemented:
+
+```lean
+theorem exists_sourcePressureBeamAddressedDepthTarget_and_margin_pos_of_seed
+```
+
+This keeps the addressed carrier and margin positivity paired at the same
+existential depth.
+
+Implemented:
+
+```lean
+theorem exists_sourcePressureBeamDepthTarget_and_margin_pos_of_seed
+```
+
+This is the thinner package for callers that need the Beam target and margin
+positivity but do not need the list-address component.
+
+## Experimental Lemma Table
+
+| experiment | theorem | status | note |
+| --- | --- | --- | --- |
+| T1 | `exists_sourcePressureMargin_pos_of_beamSeed` | passed | seed exposes some positive margin |
+| T2 | `exists_sourcePressureBeamAddressedDepthTarget_and_margin_pos_of_seed` | passed | addressed target and margin paired |
+| T3 | `exists_sourcePressureBeamDepthTarget_and_margin_pos_of_seed` | passed | target and margin paired without address projection |
+| G1 | `SourcePressureBeamSeed L -> 0 < SourcePressureMarginInt n k (r + j)` | under-specified | arbitrary external `j` is not selected by the seed |
+| G1 | `SourcePressureBeamSeed L -> SourcePressureBeamAddressedDepthTarget L j` | under-specified | arbitrary external `j` remains outside the seed address |
+
+## False Beam / Gap
+
+The known Gaps remain:
+
+```text
+SourcePressureBeamSeed L -> SourcePressureBeamDepthTarget n k r j
+SourcePressureBeamSeed L -> SourcePressureBeamAddressedDepthTarget L j
+SourcePressureBeamSeed L -> 0 < SourcePressureMarginInt n k (r + j)
+```
+
+for arbitrary external `j`.
+
+No negated theorem was added in this checkpoint.  The current evidence is
+positive but strictly existential.
+
+## Existential Projection, Not Propagation
+
+This checkpoint only composes existing addressed-carrier projections:
+
+```text
+Seed
+  -> exists AddressedDepthTarget
+  -> margin_pos at that addressed depth
+```
+
+No theorem was added for:
+
+- arbitrary target transport;
+- arbitrary margin positivity;
+- canonical target selection;
+- propagation over time or orbit;
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
+The next natural surface is the margin transition layer:
+
+```text
+positive margin at r + j
+  -> relation with the next local margin / net-drop / pulse theorem
+```
+
+This should probably be a Beam-facing wrapper over existing `PressureDecay`
+facts, not a new global propagation theorem.  The safe direction is:
+
+```text
+AddressedDepthTarget
+  -> margin_pos
+  -> local transition fact at the same addressed depth
+```
+
+Only after that layer is stable should the project ask whether a depth can move
+from `j` to `j + 1`.
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
