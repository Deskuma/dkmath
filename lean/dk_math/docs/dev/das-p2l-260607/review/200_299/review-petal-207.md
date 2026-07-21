# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam

gch: e45f1cfdadc579e473a648e8b74ed6d0a61c378b

## Report

cp206 完了です。

[PressureBeam.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean) に addressed carrier を追加しました。

追加内容:

- `SourcePressureBeamAddressedDepthTarget`
- `sourcePressureBeamSeedContainsDepth_of_addressedDepthTarget`
- `sourcePressureBeamDepthTarget_of_addressedDepthTarget`
- `sourcePressureBeamAddressedDepthTarget_mk`
- `exists_sourcePressureBeamAddressedDepthTarget_of_seed`
- `sourcePressureMargin_pos_of_addressedDepthTarget`

最後の margin positivity projection は、指示文の一歩先にあった安全な補題です。carrier から target を取り出して既存の margin positivity に繋ぐだけなので、propagation や arbitrary target transport ではありません。

レポートも追加しました:
[report-petal-206.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-206.md)

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureBeam` passed
- `lake build DkMath.Collatz.PetalBridge` passed
- 指定 pressure files の `sorry/admit` check: no matches
- `git diff --check` passed

既知の unrelated warning として `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` warning は残っています。

## Review

## 結論

**採用** じゃ。

cp206 は、cp205 で得た

```text id="sjep4l"
SourcePressureBeamSeed L
  -> exists j, SourcePressureBeamSeedContainsDepth L j
               and SourcePressureBeamDepthTarget n k r j
```

を、きちんと名前付き carrier に包んだ checkpoint じゃ。

追加された主な API はこれ。

```lean id="iyt45z"
SourcePressureBeamAddressedDepthTarget

sourcePressureBeamSeedContainsDepth_of_addressedDepthTarget
sourcePressureBeamDepthTarget_of_addressedDepthTarget
sourcePressureBeamAddressedDepthTarget_mk
exists_sourcePressureBeamAddressedDepthTarget_of_seed
sourcePressureMargin_pos_of_addressedDepthTarget
```

特に最後の `sourcePressureMargin_pos_of_addressedDepthTarget` は、一歩先の安全補題としてよい。carrier から `BeamDepthTarget` を取り出し、そこから positive margin に降りるだけなので、transport でも coverage でもない。

## 実装レビュー

今回の carrier は素直でよい。

```lean id="wt2mlt"
def SourcePressureBeamAddressedDepthTarget
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (j : ℕ) : Prop :=
  SourcePressureBeamSeedContainsDepth L j ∧
    SourcePressureBeamDepthTarget n k r j
```

意味は明確じゃ。

```text id="lqmwvb"
L が depth j の witness を含む
かつ
j は Beam depth target である
```

つまり、`j` は外部から勝手に選ばれた depth ではなく、**supplied witness list L に address された target** じゃ。

projection helpers も自然。

```lean id="r61kg8"
sourcePressureBeamSeedContainsDepth_of_addressedDepthTarget
sourcePressureBeamDepthTarget_of_addressedDepthTarget
```

constructor も自然。

```lean id="wq7ms8"
sourcePressureBeamAddressedDepthTarget_mk
```

そして seed から existential carrier が出る。

```lean id="9gk3l8"
exists_sourcePressureBeamAddressedDepthTarget_of_seed
```

ここまでで、Beam seed から「存在的に address された depth target」を取り出す API が読みやすくなった。

## 数学的意味

今回で、Beam の最初の target 抽出がこう整理された。

```text id="v2zrrz"
Seed
  -> exists AddressedDepthTarget
```

さらに carrier からは三つの projection が得られる。

```text id="b8p51t"
AddressedDepthTarget -> containsDepth

AddressedDepthTarget -> depthTarget

AddressedDepthTarget -> margin_pos
```

これは大きい。
なぜなら、Beam の最初の出力が「抽象的な target」ではなく、

```text id="dyyfvq"
list-address を持ち、
target 性を持ち、
positive margin を持つ depth
```

として固定されたからじゃ。

DkMath 哲学ではこうなる。

```text id="6vx665"
Core:
  addressed carrier が定義された

True Beam:
  seed から exists addressed target が出る
  addressed target から margin_pos が出る

Gap:
  arbitrary external j はまだ選べない
```

## True Beam / False Beam / Gap

## True Beam

今回の True Beam はこれ。

```text id="vt57wc"
SourcePressureBeamSeed L
  -> ∃ j, SourcePressureBeamAddressedDepthTarget L j
```

```text id="6kd596"
SourcePressureBeamAddressedDepthTarget L j
  -> SourcePressureBeamSeedContainsDepth L j
```

```text id="njx7z8"
SourcePressureBeamAddressedDepthTarget L j
  -> SourcePressureBeamDepthTarget n k r j
```

```text id="u2057v"
SourcePressureBeamAddressedDepthTarget L j
  -> 0 < SourcePressureMarginInt n k (r + j)
```

これで addressed target の API が閉じた。

## False Beam

新しい negated theorem はなし。
問題ない。

## Gap

既知の Gap はそのまま。

```text id="57j0he"
SourcePressureBeamSeed L
  -> SourcePressureBeamDepthTarget n k r j
```

任意の外部 `j` にはまだ行けない。
そして carrier はこの Gap を消すためのものではない。
あくまで、seed から抽出された `j` を包むものじゃ。report でもその点が明記されている。

## 注意点

今回まだ言っていないことを確認しておく。

```text id="6ittfv"
arbitrary target transport ではない。
```

```text id="lhqrdm"
canonical target selection ではない。
```

```text id="e35ziu"
time/orbit propagation ではない。
```

```text id="kwz6g0"
global coverage ではない。
```

```text id="oypuat"
aggregation ではない。
```

```text id="qvu0u1"
overlap repair ではない。
```

```text id="xj05pb"
Collatz convergence ではない。
```

この境界は守れておる。

## 次の checkpoint 方針

次は、report の一歩先推論どおり、

```text id="vcz4po"
SourcePressureBeamSeed L
  -> exists j, 0 < SourcePressureMarginInt n k (r + j)
```

を Lean に聞くのがよい。

これは、いまある API の合成で通るはずじゃ。

流れはこう。

```text id="14qd68"
seed
  -> exists addressed target
  -> margin_pos
```

候補 theorem。

```lean id="1eosxv"
theorem exists_sourcePressureMargin_pos_of_beamSeed
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hseed : SourcePressureBeamSeed L) :
    ∃ j, 0 < SourcePressureMarginInt n k (r + j)
```

これは propagation ではない。
ただし、Beam seed が **実際に正の pressure margin を持つ depth を存在的に含む** ことを示すので、次の段に効く。

さらに paired version も良い。

```lean id="s4eeba"
theorem exists_sourcePressureBeamAddressedDepthTarget_and_margin_pos_of_seed
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hseed : SourcePressureBeamSeed L) :
    ∃ j,
      SourcePressureBeamAddressedDepthTarget L j ∧
        0 < SourcePressureMarginInt n k (r + j)
```

これも自明合成だが、DkMath 哲学では固定してよい。
「seed が正の pressure depth を伴う」ことが、True Beam として Core に入る。

## 次の Codex 指示

```text id="a3r5cz"
Checkpoint: petal-207

Main goal:
  Ask Lean for the next True Beam projection from a raw Beam seed:
    seed -> exists positive source-pressure margin.
  This checkpoint should compose the addressed carrier API already added in
  cp206.  Do not add propagation, arbitrary target transport, canonical
  selection, coverage, aggregation, or overlap repair.

Primary target file:
  DkMath/Collatz/PetalBridge/PressureBeam.lean

Allowed supporting files:
  docs/dev/das-p2l-260607/review/report-petal-207.md

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
  SourcePressureBeamSeedContainsDepth
  SourcePressureBeamDepthTarget
  SourcePressureBeamAddressedDepthTarget
  exists_sourcePressureBeamAddressedDepthTarget_of_seed
  sourcePressureMargin_pos_of_addressedDepthTarget

Current known Gap:
  SourcePressureBeamSeed L -> SourcePressureBeamDepthTarget n k r j
  for arbitrary external `j`.
  SourcePressureBeamSeed L -> SourcePressureBeamAddressedDepthTarget L j
  for arbitrary external `j`.

Required experiments:

  Experiment T1:
    Prove that a raw Beam seed existentially exposes a positive
    source-pressure margin.

      theorem exists_sourcePressureMargin_pos_of_beamSeed
          {n : OddNat} {k r : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (hseed : SourcePressureBeamSeed L) :
          ∃ j, 0 < SourcePressureMarginInt n k (r + j)

    Proof strategy:
      - use `exists_sourcePressureBeamAddressedDepthTarget_of_seed`;
      - apply `sourcePressureMargin_pos_of_addressedDepthTarget`.

  Experiment T2:
    Prove the paired addressed-carrier and margin positivity statement.

      theorem exists_sourcePressureBeamAddressedDepthTarget_and_margin_pos_of_seed
          {n : OddNat} {k r : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (hseed : SourcePressureBeamSeed L) :
          ∃ j,
            SourcePressureBeamAddressedDepthTarget L j ∧
              0 < SourcePressureMarginInt n k (r + j)

  Experiment T3:
    If useful, prove a direct chain from seed to BeamDepthTarget and margin
    positivity in one existential package:

      theorem exists_sourcePressureBeamDepthTarget_and_margin_pos_of_seed
          {n : OddNat} {k r : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (hseed : SourcePressureBeamSeed L) :
          ∃ j,
            SourcePressureBeamDepthTarget n k r j ∧
              0 < SourcePressureMarginInt n k (r + j)

    This is also packaging only.

  Experiment G1:
    In scratch only, retry arbitrary external depth claims:
      SourcePressureBeamSeed L -> 0 < SourcePressureMarginInt n k (r + j)
      SourcePressureBeamSeed L -> SourcePressureBeamAddressedDepthTarget L j

    Do not commit them.  Record as Gap unless Lean unexpectedly proves them.

Guardrails:
  Do not add:
    - arbitrary target transport;
    - arbitrary margin positivity;
    - canonical target selection;
    - propagation over time or orbit;
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
    2. True Beam facts that passed.
    3. False Beam / Gap observations.
    4. Confirmation that this is existential projection, not propagation.
    5. One-step-ahead Wise Wolf inference.
    6. Experimental lemma table with passed / failed / under-specified.
    7. Explicit statement that no arbitrary target transport, arbitrary margin
       positivity, canonical selection, propagation, convergence, coverage,
       aggregation, or overlap repair theorem was added.

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

cp207 が通ると、Beam seed はこう読める。

```text id="c9g49t"
BeamSeed
  -> exists addressed target
  -> exists positive pressure margin
```

その次に試すべきは、たぶん **positive margin と net-drop / pulse の接続**じゃ。

ただし、まだ propagation ではない。
まずは `PressureDecay` 側に既にある margin transition theorem を、Beam-facing に薄く読むだけ。

候補はこの方向。

```text id="5myxn1"
positive margin at r+j
  と
next margin at r+j+1
  の関係
```

ここで初めて、Beam が「点」から「隣接点」へ伸び始める。

## 総合判断

cp206 で、Beam はかなりよい形になった。

```text id="9ycs6c"
Seed
  -> exists AddressedDepthTarget
  -> margin_pos
```

次はこの存在的 margin positivity を Core に固定する。
そこから、いよいよ margin transition、つまり Beam の線分へ進む。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
index 66f7c7b1..70cbc51f 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
@@ -271,4 +271,86 @@ theorem exists_sourcePressureBeamSeedContainsDepth_and_target_of_seed
     ⟨j, hcontains⟩
   exact ⟨j, hcontains, sourcePressureBeamDepthTarget_of_seedContainsDepth hcontains⟩

+/--
+Named addressed carrier for a Beam depth target selected from a supplied seed
+witness list.
+
+This is packaging, not new propagation.  The carrier remembers both pieces of
+data at the same explicit depth `j`:
+
+* `L` contains a local-island witness whose depth is exactly `j`;
+* `j` is a Beam depth target.
+
+It does not choose a canonical target, transport arbitrary external depths,
+aggregate multiple diagnostics, repair overlap, or claim global coverage.
+-/
+def SourcePressureBeamAddressedDepthTarget
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (j : ℕ) : Prop :=
+  SourcePressureBeamSeedContainsDepth L j ∧
+    SourcePressureBeamDepthTarget n k r j
+
+/--
+Project the list-address containment from an addressed Beam depth target.
+-/
+theorem sourcePressureBeamSeedContainsDepth_of_addressedDepthTarget
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureBeamAddressedDepthTarget L j) :
+    SourcePressureBeamSeedContainsDepth L j :=
+  h.1
+
+/--
+Project the Beam target fact from an addressed Beam depth target.
+-/
+theorem sourcePressureBeamDepthTarget_of_addressedDepthTarget
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureBeamAddressedDepthTarget L j) :
+    SourcePressureBeamDepthTarget n k r j :=
+  h.2
+
+/--
+Construct an addressed Beam depth target from its two local components.
+-/
+theorem sourcePressureBeamAddressedDepthTarget_mk
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hcontains : SourcePressureBeamSeedContainsDepth L j)
+    (htarget : SourcePressureBeamDepthTarget n k r j) :
+    SourcePressureBeamAddressedDepthTarget L j :=
+  ⟨hcontains, htarget⟩
+
+/--
+A raw Beam seed produces some addressed Beam depth target.
+
+This is the named-carrier form of
+`exists_sourcePressureBeamSeedContainsDepth_and_target_of_seed`.  The depth is
+still existentially selected from the supplied witness list; no arbitrary depth
+transport or canonical selection is introduced.
+-/
+theorem exists_sourcePressureBeamAddressedDepthTarget_of_seed
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hseed : SourcePressureBeamSeed L) :
+    ∃ j, SourcePressureBeamAddressedDepthTarget L j := by
+  rcases exists_sourcePressureBeamSeedContainsDepth_and_target_of_seed hseed with
+    ⟨j, hcontains, htarget⟩
+  exact ⟨j, sourcePressureBeamAddressedDepthTarget_mk hcontains htarget⟩
+
+/--
+An addressed Beam depth target exposes positive source-pressure margin.
+
+This is only projection composition through the target component.  It is not
+transport, propagation, or a coverage theorem.
+-/
+theorem sourcePressureMargin_pos_of_addressedDepthTarget
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureBeamAddressedDepthTarget L j) :
+    0 < SourcePressureMarginInt n k (r + j) :=
+  sourcePressureMargin_pos_of_beamDepthTarget n k r j
+    (sourcePressureBeamDepthTarget_of_addressedDepthTarget h)
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-206.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-206.md
new file mode 100644
index 00000000..a1ec64f2
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-206.md
@@ -0,0 +1,171 @@
+# report-petal-206
+
+## Situation
+
+Checkpoint `petal-206` packages the cp205 existential Beam target extraction
+as a named addressed carrier.
+
+The accepted Core before this checkpoint was:
+
+```text
+SourcePressureBeamSeed L
+  -> exists j, SourcePressureBeamSeedContainsDepth L j
+               and SourcePressureBeamDepthTarget n k r j
+```
+
+This checkpoint does not strengthen that statement.  It only gives the paired
+fact a reusable API name.
+
+## Carrier Added
+
+Implemented:
+
+```lean
+def SourcePressureBeamAddressedDepthTarget
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (j : ℕ) : Prop :=
+  SourcePressureBeamSeedContainsDepth L j ∧
+    SourcePressureBeamDepthTarget n k r j
+```
+
+Meaning:
+
+```text
+depth j is addressed by the supplied witness list L,
+and j is a Beam depth target.
+```
+
+This is a local addressed carrier.  It is not a canonical selector and does not
+transport arbitrary external depths.
+
+## True Beam Facts
+
+Implemented projection helpers:
+
+```lean
+theorem sourcePressureBeamSeedContainsDepth_of_addressedDepthTarget
+theorem sourcePressureBeamDepthTarget_of_addressedDepthTarget
+```
+
+Implemented constructor helper:
+
+```lean
+theorem sourcePressureBeamAddressedDepthTarget_mk
+```
+
+Implemented seed extraction:
+
+```lean
+theorem exists_sourcePressureBeamAddressedDepthTarget_of_seed
+```
+
+Implemented the one-step-ahead projection:
+
+```lean
+theorem sourcePressureMargin_pos_of_addressedDepthTarget
+```
+
+This last theorem is only projection composition:
+
+```text
+AddressedDepthTarget
+  -> BeamDepthTarget
+  -> positive source-pressure margin
+```
+
+It is not propagation.
+
+## Experimental Lemma Table
+
+| experiment | theorem | status | note |
+| --- | --- | --- | --- |
+| T1 | `sourcePressureBeamSeedContainsDepth_of_addressedDepthTarget` | passed | containment projection |
+| T1 | `sourcePressureBeamDepthTarget_of_addressedDepthTarget` | passed | target projection |
+| T2 | `sourcePressureBeamAddressedDepthTarget_mk` | passed | carrier constructor |
+| T3 | `exists_sourcePressureBeamAddressedDepthTarget_of_seed` | passed | seed gives existential addressed carrier |
+| bonus | `sourcePressureMargin_pos_of_addressedDepthTarget` | passed | addressed target opens to positive margin |
+| G1 | `SourcePressureBeamSeed L -> SourcePressureBeamAddressedDepthTarget L j` | under-specified | arbitrary external `j` is not selected by the seed |
+
+## False Beam / Gap
+
+The known Gap remains unchanged:
+
+```text
+SourcePressureBeamSeed L -> SourcePressureBeamDepthTarget n k r j
+```
+
+for arbitrary external `j`.
+
+The addressed carrier does not remove this Gap.  It records only the depth that
+is explicitly obtained from the supplied witness list.
+
+No new negated theorem was added.
+
+## Packaging, Not Propagation
+
+This checkpoint is strictly an API packaging step.
+
+No theorem was added for:
+
+- arbitrary target transport;
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
+The carrier now exposes three stable projections:
+
+```text
+AddressedDepthTarget -> containsDepth
+AddressedDepthTarget -> depthTarget
+AddressedDepthTarget -> margin_pos
+```
+
+The next safe step is not transport yet.  A natural next checkpoint is to add
+thin existential wrappers around these projections, for example:
+
+```text
+SourcePressureBeamSeed L
+  -> exists j, 0 < SourcePressureMarginInt n k (r + j)
+```
+
+That would still be existential and addressed by the seed.  It would not claim
+that every depth is positive, nor that the Beam propagates.
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
