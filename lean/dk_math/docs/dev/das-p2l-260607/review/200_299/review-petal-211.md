# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam

gch: 88065b2b9d61ddbf9b773e678cc884f0fbf996a4

## Report

cp210 完了です。

[PressureBeam.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean) に、sharp local sign-reading layer を追加しました。

追加 theorem:

- `sourcePressureMargin_next_pos_of_addressedDepthTarget_of_neg_current_lt_netDrop`
- `sourcePressureMargin_next_pos_of_addressedDepthTarget_of_current_add_netDrop_pos`
- `exists_sourcePressureMargin_next_pos_of_beamSeed_of_neg_current_lt_netDrop_at_addressed`

さらに bonus として、局所 classifier も Lean が通したので追加しました。

- `sourcePressureMargin_next_pos_iff_neg_current_lt_netDrop_of_addressedDepthTarget`
- `sourcePressureMargin_next_nonpos_iff_netDrop_le_neg_current_of_addressedDepthTarget`

これで局所的にはかなり綺麗に割れました。

```text
next positive iff -current < netDrop
next nonpositive iff netDrop <= -current
```

ただし、これは addressed depth の局所算術分類です。time/orbit propagation、任意 target transport、任意 next positivity は追加していません。

レポート:
[report-petal-210.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-210.md)

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureBeam` passed
- `lake build DkMath.Collatz.PetalBridge` passed
- 指定 pressure files の `sorry/admit` check: no matches
- `git diff --check` passed

既知の unrelated warning として `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` warning は残っています。

## Review

## 結論

**採用** じゃ。
cp210 はかなり大きい。ここで **局所 Beam の True / False classifier がほぼ完成**した。

今回追加された theorem は次。

```lean id="l6lq5n"
sourcePressureMargin_next_pos_of_addressedDepthTarget_of_neg_current_lt_netDrop

sourcePressureMargin_next_pos_of_addressedDepthTarget_of_current_add_netDrop_pos

exists_sourcePressureMargin_next_pos_of_beamSeed_of_neg_current_lt_netDrop_at_addressed

sourcePressureMargin_next_pos_iff_neg_current_lt_netDrop_of_addressedDepthTarget

sourcePressureMargin_next_nonpos_iff_netDrop_le_neg_current_of_addressedDepthTarget
```

特に bonus の `iff` 2 本が大きい。

```text id="ivmh7u"
next positive iff -current < netDrop

next nonpositive iff netDrop <= -current
```

これはまさに、DkMath 哲学の **Beams = True Beam / False Beam** が Lean 上で局所的に閉じた形じゃ。

## 実装レビュー

今回の sharp True Beam はよい。

```lean id="oh7h2s"
theorem sourcePressureMargin_next_pos_of_addressedDepthTarget_of_neg_current_lt_netDrop
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j)
    (hdrop :
      -SourcePressureMarginInt n k (r + j) <
        SourcePressureNetDropInt n k r j) :
    0 < SourcePressureMarginInt n k (r + j + 1)
```

これにより、`netDrop >= 0` より鋭い条件が得られた。
負の drop でも、current margin を食い切らなければ次も正に残る。

また、直接和の形も良い。

```lean id="qwi4sj"
theorem sourcePressureMargin_next_pos_of_addressedDepthTarget_of_current_add_netDrop_pos
```

これは transition equation を開いた後の利用に便利じゃ。

そして seed 版も、ちゃんと addressed depth に制限されている。

```lean id="i00mrg"
theorem exists_sourcePressureMargin_next_pos_of_beamSeed_of_neg_current_lt_netDrop_at_addressed
```

ここで仮定は任意 `j` ではなく、

```lean id="fwcp4j"
∀ j,
  SourcePressureBeamAddressedDepthTarget L j →
    -SourcePressureMarginInt n k (r + j) <
      SourcePressureNetDropInt n k r j
```

となっている。
これは安全。seed が address した場所だけを見る形になっている。

## 局所 classifier の意味

今回の本命は、次の 2 本じゃ。

```lean id="ug5siu"
sourcePressureMargin_next_pos_iff_neg_current_lt_netDrop_of_addressedDepthTarget
```

```lean id="bmdt7s"
sourcePressureMargin_next_nonpos_iff_netDrop_le_neg_current_of_addressedDepthTarget
```

これで、addressed edge における次符号は完全に `netDrop` と `-current` の比較へ落ちた。

```text id="j19557"
True:
  -current < netDrop

False:
  netDrop <= -current
```

整数順序ではこの二つが境界を分ける。
つまり局所的には、

```text id="rqrhnv"
next sign problem
  -> netDrop threshold problem
```

へ変換できた。

これは非常に大きい。
次からは「次が正か非正か」を直接悩むのではなく、**netDrop が threshold を越えるかどうか**を調べればよい。

## True Beam / False Beam / Gap

## True Beam

今回の True Beam はこれ。

```text id="ewxgpl"
-current < netDrop
  -> next positive
```

さらに classifier として、

```text id="usn8x0"
next positive iff -current < netDrop
```

まで入った。

## False Beam

False Beam も classifier になった。

```text id="phb6d0"
next nonpositive iff netDrop <= -current
```

これはかなり強い。
単なる十分条件ではなく、局所的な判定器になっている。

## Gap

Gap は次へ移動した。

もう Gap は、

```text id="b4og5c"
next sign がわからない
```

ではない。

今の Gap は、

```text id="besn35"
netDrop を retention / continuation / drift budget からどう読むか
```

じゃ。

report でも、次の layer は `SourcePressureNetDropInt = retention drop - 2 * continuation drop` を読む方向だと整理されている。

## 注意点

今回も境界は守れておる。

```text id="srh2zu"
time/orbit propagation ではない。
```

```text id="e5qfvn"
arbitrary target transport ではない。
```

```text id="poa6uc"
arbitrary next-margin positivity ではない。
```

```text id="bhgza6"
canonical target selection ではない。
```

```text id="ootc0q"
coverage / aggregation / overlap repair ではない。
```

```text id="rgfglr"
Collatz convergence ではない。
```

これはあくまで、**addressed depth の局所 sign classifier** じゃ。
だが、その局所 classifier はかなり完成した。

## 次の checkpoint 方針

次は **netDrop reading layer** じゃ。

今の classifier はこう。

```text id="tjhdj3"
next positive iff -current < netDrop

next nonpositive iff netDrop <= -current
```

次に Lean に聞くべきは、

```text id="t4qxf6"
SourcePressureNetDropInt n k r j
```

が、既存の retention / continuation / drift-budget 語彙でどう開けるかじゃ。

狙いは次の形。

```text id="u5sgjw"
netDrop = retentionDrop - 2 * continuationDrop
```

これが Beam-facing に読めるなら、次符号 classifier はさらにこうなる。

```text id="z05iit"
next positive iff
  -current < retentionDrop - 2 * continuationDrop
```

```text id="xs4x9q"
next nonpositive iff
  retentionDrop - 2 * continuationDrop <= -current
```

ここまで行くと、Beam の符号分岐が **count / drift / retention / continuation** 側へ接続される。

## 次の Codex 指示

```text id="upapqf"
Checkpoint: petal-211

Main goal:
  Start the Beam-facing netDrop reading layer.  The local sign classifier is now
  available:
    next positive iff -current < netDrop
    next nonpositive iff netDrop <= -current

  The next step is to ask Lean how `SourcePressureNetDropInt n k r j` opens in
  terms of the existing retention / continuation / drift-budget vocabulary.
  Do not prove time/orbit propagation, arbitrary target transport, canonical
  selection, coverage, aggregation, or convergence.

Primary target file:
  DkMath/Collatz/PetalBridge/PressureBeam.lean

Allowed supporting files:
  docs/dev/das-p2l-260607/review/report-petal-211.md

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
  code.  Ask Lean small questions.

Current Core:
  SourcePressureBeamAddressedDepthTarget
  sourcePressureMargin_next_pos_iff_neg_current_lt_netDrop_of_addressedDepthTarget
  sourcePressureMargin_next_nonpos_iff_netDrop_le_neg_current_of_addressedDepthTarget
  sourcePressureMargin_next_pos_of_addressedDepthTarget_of_neg_current_lt_netDrop
  sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_netDrop_le_neg_current

Known Gap:
  The next sign is now locally classified by netDrop, but netDrop itself has not
  yet been read through retention / continuation / drift-budget vocabulary at
  the Beam layer.

Required Lean exploration:

  Step 1:
    Use `#check`, `#print`, or scratch wrappers to inspect the exact definitions
    and existing theorem shapes for:

      SourcePressureNetDropInt
      SourceRetentionDropInt
      SourceContinuationDropInt

    Also inspect any existing theorem that opens `SourcePressureNetDropInt`,
    especially if there is a theorem shaped like:

      SourcePressureNetDropInt n k r j =
        SourceRetentionDropInt n k r j -
          2 * SourceContinuationDropInt n k r j

    Do not guess names.  Let Lean reveal the exact shapes.

  Experiment T1:
    If the definition unfolds directly, add a Beam-facing netDrop expansion
    wrapper at an addressed depth.

    Candidate shape, adjust to actual names and orientations:

      theorem sourcePressureNetDrop_eq_retention_sub_two_mul_continuation_of_addressedDepthTarget
          {n : OddNat} {k r j : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (_haddr : SourcePressureBeamAddressedDepthTarget L j) :
          SourcePressureNetDropInt n k r j =
            SourceRetentionDropInt n k r j -
              2 * SourceContinuationDropInt n k r j

    This should be packaging only.  The addressed hypothesis may be unused; it
    documents that the equation is being read at a Beam-addressed depth.

  Experiment T2:
    If T1 passes, add a True Beam classifier through the expanded netDrop.

    Candidate shape:

      theorem sourcePressureMargin_next_pos_iff_neg_current_lt_retention_sub_two_mul_continuation_of_addressedDepthTarget
          {n : OddNat} {k r j : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (haddr : SourcePressureBeamAddressedDepthTarget L j) :
          0 < SourcePressureMarginInt n k (r + j + 1) ↔
            -SourcePressureMarginInt n k (r + j) <
              SourceRetentionDropInt n k r j -
                2 * SourceContinuationDropInt n k r j

    This should be obtained by combining:
      - the netDrop expansion wrapper;
      - `sourcePressureMargin_next_pos_iff_neg_current_lt_netDrop_of_addressedDepthTarget`.

  Experiment F1:
    Add the False Beam classifier through the expanded netDrop if T1 passes.

      theorem sourcePressureMargin_next_nonpos_iff_retention_sub_two_mul_continuation_le_neg_current_of_addressedDepthTarget
          {n : OddNat} {k r j : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (haddr : SourcePressureBeamAddressedDepthTarget L j) :
          SourcePressureMarginInt n k (r + j + 1) <= 0 ↔
            SourceRetentionDropInt n k r j -
                2 * SourceContinuationDropInt n k r j
              <= -SourcePressureMarginInt n k (r + j)

  Experiment G1:
    If the expansion is not definitional or needs a different orientation,
    record the exact mismatch:
      - different argument order;
      - different naming;
      - expression uses addition with negation instead of subtraction;
      - expression uses Nat then casts to Int;
      - missing theorem;
      - requires an existing lower-module lemma.

    Record as Gap unless Lean proves an obstruction theorem.

Guardrails:
  Do not add:
    - time/orbit propagation;
    - arbitrary target transport;
    - arbitrary next-margin positivity;
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
    2. Exact `#check` / definition shapes discovered for netDrop, retention,
       and continuation.
    3. True Beam facts that passed.
    4. False Beam facts that passed or were packaged.
    5. Gap observations if expansion did not match the expected shape.
    6. Confirmation that this is netDrop reading, not propagation.
    7. One-step-ahead Wise Wolf inference.
    8. Experimental lemma table with passed / failed / under-specified.
    9. Explicit statement that no time/orbit propagation, arbitrary transport,
       arbitrary next-positivity, convergence, coverage, aggregation, or
       overlap repair theorem was added.

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

この次に見たいのは、おそらく count 側の条件分岐じゃ。

もし cp211 で、

```text id="etz6ky"
netDrop = retention - 2 * continuation
```

が Beam-facing に読めれば、次は

```text id="b2my0k"
retention - 2 * continuation > -current
```

をどう判定するかになる。

つまり、

```text id="w4z3z3"
retention + current > 2 * continuation
```

が True Beam 条件。

一方、

```text id="y9o8ku"
retention + current <= 2 * continuation
```

が False Beam 条件。

ここまで行くと、Beam の符号判定は **count inequality** になる。
コラッツ機械語で言えば、次は算術命令から比較命令へ進む段じゃ。

## 総合判断

cp210 により、局所 Beam classifier はかなり閉じた。

```text id="v14nns"
next positive iff -current < netDrop

next nonpositive iff netDrop <= -current
```

次は `netDrop` の内部を読む。
ここから、Beam は `margin` の符号分類から `retention / continuation` の比較分類へ移る。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
index 709ede8d..20d30ce3 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
@@ -514,4 +514,105 @@ theorem sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_netDrop_le_n
     haddr]
   omega

+/--
+Sharp local True Beam condition at an addressed depth.
+
+The next adjacent margin is positive whenever the net drop is larger than the
+negative of the current addressed margin.  This is the sharp form of the
+nonnegative-net-drop theorem: the net drop may be negative, as long as it does
+not cross the current positive margin through zero.
+-/
+theorem sourcePressureMargin_next_pos_of_addressedDepthTarget_of_neg_current_lt_netDrop
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j)
+    (hdrop :
+      -SourcePressureMarginInt n k (r + j) <
+        SourcePressureNetDropInt n k r j) :
+    0 < SourcePressureMarginInt n k (r + j + 1) := by
+  rw [sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget
+    haddr]
+  omega
+
+/--
+Direct local sum form of the sharp True Beam condition.
+
+This is often the most convenient shape after opening the local transition
+equation.
+-/
+theorem sourcePressureMargin_next_pos_of_addressedDepthTarget_of_current_add_netDrop_pos
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j)
+    (hsum :
+      0 <
+        SourcePressureMarginInt n k (r + j) +
+          SourcePressureNetDropInt n k r j) :
+    0 < SourcePressureMarginInt n k (r + j + 1) := by
+  rw [sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget
+    haddr]
+  exact hsum
+
+/--
+A raw Beam seed existentially exposes an addressed depth whose next margin is
+positive under the sharp addressed net-drop condition.
+
+The net-drop hypothesis is still restricted to addressed depths selected from
+the seed witness list.
+-/
+theorem exists_sourcePressureMargin_next_pos_of_beamSeed_of_neg_current_lt_netDrop_at_addressed
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hseed : SourcePressureBeamSeed L)
+    (hdrop :
+      ∀ j,
+        SourcePressureBeamAddressedDepthTarget L j →
+          -SourcePressureMarginInt n k (r + j) <
+            SourcePressureNetDropInt n k r j) :
+    ∃ j,
+      SourcePressureBeamAddressedDepthTarget L j ∧
+        0 < SourcePressureMarginInt n k (r + j + 1) := by
+  rcases exists_sourcePressureBeamAddressedDepthTarget_of_seed hseed with
+    ⟨j, haddr⟩
+  exact
+    ⟨j,
+      haddr,
+      sourcePressureMargin_next_pos_of_addressedDepthTarget_of_neg_current_lt_netDrop
+        haddr (hdrop j haddr)⟩
+
+/--
+Sharp local True Beam classifier at an addressed depth.
+
+This is a local arithmetic classifier for the next sign at the addressed edge:
+after opening the transition equation, next positivity is exactly
+`-current < netDrop`.
+-/
+theorem sourcePressureMargin_next_pos_iff_neg_current_lt_netDrop_of_addressedDepthTarget
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
+    0 < SourcePressureMarginInt n k (r + j + 1) ↔
+      -SourcePressureMarginInt n k (r + j) <
+        SourcePressureNetDropInt n k r j := by
+  rw [sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget
+    haddr]
+  omega
+
+/--
+Sharp local False Beam classifier at an addressed depth.
+
+The next adjacent margin is nonpositive exactly when the net drop is at most
+the negative of the current margin.
+-/
+theorem sourcePressureMargin_next_nonpos_iff_netDrop_le_neg_current_of_addressedDepthTarget
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
+    SourcePressureMarginInt n k (r + j + 1) ≤ 0 ↔
+      SourcePressureNetDropInt n k r j ≤
+        -SourcePressureMarginInt n k (r + j) := by
+  rw [sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget
+    haddr]
+  omega
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-210.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-210.md
new file mode 100644
index 00000000..5b1dcaaf
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-210.md
@@ -0,0 +1,213 @@
+# report-petal-210
+
+## Situation
+
+Checkpoint `petal-210` refines the local sign-reading layer from cp209.
+
+The previous split was:
+
+```text
+True Beam:
+  current positive + netDrop >= 0 -> next positive
+
+False Beam:
+  netDrop <= -current -> next nonpositive
+```
+
+This checkpoint sharpens the True Beam side:
+
+```text
+-current < netDrop -> next positive
+```
+
+This allows a negative net drop as long as it is not large enough to cross zero.
+
+## True Beam Facts
+
+Implemented:
+
+```lean
+theorem sourcePressureMargin_next_pos_of_addressedDepthTarget_of_neg_current_lt_netDrop
+```
+
+Meaning:
+
+```text
+AddressedDepthTarget L j
+  and -current margin < netDrop
+  -> next margin > 0
+```
+
+Implemented:
+
+```lean
+theorem sourcePressureMargin_next_pos_of_addressedDepthTarget_of_current_add_netDrop_pos
+```
+
+Meaning:
+
+```text
+AddressedDepthTarget L j
+  and current margin + netDrop > 0
+  -> next margin > 0
+```
+
+Implemented:
+
+```lean
+theorem exists_sourcePressureMargin_next_pos_of_beamSeed_of_neg_current_lt_netDrop_at_addressed
+```
+
+Meaning:
+
+```text
+SourcePressureBeamSeed L
+  and every addressed depth satisfies -current < netDrop
+  -> exists addressed j whose next margin is positive
+```
+
+The universal hypothesis remains restricted to addressed depths.
+
+## Bonus Local Classifiers
+
+Lean also accepted the exact local `iff` classifiers:
+
+```lean
+theorem sourcePressureMargin_next_pos_iff_neg_current_lt_netDrop_of_addressedDepthTarget
+```
+
+and
+
+```lean
+theorem sourcePressureMargin_next_nonpos_iff_netDrop_le_neg_current_of_addressedDepthTarget
+```
+
+These classify the next sign at the addressed edge:
+
+```text
+next positive iff -current < netDrop
+next nonpositive iff netDrop <= -current
+```
+
+This is still purely local arithmetic after opening the transition equation.
+
+## False Beam Boundary
+
+The existing fall-out theorem remains the local False Beam boundary:
+
+```lean
+theorem sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_netDrop_le_neg_current
+```
+
+The bonus iff theorem packages the same boundary as an exact classifier:
+
+```text
+next nonpositive iff netDrop <= -current
+```
+
+No global failure or propagation theorem was added.
+
+## Gap Observations
+
+The following remain under-specified:
+
+```text
+SourcePressureBeamAddressedDepthTarget L j
+  -> next margin > 0
+```
+
+```text
+SourcePressureBeamAddressedDepthTarget L j
+  -> next margin <= 0
+```
+
+An addressed target gives current positivity, but the next sign is decided by
+the comparison between `netDrop` and `-current`.  Without that comparison, Lean
+does not select a sign.
+
+## Experimental Lemma Table
+
+| experiment | theorem | status | note |
+| --- | --- | --- | --- |
+| T1 | `sourcePressureMargin_next_pos_of_addressedDepthTarget_of_neg_current_lt_netDrop` | passed | sharp local True Beam condition |
+| T2 | `sourcePressureMargin_next_pos_of_addressedDepthTarget_of_current_add_netDrop_pos` | passed | direct sum condition |
+| T3 | `exists_sourcePressureMargin_next_pos_of_beamSeed_of_neg_current_lt_netDrop_at_addressed` | passed | existential addressed seed version |
+| F1 | existing fall-out theorem | available | `netDrop <= -current -> next <= 0` |
+| bonus | `sourcePressureMargin_next_pos_iff_neg_current_lt_netDrop_of_addressedDepthTarget` | passed | exact True classifier |
+| bonus | `sourcePressureMargin_next_nonpos_iff_netDrop_le_neg_current_of_addressedDepthTarget` | passed | exact False classifier |
+| G1 | next positive from addressed target alone | under-specified | netDrop comparison missing |
+| G2 | next nonpositive from addressed target alone | under-specified | netDrop comparison missing |
+
+## Sharp Local Reading, Not Propagation
+
+This checkpoint proves only local sign facts at one addressed pressure-depth
+edge.  It does not move an orbit, extend a time path, or choose a canonical
+next target.
+
+No theorem was added for:
+
+- time/orbit propagation;
+- arbitrary target transport;
+- arbitrary margin positivity;
+- arbitrary next-margin positivity;
+- canonical target selection;
+- global coverage;
+- convergence;
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
+The local sign classifier is now essentially complete:
+
+```text
+True:
+  -current < netDrop
+
+False:
+  netDrop <= -current
+```
+
+The next useful layer is to read `netDrop` itself:
+
+```text
+SourcePressureNetDropInt
+  = retention drop - 2 * continuation drop
+```
+
+The likely next checkpoint should connect these sharp sign classifiers to the
+existing retention / continuation / drift-budget vocabulary, still locally at
+the addressed edge.
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
