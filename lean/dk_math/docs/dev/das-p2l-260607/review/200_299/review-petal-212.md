# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam

gch: fc3812a9cf2117583da490371b9c7a551b73bb39

## Report

cp211 完了です。

[PressureBeam.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean) に、Beam-facing netDrop reading layer を追加しました。

追加 theorem:

- `sourcePressureNetDrop_eq_retention_sub_two_mul_continuation_of_addressedDepthTarget`
- `sourcePressureMargin_next_pos_iff_neg_current_lt_retCont_of_addressedDepthTarget`
- `sourcePressureMargin_next_nonpos_iff_retCont_le_neg_current_of_addressedDepthTarget`

`SourcePressureNetDropInt` は定義そのものが

```lean
SourceRetentionDropInt n k r j -
  2 * SourceContinuationDropInt n k r j
```

なので、展開 wrapper は `rfl` で通りました。

これで局所 classifier は次の形まで読めます。

```text
next positive iff -current < retentionDrop - 2 * continuationDrop
next nonpositive iff retentionDrop - 2 * continuationDrop <= -current
```

レポート:
[report-petal-211.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-211.md)

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureBeam` passed
- `lake build DkMath.Collatz.PetalBridge` passed
- 指定 pressure files の `sorry/admit` check: no matches
- `git diff --check` passed

既知の unrelated warning として `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` warning は残っています。

## Review

## 結論

**採用** じゃ。

cp211 は、局所 Beam classifier を **netDrop 比較**から **retention / continuation 比較**へ一段降ろした checkpoint じゃ。

追加された theorem は次の 3 本。

```lean
sourcePressureNetDrop_eq_retention_sub_two_mul_continuation_of_addressedDepthTarget

sourcePressureMargin_next_pos_iff_neg_current_lt_retCont_of_addressedDepthTarget

sourcePressureMargin_next_nonpos_iff_retCont_le_neg_current_of_addressedDepthTarget
```

`SourcePressureNetDropInt` が定義上そのまま

```text
SourceRetentionDropInt - 2 * SourceContinuationDropInt
```

だったので、展開 wrapper が `rfl` で通っている。これは非常に良い。Lean に聞いた結果、Gap ではなく定義展開として Core 化できた。

## 実装レビュー

実装は安全で、層の意味もはっきりしている。

まず netDrop 展開。

```lean
theorem sourcePressureNetDrop_eq_retention_sub_two_mul_continuation_of_addressedDepthTarget
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (_haddr : SourcePressureBeamAddressedDepthTarget L j) :
    SourcePressureNetDropInt n k r j =
      SourceRetentionDropInt n k r j -
        2 * SourceContinuationDropInt n k r j := by
  rfl
```

ここでも `_haddr` は未使用じゃが、意味はある。
算術恒等式そのものには不要だが、Beam API としては **addressed depth で読んでいる**ことを明示している。

次に True classifier。

```lean
sourcePressureMargin_next_pos_iff_neg_current_lt_retCont_of_addressedDepthTarget
```

これで、

```text
next positive iff -current < retentionDrop - 2 * continuationDrop
```

が読める。

False classifier も対称に通っている。

```lean
sourcePressureMargin_next_nonpos_iff_retCont_le_neg_current_of_addressedDepthTarget
```

これで、

```text
next nonpositive iff retentionDrop - 2 * continuationDrop <= -current
```

が読める。

この 2 本により、局所 sign classifier は `netDrop` という中間語を越えて、retention / continuation の比較問題へ降りた。

## 数学的意味

ここで見えてきたものは大きい。

cp210 までは、

```text
next positive iff -current < netDrop

next nonpositive iff netDrop <= -current
```

だった。

cp211 で、それがこうなった。

```text
next positive iff -current < retentionDrop - 2 * continuationDrop

next nonpositive iff retentionDrop - 2 * continuationDrop <= -current
```

つまり、次符号の判定が **netDrop の符号問題**から、より構造的な

```text
retention / continuation の比較問題
```

になった。

DkMath 的にはこうじゃ。

```text
Core:
  netDrop = retentionDrop - 2 * continuationDrop

True Beam:
  retentionDrop - 2 * continuationDrop が -current を超える

False Beam:
  retentionDrop - 2 * continuationDrop が -current 以下

Gap:
  この比較を count / drift-budget からどう評価するか
```

Gap が一段具体化した。
これはかなり良い進展じゃ。

## True Beam / False Beam / Gap

## True Beam

今回の True Beam はこれ。

```text
next positive iff -current < retentionDrop - 2 * continuationDrop
```

これは、負の continuation penalty を含んでも、retention と current margin がそれを上回るなら positive に残る、という局所判定器じゃ。

## False Beam

False Beam はこれ。

```text
next nonpositive iff retentionDrop - 2 * continuationDrop <= -current
```

これは、continuation 側の重みが retention + current を押し潰すと非正へ落ちる、という境界じゃ。

## Gap

残る Gap は report の通り、定義展開ではない。
次の比較問題じゃ。

```text
-current < retentionDrop - 2 * continuationDrop
```

同値変形すれば、

```text
retentionDrop + current > 2 * continuationDrop
```

False 側は、

```text
retentionDrop + current <= 2 * continuationDrop
```

ここから先は、count / drift-budget 側の事実が必要になる。

## 注意点

今回も境界は守れている。

```text
time/orbit propagation ではない。
```

```text
arbitrary target transport ではない。
```

```text
arbitrary next-margin positivity ではない。
```

```text
canonical target selection ではない。
```

```text
global coverage / aggregation / overlap repair ではない。
```

```text
Collatz convergence ではない。
```

これはあくまで **Beam-facing netDrop reading** じゃ。
しかし、次に count inequality へ進むための準備としてはかなり強い。

## 次の checkpoint 方針

次は、report の一歩先推論どおり、

```text
-current < retentionDrop - 2 * continuationDrop
```

を

```text
retentionDrop + current > 2 * continuationDrop
```

へ変形する局所 count inequality layer じゃ。

False 側も同様に、

```text
retentionDrop - 2 * continuationDrop <= -current
```

を

```text
retentionDrop + current <= 2 * continuationDrop
```

へ変形する。

これはまだ count の中身を評価する段ではない。
まずは **比較式の正規形** を Lean に固定する段じゃ。

## 次の Codex 指示

```text
Checkpoint: petal-212

Main goal:
  Convert the Beam-facing retention/continuation classifier into normalized
  count inequalities:
    next positive iff retentionDrop + current > 2 * continuationDrop
    next nonpositive iff retentionDrop + current <= 2 * continuationDrop

  Keep this local to an addressed pressure-depth edge.  Do not prove time/orbit
  propagation, arbitrary target transport, canonical selection, coverage,
  aggregation, or convergence.

Primary target file:
  DkMath/Collatz/PetalBridge/PressureBeam.lean

Allowed supporting files:
  docs/dev/das-p2l-260607/review/report-petal-212.md

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
  sourcePressureNetDrop_eq_retention_sub_two_mul_continuation_of_addressedDepthTarget
  sourcePressureMargin_next_pos_iff_neg_current_lt_retCont_of_addressedDepthTarget
  sourcePressureMargin_next_nonpos_iff_retCont_le_neg_current_of_addressedDepthTarget

Known Gap:
  The sign classifier has been expanded through retention / continuation, but
  the comparison has not yet been normalized into the count-style inequalities:
    retentionDrop + current > 2 * continuationDrop
    retentionDrop + current <= 2 * continuationDrop

Required experiments:

  Experiment T1:
    Prove the normalized True Beam classifier.

      theorem sourcePressureMargin_next_pos_iff_retention_add_current_gt_two_mul_continuation_of_addressedDepthTarget
          {n : OddNat} {k r j : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (haddr : SourcePressureBeamAddressedDepthTarget L j) :
          0 < SourcePressureMarginInt n k (r + j + 1) ↔
            2 * SourceContinuationDropInt n k r j <
              SourceRetentionDropInt n k r j +
                SourcePressureMarginInt n k (r + j)

    Preferred orientation:
      Use `<` with `2 * continuation` on the left if it is easier for Lean.
      The mathematical reading is:
        retentionDrop + current > 2 * continuationDrop.

    Proof strategy:
      - start from
          `sourcePressureMargin_next_pos_iff_neg_current_lt_retCont_of_addressedDepthTarget haddr`;
      - use `omega` to transform the Int inequality.

  Experiment F1:
    Prove the normalized False Beam classifier.

      theorem sourcePressureMargin_next_nonpos_iff_retention_add_current_le_two_mul_continuation_of_addressedDepthTarget
          {n : OddNat} {k r j : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (haddr : SourcePressureBeamAddressedDepthTarget L j) :
          SourcePressureMarginInt n k (r + j + 1) <= 0 ↔
            SourceRetentionDropInt n k r j +
              SourcePressureMarginInt n k (r + j)
              <= 2 * SourceContinuationDropInt n k r j

    Proof strategy:
      - start from
          `sourcePressureMargin_next_nonpos_iff_retCont_le_neg_current_of_addressedDepthTarget haddr`;
      - use `omega`.

  Experiment T2:
    If T1 passes, add the one-way True Beam wrapper:

      theorem sourcePressureMargin_next_pos_of_addressedDepthTarget_of_two_mul_continuation_lt_retention_add_current
          {n : OddNat} {k r j : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (haddr : SourcePressureBeamAddressedDepthTarget L j)
          (hineq :
            2 * SourceContinuationDropInt n k r j <
              SourceRetentionDropInt n k r j +
                SourcePressureMarginInt n k (r + j)) :
          0 < SourcePressureMarginInt n k (r + j + 1)

  Experiment F2:
    If F1 passes, add the one-way False Beam wrapper:

      theorem sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_retention_add_current_le_two_mul_continuation
          {n : OddNat} {k r j : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (haddr : SourcePressureBeamAddressedDepthTarget L j)
          (hineq :
            SourceRetentionDropInt n k r j +
              SourcePressureMarginInt n k (r + j)
              <= 2 * SourceContinuationDropInt n k r j) :
          SourcePressureMarginInt n k (r + j + 1) <= 0

  Experiment G1:
    In scratch only, try to prove either next sign from `haddr` alone.
    Record as Gap because the retention/continuation comparison is missing.

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
    2. True Beam normalized classifier facts that passed.
    3. False Beam normalized classifier facts that passed.
    4. Gap observations for sign claims without the normalized inequality.
    5. Confirmation that this is inequality normalization, not propagation.
    6. One-step-ahead Wise Wolf inference.
    7. Experimental lemma table with passed / failed / under-specified.
    8. Explicit statement that no time/orbit propagation, arbitrary transport,
       arbitrary positivity, arbitrary next-positivity, convergence, coverage,
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

cp212 が通ると、局所 Beam classifier はこうなる。

```text
True Beam:
  2 * continuationDrop < retentionDrop + current

False Beam:
  retentionDrop + current <= 2 * continuationDrop
```

これはかなり読みやすい。
次に進むなら、`retentionDrop` と `continuationDrop` の定義そのもの、つまり

```text
current retention mass - next retention mass
```

```text
current continuation mass - next continuation mass
```

へ降りる。

その先では、

```text
retention mass + current pressure
```

と

```text
2 * continuation mass
```

の比較になるはずじゃ。

ここから、ようやく Collatz の pressure 会計が **mass comparison** として読めるようになる。

## 総合判断

cp211 は順調じゃ。
Beam は今、

```text
next sign
  -> netDrop threshold
  -> retention / continuation threshold
```

まで降りた。

次は threshold を count inequality として正規化する。
そこまで通れば、DkMath の True / False Beams は、かなり機械語らしい比較命令になる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
index 20d30ce3..3d38f8a8 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
@@ -615,4 +615,61 @@ theorem sourcePressureMargin_next_nonpos_iff_netDrop_le_neg_current_of_addressed
     haddr]
   omega
 
+/--
+Beam-facing expansion of the local net pressure drop at an addressed depth.
+
+This is only the definition of `SourcePressureNetDropInt` read through the Beam
+addressing API.  The addressed hypothesis is intentionally unused by the
+arithmetic identity; it records that the equation is being used at a
+Beam-selected pressure-depth edge.
+-/
+theorem sourcePressureNetDrop_eq_retention_sub_two_mul_continuation_of_addressedDepthTarget
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (_haddr : SourcePressureBeamAddressedDepthTarget L j) :
+    SourcePressureNetDropInt n k r j =
+      SourceRetentionDropInt n k r j -
+        2 * SourceContinuationDropInt n k r j := by
+  rfl
+
+/--
+True Beam classifier with net drop expanded into retention and continuation
+drops.
+
+At an addressed edge, the next margin is positive exactly when the expanded
+quantity `retentionDrop - 2 * continuationDrop` is larger than `-current`.
+-/
+theorem sourcePressureMargin_next_pos_iff_neg_current_lt_retCont_of_addressedDepthTarget
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
+    0 < SourcePressureMarginInt n k (r + j + 1) ↔
+      -SourcePressureMarginInt n k (r + j) <
+        SourceRetentionDropInt n k r j -
+          2 * SourceContinuationDropInt n k r j := by
+  rw [sourcePressureMargin_next_pos_iff_neg_current_lt_netDrop_of_addressedDepthTarget
+    haddr]
+  rw [sourcePressureNetDrop_eq_retention_sub_two_mul_continuation_of_addressedDepthTarget
+    haddr]
+
+/--
+False Beam classifier with net drop expanded into retention and continuation
+drops.
+
+At an addressed edge, the next margin is nonpositive exactly when the expanded
+quantity `retentionDrop - 2 * continuationDrop` is at most `-current`.
+-/
+theorem sourcePressureMargin_next_nonpos_iff_retCont_le_neg_current_of_addressedDepthTarget
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
+    SourcePressureMarginInt n k (r + j + 1) ≤ 0 ↔
+      SourceRetentionDropInt n k r j -
+          2 * SourceContinuationDropInt n k r j
+        ≤ -SourcePressureMarginInt n k (r + j) := by
+  rw [sourcePressureMargin_next_nonpos_iff_netDrop_le_neg_current_of_addressedDepthTarget
+    haddr]
+  rw [sourcePressureNetDrop_eq_retention_sub_two_mul_continuation_of_addressedDepthTarget
+    haddr]
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-211.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-211.md
new file mode 100644
index 00000000..362fdcd6
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-211.md
@@ -0,0 +1,199 @@
+# report-petal-211
+
+## Situation
+
+Checkpoint `petal-211` starts the Beam-facing netDrop reading layer.
+
+The local sign classifier from cp210 says:
+
+```text
+next positive iff -current < netDrop
+next nonpositive iff netDrop <= -current
+```
+
+This checkpoint opens `netDrop` into its retention / continuation components:
+
+```text
+netDrop = retentionDrop - 2 * continuationDrop
+```
+
+The result is still local to one addressed pressure-depth edge.
+
+## Definition Shapes Discovered
+
+The relevant definitions in `PressureDecay` are:
+
+```lean
+noncomputable def SourceRetentionDropInt
+    (n : OddNat) (k r j : ℕ) : ℤ :=
+  (orbitWindowRetentionMassPow2 n k (r + j) : ℤ) -
+    (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ)
+```
+
+```lean
+noncomputable def SourceContinuationDropInt
+    (n : OddNat) (k r j : ℕ) : ℤ :=
+  (orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) -
+    (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ)
+```
+
+```lean
+noncomputable def SourcePressureNetDropInt
+    (n : OddNat) (k r j : ℕ) : ℤ :=
+  SourceRetentionDropInt n k r j -
+    2 * SourceContinuationDropInt n k r j
+```
+
+The expected expansion is definitional.  No lower-module theorem was required.
+
+## True Beam Facts
+
+Implemented:
+
+```lean
+theorem sourcePressureNetDrop_eq_retention_sub_two_mul_continuation_of_addressedDepthTarget
+```
+
+This is a Beam-facing wrapper around the definitional equation:
+
+```text
+SourcePressureNetDropInt
+  = SourceRetentionDropInt - 2 * SourceContinuationDropInt
+```
+
+The addressed target hypothesis is intentionally unused by the arithmetic
+identity.  It records that the equation is being read at a Beam-selected edge.
+
+Implemented:
+
+```lean
+theorem sourcePressureMargin_next_pos_iff_neg_current_lt_retCont_of_addressedDepthTarget
+```
+
+This packages the True Beam classifier through retention / continuation:
+
+```text
+next positive iff -current < retentionDrop - 2 * continuationDrop
+```
+
+## False Beam Fact
+
+Implemented:
+
+```lean
+theorem sourcePressureMargin_next_nonpos_iff_retCont_le_neg_current_of_addressedDepthTarget
+```
+
+This packages the False Beam classifier through retention / continuation:
+
+```text
+next nonpositive iff retentionDrop - 2 * continuationDrop <= -current
+```
+
+## Experimental Lemma Table
+
+| experiment | theorem | status | note |
+| --- | --- | --- | --- |
+| Step 1 | `SourcePressureNetDropInt` definition | inspected | definitional `retention - 2 * continuation` |
+| Step 1 | `SourceRetentionDropInt` definition | inspected | current retention minus next retention |
+| Step 1 | `SourceContinuationDropInt` definition | inspected | current continuation minus next continuation |
+| T1 | `sourcePressureNetDrop_eq_retention_sub_two_mul_continuation_of_addressedDepthTarget` | passed | `rfl` |
+| T2 | `sourcePressureMargin_next_pos_iff_neg_current_lt_retCont_of_addressedDepthTarget` | passed | True classifier with expanded netDrop |
+| F1 | `sourcePressureMargin_next_nonpos_iff_retCont_le_neg_current_of_addressedDepthTarget` | passed | False classifier with expanded netDrop |
+
+## Gap Observations
+
+No mismatch was found for the expansion:
+
+```text
+netDrop = retentionDrop - 2 * continuationDrop
+```
+
+The remaining Gap is not definitional.  It is now a comparison problem:
+
+```text
+-current < retentionDrop - 2 * continuationDrop
+```
+
+or equivalently:
+
+```text
+retentionDrop + current > 2 * continuationDrop
+```
+
+That comparison is not yet connected to counting / drift-budget facts in the
+Beam layer.
+
+## NetDrop Reading, Not Propagation
+
+This checkpoint only opens the local arithmetic expression used by the sign
+classifier.  It does not move between time steps, select a canonical next
+target, or aggregate witness lists.
+
+No theorem was added for:
+
+- time/orbit propagation;
+- arbitrary target transport;
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
+The next natural checkpoint is to convert the expanded comparison into a count
+inequality:
+
+```text
+-current < retentionDrop - 2 * continuationDrop
+```
+
+should become:
+
+```text
+retentionDrop + current > 2 * continuationDrop
+```
+
+and the False side should become:
+
+```text
+retentionDrop + current <= 2 * continuationDrop
+```
+
+This would move the Beam classifier from "netDrop sign" to "retention /
+continuation count comparison", still locally at the addressed edge.
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
