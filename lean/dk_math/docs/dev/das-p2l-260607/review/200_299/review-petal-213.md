# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam

gch: ab6673c21e993ca2ee22e48ed67775c200a177b4

## Report

cp212 完了です。

[PressureBeam.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean:681) に、Beam の retention / continuation classifier を正規化する 4 定理を追加しました。

主な追加:

- `sourcePressureMargin_next_pos_iff_two_cont_lt_ret_add_current_of_addressedDepthTarget`
- `sourcePressureMargin_next_nonpos_iff_ret_add_current_le_two_cont_of_addressedDepthTarget`
- `sourcePressureMargin_next_pos_of_addressedDepthTarget_of_two_cont_lt_ret_add_current`
- `sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_ret_add_current_le_two_cont`

これで局所 addressed edge について、

```text
True:  2 * continuationDrop < retentionDrop + current
False: retentionDrop + current <= 2 * continuationDrop
```

として読めるようになりました。伝播・coverage・aggregation・convergence には踏み込んでいません。

[report-petal-212.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-212.md:1) も追加済みです。

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureBeam` passed
- `lake build DkMath.Collatz.PetalBridge` passed
- 指定 pressure files の `sorry/admit` grep: no matches
- `git diff --check` passed

既知の unrelated warning として `ZsigmondyCyclotomicResearch.lean:152` の既存 `sorry` 警告は出ています。

## Review

## 結論

**採用** じゃ。
cp212 は、局所 Beam classifier を **count inequality の形へ正規化**できた重要 checkpoint じゃ。

追加された主 theorem は次の 4 本。

```lean id="qf138v"
sourcePressureMargin_next_pos_iff_two_cont_lt_ret_add_current_of_addressedDepthTarget

sourcePressureMargin_next_nonpos_iff_ret_add_current_le_two_cont_of_addressedDepthTarget

sourcePressureMargin_next_pos_of_addressedDepthTarget_of_two_cont_lt_ret_add_current

sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_ret_add_current_le_two_cont
```

これで、addressed edge における True / False Beam がこう読めるようになった。

```text id="yoxayc"
True:
  2 * continuationDrop < retentionDrop + current
```

```text id="9ow2uh"
False:
  retentionDrop + current <= 2 * continuationDrop
```

これはかなり良い。`netDrop` 比較から、より観測しやすい **retention / continuation / current margin の比較命令**へ落ちた。

## 実装レビュー

今回の True classifier はよい。

```lean id="yjuoh7"
theorem sourcePressureMargin_next_pos_iff_two_cont_lt_ret_add_current_of_addressedDepthTarget
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
    0 < SourcePressureMarginInt n k (r + j + 1) ↔
      2 * SourceContinuationDropInt n k r j <
        SourceRetentionDropInt n k r j +
          SourcePressureMarginInt n k (r + j)
```

これは、cp211 の

```text id="w3nb4i"
-current < retentionDrop - 2 * continuationDrop
```

を `omega` で

```text id="3h81nm"
2 * continuationDrop < retentionDrop + current
```

へ移したものじゃ。
向きも読みやすい。比較命令としては、左に continuation penalty、右に retention + current が来るので直感的じゃ。

False classifier も対称に良い。

```lean id="y65d8y"
theorem sourcePressureMargin_next_nonpos_iff_ret_add_current_le_two_cont_of_addressedDepthTarget
    {n : OddNat} {k r j : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
    SourcePressureMarginInt n k (r + j + 1) ≤ 0 ↔
      SourceRetentionDropInt n k r j +
          SourcePressureMarginInt n k (r + j)
        ≤ 2 * SourceContinuationDropInt n k r j
```

これで True / False が綺麗に境界を共有する。

```text id="aimfo2"
2 * continuationDrop < retentionDrop + current
```

か、

```text id="y7ddxi"
retentionDrop + current <= 2 * continuationDrop
```

か。

整数順序では、この二つが局所的な二分を作る。
これは DkMath の Beam x2 にかなり合っている。

## 数学的意味

cp212 により、次符号問題はこう変形された。

以前は、

```text id="c7usrk"
next sign
  -> netDrop threshold
```

だった。

今は、

```text id="tx2ad2"
next sign
  -> retention / continuation count comparison
```

になった。

つまり、局所 Beam の命令語はこう読める。

```text id="jj9srj"
continuation 側の 2 倍コストより、
retention drop + current margin が大きければ True Beam 継続。
```

```text id="sdqpmi"
continuation 側の 2 倍コストが、
retention drop + current margin 以上なら False Beam へ落ちる。
```

かなり「機械語バイナリコード」らしくなってきた。
次はこの `retentionDrop` と `continuationDrop` の中身、つまり mass difference へ降りる段じゃ。

## True Beam / False Beam / Gap

## True Beam

今回の True Beam はこれ。

```text id="p35wkm"
2 * continuationDrop < retentionDrop + current
  -> next positive
```

さらに `iff` として、

```text id="u3vy3k"
next positive iff 2 * continuationDrop < retentionDrop + current
```

まで入った。

## False Beam

False Beam はこれ。

```text id="ggckwk"
retentionDrop + current <= 2 * continuationDrop
  -> next nonpositive
```

さらに `iff` として、

```text id="wlrlma"
next nonpositive iff retentionDrop + current <= 2 * continuationDrop
```

まで入った。

これは局所 addressed edge の判定器として非常に明確じゃ。

## Gap

Gap はさらに下へ移動した。

もう Gap は、

```text id="ucyeg5"
next sign の条件が分からない
```

ではない。

今の Gap は、

```text id="egkk0r"
retentionDrop と continuationDrop を mass difference として読んだとき、
この比較がどう評価されるか
```

じゃ。

report でも、次は `retentionDrop = currentRetentionMass - nextRetentionMass` と `continuationDrop = currentContinuationMass - nextContinuationMass` へ展開するのが自然だと整理されている。

## 注意点

今回も境界は守られている。

```text id="h4mzmx"
time / orbit propagation ではない。
```

```text id="krjfoj"
arbitrary target transport ではない。
```

```text id="z82y21"
arbitrary positivity / arbitrary next-positivity ではない。
```

```text id="g0g1qq"
canonical target selection ではない。
```

```text id="aemohp"
coverage / aggregation / overlap repair ではない。
```

```text id="s5kr59"
Collatz convergence ではない。
```

これは **inequality normalization** じゃ。
だが、この正規化によって次の mass comparison layer が見えるようになった。

## 次の checkpoint 方針

次は、report の Wise Wolf inference 通り、`retentionDrop` と `continuationDrop` を mass difference として開く。

まず読むべき定義はこれ。

```text id="wnt2lk"
retentionDrop
  = currentRetentionMass - nextRetentionMass
```

```text id="h4v9n2"
continuationDrop
  = currentContinuationMass - nextContinuationMass
```

これを Beam-facing に wrapper 化する。

その後、True classifier を mass difference へ変形する。

```text id="f7flfp"
2 * (currentContinuationMass - nextContinuationMass)
  <
(currentRetentionMass - nextRetentionMass) + currentMargin
```

False classifier はこれ。

```text id="pwdw0t"
(currentRetentionMass - nextRetentionMass) + currentMargin
  <=
2 * (currentContinuationMass - nextContinuationMass)
```

ここまで通れば、Beam classifier は「drop 比較」から「mass 差分比較」へ移る。

## 次の Codex 指示

```text id="hlz3cl"
Checkpoint: petal-213

Main goal:
  Open the normalized retention/continuation classifier into mass-difference
  form.  The cp212 classifier is:

    True:
      2 * continuationDrop < retentionDrop + current

    False:
      retentionDrop + current <= 2 * continuationDrop

  The next step is to read:
    retentionDrop = currentRetentionMass - nextRetentionMass
    continuationDrop = currentContinuationMass - nextContinuationMass

  Keep this local to an addressed pressure-depth edge.  Do not prove time/orbit
  propagation, arbitrary target transport, canonical selection, coverage,
  aggregation, overlap repair, or convergence.

Primary target file:
  DkMath/Collatz/PetalBridge/PressureBeam.lean

Allowed supporting files:
  docs/dev/das-p2l-260607/review/report-petal-213.md

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
  sourcePressureMargin_next_pos_iff_two_cont_lt_ret_add_current_of_addressedDepthTarget
  sourcePressureMargin_next_nonpos_iff_ret_add_current_le_two_cont_of_addressedDepthTarget
  sourcePressureMargin_next_pos_of_addressedDepthTarget_of_two_cont_lt_ret_add_current
  sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_ret_add_current_le_two_cont

Known Gap:
  The classifier is normalized in terms of retentionDrop and continuationDrop,
  but these drops have not yet been opened at the Beam layer into current/next
  mass differences.

Required Lean exploration:

  Step 1:
    Use `#check`, `#print`, or scratch wrappers to inspect exact definitions
    and theorem shapes for:

      SourceRetentionDropInt
      SourceContinuationDropInt
      orbitWindowRetentionMassPow2
      orbitWindowContinuationSiblingMassPow2

    Confirm the exact index shape:
      r + j
      r + j + 1

    Do not guess names or orientations.  Let Lean decide.

  Experiment T1:
    Add a Beam-facing retention drop expansion wrapper.

      theorem sourceRetentionDrop_eq_current_sub_next_mass_of_addressedDepthTarget
          {n : OddNat} {k r j : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (_haddr : SourcePressureBeamAddressedDepthTarget L j) :
          SourceRetentionDropInt n k r j =
            (orbitWindowRetentionMassPow2 n k (r + j) : ℤ) -
              (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ)

    Expected: likely `rfl`.

  Experiment T2:
    Add a Beam-facing continuation drop expansion wrapper.

      theorem sourceContinuationDrop_eq_current_sub_next_mass_of_addressedDepthTarget
          {n : OddNat} {k r j : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (_haddr : SourcePressureBeamAddressedDepthTarget L j) :
          SourceContinuationDropInt n k r j =
            (orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) -
              (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ)

    Expected: likely `rfl`.

  Experiment T3:
    If T1 and T2 pass, add the True Beam mass-difference classifier.

      theorem sourcePressureMargin_next_pos_iff_two_contMassDiff_lt_retMassDiff_add_current_of_addressedDepthTarget
          {n : OddNat} {k r j : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (haddr : SourcePressureBeamAddressedDepthTarget L j) :
          0 < SourcePressureMarginInt n k (r + j + 1) ↔
            2 *
              ((orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) -
                (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ))
              <
            ((orbitWindowRetentionMassPow2 n k (r + j) : ℤ) -
              (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ)) +
              SourcePressureMarginInt n k (r + j)

    Keep the expression orientation if Lean prefers a slightly different but
    equivalent normalized form.  Use `rw` and `omega` only if needed.

  Experiment F1:
    Add the False Beam mass-difference classifier.

      theorem sourcePressureMargin_next_nonpos_iff_retMassDiff_add_current_le_two_contMassDiff_of_addressedDepthTarget
          {n : OddNat} {k r j : ℕ}
          {L : List (SourcePressureLocalIslandWitness n k r)}
          (haddr : SourcePressureBeamAddressedDepthTarget L j) :
          SourcePressureMarginInt n k (r + j + 1) <= 0 ↔
            ((orbitWindowRetentionMassPow2 n k (r + j) : ℤ) -
              (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ)) +
              SourcePressureMarginInt n k (r + j)
              <=
            2 *
              ((orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) -
                (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ))

  Experiment G1:
    If mass expansion is not definitional, record exact mismatch:
      - different mass function name;
      - different index shape;
      - Nat-to-Int cast mismatch;
      - expression orientation differs;
      - lower lemma required.

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
    2. Exact definition shapes discovered for retention/continuation mass
       differences.
    3. True Beam mass-difference classifier facts that passed.
    4. False Beam mass-difference classifier facts that passed.
    5. Gap observations if mass expansion did not match expected shape.
    6. Confirmation that this is mass-difference reading, not propagation.
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

cp213 が通ると、Beam classifier はこうなる。

```text id="byh0y3"
True:
  2 * (currentContinuationMass - nextContinuationMass)
    <
  (currentRetentionMass - nextRetentionMass) + currentMargin
```

```text id="u6ty2d"
False:
  (currentRetentionMass - nextRetentionMass) + currentMargin
    <=
  2 * (currentContinuationMass - nextContinuationMass)
```

その次は、さらに式を移項して、

```text id="z2qch1"
2 * currentContinuationMass + nextRetentionMass
```

と

```text id="arkwqq"
currentRetentionMass + currentMargin + 2 * nextContinuationMass
```

の比較に変形できる可能性がある。

これはかなり「mass balance」らしい形じゃ。

つまり次の次では、Beam は **drop classifier** から **mass balance classifier** へ進む。

## 総合判断

cp212 はかなり順調。
局所 Beam classifier は今、

```text id="s7it7i"
next sign
  -> netDrop
  -> retention / continuation drop comparison
  -> normalized count inequality
```

まで降りた。

次は mass difference。
そこまで通れば、DkMath Collatz pressure 会計は、かなり読みやすい比較命令列になる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
index 3d38f8a8..3c16b35e 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
@@ -672,4 +672,74 @@ theorem sourcePressureMargin_next_nonpos_iff_retCont_le_neg_current_of_addressed
   rw [sourcePressureNetDrop_eq_retention_sub_two_mul_continuation_of_addressedDepthTarget
     haddr]

+/--
+Normalized True Beam count inequality at an addressed depth.
+
+The local True classifier can be read as a comparison between twice the
+continuation drop and the retention drop plus the current margin.
+-/
+theorem sourcePressureMargin_next_pos_iff_two_cont_lt_ret_add_current_of_addressedDepthTarget
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
+    0 < SourcePressureMarginInt n k (r + j + 1) ↔
+      2 * SourceContinuationDropInt n k r j <
+        SourceRetentionDropInt n k r j +
+          SourcePressureMarginInt n k (r + j) := by
+  rw [sourcePressureMargin_next_pos_iff_neg_current_lt_retCont_of_addressedDepthTarget
+    haddr]
+  omega
+
+/--
+Normalized False Beam count inequality at an addressed depth.
+
+The next margin is nonpositive exactly when the retention drop plus the
+current margin is at most twice the continuation drop.
+-/
+theorem sourcePressureMargin_next_nonpos_iff_ret_add_current_le_two_cont_of_addressedDepthTarget
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
+    SourcePressureMarginInt n k (r + j + 1) ≤ 0 ↔
+      SourceRetentionDropInt n k r j +
+          SourcePressureMarginInt n k (r + j)
+        ≤ 2 * SourceContinuationDropInt n k r j := by
+  rw [sourcePressureMargin_next_nonpos_iff_retCont_le_neg_current_of_addressedDepthTarget
+    haddr]
+  omega
+
+/--
+One-way True Beam wrapper for the normalized count inequality.
+-/
+theorem sourcePressureMargin_next_pos_of_addressedDepthTarget_of_two_cont_lt_ret_add_current
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j)
+    (hineq :
+      2 * SourceContinuationDropInt n k r j <
+        SourceRetentionDropInt n k r j +
+          SourcePressureMarginInt n k (r + j)) :
+    0 < SourcePressureMarginInt n k (r + j + 1) := by
+  have hiff :=
+    sourcePressureMargin_next_pos_iff_two_cont_lt_ret_add_current_of_addressedDepthTarget
+      haddr
+  exact hiff.2 hineq
+
+/--
+One-way False Beam wrapper for the normalized count inequality.
+-/
+theorem sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_ret_add_current_le_two_cont
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j)
+    (hineq :
+      SourceRetentionDropInt n k r j +
+          SourcePressureMarginInt n k (r + j)
+        ≤ 2 * SourceContinuationDropInt n k r j) :
+    SourcePressureMarginInt n k (r + j + 1) ≤ 0 := by
+  have hiff :=
+    sourcePressureMargin_next_nonpos_iff_ret_add_current_le_two_cont_of_addressedDepthTarget
+      haddr
+  exact hiff.2 hineq
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-212.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-212.md
new file mode 100644
index 00000000..4dcba110
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-212.md
@@ -0,0 +1,167 @@
+# report-petal-212
+
+## Situation
+
+Checkpoint petal-212 normalizes the Beam-facing sign classifier from cp211.
+
+The previous layer had already expanded the local net drop as
+
+```text
+netDrop = retentionDrop - 2 * continuationDrop
+```
+
+and expressed the next margin sign by comparing this value with the negative
+current margin.  This checkpoint rewrites that classifier into direct
+count-style inequalities:
+
+```text
+True Beam:
+  2 * continuationDrop < retentionDrop + current
+
+False Beam:
+  retentionDrop + current <= 2 * continuationDrop
+```
+
+This remains strictly local to an addressed pressure-depth edge.
+
+## True Beam
+
+Implemented in `DkMath.Collatz.PetalBridge.PressureBeam`:
+
+```lean
+sourcePressureMargin_next_pos_iff_two_cont_lt_ret_add_current_of_addressedDepthTarget
+```
+
+This proves the normalized True classifier:
+
+```text
+0 < nextMargin
+  iff
+2 * continuationDrop < retentionDrop + currentMargin
+```
+
+Also added the one-way wrapper:
+
+```lean
+sourcePressureMargin_next_pos_of_addressedDepthTarget_of_two_cont_lt_ret_add_current
+```
+
+## False Beam
+
+Implemented:
+
+```lean
+sourcePressureMargin_next_nonpos_iff_ret_add_current_le_two_cont_of_addressedDepthTarget
+```
+
+This proves the normalized False classifier:
+
+```text
+nextMargin <= 0
+  iff
+retentionDrop + currentMargin <= 2 * continuationDrop
+```
+
+Also added the one-way wrapper:
+
+```lean
+sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_ret_add_current_le_two_cont
+```
+
+## Arithmetic
+
+Both equivalences are obtained from the cp211 retention/continuation
+classifier, followed by `omega`.
+
+The normalized moves are:
+
+```text
+-current < retention - 2 * continuation
+  iff
+2 * continuation < retention + current
+```
+
+and
+
+```text
+retention - 2 * continuation <= -current
+  iff
+retention + current <= 2 * continuation
+```
+
+## Gap
+
+The addressed target alone still does not determine the next sign.
+
+The missing relation is exactly the normalized inequality.  In other words,
+the current Core can classify a local addressed edge once the retention /
+continuation comparison is supplied, but it does not prove arbitrary next
+positivity or arbitrary next nonpositivity from `haddr` alone.
+
+## Not Propagation
+
+This checkpoint is inequality normalization, not propagation.
+
+No theorem was added for:
+
+- time or orbit propagation
+- arbitrary target transport
+- arbitrary positivity
+- arbitrary next-positivity
+- convergence
+- global coverage
+- aggregation over multiple recovered diagnostics
+- overlap repair
+
+## Wise Wolf Inference
+
+The next natural layer is to unfold `retentionDrop` and `continuationDrop`
+themselves into mass differences.
+
+Expected next reading:
+
+```text
+retentionDrop
+  = currentRetentionMass - nextRetentionMass
+
+continuationDrop
+  = currentContinuationMass - nextContinuationMass
+```
+
+Then the Beam classifier becomes a mass-comparison instruction rather than a
+sign-comparison instruction.
+
+## Experimental Lemma Table
+
+| experiment | status | theorem |
+| --- | --- | --- |
+| T1 | passed | `sourcePressureMargin_next_pos_iff_two_cont_lt_ret_add_current_of_addressedDepthTarget` |
+| F1 | passed | `sourcePressureMargin_next_nonpos_iff_ret_add_current_le_two_cont_of_addressedDepthTarget` |
+| T2 | passed | `sourcePressureMargin_next_pos_of_addressedDepthTarget_of_two_cont_lt_ret_add_current` |
+| F2 | passed | `sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_ret_add_current_le_two_cont` |
+| G1 | under-specified | next sign from `haddr` alone still needs the normalized inequality |
+
+## Verification
+
+Commands run:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureBeam
+lake build DkMath.Collatz.PetalBridge
+rg -n "\bsorry\b|admit" DkMath/Collatz/PetalBridge/PressureBeam.lean DkMath/Collatz/PetalBridge/PressureAutomaton.lean DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean DkMath/Collatz/PetalBridge/PressureAccounting.lean DkMath/Collatz/PetalBridge/PressureFrontier.lean DkMath/Collatz/PetalBridge/PressureDecay.lean DkMath/Collatz/PetalBridge/DriftBudget.lean
+git diff --check
+```
+
+Results:
+
+- `lake build DkMath.Collatz.PetalBridge.PressureBeam`: passed
+- `lake build DkMath.Collatz.PetalBridge`: passed
+- no-sorry check on the listed pressure files: no matches
+- `git diff --check`: passed
+
+Known unrelated build warning remains:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
````
`````
