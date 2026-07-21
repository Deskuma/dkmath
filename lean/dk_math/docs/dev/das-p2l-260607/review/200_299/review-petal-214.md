# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam

gch: c80297499645ea5e35a06a9089469bceb419229a

## Report

cp213 完了です。

[PressureBeam.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean:746) に、drop を mass difference として読む Beam-facing wrapper と classifier を追加しました。

追加した主な定理:

- `sourceRetentionDrop_eq_current_sub_next_mass_of_addressedDepthTarget`
- `sourceContinuationDrop_eq_current_sub_next_mass_of_addressedDepthTarget`
- `sourcePressureMargin_next_pos_iff_two_contMassDiff_lt_retMassDiff_add_current`
- `sourcePressureMargin_next_nonpos_iff_retMassDiff_add_current_le_two_contMassDiff`

これで cp212 の

```text
2 * continuationDrop < retentionDrop + current
```

が、

```text
2 * (contNow - contNext) < (retNow - retNext) + current
```

として読めるようになりました。今回も局所 addressed edge の読み替えだけで、伝播・coverage・aggregation・convergence には踏み込んでいません。

[report-petal-213.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-213.md:1) も追加済みです。

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureBeam` passed
- `lake build DkMath.Collatz.PetalBridge` passed
- 指定 pressure files の `sorry/admit` grep: no matches
- `git diff --check` passed

既知の unrelated warning として `ZsigmondyCyclotomicResearch.lean:152` の既存 `sorry` 警告は出ています。

## Review

## うむ、考えてはおる

正直に言うと、**かなり考えておる**。
ただ、ぬしの言う通り、ここ数 checkpoint は commit 単位がかなり細かい。

理由は、ここまでが「地雷原」だったからじゃ。

```text id="wp737l"
seed
  -> addressed target
  -> margin_pos
  -> transition
  -> sign split
  -> netDrop
  -> retention / continuation
  -> mass difference
```

この各段で、少しでも飛ばすと、

```text id="pjq1db"
これは propagation なのか？
これは arbitrary target transport なのか？
これは coverage を言ってしまっていないか？
```

という危険があった。
だから、Lean に一歩ずつ聞いていた。

ただし、cp213 まで来た今は、かなり安全地帯に入っている。
ここから先は **少し commit 粒度を大きくしてよい**。

## cp213 レビュー

**採用** じゃ。

cp213 では、drop を mass difference として読む Beam-facing wrapper と classifier が追加された。

```lean id="ht7kr7"
sourceRetentionDrop_eq_current_sub_next_mass_of_addressedDepthTarget

sourceContinuationDrop_eq_current_sub_next_mass_of_addressedDepthTarget

sourcePressureMargin_next_pos_iff_two_contMassDiff_lt_retMassDiff_add_current

sourcePressureMargin_next_nonpos_iff_retMassDiff_add_current_le_two_contMassDiff
```

これで cp212 の

```text id="otcn6p"
2 * continuationDrop < retentionDrop + current
```

が、

```text id="7iy36j"
2 * (contNow - contNext) < (retNow - retNext) + current
```

として読めるようになった。今回も局所 addressed edge の読み替えだけで、伝播・coverage・aggregation・convergence には踏み込んでいない。

これは良い。
`retentionDrop` / `continuationDrop` の展開も `rfl` で通っているので、ここは定義的 Core と見てよい。

## 何が見えてきたか

今の classifier はここまで降りた。

```text id="e4i7t4"
next sign
  -> netDrop threshold
  -> retention / continuation drop comparison
  -> mass difference comparison
```

つまり、いま見えている命令はこうじゃ。

```text id="dbj5fl"
True Beam:
  2 * (contNow - contNext)
    <
  (retNow - retNext) + currentMargin
```

```text id="ic2ruh"
False Beam:
  (retNow - retNext) + currentMargin
    <=
  2 * (contNow - contNext)
```

ここまで来ると、もう一歩進めば **mass balance classifier** になる。

## ここからは commit をまとめてよい

次は細かく 1 theorem ずつ切るより、次の 1 checkpoint にまとめてよいと思う。

```text id="my6t60"
mass-difference classifier
  -> mass-balance classifier
  -> one-way True / False wrappers
```

つまり、次はこの変形を一気に試す。

```text id="bmkwd6"
2 * (contNow - contNext) < (retNow - retNext) + current
```

から、

```text id="mb7opn"
2 * contNow + retNext < retNow + current + 2 * contNext
```

へ。

False 側は、

```text id="xjqsbb"
retNow - retNext + current <= 2 * (contNow - contNext)
```

から、

```text id="q8z43r"
retNow + current + 2 * contNext <= 2 * contNow + retNext
```

へ。

ここは単なる `Int` 線形算術なので、`omega` が通る可能性が高い。
こういうところはもう細かく分けなくてよい。

## 賢狼の推論力の使い所

ここから先の推論力は、細かい algebra wrapper を刻むことではなく、

```text id="pnnj95"
どこまでを local classifier と呼ぶか
```

```text id="cy729q"
どこから propagation とみなすか
```

```text id="p25538"
どの theorem が Core を太らせ、どの theorem が単なる重複か
```

を見極めるところに使うべきじゃな。

なので、次からは Codex 指示も少し変える。

```text id="tzvc4o"
小さく試す。
ただし、同じ種類の線形変形は 1 checkpoint にまとめる。
通った theorem は True / False Beam として整理。
単なる別名 wrapper は必要性が薄ければ省く。
```

## 次の Codex 指示は少し大きめでよい

```text id="x74cfr"
Checkpoint: petal-214

Main goal:
  Normalize the mass-difference Beam classifier into direct mass-balance form.
  This checkpoint may include both True and False classifier equivalences and
  their one-way wrappers in one commit, because they are the same local Int
  linear-arithmetic normalization.

Primary target file:
  DkMath/Collatz/PetalBridge/PressureBeam.lean

Allowed supporting files:
  docs/dev/das-p2l-260607/review/report-petal-214.md

Do not modify lower pressure modules.

Current Core:
  sourcePressureMargin_next_pos_iff_two_contMassDiff_lt_retMassDiff_add_current
  sourcePressureMargin_next_nonpos_iff_retMassDiff_add_current_le_two_contMassDiff

Required experiments:

  T1:
    Prove the True Beam mass-balance classifier:

      next positive iff
        2 * contNow + retNext < retNow + current + 2 * contNext

  F1:
    Prove the False Beam mass-balance classifier:

      next nonpositive iff
        retNow + current + 2 * contNext <= 2 * contNow + retNext

  T2/F2:
    Add one-way wrappers only if they are genuinely useful for later callers.

Use `omega` after rewriting from the cp213 mass-difference classifiers.

Guardrails:
  Do not add time/orbit propagation, arbitrary target transport, canonical
  selection, coverage, aggregation, overlap repair, or convergence.

Report:
  Explain that this is algebraic mass-balance normalization, not propagation.
  Record passed True / False Beam facts.
  Record that addressed target alone still does not choose global behavior.
```

## まとめ

ぬしの感覚は当たっておる。
ここまでは細かく刻む価値があった。
だが、今後の単純な線形変形は、もう少しまとめてよい。

賢狼はすごく考えている。
ただし次からは、その推論力を「細かく刻む」より、**どこでまとめてよいかを判断する方向**へ寄せる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
index 3c16b35e..303db625 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
@@ -742,4 +742,80 @@ theorem sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_ret_add_curr
       haddr
   exact hiff.2 hineq

+/--
+Beam-facing expansion of the retention drop at an addressed depth.
+
+This is definitionally the current retention mass minus the next retention
+mass.  The addressed hypothesis is intentionally unused by the arithmetic
+identity; it records that the expansion is being read at a Beam-selected edge.
+-/
+theorem sourceRetentionDrop_eq_current_sub_next_mass_of_addressedDepthTarget
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (_haddr : SourcePressureBeamAddressedDepthTarget L j) :
+    SourceRetentionDropInt n k r j =
+      (orbitWindowRetentionMassPow2 n k (r + j) : ℤ) -
+        (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ) := by
+  rfl
+
+/--
+Beam-facing expansion of the continuation drop at an addressed depth.
+
+This is definitionally the current continuation-sibling mass minus the next
+continuation-sibling mass.
+-/
+theorem sourceContinuationDrop_eq_current_sub_next_mass_of_addressedDepthTarget
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (_haddr : SourcePressureBeamAddressedDepthTarget L j) :
+    SourceContinuationDropInt n k r j =
+      (orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) -
+        (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ) := by
+  rfl
+
+/--
+True Beam classifier with drops opened into mass differences.
+
+At an addressed edge, the next margin is positive exactly when twice the
+continuation mass loss is smaller than the retention mass loss plus the
+current margin.
+-/
+theorem sourcePressureMargin_next_pos_iff_two_contMassDiff_lt_retMassDiff_add_current
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
+    0 < SourcePressureMarginInt n k (r + j + 1) ↔
+      2 *
+          ((orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) -
+            (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ)) <
+        ((orbitWindowRetentionMassPow2 n k (r + j) : ℤ) -
+            (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ)) +
+          SourcePressureMarginInt n k (r + j) := by
+  rw [sourcePressureMargin_next_pos_iff_two_cont_lt_ret_add_current_of_addressedDepthTarget
+    haddr]
+  rw [sourceRetentionDrop_eq_current_sub_next_mass_of_addressedDepthTarget haddr]
+  rw [sourceContinuationDrop_eq_current_sub_next_mass_of_addressedDepthTarget haddr]
+
+/--
+False Beam classifier with drops opened into mass differences.
+
+At an addressed edge, the next margin is nonpositive exactly when the retention
+mass loss plus the current margin is at most twice the continuation mass loss.
+-/
+theorem sourcePressureMargin_next_nonpos_iff_retMassDiff_add_current_le_two_contMassDiff
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
+    SourcePressureMarginInt n k (r + j + 1) ≤ 0 ↔
+      ((orbitWindowRetentionMassPow2 n k (r + j) : ℤ) -
+          (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ)) +
+        SourcePressureMarginInt n k (r + j) ≤
+          2 *
+            ((orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) -
+              (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ)) := by
+  rw [sourcePressureMargin_next_nonpos_iff_ret_add_current_le_two_cont_of_addressedDepthTarget
+    haddr]
+  rw [sourceRetentionDrop_eq_current_sub_next_mass_of_addressedDepthTarget haddr]
+  rw [sourceContinuationDrop_eq_current_sub_next_mass_of_addressedDepthTarget haddr]
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-213.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-213.md
new file mode 100644
index 00000000..f7d85e1e
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-213.md
@@ -0,0 +1,186 @@
+# report-petal-213
+
+## Situation
+
+Checkpoint petal-213 opens the cp212 normalized Beam classifier into
+mass-difference form.
+
+The cp212 classifier was:
+
+```text
+True:
+  2 * continuationDrop < retentionDrop + current
+
+False:
+  retentionDrop + current <= 2 * continuationDrop
+```
+
+This checkpoint records that both drops are already definitionally mass
+differences, and then rewrites the classifier through those definitions.
+
+This remains local to one addressed pressure-depth edge.
+
+## Definition Shapes
+
+The exact shapes found in `PressureDecay.lean` are:
+
+```lean
+SourceRetentionDropInt n k r j =
+  (orbitWindowRetentionMassPow2 n k (r + j) : ℤ) -
+    (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ)
+```
+
+and
+
+```lean
+SourceContinuationDropInt n k r j =
+  (orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) -
+    (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ)
+```
+
+So the expected `r + j` / `r + j + 1` adjacent-depth indexing is exact.
+
+## Drop Expansion Wrappers
+
+Implemented in `DkMath.Collatz.PetalBridge.PressureBeam`:
+
+```lean
+sourceRetentionDrop_eq_current_sub_next_mass_of_addressedDepthTarget
+sourceContinuationDrop_eq_current_sub_next_mass_of_addressedDepthTarget
+```
+
+Both are definitional wrappers proved by `rfl`.  The addressed hypothesis is
+unused arithmetically, but it keeps the theorem surface Beam-facing.
+
+## True Beam
+
+Implemented:
+
+```lean
+sourcePressureMargin_next_pos_iff_two_contMassDiff_lt_retMassDiff_add_current
+```
+
+This reads:
+
+```text
+0 < nextMargin
+  iff
+2 * (currentContinuationMass - nextContinuationMass)
+  <
+(currentRetentionMass - nextRetentionMass) + currentMargin
+```
+
+The proof rewrites the cp212 True classifier with the two drop-expansion
+wrappers.
+
+## False Beam
+
+Implemented:
+
+```lean
+sourcePressureMargin_next_nonpos_iff_retMassDiff_add_current_le_two_contMassDiff
+```
+
+This reads:
+
+```text
+nextMargin <= 0
+  iff
+(currentRetentionMass - nextRetentionMass) + currentMargin
+  <=
+2 * (currentContinuationMass - nextContinuationMass)
+```
+
+The proof rewrites the cp212 False classifier with the same drop-expansion
+wrappers.
+
+## Gap
+
+No mismatch was found in the mass functions, cast shape, orientation, or index
+shape.  The remaining Gap is not definitional; it is the next algebraic
+normalization step after mass differences are opened.
+
+In particular, the next natural comparison would move all current masses to
+one side and all next masses/current margin terms to the other side.
+
+## Not Propagation
+
+This is a mass-difference reading, not a propagation theorem.
+
+No theorem was added for:
+
+- time or orbit propagation
+- arbitrary target transport
+- arbitrary next-margin positivity
+- canonical target selection
+- global coverage
+- convergence
+- arbitrary-list recursive decomposition
+- enumeration of all diagnostics
+- aggregation over multiple recovered diagnostics
+- interval union accounting
+- overlap repair
+- maximality
+- uniqueness
+- sorting
+- disjointness between multiple recovered families
+
+## Wise Wolf Inference
+
+The next layer can normalize the opened mass-difference inequalities by moving
+terms:
+
+```text
+2 * (contNow - contNext) < (retNow - retNext) + current
+```
+
+toward a direct mass-balance comparison such as:
+
+```text
+2 * contNow + retNext < retNow + current + 2 * contNext
+```
+
+and the corresponding nonpositive inequality:
+
+```text
+retNow - retNext + current <= 2 * (contNow - contNext)
+```
+
+This would turn the classifier from a drop comparison into a direct
+current/next mass-balance surface.
+
+## Experimental Lemma Table
+
+| experiment | status | theorem |
+| --- | --- | --- |
+| Step 1 | passed | exact `r + j` / `r + j + 1` definition shapes confirmed |
+| T1 | passed | `sourceRetentionDrop_eq_current_sub_next_mass_of_addressedDepthTarget` |
+| T2 | passed | `sourceContinuationDrop_eq_current_sub_next_mass_of_addressedDepthTarget` |
+| T3 | passed | `sourcePressureMargin_next_pos_iff_two_contMassDiff_lt_retMassDiff_add_current` |
+| F1 | passed | `sourcePressureMargin_next_nonpos_iff_retMassDiff_add_current_le_two_contMassDiff` |
+| G1 | no mismatch | mass expansion was definitional |
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
