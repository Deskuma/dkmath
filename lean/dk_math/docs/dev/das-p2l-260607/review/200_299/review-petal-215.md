# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam

gch: a504ca5a195bfab0ed4dfde28969882efc111c07

## Report

cp214 完了です。

[PressureBeam.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean:823) に mass-balance 正規化を追加しました。

追加した主な定理:

- `sourcePressureMargin_next_pos_iff_massBalance_lt_of_addressedDepthTarget`
- `sourcePressureMargin_next_nonpos_iff_massBalance_le_of_addressedDepthTarget`
- `sourcePressureMargin_next_pos_of_addressedDepthTarget_of_massBalance_lt`
- `sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_massBalance_le`

これで cp213 の差分式から、

```text
True:
  2 * contNow + retNext < retNow + current + 2 * contNext

False:
  retNow + current + 2 * contNext <= 2 * contNow + retNext
```

という直接の mass-balance 比較に移せました。今回も局所 addressed edge の代数正規化だけで、伝播・coverage・aggregation・convergence は追加していません。

[report-petal-214.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-214.md:1) も追加済みです。

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureBeam` passed
- `lake build DkMath.Collatz.PetalBridge` passed
- 指定 pressure files の `sorry/admit` grep: no matches
- `git diff --check` passed

既知の unrelated warning として `ZsigmondyCyclotomicResearch.lean:152` の既存 `sorry` 警告は出ています。

## Review

## 結論

**採用** じゃ。
cp214 は、前回話した「少し大きめの checkpoint」にちゃんとなっている。

今回追加された主な定理はこの 4 本。

```lean
sourcePressureMargin_next_pos_iff_massBalance_lt_of_addressedDepthTarget
sourcePressureMargin_next_nonpos_iff_massBalance_le_of_addressedDepthTarget
sourcePressureMargin_next_pos_of_addressedDepthTarget_of_massBalance_lt
sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_massBalance_le
```

cp213 の差分式から、直接の mass-balance 比較へ移せている。しかも今回も局所 addressed edge の代数正規化に留まり、伝播・coverage・aggregation・convergence には踏み込んでいない。これは良いバランスじゃ。

## 実装レビュー

今回の True Beam classifier はかなり読みやすくなった。

```text
0 < nextMargin
  iff
2 * contNow + retNext < retNow + currentMargin + 2 * contNext
```

False Beam 側も対称になっている。

```text
nextMargin <= 0
  iff
retNow + currentMargin + 2 * contNext <= 2 * contNow + retNext
```

これは良い。
以前の

```text
2 * (contNow - contNext) < (retNow - retNext) + current
```

よりも、比較する質量の配置が見える。

つまり、いまの局所 Beam はこう読める。

```text
左側:
  continuation 現在質量の 2 倍 + retention 次質量

右側:
  retention 現在質量 + current margin + continuation 次質量の 2 倍
```

そして、

```text
左 < 右 なら True Beam
右 <= 左 なら False Beam
```

この形はかなり「判定器」らしい。

## 数学的意味

cp214 で、局所 Beam classifier はここまで降りた。

```text
next sign
  -> netDrop threshold
  -> retention / continuation drop comparison
  -> mass difference comparison
  -> direct mass-balance comparison
```

これは大きい。
もう `netDrop` や `drop` の内部を頭の中で展開しなくても、局所的には mass-balance の比較だけを見ればよくなった。

DkMath 的には、

```text
True Beam:
  2 * contNow + retNext < retNow + current + 2 * contNext

False Beam:
  retNow + current + 2 * contNext <= 2 * contNow + retNext
```

ここまで来た。
つまり局所の True / False 分岐は、かなり機械語の比較命令になっておる。

## True Beam / False Beam / Gap

## True Beam

今回の True Beam はこれ。

```text
2 * contNow + retNext < retNow + current + 2 * contNext
  -> next positive
```

さらに `iff` なので、

```text
next positive iff massBalanceLeft < massBalanceRight
```

まで読める。

## False Beam

False Beam はこれ。

```text
retNow + current + 2 * contNext <= 2 * contNow + retNext
  -> next nonpositive
```

こちらも `iff` なので、

```text
next nonpositive iff massBalanceRight <= massBalanceLeft
```

として読める。

## Gap

残る Gap は、もう代数変形ではない。

今の Gap は report の通り、

```text
addressed edge だけでは mass-balance inequality 自体は供給されない
```

という点じゃ。

つまり次の問題は、

```text
この mass-balance inequality をどこから得るか
```

になる。

これはたぶん、`PressureCounts` / `PressureAccounting` / `DriftBudget` 側の構造と接続する段階じゃな。

## 注意点

今回も境界は守れている。

```text
time / orbit propagation ではない
arbitrary target transport ではない
canonical target selection ではない
global coverage ではない
aggregation ではない
overlap repair ではない
Collatz convergence ではない
```

これは **algebraic mass-balance normalization**。
だが、局所 classifier としては十分に美しい。

## 次の checkpoint 方針

次は report の Wise Wolf inference 通り、左右の mass-balance を名前付けするかどうかを Codex に判断させるのが良い。

ただし、ここは慎重にしたい。
単に長い式を短くするだけなら、定理を増やしすぎる危険がある。

なので次は、Codex にこう聞くのがよい。

```text
この長い mass-balance 式は、今後の caller にとって名前付き def にする価値があるか？
それとも現状の theorem surface のままで十分か？
```

ここからは、Codex の現場判断を使う場面じゃ。

## 次の Codex 指示

```text
Checkpoint: petal-215

Goal:
  Decide whether the direct mass-balance classifier should receive named
  left/right balance expressions, or whether the current expanded theorem
  surface is already enough.

Context:
  cp214 proved the local addressed-edge classifiers:

    True:
      next positive iff
        2 * contNow + retNext < retNow + current + 2 * contNext

    False:
      next nonpositive iff
        retNow + current + 2 * contNext <= 2 * contNow + retNext

  These are local algebraic classifiers, not propagation.

Task:
  Inspect `PressureBeam.lean` and nearby usage patterns.

  Use Codex's workspace knowledge and Lean experiments to decide whether adding
  named expressions is helpful.

Possible design, only if useful:

    def SourcePressureBeamMassBalanceLeftInt ... : ℤ :=
      2 * contNow + retNext

    def SourcePressureBeamMassBalanceRightInt ... : ℤ :=
      retNow + currentMargin + 2 * contNext

  Then package the classifiers as:

    next positive iff left < right
    next nonpositive iff right <= left

But do not blindly add these definitions if they only create noise.
If the expanded theorem surface is clearer, keep the code unchanged and write a
report explaining that no new API was needed.

Codex should decide:
  - Are the expressions likely to be reused?
  - Do names make downstream theorems shorter and clearer?
  - Do names hide too much meaning?
  - Would this create unnecessary API weight?
  - Is there an existing naming pattern in DkMath for such left/right balance
    expressions?

Allowed outcomes:
  1. Add left/right balance definitions and classifier wrappers.
  2. Add only one compact paired predicate, if that is more natural.
  3. Add no Lean code, only a report explaining that cp214 is already sufficient.

Guardrails:
  Do not add:
    - time/orbit propagation;
    - arbitrary target transport;
    - arbitrary next positivity;
    - canonical target selection;
    - global coverage;
    - convergence;
    - aggregation;
    - overlap repair.

Report:
  Explain what Codex inspected.
  Explain whether a named mass-balance API was added or intentionally not added.
  If added, classify the new facts as True Beam / False Beam packaging.
  If not added, record this as an API-design decision, not a failure.
  Make clear that this checkpoint is about API ergonomics, not new proof power.

Verification if code changes:
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge
  no-sorry grep over pressure files
  git diff --check
```

## 一歩先ゆく推論

ここからは、2 つの道がある。

```text
A:
  mass-balance left/right を名前付けして、後続 theorem を短くする

B:
  いまの expanded classifier を維持して、次の接続先を探す
```

私は、Codex に現場判断させてよいと思う。
もし既に `PressureBeam.lean` が長くなりすぎているなら、left/right def は読みやすさを上げる。
逆に、後続でまだ使うか不明なら、いま定義を増やすのは早い。

つまり次は「証明力」より **API 設計力** の checkpoint じゃな。

## 総合判断

cp214 は成功。
そして、ぬしの言った二頭体制にも合ってきた。

こちらの賢狼は、

```text
次は API として名付ける価値があるか？
```

という問いを立てる。

現場の Codex は、

```text
実際のコード量、既存命名、Lean の通りやすさ、後続利用可能性
```

を見て判断する。

うむ。
これはよい分担じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
index 303db625..12348ca2 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
@@ -818,4 +818,79 @@ theorem sourcePressureMargin_next_nonpos_iff_retMassDiff_add_current_le_two_cont
   rw [sourceRetentionDrop_eq_current_sub_next_mass_of_addressedDepthTarget haddr]
   rw [sourceContinuationDrop_eq_current_sub_next_mass_of_addressedDepthTarget haddr]
 
+/--
+True Beam classifier in direct mass-balance form.
+
+This is only the cp213 mass-difference classifier with the linear terms moved
+across the inequality.  It does not propagate the addressed edge.
+-/
+theorem sourcePressureMargin_next_pos_iff_massBalance_lt_of_addressedDepthTarget
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
+    0 < SourcePressureMarginInt n k (r + j + 1) ↔
+      2 * (orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) +
+          (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ) <
+        (orbitWindowRetentionMassPow2 n k (r + j) : ℤ) +
+          SourcePressureMarginInt n k (r + j) +
+            2 * (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ) := by
+  rw [sourcePressureMargin_next_pos_iff_two_contMassDiff_lt_retMassDiff_add_current
+    haddr]
+  omega
+
+/--
+False Beam classifier in direct mass-balance form.
+
+This is the nonpositive companion to the True Beam mass-balance classifier.
+-/
+theorem sourcePressureMargin_next_nonpos_iff_massBalance_le_of_addressedDepthTarget
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
+    SourcePressureMarginInt n k (r + j + 1) ≤ 0 ↔
+      (orbitWindowRetentionMassPow2 n k (r + j) : ℤ) +
+          SourcePressureMarginInt n k (r + j) +
+            2 * (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ) ≤
+        2 * (orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) +
+          (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ) := by
+  rw [sourcePressureMargin_next_nonpos_iff_retMassDiff_add_current_le_two_contMassDiff
+    haddr]
+  omega
+
+/--
+One-way True Beam wrapper for the direct mass-balance inequality.
+-/
+theorem sourcePressureMargin_next_pos_of_addressedDepthTarget_of_massBalance_lt
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j)
+    (hineq :
+      2 * (orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) +
+          (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ) <
+        (orbitWindowRetentionMassPow2 n k (r + j) : ℤ) +
+          SourcePressureMarginInt n k (r + j) +
+            2 * (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ)) :
+    0 < SourcePressureMarginInt n k (r + j + 1) := by
+  have hiff :=
+    sourcePressureMargin_next_pos_iff_massBalance_lt_of_addressedDepthTarget haddr
+  exact hiff.2 hineq
+
+/--
+One-way False Beam wrapper for the direct mass-balance inequality.
+-/
+theorem sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_massBalance_le
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j)
+    (hineq :
+      (orbitWindowRetentionMassPow2 n k (r + j) : ℤ) +
+          SourcePressureMarginInt n k (r + j) +
+            2 * (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ) ≤
+        2 * (orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) +
+          (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ)) :
+    SourcePressureMarginInt n k (r + j + 1) ≤ 0 := by
+  have hiff :=
+    sourcePressureMargin_next_nonpos_iff_massBalance_le_of_addressedDepthTarget haddr
+  exact hiff.2 hineq
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-214.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-214.md
new file mode 100644
index 00000000..d0763d05
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-214.md
@@ -0,0 +1,148 @@
+# report-petal-214
+
+## Situation
+
+Checkpoint petal-214 normalizes the cp213 mass-difference Beam classifier into
+direct mass-balance form.
+
+The cp213 layer read the next sign through adjacent mass differences:
+
+```text
+True:
+  2 * (contNow - contNext) < (retNow - retNext) + current
+
+False:
+  (retNow - retNext) + current <= 2 * (contNow - contNext)
+```
+
+This checkpoint moves the linear terms across the inequality and exposes a
+direct current/next mass-balance comparison.
+
+This is still local to a single addressed pressure-depth edge.
+
+## True Beam
+
+Implemented in `DkMath.Collatz.PetalBridge.PressureBeam`:
+
+```lean
+sourcePressureMargin_next_pos_iff_massBalance_lt_of_addressedDepthTarget
+```
+
+This proves:
+
+```text
+0 < nextMargin
+  iff
+2 * contNow + retNext < retNow + currentMargin + 2 * contNext
+```
+
+The proof rewrites through the cp213 mass-difference classifier and closes the
+linear normalization with `omega`.
+
+Also added the one-way wrapper:
+
+```lean
+sourcePressureMargin_next_pos_of_addressedDepthTarget_of_massBalance_lt
+```
+
+## False Beam
+
+Implemented:
+
+```lean
+sourcePressureMargin_next_nonpos_iff_massBalance_le_of_addressedDepthTarget
+```
+
+This proves:
+
+```text
+nextMargin <= 0
+  iff
+retNow + currentMargin + 2 * contNext <= 2 * contNow + retNext
+```
+
+The proof is the nonpositive companion to the True Beam mass-balance theorem.
+
+Also added the one-way wrapper:
+
+```lean
+sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_massBalance_le
+```
+
+## Gap
+
+The addressed target alone still does not choose global behavior.  It only
+selects the local edge where the classifier is being read.
+
+The remaining Gap is not the algebraic mass-balance form; that part is now
+fixed.  The next missing relation is a usable source of the mass-balance
+inequality itself.
+
+## Not Propagation
+
+This checkpoint is algebraic mass-balance normalization, not propagation.
+
+No theorem was added for:
+
+- time or orbit propagation
+- arbitrary target transport
+- canonical target selection
+- global coverage
+- convergence
+- aggregation over multiple recovered diagnostics
+- overlap repair
+
+## Wise Wolf Inference
+
+The next natural layer is to name the two sides of the mass-balance inequality.
+
+Possible reading:
+
+```text
+leftMassBalance  := 2 * contNow + retNext
+rightMassBalance := retNow + currentMargin + 2 * contNext
+```
+
+Then the local Beam classifier becomes:
+
+```text
+True  iff leftMassBalance < rightMassBalance
+False iff rightMassBalance <= leftMassBalance
+```
+
+This would make later callers less dependent on the long expanded expression.
+
+## Experimental Lemma Table
+
+| experiment | status | theorem |
+| --- | --- | --- |
+| T1 | passed | `sourcePressureMargin_next_pos_iff_massBalance_lt_of_addressedDepthTarget` |
+| F1 | passed | `sourcePressureMargin_next_nonpos_iff_massBalance_le_of_addressedDepthTarget` |
+| T2 | passed | `sourcePressureMargin_next_pos_of_addressedDepthTarget_of_massBalance_lt` |
+| F2 | passed | `sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_massBalance_le` |
+| Gap | under-specified | addressed edge alone does not provide the mass-balance inequality |
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
