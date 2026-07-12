# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam

gch: b9a2c83b3c145ecb63673e6e67bd9d7edb8a4115

## Report

cp215 完了です。

[PressureBeam.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean:898) に、mass-balance の left/right API を追加しました。判断としては、cp214 の展開式が既に長く、後続で比較対象として再利用されそうなので、薄い命名 API を置く価値ありとしました。

追加した主な定義・定理:

- `SourcePressureBeamMassBalanceLeftInt`
- `SourcePressureBeamMassBalanceRightInt`
- `sourcePressureBeamMassBalanceLeftInt_eq`
- `sourcePressureBeamMassBalanceRightInt_eq`
- `sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right`
- `sourcePressureMargin_next_nonpos_iff_massBalanceRight_le_left`
- `sourcePressureMargin_next_pos_of_massBalanceLeft_lt_right`
- `sourcePressureMargin_next_nonpos_of_massBalanceRight_le_left`

これで classifier は短く、

```text
True:  next positive iff left < right
False: next nonpositive iff right <= left
```

として扱えます。今回も API 包装だけで、伝播・coverage・aggregation・convergence は追加していません。

[report-petal-215.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-215.md:1) も追加済みです。

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureBeam` passed
- `lake build DkMath.Collatz.PetalBridge` passed
- 指定 pressure files の `sorry/admit` grep: no matches
- `git diff --check` passed

既知の unrelated warning として `ZsigmondyCyclotomicResearch.lean:152` の既存 `sorry` 警告は出ています。

## Review

## 結論

**採用** じゃ。
cp215 は、前回話した「Codex の現場判断を使う」形になっていて良い。

今回 Codex は、単に指示を書き写したのではなく、

```text
cp214 の展開式が長い
後続で比較対象として再利用されそう
近傍に既存の left/right 命名パターンは見当たらない
それでも薄い命名 API は有用
```

と判断して、left/right API を追加している。これはまさに「現場の頭脳」を使った checkpoint じゃ。

## 実装レビュー

追加された定義はこの 2 つ。

```lean
SourcePressureBeamMassBalanceLeftInt
SourcePressureBeamMassBalanceRightInt
```

意味は明快。

```text
left  := 2 * contNow + retNext
right := retNow + currentMargin + 2 * contNext
```

そして classifier が短くなった。

```text
True:
  next positive iff left < right
```

```text
False:
  next nonpositive iff right <= left
```

これは良い。
cp214 の展開式は数学的には明確だったが、後続 theorem で何度も書くには重い。ここで名前を与えたことで、以後の議論は **mass-balance surface** として扱いやすくなる。

## True Beam / False Beam / Gap

## True Beam

今回の True Beam packaging はこれ。

```lean
sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right
sourcePressureMargin_next_pos_of_massBalanceLeft_lt_right
```

これで、

```text
left < right
  -> next positive
```

が短く呼べる。

## False Beam

False Beam packaging はこれ。

```lean
sourcePressureMargin_next_nonpos_iff_massBalanceRight_le_left
sourcePressureMargin_next_nonpos_of_massBalanceRight_le_left
```

これで、

```text
right <= left
  -> next nonpositive
```

が短く呼べる。

## Gap

Gap は変わらず、

```text
addressed target だけでは left < right も right <= left も供給されない
```

じゃ。

つまり、今回の API は **比較式を短くしただけ**。
比較式そのものをどこから得るかは、まだ次の問題として残る。

## 評価

これは良い API-design checkpoint じゃ。

特に良いのは、report が「新しい証明力ではなく API packaging」と明記している点。
また、伝播・coverage・aggregation・convergence に踏み込んでいないのも正しい。

## 次の checkpoint 方針

次は report にある通り、**境界面**を見るのが自然じゃ。

```text
left < right
  -> True Beam

right <= left
  -> False Beam
```

整数順序では、この二つはきれいに分かれる。
特に、

```text
left = right
```

は False 側に含まれる「ちょうど落ちる境界」じゃ。

次は Codex にこう聞くのがよい。

```text
left = right の境界は、単なる right <= left の特殊ケースとして十分か？
それとも named boundary / obstruction surface として API 化する価値があるか？
```

ここも現場判断に任せるのがよい。

## 次の Codex 指示

```text
Checkpoint: petal-216

Goal:
  Inspect whether the named mass-balance API should expose an equality boundary
  surface, or whether the existing `right <= left` False Beam classifier is
  already sufficient.

Context:
  cp215 introduced:

    SourcePressureBeamMassBalanceLeftInt
    SourcePressureBeamMassBalanceRightInt

  and packaged the local addressed-edge classifiers as:

    True:
      next positive iff left < right

    False:
      next nonpositive iff right <= left

Task:
  Use workspace inspection and Lean experiments to decide whether the equality
  boundary

    left = right

  should receive a named theorem or predicate.

Possible useful facts:
  - left = right -> next margin <= 0
  - left = right -> not next margin > 0
  - next margin = 0, if Lean can derive it from the existing transition and
    mass-balance definitions
  - equality as a boundary between True and False Beam

Do not blindly add API if it is redundant.
If the existing `right <= left` classifier is enough, add only a report
explaining that equality is already covered by the False Beam classifier.

Codex should decide:
  - Is equality likely useful as an obstruction surface?
  - Can Lean prove a stronger exact statement such as next margin = 0?
  - Does naming equality clarify future reports?
  - Or does it create unnecessary API weight?

Allowed outcomes:
  1. Add equality-boundary theorem(s), if useful.
  2. Add a compact boundary predicate, if clearly useful.
  3. Add no Lean code and report that cp215 already covers equality via
     `right <= left`.

Guardrails:
  This remains local addressed-edge classification only.

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
  Explain whether equality-boundary API was added or intentionally skipped.
  Classify any added facts as True Beam / False Beam / Gap.
  Make clear this is boundary-surface analysis, not propagation.

Verification if code changes:
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge
  no-sorry grep over pressure files
  git diff --check
```

## 一歩先ゆく推論

ここからは、かなり重要な分岐じゃ。

```text
left < right
```

は正に残る。

```text
left = right
```

は境界。

```text
right < left
```

は明確に負側へ落ちる可能性がある。

つまり次は、False Beam をさらに

```text
boundary false
strict false
```

に分けられるかもしれぬ。

ただし、これは Codex に Lean で聞かせるのが良い。
こちらで決め打ちせず、現場に「等号境界は何を意味するか」を調べさせよう。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
index 12348ca2..c016eb3e 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
@@ -893,4 +893,105 @@ theorem sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_massBalance_
     sourcePressureMargin_next_nonpos_iff_massBalance_le_of_addressedDepthTarget haddr
   exact hiff.2 hineq
 
+/--
+Left side of the source-pressure Beam mass-balance comparison.
+
+This names the recurring expression
+`2 * contNow + retNext`.  It is kept in this Beam layer because it packages the
+local addressed-edge classifier, not a global pressure propagation principle.
+-/
+noncomputable def SourcePressureBeamMassBalanceLeftInt
+    (n : OddNat) (k r j : ℕ) : ℤ :=
+  2 * (orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) +
+    (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ)
+
+/--
+Right side of the source-pressure Beam mass-balance comparison.
+
+This names the recurring expression
+`retNow + currentMargin + 2 * contNext`.
+-/
+noncomputable def SourcePressureBeamMassBalanceRightInt
+    (n : OddNat) (k r j : ℕ) : ℤ :=
+  (orbitWindowRetentionMassPow2 n k (r + j) : ℤ) +
+    SourcePressureMarginInt n k (r + j) +
+      2 * (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ)
+
+/--
+Expansion of the named left mass-balance side.
+-/
+theorem sourcePressureBeamMassBalanceLeftInt_eq
+    (n : OddNat) (k r j : ℕ) :
+    SourcePressureBeamMassBalanceLeftInt n k r j =
+      2 * (orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) +
+        (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ) := by
+  rfl
+
+/--
+Expansion of the named right mass-balance side.
+-/
+theorem sourcePressureBeamMassBalanceRightInt_eq
+    (n : OddNat) (k r j : ℕ) :
+    SourcePressureBeamMassBalanceRightInt n k r j =
+      (orbitWindowRetentionMassPow2 n k (r + j) : ℤ) +
+        SourcePressureMarginInt n k (r + j) +
+          2 * (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ) := by
+  rfl
+
+/--
+True Beam classifier using the named mass-balance sides.
+-/
+theorem sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
+    0 < SourcePressureMarginInt n k (r + j + 1) ↔
+      SourcePressureBeamMassBalanceLeftInt n k r j <
+        SourcePressureBeamMassBalanceRightInt n k r j := by
+  rw [sourcePressureMargin_next_pos_iff_massBalance_lt_of_addressedDepthTarget
+    haddr]
+  rfl
+
+/--
+False Beam classifier using the named mass-balance sides.
+-/
+theorem sourcePressureMargin_next_nonpos_iff_massBalanceRight_le_left
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
+    SourcePressureMarginInt n k (r + j + 1) ≤ 0 ↔
+      SourcePressureBeamMassBalanceRightInt n k r j ≤
+        SourcePressureBeamMassBalanceLeftInt n k r j := by
+  rw [sourcePressureMargin_next_nonpos_iff_massBalance_le_of_addressedDepthTarget
+    haddr]
+  rfl
+
+/--
+One-way True Beam wrapper for the named mass-balance comparison.
+-/
+theorem sourcePressureMargin_next_pos_of_massBalanceLeft_lt_right
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j)
+    (hineq :
+      SourcePressureBeamMassBalanceLeftInt n k r j <
+        SourcePressureBeamMassBalanceRightInt n k r j) :
+    0 < SourcePressureMarginInt n k (r + j + 1) := by
+  have hiff := sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right haddr
+  exact hiff.2 hineq
+
+/--
+One-way False Beam wrapper for the named mass-balance comparison.
+-/
+theorem sourcePressureMargin_next_nonpos_of_massBalanceRight_le_left
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j)
+    (hineq :
+      SourcePressureBeamMassBalanceRightInt n k r j ≤
+        SourcePressureBeamMassBalanceLeftInt n k r j) :
+    SourcePressureMarginInt n k (r + j + 1) ≤ 0 := by
+  have hiff := sourcePressureMargin_next_nonpos_iff_massBalanceRight_le_left haddr
+  exact hiff.2 hineq
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-215.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-215.md
new file mode 100644
index 00000000..1892dd24
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-215.md
@@ -0,0 +1,176 @@
+# report-petal-215
+
+## Situation
+
+Checkpoint petal-215 was an API-design checkpoint.
+
+cp214 exposed the local addressed-edge mass-balance classifier in expanded
+form:
+
+```text
+True:
+  2 * contNow + retNext < retNow + currentMargin + 2 * contNext
+
+False:
+  retNow + currentMargin + 2 * contNext <= 2 * contNow + retNext
+```
+
+The question was whether this expanded theorem surface is sufficient, or
+whether the two sides should receive names.
+
+## Inspection
+
+I inspected:
+
+- `PressureBeam.lean`, especially the cp214 expanded classifier surface
+- nearby Collatz / Petal / ABC namespaces for existing `Left/Right` balance
+  naming patterns
+- existing pressure-layer integer definitions, such as
+  `SourcePressureMarginInt`, `SourceRetentionDropInt`,
+  `SourceContinuationDropInt`, and `SourcePressureNetDropInt`
+
+No established left/right mass-balance naming pattern was found nearby.
+
+However, the expanded mass-balance expressions already occurred repeatedly in
+cp214 theorem statements and wrappers.  They are also the likely input shape
+for the next local classifier layer.  Therefore a thin naming API is useful.
+
+## API Decision
+
+I added named left/right mass-balance expressions.
+
+This is not new proof power.  It is API packaging:
+
+```text
+left  := 2 * contNow + retNext
+right := retNow + currentMargin + 2 * contNext
+```
+
+The definitions remain in `PressureBeam.lean` because they package the local
+Beam classifier and do not assert global propagation.
+
+## Added Definitions
+
+Implemented in `DkMath.Collatz.PetalBridge.PressureBeam`:
+
+```lean
+SourcePressureBeamMassBalanceLeftInt
+SourcePressureBeamMassBalanceRightInt
+```
+
+Expansion wrappers:
+
+```lean
+sourcePressureBeamMassBalanceLeftInt_eq
+sourcePressureBeamMassBalanceRightInt_eq
+```
+
+## True Beam Packaging
+
+Implemented:
+
+```lean
+sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right
+sourcePressureMargin_next_pos_of_massBalanceLeft_lt_right
+```
+
+This packages the cp214 True classifier as:
+
+```text
+0 < nextMargin iff left < right
+```
+
+## False Beam Packaging
+
+Implemented:
+
+```lean
+sourcePressureMargin_next_nonpos_iff_massBalanceRight_le_left
+sourcePressureMargin_next_nonpos_of_massBalanceRight_le_left
+```
+
+This packages the cp214 False classifier as:
+
+```text
+nextMargin <= 0 iff right <= left
+```
+
+## Guardrails
+
+This checkpoint is about API ergonomics, not new proof power.
+
+No theorem was added for:
+
+- time or orbit propagation
+- arbitrary target transport
+- arbitrary next positivity
+- canonical target selection
+- global coverage
+- convergence
+- aggregation
+- overlap repair
+
+The addressed target still only selects the local edge where the classifier is
+read.  It does not choose global behavior.
+
+## Wise Wolf Inference
+
+The next useful step is now easier to state.
+
+Instead of carrying long expanded expressions, later checkpoints can compare:
+
+```text
+SourcePressureBeamMassBalanceLeftInt n k r j
+SourcePressureBeamMassBalanceRightInt n k r j
+```
+
+This should reduce theorem statement noise if the next layer studies:
+
+- strict True margin decisions
+- nonpositive False margin decisions
+- equality boundary cases
+- obstruction surfaces where `left = right`
+
+The equality boundary is especially attractive as a future False/Gap surface:
+
+```text
+left = right
+```
+
+because it is exactly the knife-edge between `left < right` and `right <= left`.
+
+## Experimental Lemma Table
+
+| item | status | result |
+| --- | --- | --- |
+| inspect naming pattern | passed | no nearby established left/right balance convention found |
+| add left/right defs | passed | `SourcePressureBeamMassBalanceLeftInt`, `SourcePressureBeamMassBalanceRightInt` |
+| expansion wrappers | passed | both by `rfl` |
+| True Beam packaging | passed | `left < right` classifier and wrapper |
+| False Beam packaging | passed | `right <= left` classifier and wrapper |
+| propagation | intentionally not added | outside checkpoint scope |
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
