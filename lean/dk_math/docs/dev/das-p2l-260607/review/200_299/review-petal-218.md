# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam

gch: dd372b7e6fad2c20cef40dadc3b3baf1336bdfeb

## Report

cp217 完了です。

[PressureBeam.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean:1093) に、局所 decision surface の trichotomy wrapper を追加しました。

追加定理:

- `sourcePressureMargin_next_sign_massBalance_trichotomy_of_addressedDepthTarget`

これは単なる `lt_trichotomy` の再掲ではなく、各 mass-balance 分岐と next-margin の符号をペアで返します。

```text
(nextMargin > 0 and left < right)
or
(nextMargin = 0 and left = right)
or
(nextMargin < 0 and right < left)
```

raw な `left/right` だけの trichotomy は、整数の通常順序の重複になるので追加しませんでした。今回の追加は局所 addressed edge の分類包装だけで、伝播・coverage・aggregation・convergence は追加していません。

[report-petal-217.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-217.md:1) も追加済みです。

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureBeam` passed
- `lake build DkMath.Collatz.PetalBridge` passed
- 指定 pressure files の `sorry/admit` grep: no matches
- `git diff --check` passed

既知の unrelated warning として `ZsigmondyCyclotomicResearch.lean:152` の既存 `sorry` 警告は出ています。

## Review

## 結論

**採用** じゃ。
cp217 は、局所 Beam classifier の締めとしてかなり良い。

今回追加されたのはこれ。

```lean id="gujrb4"
sourcePressureMargin_next_sign_massBalance_trichotomy_of_addressedDepthTarget
```

これは単なる `lt_trichotomy` の再掲ではなく、

```text id="chzcmt"
nextMargin > 0 and left < right
or
nextMargin = 0 and left = right
or
nextMargin < 0 and right < left
```

という **符号と mass-balance 分岐をペアで返す局所 decision surface** になっている。raw な left/right だけの三分岐は重複として追加せず、addressed edge に意味のある包装だけ追加した判断も良い。

## 実装レビュー

実装は綺麗じゃ。

```lean id="x81z96"
rcases lt_trichotomy
    (SourcePressureBeamMassBalanceLeftInt n k r j)
    (SourcePressureBeamMassBalanceRightInt n k r j) with hlt | heq | hgt
```

この分岐で、

```text id="0qmffg"
left < right
left = right
right < left
```

を取り、その各 branch に既存の classifier を接続している。

```lean id="lm09uc"
sourcePressureMargin_next_pos_of_massBalanceLeft_lt_right
sourcePressureMargin_next_eq_zero_of_massBalanceLeft_eq_right
sourcePressureMargin_next_neg_iff_massBalanceRight_lt_left
```

既存 Core の再利用として自然。
余計な補題を増やさず、局所三分岐を caller-friendly にしただけなので、API 包装として採用できる。

## 数学的意味

これで局所 Beam classifier はほぼ閉じた。

中核は cp216 の、

```text id="j257je"
nextMargin = right - left
```

そして cp217 で、その符号分類が一つの theorem にまとまった。

```text id="48kjeo"
left < right
  -> positive

left = right
  -> zero boundary

right < left
  -> negative
```

つまり、局所 addressed edge では、次の margin の符号は mass-balance の三分岐と完全に同期している。

DkMath 的にはこう読める。

```text id="fy3lzf"
True Beam:
  left < right

Boundary:
  left = right

Strict False Beam:
  right < left
```

これはかなり完成度が高い。

## True Beam / Boundary / False Beam / Gap

## True Beam

```text id="c1qbz3"
nextMargin > 0
and
left < right
```

正領域に残る branch。

## Boundary

```text id="4u3vk4"
nextMargin = 0
and
left = right
```

ちょうど境界に落ちる branch。

## Strict False Beam

```text id="c9nyde"
nextMargin < 0
and
right < left
```

明確に負側へ落ちる branch。

## Gap

今回の report にもある通り、残る Gap はもう局所分類ではない。

```text id="3jz4p3"
left < right
left = right
right < left
```

のどれが起きるかを、上流構造からどう供給するかじゃ。候補として `PressureAccounting`、`DriftBudget`、`PressureFrontier`、local-island witness structure が挙がっている。

## ここで一区切り

ここまでで `PressureBeam.lean` の局所 classifier 系はかなり厚くなった。
次に同じ方向で theorem を足すと、重複 API になりやすい。

なので次は、もう classifier の言い換えではなく、

```text id="y56pn3"
mass-balance inequality source
```

を探す段階じゃ。

つまり、

```text id="8y9pxv"
left < right はどこから来るのか？
left = right はどんな obstruction なのか？
right < left はどの既存 failure / overlap / budget と対応するのか？
```

ここを Codex に調査させるのがよい。

## 次の Codex 指示

```text id="mqa619"
Checkpoint: petal-218

Goal:
  Stop adding local classifier rewrites for now.  The local addressed-edge Beam
  classifier is essentially closed:

    nextMargin = right - left

  and cp217 packages the three-way decision surface:

    positive / zero / negative
    paired with
    left < right / left = right / right < left

  The next task is to investigate where the mass-balance inequality comes from
  upstream.

Main question:
  What existing pressure-layer structure can supply or obstruct:

    SourcePressureBeamMassBalanceLeftInt n k r j
      <
    SourcePressureBeamMassBalanceRightInt n k r j

  or the boundary / false alternatives?

Modules to inspect:
  - DkMath.Collatz.PetalBridge.DriftBudget
  - DkMath.Collatz.PetalBridge.PressureDecay
  - DkMath.Collatz.PetalBridge.PressureFrontier
  - DkMath.Collatz.PetalBridge.PressureAccounting
  - DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
  - DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
  - DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition

Codex should use its workspace head:
  - inspect definitions and theorem names;
  - use `#check`, `#print`, and scratch lemmas;
  - look for existing inequalities involving retention mass, continuation mass,
    drift budget, local-island witnesses, overlap, or recovered/accounted
    families;
  - decide whether there is an immediate theorem to add, or whether this should
    be a report-only investigation.

Possible outcomes:
  1. Add a small theorem connecting an existing upstream inequality to
     `left < right`.
  2. Add a small theorem connecting an existing obstruction/boundary condition
     to `left = right` or `right < left`.
  3. Add no Lean code and write a report identifying the missing relation,
     exact candidate definitions, and the next viable proof route.

Do not force a theorem.
  If no existing upstream fact supplies the mass-balance inequality, record this
  as a Gap, not a failure.

Useful target shapes, only if Lean and the workspace support them:

  theorem sourcePressureMargin_next_pos_of_<upstream_condition>
      ...
      (haddr : SourcePressureBeamAddressedDepthTarget L j)
      (hup : <existing upstream condition>) :
      0 < SourcePressureMarginInt n k (r + j + 1)

  theorem sourcePressureBeamMassBalanceLeft_lt_right_of_<upstream_condition>
      ...
      (haddr : SourcePressureBeamAddressedDepthTarget L j)
      (hup : <existing upstream condition>) :
      SourcePressureBeamMassBalanceLeftInt n k r j <
        SourcePressureBeamMassBalanceRightInt n k r j

Guardrails:
  Do not add:
    - time/orbit propagation;
    - arbitrary target transport;
    - global coverage;
    - convergence;
    - aggregation over all witnesses;
    - overlap repair;
    - canonical next target selection.

Report requirements:
  - Explain what modules and theorem families were inspected.
  - List promising upstream definitions / lemmas found.
  - State whether any theorem was added.
  - If no theorem was added, identify the precise missing relation.
  - Classify findings as True Beam / Boundary / False Beam / Gap.
  - Make clear this is an upstream inequality-source investigation, not
    propagation.

Verification if code changes:
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge
  no-sorry grep over pressure files
  git diff --check
```

## 一歩先ゆく推論

ここから先の本命は、おそらくこの形じゃ。

```text id="ru1pxw"
local classifier:
  next sign is decided by right - left

upstream source:
  accounting / drift / frontier structure decides left vs right
```

つまり、`PressureBeam` は判定器を得た。
次に必要なのは、判定器へ入力する inequality をどの既存構造が供給するか。

ここからは「分類器を作る段階」から「分類器に値を入れる段階」へ移る。
良い一区切りじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
index 6e347e8e..3b13eac4 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
@@ -1088,4 +1088,38 @@ theorem sourcePressureMargin_next_neg_iff_massBalanceRight_lt_left
   rw [sourcePressureMargin_next_eq_massBalanceRight_sub_left haddr]
   omega
 
+/--
+Local three-way Beam decision surface at an addressed depth.
+
+This packages the useful information, not just the ambient linear-order
+trichotomy: each mass-balance case is paired with the corresponding next-margin
+sign.  It remains a local classifier for one addressed edge.
+-/
+theorem sourcePressureMargin_next_sign_massBalance_trichotomy_of_addressedDepthTarget
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
+    (0 < SourcePressureMarginInt n k (r + j + 1) ∧
+        SourcePressureBeamMassBalanceLeftInt n k r j <
+          SourcePressureBeamMassBalanceRightInt n k r j) ∨
+      (SourcePressureMarginInt n k (r + j + 1) = 0 ∧
+          SourcePressureBeamMassBalanceLeftInt n k r j =
+            SourcePressureBeamMassBalanceRightInt n k r j) ∨
+        (SourcePressureMarginInt n k (r + j + 1) < 0 ∧
+          SourcePressureBeamMassBalanceRightInt n k r j <
+            SourcePressureBeamMassBalanceLeftInt n k r j) := by
+  rcases lt_trichotomy
+      (SourcePressureBeamMassBalanceLeftInt n k r j)
+      (SourcePressureBeamMassBalanceRightInt n k r j) with hlt | heq | hgt
+  · left
+    exact ⟨sourcePressureMargin_next_pos_of_massBalanceLeft_lt_right haddr hlt, hlt⟩
+  · right
+    left
+    exact ⟨sourcePressureMargin_next_eq_zero_of_massBalanceLeft_eq_right haddr heq, heq⟩
+  · right
+    right
+    have hneg :=
+      (sourcePressureMargin_next_neg_iff_massBalanceRight_lt_left haddr).2 hgt
+    exact ⟨hneg, hgt⟩
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-217.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-217.md
new file mode 100644
index 00000000..9a1dd9bb
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-217.md
@@ -0,0 +1,148 @@
+# report-petal-217
+
+## Situation
+
+Checkpoint petal-217 asked whether the local Beam mass-balance classifier
+should expose a compact three-way decision surface:
+
+```text
+left < right
+left = right
+right < left
+```
+
+cp216 already provided the individual classifiers:
+
+```text
+nextMargin > 0 iff left < right
+nextMargin = 0 iff left = right
+nextMargin < 0 iff right < left
+```
+
+The question was whether a compact trichotomy theorem would reduce future proof
+noise or merely duplicate ambient order facts.
+
+## API Decision
+
+I added one compact addressed-edge trichotomy wrapper.
+
+I did not add a raw mass-balance-only trichotomy theorem, because that would
+mostly duplicate `lt_trichotomy` for integers.  The useful theorem is the
+paired local classifier: each mass-balance case is returned together with the
+corresponding next-margin sign.
+
+## Added Theorem
+
+Implemented in `DkMath.Collatz.PetalBridge.PressureBeam`:
+
+```lean
+sourcePressureMargin_next_sign_massBalance_trichotomy_of_addressedDepthTarget
+```
+
+It returns:
+
+```text
+(nextMargin > 0 and left < right)
+or
+(nextMargin = 0 and left = right)
+or
+(nextMargin < 0 and right < left)
+```
+
+This packages the local decision surface without claiming any propagation.
+
+## Classification
+
+True Beam:
+
+- the positive branch is paired with `left < right`
+
+Boundary:
+
+- the zero branch is paired with `left = right`
+
+False Beam:
+
+- the negative branch is paired with `right < left`
+
+Gap:
+
+- this theorem does not provide the upstream source of the mass-balance
+  inequality
+- it only classifies one addressed edge once the local quantities are known
+
+## Guardrails
+
+This checkpoint is local decision-surface analysis, not propagation.
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
+## Wise Wolf Inference
+
+The local classifier is now essentially closed:
+
+```text
+nextMargin = right - left
+```
+
+and the three sign cases are packaged.
+
+The next major investigation should likely move upstream and ask where
+`left < right`, `left = right`, or `right < left` comes from:
+
+```text
+mass-balance inequality source
+```
+
+Candidate upstream modules:
+
+- `PressureAccounting`
+- `DriftBudget`
+- `PressureFrontier`
+- local-island witness structure
+
+This is a source-of-inequality question, not another local classifier
+normalization.
+
+## Experimental Lemma Table
+
+| experiment | status | result |
+| --- | --- | --- |
+| raw mass-balance trichotomy | skipped | would mostly duplicate `lt_trichotomy` |
+| addressed paired trichotomy | passed | `sourcePressureMargin_next_sign_massBalance_trichotomy_of_addressedDepthTarget` |
+| propagation | intentionally not added | outside checkpoint scope |
+| upstream inequality source | open | next investigation target |
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
