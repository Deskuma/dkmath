# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureBeam

gch: 40db0c53fa8497bfc2ba1157d4a4d7b69945e2fd

## Report

cp216 完了です。

[PressureBeam.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean:999) に、mass-balance の等号境界 API を追加しました。

Lean に聞いた結果、等号境界は単に `right <= left` に含まれるだけではなく、

```text
nextMargin = right - left
```

として読めるため、

```text
nextMargin = 0 iff left = right
```

が通りました。これは境界面として残す価値ありです。

追加した主な定理:

- `sourcePressureMargin_next_eq_massBalanceRight_sub_left`
- `sourcePressureMargin_next_eq_zero_iff_massBalanceLeft_eq_right`
- `sourcePressureMargin_next_eq_zero_of_massBalanceLeft_eq_right`
- `sourcePressureMargin_next_nonpos_of_massBalanceLeft_eq_right`
- `not_sourcePressureMargin_next_pos_of_massBalanceLeft_eq_right`
- `sourcePressureMargin_next_neg_iff_massBalanceRight_lt_left`

これで局所 Beam は、

```text
left < right  -> positive
left = right  -> zero boundary
right < left  -> negative
```

まで分解できました。今回も局所分類だけで、伝播・coverage・aggregation・convergence は追加していません。

[report-petal-216.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-216.md:1) も追加済みです。

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureBeam` passed
- `lake build DkMath.Collatz.PetalBridge` passed
- 指定 pressure files の `sorry/admit` grep: no matches
- `git diff --check` passed

既知の unrelated warning として `ZsigmondyCyclotomicResearch.lean:152` の既存 `sorry` 警告は出ています。

## Review

## 結論

**採用** じゃ。
cp216 はかなり良い。しかも今回は、まさに「現場の頭脳」が効いている。

こちらは前回、

```text
left = right は False 側に含まれるが、API 化する価値があるかを現場判断せよ
```

と投げた。
それに対して Codex は Lean に聞き、単なる `right <= left` の特殊ケースではなく、

```text
nextMargin = right - left
```

という、より強い正確な関係を発見している。
そこから

```text
nextMargin = 0 iff left = right
```

まで通した。これは良い発見じゃ。

## 実装レビュー

追加された主な theorem は次。

```lean
sourcePressureMargin_next_eq_massBalanceRight_sub_left
sourcePressureMargin_next_eq_zero_iff_massBalanceLeft_eq_right
sourcePressureMargin_next_eq_zero_of_massBalanceLeft_eq_right
sourcePressureMargin_next_nonpos_of_massBalanceLeft_eq_right
not_sourcePressureMargin_next_pos_of_massBalanceLeft_eq_right
sourcePressureMargin_next_neg_iff_massBalanceRight_lt_left
```

特に重要なのはこれ。

```lean
theorem sourcePressureMargin_next_eq_massBalanceRight_sub_left
```

これは局所 Beam の中核式じゃ。

```text
nextMargin = right - left
```

これにより、これまでの分類が単なる不等式分類ではなく、差分そのものとして読めるようになった。

つまり、

```text
left < right
```

なら `right - left > 0` なので next positive。

```text
left = right
```

なら `right - left = 0` なので zero boundary。

```text
right < left
```

なら `right - left < 0` なので strict false。

これは非常に綺麗じゃ。

## 数学的意味

cp215 までの局所分類はこうだった。

```text
True:
  left < right

False:
  right <= left
```

cp216 で、これが三分割された。

```text
left < right
  -> positive
```

```text
left = right
  -> zero boundary
```

```text
right < left
  -> negative
```

これは DkMath の Beam x2 に、さらに **境界 Beam** が見えた形じゃ。

```text
True Beam:
  正領域に残る

Boundary:
  ちょうど 0 に落ちる

Strict False Beam:
  負側へ落ちる
```

しかも `nextMargin = right - left` があるので、この三分割は見かけの分類ではなく、局所算術として鋭い。

## True Beam / Boundary / False Beam / Gap

## True Beam

True Beam は従来通り。

```text
left < right
  -> nextMargin > 0
```

これは cp215 の classifier が保持している。

## Boundary

今回の新しい成果はここ。

```text
left = right
  iff
nextMargin = 0
```

さらに、

```text
left = right
  -> nextMargin <= 0
```

```text
left = right
  -> not nextMargin > 0
```

が入った。

これは境界面として API 化する価値がある。Codex の判断は正しい。

## Strict False Beam

今回、False 側も鋭くなった。

```text
nextMargin < 0 iff right < left
```

これにより、False Beam は二段に分かれる。

```text
boundary false:
  left = right, nextMargin = 0

strict false:
  right < left, nextMargin < 0
```

ここまで行くと、local classifier としてはかなり完成度が高い。

## Gap

Gap は変わらず、大域側にある。

```text
この local edge が次の orbit / time propagation にどう接続されるか
```

```text
mass-balance inequality を大域的にどう供給するか
```

```text
複数 addressed edge をどう集約するか
```

ここにはまだ入っていない。report でも、今回が boundary-surface analysis であり propagation ではないことが明記されている。

## 評価

これは、かなり良い「二頭体制」の成功例じゃ。

こちらの指示は、

```text
等号境界は API 化すべきか調べよ
```

だった。

Codex は現場で、

```text
nextMargin = right - left
```

を発見し、そこから境界 API を構築した。

つまり、ただ候補 theorem を写したのではなく、ワークスペースと Lean を使って一段深い構造を取り出している。これは理想的じゃ。

## 次の checkpoint 方針

次は、report の Wise Wolf Inference にあるように、三分割を API として包むかどうかが候補になる。

ただし、ここでも Codex に判断させるのがよい。

選択肢は三つ。

```text
A:
  三分割 theorem を追加する

B:
  既存の pos / zero / neg classifier で十分として、追加しない

C:
  small predicate として local decision surface を定義する
```

個人的には、次は **三分割 theorem を試す価値はある**。
ただし、Lean の theorem shape が重くなるなら、無理に入れなくてよい。

## 次の Codex 指示

```text
Checkpoint: petal-217

Goal:
  Decide whether the local Beam mass-balance classifier should expose a compact
  three-way decision surface:
    left < right
    left = right
    right < left

Context:
  cp216 proved the exact local relation:

    nextMargin = right - left

  and added:
    nextMargin = 0 iff left = right
    nextMargin < 0 iff right < left

  Together with the existing positive classifier:
    nextMargin > 0 iff left < right

  the local addressed-edge picture is now:
    left < right  -> positive
    left = right  -> zero boundary
    right < left  -> negative

Task:
  Inspect the current PressureBeam API and decide whether a compact trichotomy
  theorem or wrapper is useful.

  Do not blindly add API.  Codex should use workspace judgment.

Possible useful theorem shapes:

  Option 1: direct trichotomy over mass-balance sides

    theorem sourcePressureBeamMassBalance_trichotomy
        {n : OddNat} {k r j : ℕ} :
        SourcePressureBeamMassBalanceLeftInt n k r j <
            SourcePressureBeamMassBalanceRightInt n k r j ∨
          SourcePressureBeamMassBalanceLeftInt n k r j =
            SourcePressureBeamMassBalanceRightInt n k r j ∨
          SourcePressureBeamMassBalanceRightInt n k r j <
            SourcePressureBeamMassBalanceLeftInt n k r j

  Option 2: addressed next-margin trichotomy

    theorem sourcePressureMargin_next_sign_trichotomy_of_addressedDepthTarget
        {n : OddNat} {k r j : ℕ}
        {L : List (SourcePressureLocalIslandWitness n k r)}
        (haddr : SourcePressureBeamAddressedDepthTarget L j) :
        0 < SourcePressureMarginInt n k (r + j + 1) ∨
          SourcePressureMarginInt n k (r + j + 1) = 0 ∨
          SourcePressureMarginInt n k (r + j + 1) < 0

  Option 3:
    Add no Lean code if the existing pos / zero / neg classifiers are already
    clearer for callers.

Codex should decide:
  - Is a trichotomy theorem useful downstream?
  - Does it reduce future proof noise?
  - Does it merely duplicate `lt_trichotomy` / existing order facts?
  - Is the addressed next-margin trichotomy more useful than the raw
    mass-balance trichotomy?
  - Would a report-only decision be cleaner?

Allowed outcomes:
  1. Add a compact trichotomy theorem if useful.
  2. Add only a small caller-friendly wrapper if clearly useful.
  3. Add no code and report that cp216 already provides enough classifiers.

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
  Explain whether trichotomy API was added or intentionally skipped.
  If added, classify the result as local classification packaging.
  If skipped, record this as an API-design decision, not a failure.
  Make clear that this checkpoint is local decision-surface analysis, not
  propagation.

Verification if code changes:
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge
  no-sorry grep over pressure files
  git diff --check
```

## 一歩先ゆく推論

ここまでで、局所 classifier はかなり閉じた。

```text
nextMargin = right - left
```

これが本体じゃ。
この式があるなら、以後は `nextMargin` を直接追うより、`right - left` を追えばよい。

次の大きな課題は、おそらく三分割そのものではなく、

```text
right - left
```

をどの上流構造が供給するかじゃ。

つまり次の大きな探索先は、

```text
mass-balance inequality source
```

じゃな。

`PressureAccounting` なのか、`DriftBudget` なのか、あるいは `PressureFrontier` の local island 構造なのか。
ここは Codex に調査させる価値がある。

## 総合判断

cp216 は成功。
しかも「Codex に判断させる」方針がよく効いた。

今回の収穫は、等号境界そのものよりも、

```text
nextMargin = right - left
```

が出たことじゃ。

これは局所 Beam classifier の心臓部と言ってよい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
index c016eb3e..6e347e8e 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
@@ -994,4 +994,98 @@ theorem sourcePressureMargin_next_nonpos_of_massBalanceRight_le_left
   have hiff := sourcePressureMargin_next_nonpos_iff_massBalanceRight_le_left haddr
   exact hiff.2 hineq

+/--
+Exact local relation between the next margin and the named mass-balance sides.
+
+At an addressed Beam edge, the next margin is the right side minus the left
+side.  This is stronger than the sign classifiers and explains why equality is
+the zero boundary.
+-/
+theorem sourcePressureMargin_next_eq_massBalanceRight_sub_left
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (_haddr : SourcePressureBeamAddressedDepthTarget L j) :
+    SourcePressureMarginInt n k (r + j + 1) =
+      SourcePressureBeamMassBalanceRightInt n k r j -
+        SourcePressureBeamMassBalanceLeftInt n k r j := by
+  unfold SourcePressureBeamMassBalanceLeftInt
+  unfold SourcePressureBeamMassBalanceRightInt SourcePressureMarginInt
+  ring
+
+/--
+Boundary Beam classifier: the next margin is zero exactly on the equality
+surface between the named mass-balance sides.
+-/
+theorem sourcePressureMargin_next_eq_zero_iff_massBalanceLeft_eq_right
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
+    SourcePressureMarginInt n k (r + j + 1) = 0 ↔
+      SourcePressureBeamMassBalanceLeftInt n k r j =
+        SourcePressureBeamMassBalanceRightInt n k r j := by
+  rw [sourcePressureMargin_next_eq_massBalanceRight_sub_left haddr]
+  omega
+
+/--
+Boundary Beam wrapper: equality of the named mass-balance sides forces the next
+margin to be zero.
+-/
+theorem sourcePressureMargin_next_eq_zero_of_massBalanceLeft_eq_right
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j)
+    (hboundary :
+      SourcePressureBeamMassBalanceLeftInt n k r j =
+        SourcePressureBeamMassBalanceRightInt n k r j) :
+    SourcePressureMarginInt n k (r + j + 1) = 0 := by
+  have hiff :=
+    sourcePressureMargin_next_eq_zero_iff_massBalanceLeft_eq_right haddr
+  exact hiff.2 hboundary
+
+/--
+False Beam boundary wrapper: equality of the named mass-balance sides is already
+inside the nonpositive side.
+-/
+theorem sourcePressureMargin_next_nonpos_of_massBalanceLeft_eq_right
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j)
+    (hboundary :
+      SourcePressureBeamMassBalanceLeftInt n k r j =
+        SourcePressureBeamMassBalanceRightInt n k r j) :
+    SourcePressureMarginInt n k (r + j + 1) ≤ 0 := by
+  have hzero :=
+    sourcePressureMargin_next_eq_zero_of_massBalanceLeft_eq_right haddr hboundary
+  omega
+
+/--
+Boundary obstruction wrapper: equality of the named mass-balance sides rules out
+the positive next-margin side.
+-/
+theorem not_sourcePressureMargin_next_pos_of_massBalanceLeft_eq_right
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j)
+    (hboundary :
+      SourcePressureBeamMassBalanceLeftInt n k r j =
+        SourcePressureBeamMassBalanceRightInt n k r j) :
+    ¬ 0 < SourcePressureMarginInt n k (r + j + 1) := by
+  have hzero :=
+    sourcePressureMargin_next_eq_zero_of_massBalanceLeft_eq_right haddr hboundary
+  omega
+
+/--
+Strict False Beam classifier: the next margin is negative exactly when the
+right mass-balance side is strictly smaller than the left side.
+-/
+theorem sourcePressureMargin_next_neg_iff_massBalanceRight_lt_left
+    {n : OddNat} {k r j : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (haddr : SourcePressureBeamAddressedDepthTarget L j) :
+    SourcePressureMarginInt n k (r + j + 1) < 0 ↔
+      SourcePressureBeamMassBalanceRightInt n k r j <
+        SourcePressureBeamMassBalanceLeftInt n k r j := by
+  rw [sourcePressureMargin_next_eq_massBalanceRight_sub_left haddr]
+  omega
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-216.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-216.md
new file mode 100644
index 00000000..3cfe146e
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-216.md
@@ -0,0 +1,187 @@
+# report-petal-216
+
+## Situation
+
+Checkpoint petal-216 asked whether the named mass-balance API from cp215 should
+expose an equality boundary surface.
+
+cp215 had:
+
+```text
+True:
+  next positive iff left < right
+
+False:
+  next nonpositive iff right <= left
+```
+
+The equality surface
+
+```text
+left = right
+```
+
+is already included in the False Beam side by `right <= left`, but it was not
+yet clear whether equality had a sharper meaning.
+
+## Inspection and Lean Result
+
+Lean confirms a stronger exact relation:
+
+```text
+nextMargin = right - left
+```
+
+Therefore equality is not merely a weak False-side case.  It is the exact zero
+boundary:
+
+```text
+nextMargin = 0 iff left = right
+```
+
+So the equality boundary deserved a small named API.
+
+## Added Exact Relation
+
+Implemented in `DkMath.Collatz.PetalBridge.PressureBeam`:
+
+```lean
+sourcePressureMargin_next_eq_massBalanceRight_sub_left
+```
+
+This proves:
+
+```text
+nextMargin = right - left
+```
+
+The proof unfolds the named mass-balance sides and `SourcePressureMarginInt`
+and closes by `ring`.
+
+## Boundary Beam
+
+Implemented:
+
+```lean
+sourcePressureMargin_next_eq_zero_iff_massBalanceLeft_eq_right
+sourcePressureMargin_next_eq_zero_of_massBalanceLeft_eq_right
+```
+
+These prove that equality of the named mass-balance sides is exactly the
+zero-margin boundary.
+
+## False Beam Boundary
+
+Implemented:
+
+```lean
+sourcePressureMargin_next_nonpos_of_massBalanceLeft_eq_right
+not_sourcePressureMargin_next_pos_of_massBalanceLeft_eq_right
+```
+
+These make explicit that equality belongs to the False Beam side and rules out
+the positive side.
+
+## Strict False Beam
+
+Implemented:
+
+```lean
+sourcePressureMargin_next_neg_iff_massBalanceRight_lt_left
+```
+
+This separates strict failure from boundary failure:
+
+```text
+nextMargin < 0 iff right < left
+```
+
+So the local Beam picture is now:
+
+```text
+left < right   -> positive
+left = right   -> zero boundary
+right < left   -> negative
+```
+
+## Classification
+
+True Beam:
+
+- positive side remains `left < right`
+
+False Beam:
+
+- nonpositive side remains `right <= left`
+- equality boundary gives `nextMargin = 0`
+- strict false side is `right < left`
+
+Gap:
+
+- no global behavior follows from these local classifiers
+- the addressed edge still only says where the comparison is being read
+
+## Guardrails
+
+This checkpoint is boundary-surface analysis, not propagation.
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
+The next natural API layer could package the three-way local decision surface:
+
+```text
+left < right
+left = right
+right < left
+```
+
+as a small trichotomy theorem or as separate caller-friendly wrappers.  That
+would still be local classification only, but it would make future obstruction
+reports more precise.
+
+## Experimental Lemma Table
+
+| experiment | status | result |
+| --- | --- | --- |
+| exact relation | passed | `nextMargin = right - left` |
+| equality boundary | passed | `nextMargin = 0 iff left = right` |
+| boundary implies false side | passed | equality gives `nextMargin <= 0` |
+| boundary excludes true side | passed | equality gives `¬ 0 < nextMargin` |
+| strict false side | passed | `nextMargin < 0 iff right < left` |
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
