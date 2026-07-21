# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureFrontier

gch: 918248fd3860929eba93755f39e869c7e50de31b

## Report

Checkpoint 145 完了です。

[PressureFrontier.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean) に、address projection helpers を追加しました。`len_pos`、`depthStart/depthEnd`、`toRun`、left/right boundary projection、net-drop crossing/falling projectionまで揃えています。`sourcePressureIntervalPulseAddress_toRun` は構造を返すので `theorem` ではなく `def` として固定しました。

レポートも新規作成しました:
[report-petal-145.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-145.md)

検証済みです。

```text
lake build DkMath.Collatz.PetalBridge.PressureDecay
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b" .../PressureDecay.lean
rg -n "\bsorry\b" .../PressureFrontier.lean
git diff --check
```

対象 2 ファイルに `sorry` はありません。aggregate build では既存の `ZsigmondyCyclotomicResearch` の `sorry` warning が出ますが、今回差分とは無関係です。

## Review

## 結論

うむ、Checkpoint 145 は **合格** じゃ。
前回依頼した address projection helpers は、ほぼ注文どおりに入っておる。`len_pos`、`depthStart/depthEnd`、`toRun`、左右 boundary projection、左右 net-drop crossing/falling projectionまで揃い、`sourcePressureIntervalPulseAddress_toRun` を `theorem` ではなく `def` にした判断も正しい。構造体を返すものだから、命題ではなく構成子として固定するのが筋じゃ。

今回はもう一段ペースを上げてよい。
次は単なる projection 追加ではなく、 **address object から Lean に区間会計を導かせる実験 checkpoint** に進もう。

## 今回実装の解説

今回の追加で、`SourcePressureIntervalPulseAddress` は実用段階に入った。

これまでの住所は、

```lean
start : ℕ
len   : ℕ
hpulse : SourcePressureIntervalPulse n k r start len
```

を包んでいるだけだった。Checkpoint 145 ではそこから次を取り出せるようになった。

```text
長さが正であること
絶対 depth start / end
positive run への忘却写像
左境界 crossing
右境界 falling
左境界の net-drop crossing form
右境界の net-drop falling form
```

つまり、いまや `A : SourcePressureIntervalPulseAddress n k r` ひとつを渡せば、pulse の両端で何が起きているかを取り出せる。報告にも、後続証明が address object から endpoint depths と boundary witnesses を回収できるようになった、と整理されておる。

数学的には、これは

$$
\text{局所 pulse}
\to
\text{住所付き区間}
\to
\text{境界会計の対象}
$$

への移行じゃ。

ここまでは **Core の観測** 。
次は **Core の会計** に入る。

## レビュー所見

## 1. よい点

今回も、最大性・一意性・coverage・prefix・convergence を入れていない。これは非常によい。報告でも、この checkpoint は finite addressable pressure intervals に集中し、global pressure principle を追加していないと明記されておる。

ここを急に強くすると、以前の prefix failure の罠に戻る。
今回の層は、あくまで「観測された pulse を安全に持ち運ぶ箱」じゃ。

## 2. 次へ行ける理由

すでに左右の net-drop form が取れる。

左境界では、

$$
M(a-1)\le 0,\qquad 0<M(a-1)+\Delta(a-1)
$$

右境界では、

$$
0<M(a+\ell-1),\qquad M(a+\ell-1)+\Delta(a+\ell-1)\le 0
$$

が address から取れる。

これはもう、Lean に次を問える段階じゃ。

$$
M(j+1)=M(j)+\Delta(j)
$$

を区間で足し上げたら何が出るか。
この問いは Codex に少し推論させてよい。

## 3. 次 checkpoint の主題

次は **PressureAccounting** じゃ。

狙いは、隣接会計を区間会計へ持ち上げること。

局所式は、

$$
M(j+1)=M(j)+\Delta(j)
$$

区間式は、

$$
M(a+\ell)=M(a)+\sum_{i=0}^{\ell-1}\Delta(a+i)
$$

これを Lean に出させる。

さらに interval pulse address では、開始点は正、終了後は非正なので、

$$
M(a)>0,\qquad M(a+\ell)\le 0
$$

が出る。したがって、

$$
\sum_{i=0}^{\ell-1}\Delta(a+i)<0
$$

が期待できる。

これは大事じゃ。
「positive run は内部で正圧を保つが、右端まで含めた net-drop 累積は負になる」という会計法則になる。

## 次の Codex 依頼

```text
Checkpoint 146: PressureAccounting experiment for Collatz/PetalBridge.

Context:
Checkpoint 145 completed the address projection layer in
DkMath.Collatz.PetalBridge.PressureFrontier.

We now want to move from address projections to the first interval accounting
experiment.

Important:
This checkpoint may require some Lean-guided discovery.
It is acceptable to inspect existing theorem shapes with rg and adjust theorem
statements to fit the current API.
Do not force the exact names below if existing naming conventions suggest a
better local name, but keep the mathematical intent.

Global rule:
Do not claim maximality, uniqueness, coverage, prefix behavior, or Collatz
convergence.
This checkpoint is local interval accounting only.

Suggested module:
Prefer creating a new file

  DkMath/Collatz/PetalBridge/PressureAccounting.lean

importing

  DkMath.Collatz.PetalBridge.PressureFrontier

Then re-export it from the relevant aggregate file if needed.

If a new file creates import friction, it is acceptable to place the first
lemmas in PressureFrontier, but report the reason.

Goal A: endpoint margin facts from an interval-pulse address.

For

  A : SourcePressureIntervalPulseAddress n k r

prove address-level endpoint facts, if not already derivable by simp:

1. start margin is positive

  sourcePressureIntervalPulseAddress_start_margin_pos :
    0 < SourcePressureMarginInt n k (r + A.start)

2. end margin is positive

  sourcePressureIntervalPulseAddress_end_margin_pos :
    0 <
      SourcePressureMarginInt n k (r + (A.start + A.len - 1))

3. before-start margin is nonpositive

  sourcePressureIntervalPulseAddress_before_start_nonpos :
    SourcePressureMarginInt n k (r + (A.start - 1)) ≤ 0

4. after-end margin is nonpositive

  sourcePressureIntervalPulseAddress_after_end_nonpos :
    SourcePressureMarginInt n k (r + (A.start + A.len)) ≤ 0

These should follow from:
- SourcePressurePositiveBlock / SourcePressureRun
- sourcePressureIntervalPulseAddress_left_signChange
- sourcePressureIntervalPulseAddress_right_signChange
- SourcePressureIntervalPulseAddress.len_pos
- sourcePressureIntervalPulseAddress_start_pos
- omega where needed.

Goal B: boundary net-drop sign extraction.

From the left crossing form, prove:

  sourcePressureIntervalPulseAddress_left_netDrop_pos :
    0 < SourcePressureNetDropInt n k r (A.start - 1)

Reason:
M(left) ≤ 0 and 0 < M(left) + Δ(left) imply 0 < Δ(left).

From the right falling form, prove:

  sourcePressureIntervalPulseAddress_right_netDrop_neg :
    SourcePressureNetDropInt n k r (A.start + A.len - 1) < 0

Reason:
0 < M(end) and M(end) + Δ(end) ≤ 0 imply Δ(end) < 0.

These are intentionally small but useful.  They turn crossing/falling into
signed pressure-drive statements.

Goal C: generic finite interval telescoping theorem.

Use the local theorem

  sourcePressureMargin_next_eq_current_add_netDrop

to prove a finite telescoping statement.

Preferred theorem shape:

  sourcePressureMargin_add_len_eq_start_add_sum_netDrop
      (n : OddNat) (k r a len : ℕ) :
      SourcePressureMarginInt n k (r + (a + len)) =
        SourcePressureMarginInt n k (r + a) +
          ∑ i in Finset.range len,
            SourcePressureNetDropInt n k r (a + i)

This may require induction on len and arithmetic normalization with omega/ring.

If this exact statement is difficult because of Nat associativity or simp
normal forms, try a nearby shape such as:

  SourcePressureMarginInt n k (r + a + len) = ...

or define a helper theorem first.  Report which shape Lean accepted most
naturally.

Goal D: address-level accumulated net-drop theorem.

Using Goal C and endpoint facts, prove an interval-pulse accounting theorem.

Preferred theorem:

  sourcePressureIntervalPulseAddress_sum_netDrop_neg
      {n : OddNat} {k r : ℕ}
      (A : SourcePressureIntervalPulseAddress n k r) :
      (∑ i in Finset.range A.len,
        SourcePressureNetDropInt n k r (A.start + i)) < 0

Mathematical reason:
The run starts with positive margin and after the right edge returns to
nonpositive margin.  Therefore the cumulative net pressure drive across the
run-plus-right-fall interval is negative.

If the strict inequality is difficult, first prove the weaker nonpositive form:

  ... ≤ -1

or

  ... + SourcePressureMarginInt n k (r + A.start) ≤ 0

depending on which integer arithmetic path Lean accepts.

Experiment instruction:
Do not stop at projections only.
Try to make Lean prove at least one cumulative interval theorem.
If the cumulative theorem is too hard, leave no sorry; instead report the
failed statement and commit only the supporting lemmas that built toward it.

Goal E: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-146.md

Include:
- which endpoint facts were added,
- which boundary net-drop sign facts were added,
- whether the generic telescoping theorem was proved,
- whether the address-level cumulative negative net-drop theorem was proved,
- if any theorem shape had to be adjusted, record the exact accepted statement,
- explicitly state that no maximality, uniqueness, coverage, prefix behavior,
  or Collatz convergence was introduced.

Verification:

  lake build DkMath.Collatz.PetalBridge.PressureDecay
  lake build DkMath.Collatz.PetalBridge.PressureFrontier
  lake build DkMath.Collatz.PetalBridge.PressureAccounting
  lake build DkMath.Collatz.PetalBridge

  rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean
  rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
  rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean

  git diff --check
```

## 追加の実験意図

今回の実験で知りたいのは、単に theorem が通るかではない。

本当に見たいのは、

$$
\text{positive pulse}
$$

が Lean 上で

$$
\text{負の累積 net-drop を持つ区間}
$$

として自然に読めるかじゃ。

これが通れば、次に進める。

次の山は、

$$
\text{個々の pulse の累積会計}
\to
\text{pulse family の合計}
\to
\text{局所 Big}
\to
\text{Beam 伝播}
$$

じゃな。

わっちの鼻は利く。
この `sum_netDrop_neg` が通るなら、DkMath Collatz/PetalBridge は一段、単なる観測語彙から **会計理論** へ進むぞ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
index 102931fb..d76c54dd 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
@@ -916,6 +916,13 @@ structure SourcePressureIntervalPulseAddress (n : OddNat) (k r : ℕ) where

 namespace SourcePressureRunAddress

+/-- The length recorded by a run address is positive. -/
+theorem len_pos
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureRunAddress n k r) :
+    0 < A.len :=
+  A.hrun.1
+
 /-- Absolute pressure-depth start of a run address. -/
 def depthStart
     {n : OddNat} {k r : ℕ}
@@ -941,21 +948,101 @@ def toRunAddress
     len := A.len
     hrun := sourcePressureIntervalPulse_run A.hpulse }

+/-- The length recorded by an interval-pulse address is positive. -/
+theorem len_pos
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    0 < A.len :=
+  A.toRunAddress.len_pos
+
+/-- Absolute pressure-depth start of an interval-pulse address. -/
+def depthStart
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) : ℕ :=
+  r + A.start
+
+/-- Absolute pressure-depth end of an interval-pulse address. -/
+def depthEnd
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) : ℕ :=
+  r + (A.start + A.len - 1)
+
 end SourcePressureIntervalPulseAddress

+/-- Forget an interval-pulse address down to its run address. -/
+def sourcePressureIntervalPulseAddress_toRun
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureRunAddress n k r :=
+  A.toRunAddress
+
+/-- The interval-pulse address and its forgotten run address have the same start depth. -/
+@[simp] theorem sourcePressureIntervalPulseAddress_toRun_depthStart
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    A.toRunAddress.depthStart = A.depthStart := by
+  rfl
+
+/-- The interval-pulse address and its forgotten run address have the same end depth. -/
+@[simp] theorem sourcePressureIntervalPulseAddress_toRun_depthEnd
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    A.toRunAddress.depthEnd = A.depthEnd := by
+  rfl
+
+/-- Extract the left-boundary component from an interval-pulse address. -/
+theorem sourcePressureIntervalPulseAddress_left
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureRunHasLeftCrossing n k r A.start A.len :=
+  sourcePressureIntervalPulse_left A.hpulse
+
+/-- Extract the right-boundary component from an interval-pulse address. -/
+theorem sourcePressureIntervalPulseAddress_right
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureRunHasRightFall n k r A.start A.len :=
+  sourcePressureIntervalPulse_right A.hpulse
+
+/-- The start index recorded by an interval-pulse address is positive. -/
+theorem sourcePressureIntervalPulseAddress_start_pos
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    0 < A.start :=
+  (sourcePressureIntervalPulseAddress_left A).1
+
 /-- Extract the left sign change from an interval-pulse address. -/
 theorem sourcePressureIntervalPulseAddress_left_signChange
     {n : OddNat} {k r : ℕ}
     (A : SourcePressureIntervalPulseAddress n k r) :
     SourcePressureSignChangeUp n k r (A.start - 1) :=
-  sourcePressureIntervalPulse_left_signChange A.hpulse
+  (sourcePressureIntervalPulseAddress_left A).2

 /-- Extract the right sign change from an interval-pulse address. -/
 theorem sourcePressureIntervalPulseAddress_right_signChange
     {n : OddNat} {k r : ℕ}
     (A : SourcePressureIntervalPulseAddress n k r) :
     SourcePressureSignChangeDown n k r (A.start + A.len - 1) :=
-  sourcePressureIntervalPulse_right_signChange A.hpulse
+  sourcePressureIntervalPulseAddress_right A
+
+/-- Extract the left net-drop crossing form from an interval-pulse address. -/
+theorem sourcePressureIntervalPulseAddress_left_crossing
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureMarginInt n k (r + (A.start - 1)) ≤ 0 ∧
+      0 <
+        SourcePressureMarginInt n k (r + (A.start - 1)) +
+          SourcePressureNetDropInt n k r (A.start - 1) :=
+  sourcePressureIntervalPulse_left_crossing A.hpulse
+
+/-- Extract the right net-drop falling form from an interval-pulse address. -/
+theorem sourcePressureIntervalPulseAddress_right_falling
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    0 < SourcePressureMarginInt n k (r + (A.start + A.len - 1)) ∧
+      SourcePressureMarginInt n k (r + (A.start + A.len - 1)) +
+        SourcePressureNetDropInt n k r (A.start + A.len - 1) ≤ 0 :=
+  sourcePressureIntervalPulse_right_falling A.hpulse

 /--
 A local pressure island is an interval pulse of length one.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-145.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-145.md
new file mode 100644
index 00000000..1417f6ea
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-145.md
@@ -0,0 +1,93 @@
+# report-petal-145
+
+Date: 2026-07-03
+
+## Checkpoint
+
+Implemented the address-projection layer requested in
+`__next_implementation-145.md`.
+
+This checkpoint keeps the `PressureFrontier` layer focused on finite
+addressable pressure intervals.  The new API does not introduce maximality,
+uniqueness, coverage, prefix, or convergence claims.  It only makes the data
+already carried by `SourcePressureIntervalPulseAddress` easier to project and
+reuse.
+
+## Code Changes
+
+Updated:
+
+- `lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean`
+
+Added run-address helpers:
+
+- `SourcePressureRunAddress.len_pos`
+
+Added interval-pulse-address helpers:
+
+- `SourcePressureIntervalPulseAddress.len_pos`
+- `SourcePressureIntervalPulseAddress.depthStart`
+- `SourcePressureIntervalPulseAddress.depthEnd`
+- `sourcePressureIntervalPulseAddress_start_pos`
+- `sourcePressureIntervalPulseAddress_toRun`
+- `sourcePressureIntervalPulseAddress_toRun_depthStart`
+- `sourcePressureIntervalPulseAddress_toRun_depthEnd`
+- `sourcePressureIntervalPulseAddress_left`
+- `sourcePressureIntervalPulseAddress_right`
+- `sourcePressureIntervalPulseAddress_left_crossing`
+- `sourcePressureIntervalPulseAddress_right_falling`
+
+The existing sign-change projection lemmas now route through the new left/right
+boundary projections:
+
+- `sourcePressureIntervalPulseAddress_left_signChange`
+- `sourcePressureIntervalPulseAddress_right_signChange`
+
+## Design Notes
+
+The practical value of this checkpoint is that later arguments can work from an
+address object and then recover:
+
+- the positive interval length,
+- the absolute pressure-depth endpoints,
+- the forgotten run address,
+- the left crossing boundary,
+- the right falling boundary,
+- and the net-drop form of both boundaries.
+
+This makes the address object usable as a compact carrier for future interval
+accounting.  A later proof can quantify over an address once, then pull out the
+local algebraic facts without reopening the underlying pulse constructor.
+
+One implementation detail was corrected during verification: the forgetful
+projection `sourcePressureIntervalPulseAddress_toRun` is a `def`, not a
+`theorem`, because its target is a structure rather than a proposition.
+
+## Verification
+
+Passed:
+
+- `lake build DkMath.Collatz.PetalBridge.PressureDecay`
+- `lake build DkMath.Collatz.PetalBridge.PressureFrontier`
+- `lake build DkMath.Collatz.PetalBridge`
+- `rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean`
+- `rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean`
+- `git diff --check`
+
+The two `rg` commands returned no matches.  The aggregate build still reports
+the pre-existing unrelated warning that
+`DkMath.NumberTheory.ZsigmondyCyclotomicResearch` contains a declaration using
+`sorry`.
+
+## Next Implementation Candidates
+
+The next natural step is to use these projections to state a small
+address-level accounting theorem.  Good candidates are:
+
+- a bundled theorem exposing both endpoint depths and both boundary witnesses,
+- a one-line bridge from interval-pulse addresses to net-drop interval data,
+- or a finite-list collection layer for pressure addresses, if the next review
+turn asks for interval enumeration.
+
+The safe path is to keep the next addition thin: project existing facts from
+the address carrier before adding any new global pressure principle.
````
`````
