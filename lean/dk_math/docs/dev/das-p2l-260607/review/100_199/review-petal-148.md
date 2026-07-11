# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAccounting

gch: c4864a1c6e4b1ff51d4bdab6f4c683453f9ec1a1

## Report

続きとして、146 の結果から直接言える補題を追加しました。

[PressureAccounting.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean) に、累積 net-drop の等式形・上界形・整数強化形・bundle profile を追加しています。

主な追加はこのあたりです。

```lean
sourcePressureIntervalPulseAddress_sum_netDrop_eq_after_sub_start
sourcePressureIntervalPulseAddress_sum_netDrop_le_neg_start_margin
sourcePressureIntervalPulseAddress_start_margin_add_sum_netDrop_nonpos
sourcePressureIntervalPulseAddress_sum_netDrop_le_neg_one
sourcePressureIntervalPulseAddress_endpoint_profile
sourcePressureIntervalPulseAddress_accounting_profile
```

これで単に `sum netDrop < 0` だけでなく、

```text
sum netDrop = afterMargin - startMargin
afterMargin <= 0
startMargin > 0
therefore sum netDrop <= -startMargin <= -1
```

まで Lean 上で固定できました。後続の有限予算・区間会計では `≤ -1` や `≤ -startMargin` の形が使いやすいはずです。

追加レポートも作りました:
[report-petal-147.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-147.md)

検証済みです。

```text
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b" .../PressureAccounting.lean
git diff --check
```

`PressureAccounting.lean` に `sorry` はありません。既存の `ZsigmondyCyclotomicResearch` warning は今回差分とは無関係です。

## Review

## 結論

うむ、これは **採用** でよい。
ただし、前回わっちが出した「`SourcePressureAccountedInterval` carrier / finite-family 実験」そのものにはまだ入っておらぬ。代わりに、Checkpoint 146 で得た単一区間の負性を、 **等式形・上界形・整数予算形・bundle profile** へ強化してきた実装じゃ。

これは寄り道ではない。むしろ次の finite-family に進む前の、かなり良い **会計補題の砥石** じゃな。追加された主補題は、`sum netDrop < 0` だけでなく、`sum netDrop = afterMargin - startMargin`、`sum netDrop ≤ -startMargin`、`sum netDrop ≤ -1` まで固定している。後続の有限予算では、特に `≤ -1` が使いやすい。

## 実装内容の意味

今回の核はこれじゃ。

$$
\sum_i \Delta_i = M_{\mathrm{after}}-M_{\mathrm{start}}
$$

つまり、累積 net-drop が単に負であるだけでなく、 **開始 margin をどれだけ食い潰したか** として読めるようになった。

追加された流れはこうじゃな。

$$
\sum_i\Delta_i=M_{\mathrm{after}}-M_{\mathrm{start}}
$$

$$
M_{\mathrm{after}}\le 0
$$

$$
0<M_{\mathrm{start}}
$$

ゆえに、

$$
\sum_i\Delta_i\le -M_{\mathrm{start}}\le -1
$$

これはかなり強い。
「positive pulse は負の累積 drive を持つ」から一歩進んで、 **positive pulse は少なくとも 1 単位の pressure budget を消費して閉じる** と言える。

DkMath 語彙で言えば、pulse が **負の会計単位** になったわけじゃ。

## 良い点

## 1. `≤ -1` が入ったのが大きい

`< 0` は直感的には分かりやすいが、有限和の予算論では `≤ -1` の方がずっと扱いやすい。

次に list / family で \(m\) 本の pulse を合計するとき、

$$
\sum_{A\in L}\mathrm{NetDrop}(A)\le -|L|
$$

という形へ持ち込めるからじゃ。

これは次の checkpoint の主砲になる。

## 2. `≤ -startMargin` がさらに強い

`≤ -1` は粗い最低保証。
`≤ -startMargin` は、開始時の正圧そのものを消すだけの負 drive が必要だ、という精密な保証じゃ。

後で pulse の高さや山の形を扱うなら、こっちが効く。

$$
\mathrm{NetDrop}(A)\le -M(A.start)
$$

これは、局所 Big の上界づくりに使える。

## 3. profile bundle は後続コードを楽にする

`sourcePressureIntervalPulseAddress_endpoint_profile` と `sourcePressureIntervalPulseAddress_accounting_profile` は、証明力そのものを増やす補題ではないが、後続で毎回 endpoint signs を unpack しなくて済む。
こういう bundle theorem は Lean 実装ではかなり効く。長い補題列が散らばらなくなるからの。

## 注意点

今回の profile は theorem bundle であって、まだ named carrier ではない。

つまり、まだ次は作っていない。

```lean
SourcePressureAccountedInterval
```

また、finite-family もまだない。

ただ、これは悪くない。
先に単一区間の代数補題を厚くしたので、次に carrier / list budget を実装するときの摩擦が減った。

## ロードマップ上の位置

いまの状態はこうじゃ。

```text
PressureFrontier:
  pulse / run / address / endpoint signs

PressureAccounting:
  single pulse accounting
  endpoint difference
  negative accumulated drive
  budget form <= -1
  profile bundle

Next:
  accounted interval carrier
  interval net-drop abbreviation
  finite list/family budget
```

つまり、Core の単位は固まった。
次は Core 単位を束ねて、Beam へ進む準備じゃ。

## 次の Codex 依頼

今回こそ、carrier と finite-family へ進ませてよい。
少し推論を要する問題として、list の総予算

$$
\sum_{A\in L}\mathrm{NetDrop}(A)\le -|L|
$$

を出すのがよい。

```text
Checkpoint 148: AccountedInterval carrier and finite-family pressure budget.

Context:
Checkpoint 146 introduced PressureAccounting and proved that a single
SourcePressureIntervalPulseAddress has negative accumulated net-drop.

Checkpoint 147 strengthened that result with:

- sourcePressureIntervalPulseAddress_sum_netDrop_eq_after_sub_start
- sourcePressureIntervalPulseAddress_sum_netDrop_le_neg_start_margin
- sourcePressureIntervalPulseAddress_start_margin_add_sum_netDrop_nonpos
- sourcePressureIntervalPulseAddress_sum_netDrop_le_neg_one
- sourcePressureIntervalPulseAddress_endpoint_profile
- sourcePressureIntervalPulseAddress_accounting_profile

Now move from theorem-only single-address accounting to a small reusable carrier
and finite-family budget experiments.

Global rule:
Do not claim maximality, uniqueness, coverage, prefix behavior, disjointness of
addresses unless explicitly assumed, or Collatz convergence.
Only sum over explicitly provided addresses or accounted intervals.

Preferred file:
Continue in:

  DkMath/Collatz/PetalBridge/PressureAccounting.lean

If the file becomes too large, create:

  DkMath/Collatz/PetalBridge/PressureFamily.lean

and import it from:

  DkMath/Collatz/PetalBridge.lean

Goal A: define a reusable interval net-drop abbreviation.

Implement:

  def SourcePressureIntervalNetDrop
      (n : OddNat) (k r start len : ℕ) : ℤ :=
    (Finset.range len).sum (fun i =>
      SourcePressureNetDropInt n k r (start + i))

Then add address-level rewrite / wrapper theorems:

  sourcePressureIntervalPulseAddress_intervalNetDrop_eq_after_sub_start
  sourcePressureIntervalPulseAddress_intervalNetDrop_le_neg_start_margin
  sourcePressureIntervalPulseAddress_intervalNetDrop_le_neg_one
  sourcePressureIntervalPulseAddress_intervalNetDrop_neg

These should be wrappers around the existing checkpoint 147 theorems.

If the abbreviation causes simp friction, keep it but avoid marking too many
lemmas as simp.  Report which statements worked naturally.

Goal B: define a thin accounted interval carrier.

Prefer a structure:

  structure SourcePressureAccountedInterval
      (n : OddNat) (k r : ℕ) where
    start : ℕ
    len : ℕ
    hlen : 0 < len
    startMarginPos :
      0 < SourcePressureMarginInt n k (r + start)
    afterMarginNonpos :
      SourcePressureMarginInt n k (r + (start + len)) ≤ 0
    accounting :
      SourcePressureMarginInt n k (r + (start + len)) =
        SourcePressureMarginInt n k (r + start) +
          SourcePressureIntervalNetDrop n k r start len

Then prove:

  sourcePressureAccountedInterval_intervalNetDrop_neg
  sourcePressureAccountedInterval_intervalNetDrop_le_neg_one
  sourcePressureAccountedInterval_intervalNetDrop_le_neg_start_margin

The last theorem should state:

  SourcePressureIntervalNetDrop n k r A.start A.len ≤
    -SourcePressureMarginInt n k (r + A.start)

Goal C: construct accounted intervals from interval-pulse addresses.

Implement:

  sourcePressureAccountedInterval_of_intervalPulseAddress :
    SourcePressureIntervalPulseAddress n k r →
      SourcePressureAccountedInterval n k r

Use:
- SourcePressureIntervalPulseAddress.len_pos
- sourcePressureIntervalPulseAddress_start_margin_pos
- sourcePressureIntervalPulseAddress_after_end_nonpos
- sourcePressureIntervalPulseAddress_margin_after_eq_start_add_sum_netDrop
or the new intervalNetDrop wrapper.

Goal D: finite-list budget theorem.

Now try a real finite-family theorem.

For a list of accounted intervals:

  L : List (SourcePressureAccountedInterval n k r)

prove:

  sourcePressureAccountedInterval_list_sum_le_neg_length :
    (L.map (fun A =>
      SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤
        -((L.length : ℕ) : ℤ)

This is the key experiment.

Mathematical reason:
each accounted interval contributes at most -1, so a list of m explicitly
provided intervals contributes at most -m.

Important:
This theorem does NOT require disjointness.
It is NOT a pressure-over-union theorem.
It is only a finite budget theorem over explicitly provided interval objects.

If List.sum over ℤ is awkward, try an auxiliary induction theorem first.
If the exact cast shape is difficult, use the Lean-accepted normal form and
record it in the report.

Goal E: optional list negativity theorem.

If Goal D passes, also prove:

  sourcePressureAccountedInterval_list_sum_neg_of_nonempty :
    L ≠ [] →
      (L.map (fun A =>
        SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0

This should follow from Goal D and L.length > 0.

Goal F: optional disjointness vocabulary only.

If time remains, add simple interval-disjoint vocabulary:

  def NatIntervalsDisjoint (a len b len' : ℕ) : Prop :=
    a + len ≤ b ∨ b + len' ≤ a

  def SourcePressureAccountedIntervalsDisjoint
      (A B : SourcePressureAccountedInterval n k r) : Prop :=
    NatIntervalsDisjoint A.start A.len B.start B.len

Optionally prove symmetry:

  NatIntervalsDisjoint.symm
  SourcePressureAccountedIntervalsDisjoint.symm

Do not use disjointness to claim coverage or decomposition yet.

Goal G: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-148.md

Include:
- whether SourcePressureIntervalNetDrop was added,
- whether SourcePressureAccountedInterval was added,
- whether interval-pulse addresses construct accounted intervals,
- whether the finite-list budget theorem was proved,
- exact accepted theorem statement for the list budget,
- whether optional nonempty negativity was proved,
- whether disjointness vocabulary was added,
- explicit note that no maximality, uniqueness, coverage, prefix behavior,
  disjointness conclusion, union accounting, or Collatz convergence was introduced.

Verification:

  lake build DkMath.Collatz.PetalBridge.PressureAccounting
  lake build DkMath.Collatz.PetalBridge

If a new file is created:

  lake build DkMath.Collatz.PetalBridge.PressureFamily

Run:

  rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean

and if created:

  rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFamily.lean

Also run:

  git diff --check
```

## 総評

今回の実装で、単一区間はもう十分に硬い。
次は、複数区間を **明示的に与えたときだけ** 合計する段階へ進むべきじゃ。

ここで、

$$
\sum_{A\in L}\mathrm{NetDrop}(A)\le -|L|
$$

が通れば、いよいよ「pulse は数えれば数えるほど負予算を積む」という Core-family の骨格ができる。
これは大域 Big へ向かう山道の、かなり重要な石段じゃよ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
index 024a93bc..5f613584 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -160,4 +160,114 @@ theorem sourcePressureIntervalPulseAddress_sum_netDrop_neg
   have hafter := sourcePressureIntervalPulseAddress_after_end_nonpos A
   omega
 
+/--
+The accumulated net drop is exactly the after-margin minus the start-margin.
+
+This is often the most convenient algebraic form of interval accounting:
+the finite sum is no longer just known to be negative; it is identified with
+the endpoint margin difference.
+-/
+theorem sourcePressureIntervalPulseAddress_sum_netDrop_eq_after_sub_start
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    (Finset.range A.len).sum (fun i =>
+      SourcePressureNetDropInt n k r (A.start + i)) =
+      SourcePressureMarginInt n k (r + (A.start + A.len)) -
+        SourcePressureMarginInt n k (r + A.start) := by
+  have hacc :=
+    sourcePressureIntervalPulseAddress_margin_after_eq_start_add_sum_netDrop A
+  omega
+
+/--
+The accumulated net drop is bounded above by the negative start margin.
+
+The after-margin is nonpositive, so the endpoint-difference form immediately
+shows that the interval drive must cancel at least the initial positive
+pressure margin.
+-/
+theorem sourcePressureIntervalPulseAddress_sum_netDrop_le_neg_start_margin
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    (Finset.range A.len).sum (fun i =>
+      SourcePressureNetDropInt n k r (A.start + i)) ≤
+      -SourcePressureMarginInt n k (r + A.start) := by
+  have hacc :=
+    sourcePressureIntervalPulseAddress_margin_after_eq_start_add_sum_netDrop A
+  have hafter := sourcePressureIntervalPulseAddress_after_end_nonpos A
+  omega
+
+/--
+The endpoint accounting inequality in unsolved-for form.
+
+This form is useful when a later proof wants to keep the starting margin and
+the accumulated drive on the same side instead of rewriting the sum alone.
+-/
+theorem sourcePressureIntervalPulseAddress_start_margin_add_sum_netDrop_nonpos
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureMarginInt n k (r + A.start) +
+      (Finset.range A.len).sum (fun i =>
+        SourcePressureNetDropInt n k r (A.start + i)) ≤ 0 := by
+  have hacc :=
+    sourcePressureIntervalPulseAddress_margin_after_eq_start_add_sum_netDrop A
+  have hafter := sourcePressureIntervalPulseAddress_after_end_nonpos A
+  omega
+
+/--
+Integer-strength form of negative accumulated net drop.
+
+Since the accumulated drive is an integer, strict negativity is equivalent to
+being at most `-1`.  This is a convenient bridge for later finite budget
+arguments that prefer non-strict inequalities.
+-/
+theorem sourcePressureIntervalPulseAddress_sum_netDrop_le_neg_one
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    (Finset.range A.len).sum (fun i =>
+      SourcePressureNetDropInt n k r (A.start + i)) ≤ -1 := by
+  have hneg := sourcePressureIntervalPulseAddress_sum_netDrop_neg A
+  omega
+
+/--
+Endpoint profile bundled for callers that only need signs.
+
+This theorem is intentionally just packaging of local facts.  It does not say
+that the pulse is maximal, unique, covering, prefix-shaped, or convergent.
+-/
+theorem sourcePressureIntervalPulseAddress_endpoint_profile
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureMarginInt n k (r + (A.start - 1)) ≤ 0 ∧
+      0 < SourcePressureMarginInt n k (r + A.start) ∧
+      0 < SourcePressureMarginInt n k (r + (A.start + A.len - 1)) ∧
+      SourcePressureMarginInt n k (r + (A.start + A.len)) ≤ 0 :=
+  ⟨sourcePressureIntervalPulseAddress_before_start_nonpos A,
+    sourcePressureIntervalPulseAddress_start_margin_pos A,
+    sourcePressureIntervalPulseAddress_end_margin_pos A,
+    sourcePressureIntervalPulseAddress_after_end_nonpos A⟩
+
+/--
+Accounting profile bundled for callers that need both boundary signs and the
+finite negative drive.
+
+This is the compact observation form of checkpoint 146 plus the follow-up
+accounting consequences.
+-/
+theorem sourcePressureIntervalPulseAddress_accounting_profile
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureMarginInt n k (r + (A.start - 1)) ≤ 0 ∧
+      0 < SourcePressureMarginInt n k (r + A.start) ∧
+      SourcePressureMarginInt n k (r + (A.start + A.len)) ≤ 0 ∧
+      (Finset.range A.len).sum (fun i =>
+        SourcePressureNetDropInt n k r (A.start + i)) < 0 ∧
+      (Finset.range A.len).sum (fun i =>
+        SourcePressureNetDropInt n k r (A.start + i)) ≤
+        -SourcePressureMarginInt n k (r + A.start) :=
+  ⟨sourcePressureIntervalPulseAddress_before_start_nonpos A,
+    sourcePressureIntervalPulseAddress_start_margin_pos A,
+    sourcePressureIntervalPulseAddress_after_end_nonpos A,
+    sourcePressureIntervalPulseAddress_sum_netDrop_neg A,
+    sourcePressureIntervalPulseAddress_sum_netDrop_le_neg_start_margin A⟩
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-147.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-147.md
new file mode 100644
index 00000000..8ade050e
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-147.md
@@ -0,0 +1,109 @@
+# report-petal-147
+
+Date: 2026-07-04
+
+## Checkpoint
+
+Follow-up implementation after checkpoint 146.
+
+Checkpoint 146 proved that an interval-pulse address has a negative accumulated
+net pressure drive.  This follow-up extracts stronger and more reusable
+accounting consequences from the same proof state.
+
+No maximality, uniqueness, coverage, prefix behavior, or Collatz convergence is
+introduced.
+
+## Code Changes
+
+Updated:
+
+- `lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean`
+
+Added algebraic/accounting corollaries:
+
+- `sourcePressureIntervalPulseAddress_sum_netDrop_eq_after_sub_start`
+- `sourcePressureIntervalPulseAddress_sum_netDrop_le_neg_start_margin`
+- `sourcePressureIntervalPulseAddress_start_margin_add_sum_netDrop_nonpos`
+- `sourcePressureIntervalPulseAddress_sum_netDrop_le_neg_one`
+
+Added bundled observation profiles:
+
+- `sourcePressureIntervalPulseAddress_endpoint_profile`
+- `sourcePressureIntervalPulseAddress_accounting_profile`
+
+## Resulting Reading
+
+The prior theorem said:
+
+```text
+sum netDrop < 0
+```
+
+The new theorems make the reason explicit:
+
+```text
+sum netDrop = afterMargin - startMargin
+afterMargin <= 0
+startMargin > 0
+therefore sum netDrop <= -startMargin <= -1
+```
+
+This is stronger than just proving negativity.  It says that the interval must
+pay at least the whole positive starting margin.
+
+## Why This Helps
+
+Later finite-budget arguments usually prefer non-strict inequalities over
+strict inequalities.  The new theorem
+
+```lean
+sourcePressureIntervalPulseAddress_sum_netDrop_le_neg_one
+```
+
+turns strict integer negativity into a budget-friendly `<= -1` form.
+
+The theorem
+
+```lean
+sourcePressureIntervalPulseAddress_sum_netDrop_le_neg_start_margin
+```
+
+is more informative: it records how much pressure must be cancelled by the
+finite interval drive.
+
+The bundled profile theorems are deliberately just projection conveniences.
+They let downstream code unpack one address object into the endpoint signs and
+accounting facts without repeatedly reopening the pulse construction.
+
+## Verification
+
+Passed:
+
+- `lake build DkMath.Collatz.PetalBridge.PressureAccounting`
+- `lake build DkMath.Collatz.PetalBridge`
+- `rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean`
+- `git diff --check`
+
+The `rg` command returned no matches.  The aggregate build still reports the
+pre-existing unrelated warning that
+`DkMath.NumberTheory.ZsigmondyCyclotomicResearch` contains a declaration using
+`sorry`.
+
+## Next Implementation Candidates
+
+The next useful layer is probably a named local carrier:
+
+```lean
+def SourcePressureAccountedInterval ...
+```
+
+This should remain thin and local.  It can package:
+
+- the address,
+- endpoint profile,
+- accumulated drive identity,
+- accumulated drive budget bound.
+
+Alternatively, if the next review prefers theorem-only growth, add list/finite
+family versions that sum over explicitly provided addresses.  That route should
+still avoid coverage and maximality claims unless they are separately proved.
````
`````
