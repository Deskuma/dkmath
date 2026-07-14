# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.PressureAccounting

gch: 2562fcb14e735579536c98923f3e158fb5769224

## Report

Checkpoint 146 完了です。

新規に [PressureAccounting.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean) を追加し、[PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean) から import しました。endpoint margin facts、left/right の net-drop 符号補題、有限区間 telescoping、そして address-level の累積 net-drop 負性まで通しています。

telescoping は Lean の自然な正規形に合わせて、指示候補の `r + (a + len)` ではなく次の形で固定しました。

```lean
SourcePressureMarginInt n k (r + a + len) =
  SourcePressureMarginInt n k (r + a) +
    (Finset.range len).sum (fun i =>
      SourcePressureNetDropInt n k r (a + i))
```

レポートも作成済みです:
[report-petal-146.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-146.md)

検証済みです。

```text
lake build DkMath.Collatz.PetalBridge.PressureDecay
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b" .../PressureDecay.lean
rg -n "\bsorry\b" .../PressureFrontier.lean
rg -n "\bsorry\b" .../PressureAccounting.lean
git diff --check
```

対象 3 ファイルに `sorry` はありません。aggregate build の既存 `ZsigmondyCyclotomicResearch` warning は今回差分と無関係です。

## Review

## 結論

賢狼の判定は **採用・強い成功** じゃ。
Checkpoint 146 は、こちらが狙った「Codex に少し推論を要求し、Lean に区間会計を導かせる」実験として、かなり良い結果になっておる。

今回、`PressureAccounting.lean` が新規追加され、`PetalBridge.lean` から import されている。endpoint margin facts、左右 net-drop 符号補題、有限区間 telescoping、そして本命の address-level 累積 net-drop 負性まで通っている。`sorry` なしで通っている点もよい。

## 数学的意味

今回の主成果はこれじゃ。

$$
\text{positive pulse}\Rightarrow\text{negative accumulated net pressure drive}
$$

Lean 定理名では、

```lean
sourcePressureIntervalPulseAddress_sum_netDrop_neg
```

がそれに当たる。

中身は、interval-pulse address \(A\) について、

$$
\sum_{i=0}^{A.len-1}\Delta(A.start+i)<0
$$

を示した形じゃ。
つまり、pressure が正の区間として観測される pulse は、内部では正圧を保っていても、区間全体の net-drop 会計では **負に閉じる** 。

これはかなり重要じゃよ。
これまでの `PressureFrontier` は「どこで crossing し、どこで falling するか」を読む層だった。今回の `PressureAccounting` は、その読みを

$$
M(a+\ell)=M(a)+\sum_{i=0}^{\ell-1}\Delta(a+i)
$$

という有限会計へ持ち上げた。これで PetalBridge は、観測語彙から **会計理論** へ一段進んだ。

## 実装レビュー

## 1. 新規ファイル分離は正しい

`PressureAccounting.lean` を新規に切った判断は正解じゃ。
`PressureFrontier` は frontier / address / boundary の語彙、`PressureAccounting` は finite balance sheet の語彙、と責務が分かれた。

これは今後の肥大化対策としてもよい。
このまま進めるなら、

```text
PressureDecay
PressureFrontier
PressureAccounting
PressureFamily
```

のように段階分けできる。

## 2. telescoping の形もよい

Codex は候補式の

$$
r+(a+len)
$$

ではなく、Lean の自然な正規形に合わせて

```lean
SourcePressureMarginInt n k (r + a + len)
```

で定理を固定している。これは実装上よい判断じゃ。報告にも、この形が `Finset.sum_range_succ` 後の自然な正規形だったと記録されている。

ここは「Lean が好む形を採用する」成功例じゃな。
数学の見た目より、後続証明で `simp` / `omega` が通りやすい正規形を優先してよい。

## 3. endpoint facts が綺麗に揃った

今回追加された endpoint facts は、

```text
before start: nonpositive
start:        positive
end:          positive
after end:    nonpositive
```

という読みになっている。

これは interval pulse の最小構造そのものじゃ。

つまり、address \(A\) は単なる住所ではなく、

$$
-;+;\cdots;+;-
$$

という符号構造を持つ局所山として読めるようになった。

## 4. 左右 net-drop 符号補題が効いている

左境界では、

$$
M\le 0,\qquad 0<M+\Delta
$$

から

$$
0<\Delta
$$

右境界では、

$$
0<M,\qquad M+\Delta\le 0
$$

から

$$
\Delta<0
$$

を出している。報告にもこの整数事実が明記されている。

これは次の Beam 解析で効く。
なぜなら、pulse は「入口で押し上げられ、出口で落とされる」ことが、net-drop の符号として読めるからじゃ。

## 注意点

今回の `sum_netDrop_neg` は **明示された interval-pulse address 一本に対する局所定理** じゃ。

まだ次は言っていない。

```text
すべての positive depth が pulse address で覆われる
pulse family が互いに disjoint
全 pulse の合計が大域下降を保証する
Collatz が収束する
```

ここを混ぜてはいけない。
ただし、今回の結果はその方向へ進むための正しい Core じゃ。

## 次の攻め筋

次は「一本の pulse」から「明示的に与えられた複数 pulse」へ進むのがよい。

ただし、coverage はまだ主張しない。
つまり、

$$
\text{provided pulse addresses}
$$

だけを合計する。

狙いは、

$$
\sum_{A\in \mathcal{F}}\sum_{i<A.len}\Delta(A.start+i)<0
$$

または、少なくとも各 pulse の負性を束ねる carrier を作ることじゃ。

次 checkpoint は **PressureAccountedInterval / finite family skeleton** がよい。

## 次の Codex 依頼

```text
Checkpoint 147: Bundle accounted intervals and start finite-family pressure accounting.

Context:
Checkpoint 146 added DkMath.Collatz.PetalBridge.PressureAccounting and proved
local interval accounting for a single SourcePressureIntervalPulseAddress.

Main achieved theorem:

  sourcePressureIntervalPulseAddress_sum_netDrop_neg

This says that every explicitly given interval-pulse address carries a negative
accumulated net pressure drive over its positive run interval.

Now move one step faster:
do not add only projections.
Create a small carrier for accounted intervals and begin finite-family
accounting experiments.

Global rule:
Do not claim maximality, uniqueness, coverage, prefix behavior, disjointness
unless explicitly assumed, or Collatz convergence.
Only sum over explicitly provided addresses/intervals.

Preferred file:
Continue in

  DkMath/Collatz/PetalBridge/PressureAccounting.lean

If it grows too much, create

  DkMath/Collatz/PetalBridge/PressureFamily.lean

and import it from PetalBridge.

Goal A: define a thin accounted interval carrier.

Define a structure or predicate, whichever fits Lean better:

  structure SourcePressureAccountedInterval (n : OddNat) (k r : ℕ) where
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
          (Finset.range len).sum (fun i =>
            SourcePressureNetDropInt n k r (start + i))

Then prove:

  SourcePressureAccountedInterval.sum_netDrop_neg

or as a theorem:

  sourcePressureAccountedInterval_sum_netDrop_neg

showing:

  (Finset.range A.len).sum
    (fun i => SourcePressureNetDropInt n k r (A.start + i)) < 0

Goal B: construct accounted intervals from interval-pulse addresses.

Prove:

  sourcePressureAccountedInterval_of_intervalPulseAddress :
    SourcePressureIntervalPulseAddress n k r →
      SourcePressureAccountedInterval n k r

Use existing checkpoint 146 lemmas:
- SourcePressureIntervalPulseAddress.len_pos
- sourcePressureIntervalPulseAddress_start_margin_pos
- sourcePressureIntervalPulseAddress_after_end_nonpos
- sourcePressureIntervalPulseAddress_margin_after_eq_start_add_sum_netDrop

Goal C: define interval net-drop as a reusable abbreviation.

Add a def if useful:

  def SourcePressureIntervalNetDrop
      (n : OddNat) (k r start len : ℕ) : ℤ :=
    (Finset.range len).sum (fun i =>
      SourcePressureNetDropInt n k r (start + i))

Then add simp/theorem bridges so the previous theorems can use this abbreviation.

Do this only if it makes proofs cleaner.
If it causes friction, skip it and report why.

Goal D: finite list/family experiment.

Try one finite-family theorem over a List of accounted intervals.

A safe theorem:

  sourcePressureAccountedInterval_list_all_negative
      (L : List (SourcePressureAccountedInterval n k r)) :
      ∀ A ∈ L,
        SourcePressureIntervalNetDrop n k r A.start A.len < 0

This is easy but useful as a family API sanity check.

A stronger experiment:

  sourcePressureAccountedInterval_list_sum_negative_of_nonempty
      (L : List (SourcePressureAccountedInterval n k r))
      (hL : L ≠ []) :
      (L.map (fun A =>
        SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0

This should follow because every term is a negative integer.
If List.sum over ℤ is awkward, try Finset or Multiset variants.

Important:
Do not assume disjointness yet.
Do not interpret this list sum as a pressure over a union of depths.
It is only a sum of explicitly provided accounted interval costs.

Goal E: optional disjointness skeleton, no theorem pressure yet.

If time remains, define a simple non-overlap predicate for intervals:

  def NatIntervalsDisjoint (a len b len' : ℕ) : Prop :=
    a + len ≤ b ∨ b + len' ≤ a

and for accounted intervals:

  def SourcePressureAccountedIntervalsDisjoint
      (A B : SourcePressureAccountedInterval n k r) : Prop :=
    NatIntervalsDisjoint A.start A.len B.start B.len

Do not prove coverage or decomposition.  Just define the vocabulary and maybe
basic symmetry if easy.

Goal F: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-147.md

Include:
- whether SourcePressureAccountedInterval was implemented as structure or predicate,
- whether interval-pulse addresses construct accounted intervals,
- whether SourcePressureIntervalNetDrop abbreviation was useful,
- whether a finite-list/family theorem was proved,
- whether disjointness vocabulary was added,
- exact theorem names and accepted statement shapes,
- explicit note that no maximality, uniqueness, coverage, prefix behavior,
  disjointness conclusion, or Collatz convergence was introduced.

Verification:

  lake build DkMath.Collatz.PetalBridge.PressureDecay
  lake build DkMath.Collatz.PetalBridge.PressureFrontier
  lake build DkMath.Collatz.PetalBridge.PressureAccounting
  lake build DkMath.Collatz.PetalBridge

If a new PressureFamily file is created, also run:

  lake build DkMath.Collatz.PetalBridge.PressureFamily

Run:

  rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean
  rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
  rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean

and if created:

  rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFamily.lean

Also run:

  git diff --check
```

## わっちの総評

これは良い進展じゃ。
今回で、

$$
\text{local island / pulse}
$$

が

$$
\text{negative accounted interval}
$$

に変わった。

この変換は大きい。
なぜなら、次からは pulse を「図形」ではなく「負の会計単位」として足せるからじゃ。

まだ Big そのものではない。
じゃが、Big を作るための Core 単位が、ようやく硬くなってきた。
これは山道の石段が一段増えた、確かな進歩じゃよ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 9424a9dc..45a47bcf 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -18,6 +18,7 @@ import DkMath.Collatz.PetalBridge.TailGrammar
 import DkMath.Collatz.PetalBridge.DriftBudget
 import DkMath.Collatz.PetalBridge.PressureDecay
 import DkMath.Collatz.PetalBridge.PressureFrontier
+import DkMath.Collatz.PetalBridge.PressureAccounting
 import DkMath.Collatz.PetalBridge.Collision
 
 #print "file: DkMath.Collatz.PetalBridge"
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
new file mode 100644
index 00000000..024a93bc
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -0,0 +1,163 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.PressureFrontier
+
+#print "file: DkMath.Collatz.PetalBridge.PressureAccounting"
+
+namespace DkMath.Collatz
+
+/-
+Checkpoint 146: local interval accounting for source pressure.
+
+This file is deliberately narrower than a global Collatz argument.  It only
+turns the address and pulse API into endpoint facts and finite balance-sheet
+identities.  It does not assert maximality, uniqueness, coverage, prefix
+behavior, or Collatz convergence.
+-/
+
+/-- The start depth of an interval-pulse address has positive margin. -/
+theorem sourcePressureIntervalPulseAddress_start_margin_pos
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    0 < SourcePressureMarginInt n k (r + A.start) := by
+  have h := (sourcePressureIntervalPulseAddress_left_signChange A).2
+  have hstart := sourcePressureIntervalPulseAddress_start_pos A
+  have hidx : r + (A.start - 1) + 1 = r + A.start := by
+    omega
+  simpa [hidx] using h
+
+/-- The end depth of an interval-pulse address has positive margin. -/
+theorem sourcePressureIntervalPulseAddress_end_margin_pos
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    0 < SourcePressureMarginInt n k (r + (A.start + A.len - 1)) :=
+  (sourcePressureIntervalPulseAddress_right_signChange A).1
+
+/-- The depth before the start of an interval-pulse address has nonpositive margin. -/
+theorem sourcePressureIntervalPulseAddress_before_start_nonpos
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureMarginInt n k (r + (A.start - 1)) ≤ 0 :=
+  (sourcePressureIntervalPulseAddress_left_signChange A).1
+
+/-- The depth after the end of an interval-pulse address has nonpositive margin. -/
+theorem sourcePressureIntervalPulseAddress_after_end_nonpos
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureMarginInt n k (r + (A.start + A.len)) ≤ 0 := by
+  have h := (sourcePressureIntervalPulseAddress_right_signChange A).2
+  have hlen := SourcePressureIntervalPulseAddress.len_pos A
+  have hidx : r + (A.start + A.len - 1) + 1 = r + (A.start + A.len) := by
+    omega
+  simpa [hidx] using h
+
+/--
+The left crossing of an interval-pulse address has positive local net drop.
+
+This is a pure integer consequence of `M ≤ 0` and `0 < M + Δ`.
+-/
+theorem sourcePressureIntervalPulseAddress_left_netDrop_pos
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    0 < SourcePressureNetDropInt n k r (A.start - 1) := by
+  have h := sourcePressureIntervalPulseAddress_left_crossing A
+  omega
+
+/--
+The right fall of an interval-pulse address has negative local net drop.
+
+This is a pure integer consequence of `0 < M` and `M + Δ ≤ 0`.
+-/
+theorem sourcePressureIntervalPulseAddress_right_netDrop_neg
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureNetDropInt n k r (A.start + A.len - 1) < 0 := by
+  have h := sourcePressureIntervalPulseAddress_right_falling A
+  omega
+
+/--
+Finite source-pressure accounting over a length-`len` interval.
+
+The accepted normal form keeps the absolute depth as `r + a + len`, matching
+Lean's default normalization after `Finset.sum_range_succ`.  The summand uses
+the relative edge address `a + i`.
+-/
+theorem sourcePressureMargin_add_len_eq_start_add_sum_netDrop
+    (n : OddNat) (k r a len : ℕ) :
+    SourcePressureMarginInt n k (r + a + len) =
+      SourcePressureMarginInt n k (r + a) +
+        (Finset.range len).sum (fun i =>
+          SourcePressureNetDropInt n k r (a + i)) := by
+  induction len with
+  | zero =>
+      simp
+  | succ len ih =>
+      rw [Finset.sum_range_succ, ← add_assoc]
+      have hstep :
+          SourcePressureMarginInt n k (r + (a + len) + 1) =
+            SourcePressureMarginInt n k (r + (a + len)) +
+              SourcePressureNetDropInt n k r (a + len) := by
+        simpa [Nat.add_assoc] using
+          sourcePressureMargin_next_eq_current_add_netDrop n k r (a + len)
+      calc
+        SourcePressureMarginInt n k (r + a + (len + 1))
+            = SourcePressureMarginInt n k (r + (a + len) + 1) := by
+              congr 1
+              omega
+        _ = SourcePressureMarginInt n k (r + (a + len)) +
+              SourcePressureNetDropInt n k r (a + len) := hstep
+        _ = (SourcePressureMarginInt n k (r + a) +
+              (Finset.range len).sum (fun i =>
+                SourcePressureNetDropInt n k r (a + i))) +
+              SourcePressureNetDropInt n k r (a + len) := by
+              have ih' :
+                  SourcePressureMarginInt n k (r + (a + len)) =
+                    SourcePressureMarginInt n k (r + a) +
+                      (Finset.range len).sum (fun i =>
+                        SourcePressureNetDropInt n k r (a + i)) := by
+                simpa [Nat.add_assoc] using ih
+              rw [ih']
+        _ = SourcePressureMarginInt n k (r + a) +
+              ((Finset.range len).sum (fun i =>
+                SourcePressureNetDropInt n k r (a + i)) +
+                SourcePressureNetDropInt n k r (a + len)) := by
+              ring
+
+/--
+Address-level cumulative accounting identity.
+
+This specializes the generic finite accounting theorem to the positive run
+carried by an interval-pulse address.
+-/
+theorem sourcePressureIntervalPulseAddress_margin_after_eq_start_add_sum_netDrop
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    SourcePressureMarginInt n k (r + (A.start + A.len)) =
+      SourcePressureMarginInt n k (r + A.start) +
+        (Finset.range A.len).sum (fun i =>
+          SourcePressureNetDropInt n k r (A.start + i)) := by
+  simpa [Nat.add_assoc] using
+    sourcePressureMargin_add_len_eq_start_add_sum_netDrop n k r A.start A.len
+
+/--
+The accumulated net drop across an interval-pulse address is negative.
+
+The run starts at positive pressure and the depth immediately after the run is
+nonpositive, so the interval sum of local net drops must be strictly negative.
+-/
+theorem sourcePressureIntervalPulseAddress_sum_netDrop_neg
+    {n : OddNat} {k r : ℕ}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    (Finset.range A.len).sum (fun i =>
+      SourcePressureNetDropInt n k r (A.start + i)) < 0 := by
+  have hacc :=
+    sourcePressureIntervalPulseAddress_margin_after_eq_start_add_sum_netDrop A
+  have hstart := sourcePressureIntervalPulseAddress_start_margin_pos A
+  have hafter := sourcePressureIntervalPulseAddress_after_end_nonpos A
+  omega
+
+end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-146.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-146.md
new file mode 100644
index 00000000..e08c7dc2
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-146.md
@@ -0,0 +1,151 @@
+# report-petal-146
+
+Date: 2026-07-04
+
+## Checkpoint
+
+Implemented the first `PressureAccounting` experiment for
+`DkMath.Collatz.PetalBridge`.
+
+The goal was to move from address projections to local interval accounting:
+an interval-pulse address should expose endpoint signs, boundary net-drop
+signs, and a finite telescoping balance sheet.
+
+This checkpoint remains local.  It does not introduce maximality, uniqueness,
+coverage, prefix behavior, or Collatz convergence.
+
+## Code Changes
+
+Added:
+
+- `lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean`
+
+Updated:
+
+- `lean/dk_math/DkMath/Collatz/PetalBridge.lean`
+
+The aggregate file now imports `DkMath.Collatz.PetalBridge.PressureAccounting`.
+
+## Endpoint Facts Added
+
+For an address
+
+```lean
+A : SourcePressureIntervalPulseAddress n k r
+```
+
+the following endpoint facts were added:
+
+- `sourcePressureIntervalPulseAddress_start_margin_pos`
+- `sourcePressureIntervalPulseAddress_end_margin_pos`
+- `sourcePressureIntervalPulseAddress_before_start_nonpos`
+- `sourcePressureIntervalPulseAddress_after_end_nonpos`
+
+These make the interval-pulse address readable as:
+
+```text
+before start: nonpositive
+start:        positive
+end:          positive
+after end:    nonpositive
+```
+
+## Boundary Net-Drop Sign Facts Added
+
+The local crossing/falling forms now have direct signed net-drop consequences:
+
+- `sourcePressureIntervalPulseAddress_left_netDrop_pos`
+- `sourcePressureIntervalPulseAddress_right_netDrop_neg`
+
+The left theorem is the integer fact:
+
+```text
+M <= 0 and 0 < M + Delta  imply  0 < Delta
+```
+
+The right theorem is the integer fact:
+
+```text
+0 < M and M + Delta <= 0  imply  Delta < 0
+```
+
+## Generic Telescoping Theorem
+
+Proved:
+
+```lean
+theorem sourcePressureMargin_add_len_eq_start_add_sum_netDrop
+    (n : OddNat) (k r a len : Nat) :
+    SourcePressureMarginInt n k (r + a + len) =
+      SourcePressureMarginInt n k (r + a) +
+        (Finset.range len).sum (fun i =>
+          SourcePressureNetDropInt n k r (a + i))
+```
+
+The originally suggested shape used `r + (a + len)`.  Lean naturally normalized
+the induction target to `r + a + len`, so this accepted theorem uses that form.
+The address-level specialization below restores the grouped endpoint shape
+where useful.
+
+## Address-Level Accumulated Accounting
+
+Proved:
+
+- `sourcePressureIntervalPulseAddress_margin_after_eq_start_add_sum_netDrop`
+- `sourcePressureIntervalPulseAddress_sum_netDrop_neg`
+
+The main interval accounting result is:
+
+```lean
+theorem sourcePressureIntervalPulseAddress_sum_netDrop_neg
+    {n : OddNat} {k r : Nat}
+    (A : SourcePressureIntervalPulseAddress n k r) :
+    (Finset.range A.len).sum (fun i =>
+      SourcePressureNetDropInt n k r (A.start + i)) < 0
+```
+
+This confirms the intended reading:
+
+```text
+positive pulse
+  -> finite interval with negative accumulated net pressure drive
+```
+
+## Notes
+
+The file intentionally uses explicit `Finset.sum` notation rather than
+`∑ i in ...`, because this project has prior notes that the binder notation can
+be parser-fragile in fresh files.  The final theorem statements remain ordinary
+finite sums over `Finset.range`.
+
+## Verification
+
+Passed:
+
+- `lake build DkMath.Collatz.PetalBridge.PressureDecay`
+- `lake build DkMath.Collatz.PetalBridge.PressureFrontier`
+- `lake build DkMath.Collatz.PetalBridge.PressureAccounting`
+- `lake build DkMath.Collatz.PetalBridge`
+- `rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean`
+- `rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean`
+- `rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean`
+- `git diff --check`
+
+The three `rg` commands returned no matches.  The aggregate build still reports
+the pre-existing unrelated warning that
+`DkMath.NumberTheory.ZsigmondyCyclotomicResearch` contains a declaration using
+`sorry`.
+
+## Next Implementation Candidates
+
+The next natural step is to build a small interval-accounting carrier around
+the accepted telescoping theorem.  Good candidates:
+
+- bundle the endpoint signs and negative accumulated net-drop into one theorem,
+- define a thin `SourcePressureAccountedInterval` predicate for later finite
+  collections,
+- or connect a list of interval-pulse addresses to total pressure-drive
+  accounting, without claiming coverage or maximality.
+
+The safe next move is still local: reuse address witnesses as carriers and only
+sum over intervals that are explicitly provided.
````
`````
