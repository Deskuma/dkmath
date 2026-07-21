# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.PressureDecay

gch: 7b5fae411f4f765829b55f96e38eafe6f5dcfc5e

## Report

Checkpoint 143 完了です。

新規 [PressureDecay.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean) を作り、汎用の pressure-decay 層を `PressureFrontier` から分離しました。移動対象は `SourcePressureMarginInt`、drop/net-drop、sign-change、margin jump、pulse 系の import-safe な宣言群です。

[PressureFrontier.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean) には、frontier / local-island / prefix / positive block / run / interval pulse と、それらに関わる bridge theorem を残しています。`SourcePressureRun` / interval 系は `SourcePressurePositiveBlock` と `IsSourcePressureDepth` に依存するため、今回は安全側で移動しませんでした。

親 aggregate [PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean) には `PressureDecay` import を `PressureFrontier` の前に追加済みです。report は [report-petal-143.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-143.md) に作成しました。

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureDecay` pass
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier` pass
- `lake build DkMath.Collatz.PetalBridge` pass
- `rg -n "\bsorry\b" .../PressureDecay.lean` no hits
- `rg -n "\bsorry\b" .../PressureFrontier.lean` no hits
- `git diff --check` pass

既存の `ZsigmondyCyclotomicResearch` の `sorry` warning は今回範囲外です。

## Review

## 状況分析

Checkpoint `143` は、かなり良い分割 checkpoint じゃ。

新規 `PressureDecay.lean` が作られ、`PressureFrontier.lean` から汎用の pressure-decay 層が分離された。移動されたのは `SourcePressureMarginInt`、drop / net-drop、sign-change、margin jump、pulse 系の import-safe な宣言群で、`PressureFrontier.lean` には frontier / local-island / prefix / positive block / run / interval pulse と、それらに関わる bridge theorem が残されている。

親 aggregate `PetalBridge.lean` でも `PressureDecay` が `PressureFrontier` の前に import されており、依存形は、

```text id="xg1lwv"
DriftBudget
  -> PressureDecay
  -> PressureFrontier
  -> Collision / parent aggregate
```

として整理された。これはかなり綺麗じゃ。

## レビュー

## 良い点

第一に、分割範囲がちょうど良い。

今回 `PressureDecay.lean` に移したのは、frontier や local island に依存しない **汎用の整数 pressure 保存会計層**じゃ。

```text id="fvwzvj"
SourcePressureMarginInt
SourceRetentionDropInt
SourceContinuationDropInt
SourcePressureNetDropInt
SourcePressureNetDropPositive

sourcePressureMarginStepDiff_eq
sourcePressureMargin_next_eq_current_add_netDrop

SourcePressureSignChangeUp
SourcePressureSignChangeDown
SourcePressureMarginJumpUp

SourcePressurePulse
SourcePressureSignPulse
```

このあたりは、frontier という観測語彙より下にある「力学層」なので、切り出し先として自然じゃ。

第二に、`SourcePressureRun` / interval 系を無理に移さなかったのが良い。

`SourcePressureRun` は `SourcePressurePositiveBlock` の alias であり、`SourcePressurePositiveBlock` は `IsSourcePressureDepth` に依存している。ここを無理に `PressureDecay` 側へ動かすと、selected pressure-depth 層まで移動する必要が出て、分割が大きくなる。今回そこを避けたのは正しい。

第三に、public API を壊していない。

親 aggregate が `PressureDecay` を import するので、

```lean id="uvnmuj"
import DkMath.Collatz.PetalBridge
```

を使う側からは、移動後も同じ宣言名が見える。これは refactor checkpoint として重要じゃ。

第四に、`PressureFrontier` の意味がはっきりした。

今後はこう読める。

```text id="lv8pfq"
PressureDecay:
  margin / drop / netDrop / crossing / falling / pulse の保存会計層

PressureFrontier:
  IsSourcePressureDepth / frontier / local island / prefix / positive block / run / interval pulse の観測層
```

これは、宇宙式語彙で言えば、

```text id="3xafnv"
PressureDecay:
  保存会計の力学

PressureFrontier:
  境界に現れる観測構造
```

じゃ。

## 注意点

次に注意すべきは、これ以上 `PressureFrontier.lean` に数学語彙を積みすぎると、また肥大化する点じゃ。

今回の split で `PressureDecay` は切れた。
しかし `PressureFrontier` にはまだ、

```text id="oz7y9c"
frontier
local island
positive block
run
interval pulse
prefix failure
existence below
island-facing bridge
```

が残っている。

したがって、次の数学追加は薄くするのがよい。
いきなり maximality / uniqueness / coverage へ進むより、まず **address vocabulary** を置くのが安全じゃ。

## 解説

ここまでの構造は、かなり DkMath らしくなった。

最下層に、

```text id="wwe32g"
next margin = current margin + netDrop
```

という局所保存会計がある。

その上に、

```text id="wq2do8"
crossing up
falling down
pulse
```

がある。

さらにその上に、

```text id="lymunp"
positive block
run
interval pulse
frontier
local island
```

がある。

つまり、以前の「prefix failure」は単なる失敗ではなく、

```text id="3twgpg"
保存会計の上に現れる圧力島の住所
```

として扱えるところまで来ている。

今回の分割は、その層構造を Lean ファイル構造に反映したものじゃ。

## 次の指示

Checkpoint `144` は、数学へ戻って **SourcePressureRunAddress / SourcePressureIntervalPulseAddress** を薄く置くのがよい。

目的は、positive run / interval pulse を「住所」として扱う準備をすることじゃ。
ただし、まだ maximality や uniqueness は入れない。

## Checkpoint 144 推奨内容

## 1. run address 構造体を置く

`PressureFrontier.lean` 側に置くのが自然じゃ。
`SourcePressureRun` と `SourcePressureIntervalPulse` が frontier 側に残っているからじゃ。

未検証スケッチ：

```lean id="u8xzxu"
structure SourcePressureRunAddress
    (n : OddNat) (k r : ℕ) where
  start : ℕ
  len : ℕ
  hrun : SourcePressureRun n k r start len
```

これは、

```text id="jz8sk8"
n, k, r の観測窓において、
start から len だけ positive run がある
```

という住所じゃ。

## 2. interval pulse address 構造体を置く

```lean id="v3wx0n"
structure SourcePressureIntervalPulseAddress
    (n : OddNat) (k r : ℕ) where
  start : ℕ
  len : ℕ
  hpulse : SourcePressureIntervalPulse n k r start len
```

これは、

```text id="hq6zn9"
run + left crossing + right fall
```

まで持つ住所じゃ。

## 3. interval pulse address から run address を取り出す

```lean id="b6z30n"
def SourcePressureIntervalPulseAddress.toRunAddress
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    SourcePressureRunAddress n k r where
  start := A.start
  len := A.len
  hrun := sourcePressureIntervalPulse_run A.hpulse
```

これは綺麗に通る可能性が高い。

## 4. address の depth start / end を定義する

住所として扱うなら、実際の pressure depth も欲しい。

```lean id="oysd9e"
def SourcePressureRunAddress.depthStart
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureRunAddress n k r) : ℕ :=
  r + A.start
```

```lean id="7i8jgt"
def SourcePressureRunAddress.depthEnd
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureRunAddress n k r) : ℕ :=
  r + (A.start + A.len - 1)
```

interval 側も同様にしてもよいが、まず `toRunAddress` 経由で十分かもしれぬ。

## 5. projection helper を薄く置く

```lean id="gh93bt"
theorem sourcePressureIntervalPulseAddress_left_signChange
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    SourcePressureSignChangeUp n k r (A.start - 1) :=
  sourcePressureIntervalPulse_left_signChange A.hpulse
```

```lean id="cwuzjb"
theorem sourcePressureIntervalPulseAddress_right_signChange
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    SourcePressureSignChangeDown n k r (A.start + A.len - 1) :=
  sourcePressureIntervalPulse_right_signChange A.hpulse
```

## 6. local island から interval pulse address を作る

既に `sourcePressureIntervalPulse_singleton_of_localIsland` があるので、これを住所に包む。

```lean id="ozjfxi"
def sourcePressureIntervalPulseAddress_of_localIsland
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j) :
    SourcePressureIntervalPulseAddress n k r where
  start := j
  len := 1
  hpulse := sourcePressureIntervalPulse_singleton_of_localIsland n k r j hisland
```

これにより、

```text id="eypbvn"
local island
  -> interval pulse of length 1
  -> interval pulse address
```

が閉じる。

## 一歩先ゆく推論

この address vocabulary が入ると、positive pressure の扱いがかなり変わる。

今までは、

```text id="6fbvje"
どの depth が positive か
```

を見ていた。

次は、

```text id="9lzvnu"
positive run はどこから始まり、
どれだけ続き、
どこで落ちるか
```

を住所として扱える。

これは宇宙式語彙でいうと、

```text id="hx1lql"
Body が現れる区間
Gap が境界を作る位置
NetDrop が境界を跨がせる edge
```

を持つということじゃ。

この段階に来ると、Collatz/PetalBridge の pressure 解析は、単なる sign scan から **finite pressure geometry** に移り始める。

## さらなる次の一手

Checkpoint `144` で address が入ったら、Checkpoint `145` では二択。

## Route A: address extraction from interval pulse

`SourcePressureIntervalPulseAddress` の左右 crossing / falling / run / start / end を、さらに projection theorem として整える。

## Route B: frontier/run-facing split

`PressureFrontier.lean` がさらに育つなら、次は `PressureRun.lean` や `PressureAddress.lean` を切る可能性がある。

候補：

```text id="jagqrb"
DkMath.Collatz.PetalBridge.PressureRun
```

または、

```text id="cm4jq2"
DkMath.Collatz.PetalBridge.PressureAddress
```

ただし、今はまだ新ファイルを増やしすぎない方がよい。
Checkpoint `144` は `PressureFrontier.lean` に薄く address を置くだけで十分じゃ。

## 賢狼が試して欲しい実験補題

## 実験 A: run address

```lean id="h7yiga"
structure SourcePressureRunAddress
    (n : OddNat) (k r : ℕ) where
  start : ℕ
  len : ℕ
  hrun : SourcePressureRun n k r start len
```

## 実験 B: interval pulse address

```lean id="t9f53i"
structure SourcePressureIntervalPulseAddress
    (n : OddNat) (k r : ℕ) where
  start : ℕ
  len : ℕ
  hpulse : SourcePressureIntervalPulse n k r start len
```

## 実験 C: interval address to run address

```lean id="l62ga4"
def SourcePressureIntervalPulseAddress.toRunAddress
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    SourcePressureRunAddress n k r where
  start := A.start
  len := A.len
  hrun := sourcePressureIntervalPulse_run A.hpulse
```

## 実験 D: depth start / end

```lean id="m9qld4"
def SourcePressureRunAddress.depthStart
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureRunAddress n k r) : ℕ :=
  r + A.start
```

```lean id="aqud78"
def SourcePressureRunAddress.depthEnd
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureRunAddress n k r) : ℕ :=
  r + (A.start + A.len - 1)
```

## 実験 E: local island to interval address

```lean id="oqy6ch"
def sourcePressureIntervalPulseAddress_of_localIsland
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j) :
    SourcePressureIntervalPulseAddress n k r where
  start := j
  len := 1
  hpulse := sourcePressureIntervalPulse_singleton_of_localIsland n k r j hisland
```

## Python 側

今回は Python 変更なしでよい。
Checkpoint `144` は Lean vocabulary の整備を主にするのがよい。

## 総括

Checkpoint `143` は成功じゃ。

`PressureDecay.lean` ができたことで、pressure 保存会計層がきれいに分離された。

```text id="k9g2qy"
PressureDecay:
  局所保存会計

PressureFrontier:
  境界・島・run 観測
```

次は、`PressureFrontier` 側で `SourcePressureRunAddress` / `SourcePressureIntervalPulseAddress` を薄く入れる。
これにより、positive run / interval pulse を「圧力島の住所」として扱う準備ができる。

## Codex instructions

```text id="h2b9l6"
Checkpoint 144:
Return to math after the PressureDecay split by adding thin address vocabulary
for positive pressure runs and interval pulses.

Context:
  Checkpoint 143 created:
    DkMath.Collatz.PetalBridge.PressureDecay

  Moved generic pressure-decay declarations there.
  Kept frontier/local-island/positive-block/run/interval-facing vocabulary in:
    DkMath.Collatz.PetalBridge.PressureFrontier

  SourcePressureRun and SourcePressureIntervalPulse remain in PressureFrontier.

Primary goal:
  Add a small address layer for runs and interval pulses.
  This should package start/length witnesses without adding maximality,
  uniqueness, coverage, or prefix claims.

Preferred Lean location:
  DkMath.Collatz.PetalBridge.PressureFrontier

Implement:
  1. Define structure:
     SourcePressureRunAddress (n : OddNat) (k r : Nat)

     Suggested fields:
       start : Nat
       len   : Nat
       hrun  : SourcePressureRun n k r start len

  2. Define structure:
     SourcePressureIntervalPulseAddress (n : OddNat) (k r : Nat)

     Suggested fields:
       start  : Nat
       len    : Nat
       hpulse : SourcePressureIntervalPulse n k r start len

  3. Define:
     SourcePressureIntervalPulseAddress.toRunAddress

     It should produce a SourcePressureRunAddress using:
       sourcePressureIntervalPulse_run

  4. Add simple address helpers:
       SourcePressureRunAddress.depthStart
       SourcePressureRunAddress.depthEnd

     Suggested:
       depthStart := r + A.start
       depthEnd   := r + (A.start + A.len - 1)

  5. Add interval-address projection helpers:
       sourcePressureIntervalPulseAddress_left_signChange
       sourcePressureIntervalPulseAddress_right_signChange

     Use:
       sourcePressureIntervalPulse_left_signChange
       sourcePressureIntervalPulse_right_signChange

  6. Add local-island constructor:
       sourcePressureIntervalPulseAddress_of_localIsland

     Suggested:
       start := j
       len := 1
       hpulse := sourcePressureIntervalPulse_singleton_of_localIsland n k r j hisland

Python:
  No Python change required.

Verification:
  Run:
    lake build DkMath.Collatz.PetalBridge.PressureDecay
    lake build DkMath.Collatz.PetalBridge.PressureFrontier
    lake build DkMath.Collatz.PetalBridge
    rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean
    rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
    git diff --check

Do not:
  introduce Real.log
  claim a pressure prefix theorem
  define full ShapePressureGrid
  prove deep all-ones excursion implies positive block
  conflate time index i with pressure-depth index j
  add maximality or uniqueness for runs
  perform broad refactoring
  change public theorem names

Next checkpoint hint:
  After address vocabulary is in place, consider:
    - projection helpers from addresses,
    - or a small PressureAddress / PressureRun split if PressureFrontier grows.
```

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 919af434..9424a9dc 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -16,6 +16,7 @@ import DkMath.Collatz.PetalBridge.HeightBudget
 import DkMath.Collatz.PetalBridge.TailSplits
 import DkMath.Collatz.PetalBridge.TailGrammar
 import DkMath.Collatz.PetalBridge.DriftBudget
+import DkMath.Collatz.PetalBridge.PressureDecay
 import DkMath.Collatz.PetalBridge.PressureFrontier
 import DkMath.Collatz.PetalBridge.Collision

diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean
new file mode 100644
index 00000000..c1ce02e7
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean
@@ -0,0 +1,328 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.DriftBudget
+
+#print "file: DkMath.Collatz.PetalBridge.PressureDecay"
+
+namespace DkMath.Collatz
+
+
+/-
+This module is the first import-safe split from `PressureFrontier`.
+
+It owns the generic pressure-depth balance vocabulary:
+
+* integer margin and adjacent drops,
+* net-drop balance identities,
+* adjacent sign changes,
+* pressure-margin jumps,
+* local pulse predicates that do not mention frontiers or local islands.
+
+Island-facing and frontier-facing bridge theorems stay in
+`PressureFrontier`.  In particular, this file deliberately does not import
+frontier/local-island predicates, so it can sit below `PressureFrontier`
+without creating an import cycle.
+-/
+
+/--
+Integer-valued source pressure margin at a single depth.
+
+The margin is positive exactly when source continuation occupies more than
+half of source retention.  It is intentionally integer-valued, because the
+natural-number subtraction would truncate negative margins and hide failures.
+-/
+noncomputable def SourcePressureMarginInt
+    (n : OddNat) (k r : ℕ) : ℤ :=
+  (2 * orbitWindowContinuationSiblingMassPow2 n k r : ℤ) -
+    (orbitWindowRetentionMassPow2 n k r : ℤ)
+
+/--
+Integer-valued retention drop across adjacent pressure depths.
+
+The sign convention is `current - next`.  This is the convention used by the
+Python pressure scan and by the checkpoint-136 balance sheet.  Keeping it as
+an integer avoids truncation when a later experiment crosses a non-monotone
+edge.
+-/
+noncomputable def SourceRetentionDropInt
+    (n : OddNat) (k r j : ℕ) : ℤ :=
+  (orbitWindowRetentionMassPow2 n k (r + j) : ℤ) -
+    (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ)
+
+/--
+Integer-valued continuation drop across adjacent pressure depths.
+
+This uses the same `current - next` convention as `SourceRetentionDropInt`.
+The continuation term appears with coefficient `2` in the source pressure
+margin, so the net pressure contribution is
+`retention_drop - 2 * continuation_drop`.
+-/
+noncomputable def SourceContinuationDropInt
+    (n : OddNat) (k r j : ℕ) : ℤ :=
+  (orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) -
+    (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ)
+
+/--
+Integer-valued net pressure drop across adjacent pressure depths.
+
+This is only a name for the balance quantity
+`retention_drop - 2 * continuation_drop`.  Existing predicates keep their
+current API, while later zero-crossing theorems can refer to this single
+integer expression.
+-/
+noncomputable def SourcePressureNetDropInt
+    (n : OddNat) (k r j : ℕ) : ℤ :=
+  SourceRetentionDropInt n k r j -
+    2 * SourceContinuationDropInt n k r j
+
+/--
+Adjacent source-pressure margin accounting identity.
+
+This is the checkpoint-136 balance sheet.  A positive pressure step is exactly
+the net effect of losing retention mass faster than twice the continuation
+mass across the same adjacent pressure-depth edge.  No global pressure-prefix
+or dominance theorem is asserted here.
+-/
+theorem sourcePressureMarginStepDiff_eq
+    (n : OddNat) (k r j : ℕ) :
+    SourcePressureMarginInt n k (r + j + 1) -
+        SourcePressureMarginInt n k (r + j) =
+      SourcePressureNetDropInt n k r j := by
+  unfold SourcePressureMarginInt
+  unfold SourcePressureNetDropInt SourceRetentionDropInt SourceContinuationDropInt
+  ring
+
+/--
+Next adjacent source-pressure margin as current margin plus net pressure drop.
+
+This is the additive zero-crossing form of the checkpoint-136 balance sheet.
+It is still local to one adjacent pressure-depth edge.
+-/
+theorem sourcePressureMargin_next_eq_current_add_netDrop
+    (n : OddNat) (k r j : ℕ) :
+    SourcePressureMarginInt n k (r + j + 1) =
+      SourcePressureMarginInt n k (r + j) +
+        SourcePressureNetDropInt n k r j := by
+  have h := sourcePressureMarginStepDiff_eq n k r j
+  rw [← h]
+  ring
+
+/--
+Upward sign change of the source-pressure margin between adjacent depths.
+
+This is a small building block for pressure-frontier and pressure-island
+classification.  It is stated directly in margin language because the
+checkpoint-125 correction is that pressure should be studied as a sign profile,
+not as raw carrier membership.
+-/
+def SourcePressureSignChangeUp
+    (n : OddNat) (k r j : ℕ) : Prop :=
+  SourcePressureMarginInt n k (r + j) ≤ 0 ∧
+    0 < SourcePressureMarginInt n k (r + j + 1)
+
+/--
+Downward sign change of the source-pressure margin between adjacent depths.
+
+This is the right-edge companion to `SourcePressureSignChangeUp`: the current
+depth is positive, while the next adjacent pressure depth is nonpositive.
+-/
+def SourcePressureSignChangeDown
+    (n : OddNat) (k r j : ℕ) : Prop :=
+  0 < SourcePressureMarginInt n k (r + j) ∧
+    SourcePressureMarginInt n k (r + j + 1) ≤ 0
+
+/--
+Named pressure-margin jump between adjacent pressure depths.
+
+Checkpoint 134 starts the thin `PressureDecayProfile` vocabulary here rather
+than introducing a full grid.  The predicate only compares adjacent pressure
+depths `r + j` and `r + j + 1`; it says nothing about time indices and does
+not assert that selected pressure depths form a prefix.
+-/
+def SourcePressureMarginJumpUp
+    (n : OddNat) (k r j : ℕ) : Prop :=
+  SourcePressureMarginInt n k (r + j) <
+    SourcePressureMarginInt n k (r + j + 1)
+
+/--
+Positive net integer drop across an adjacent pressure-depth edge.
+
+This is intentionally not named `RetentionDropDominant` yet.  The predicate is
+the algebraic quantity that actually appears in the margin-step identity:
+retention loss minus twice continuation loss.
+-/
+def SourcePressureNetDropPositive
+    (n : OddNat) (k r j : ℕ) : Prop :=
+  0 < SourcePressureNetDropInt n k r j
+
+/--
+Strict adjacent margin jump is equivalent to positive integer step
+difference.
+-/
+theorem sourcePressureMarginJumpUp_iff_stepDiff_pos
+    (n : OddNat) (k r j : ℕ) :
+    SourcePressureMarginJumpUp n k r j ↔
+      0 <
+        SourcePressureMarginInt n k (r + j + 1) -
+          SourcePressureMarginInt n k (r + j) := by
+  unfold SourcePressureMarginJumpUp
+  omega
+
+/--
+Positive net retention/continuation drop forces a named pressure-margin jump.
+
+This is the first Lean use of the checkpoint-136 balance sheet.  It remains a
+local adjacent-edge theorem; it does not claim any global prefix shape for
+selected pressure depths.
+-/
+theorem sourcePressureMarginJumpUp_of_netDropPositive
+    (n : OddNat) (k r j : ℕ)
+    (h : SourcePressureNetDropPositive n k r j) :
+    SourcePressureMarginJumpUp n k r j := by
+  rw [sourcePressureMarginJumpUp_iff_stepDiff_pos]
+  unfold SourcePressureNetDropPositive at h
+  rw [sourcePressureMarginStepDiff_eq]
+  exact h
+
+/--
+A named pressure-margin jump gives positive net integer pressure drop.
+
+Together with `sourcePressureMarginJumpUp_of_netDropPositive`, this closes the
+local checkpoint-137 equivalence between adjacent margin jumps and the integer
+balance sheet.  This remains strictly local to one adjacent pressure-depth
+edge.
+-/
+theorem sourcePressureNetDropPositive_of_marginJumpUp
+    (n : OddNat) (k r j : ℕ)
+    (h : SourcePressureMarginJumpUp n k r j) :
+    SourcePressureNetDropPositive n k r j := by
+  unfold SourcePressureNetDropPositive
+  rw [← sourcePressureMarginStepDiff_eq]
+  exact (sourcePressureMarginJumpUp_iff_stepDiff_pos n k r j).1 h
+
+/--
+Adjacent pressure-margin jump is exactly positive net pressure drop.
+
+This theorem is the stable local API for later pressure-decay work.  It should
+be preferred over introducing a global or dominance-sounding predicate until a
+specific downstream theorem requires that stronger vocabulary.
+-/
+theorem sourcePressureMarginJumpUp_iff_netDropPositive
+    (n : OddNat) (k r j : ℕ) :
+    SourcePressureMarginJumpUp n k r j ↔
+      SourcePressureNetDropPositive n k r j :=
+  ⟨sourcePressureNetDropPositive_of_marginJumpUp n k r j,
+    sourcePressureMarginJumpUp_of_netDropPositive n k r j⟩
+
+/--
+Upward source-pressure sign change as a local zero-crossing.
+
+The statement keeps the two axes separated: `j` is a pressure-depth edge, not a
+time index.  The theorem says that the next margin is positive exactly when
+the current nonpositive margin crosses zero after adding the local net pressure
+drop.
+-/
+theorem sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses
+    (n : OddNat) (k r j : ℕ) :
+    SourcePressureSignChangeUp n k r j ↔
+      SourcePressureMarginInt n k (r + j) ≤ 0 ∧
+        0 <
+          SourcePressureMarginInt n k (r + j) +
+            SourcePressureNetDropInt n k r j := by
+  unfold SourcePressureSignChangeUp
+  rw [← sourcePressureMargin_next_eq_current_add_netDrop n k r j]
+
+/--
+Downward source-pressure sign change as a local falling condition.
+
+This is the right-edge companion to
+`sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses`: the current
+positive margin falls to a nonpositive next margin after adding the local net
+pressure drop.
+-/
+theorem sourcePressureSignChangeDown_iff_margin_pos_and_netDrop_falls
+    (n : OddNat) (k r j : ℕ) :
+    SourcePressureSignChangeDown n k r j ↔
+      0 < SourcePressureMarginInt n k (r + j) ∧
+        SourcePressureMarginInt n k (r + j) +
+          SourcePressureNetDropInt n k r j ≤ 0 := by
+  unfold SourcePressureSignChangeDown
+  rw [← sourcePressureMargin_next_eq_current_add_netDrop n k r j]
+
+/--
+Named local source-pressure pulse.
+
+`SourcePressurePulse n k r j` records the two adjacent pressure-depth edges
+around the selected depth `j`:
+
+* the left edge crosses upward from a nonpositive margin after adding the
+  local net pressure drop;
+* the right edge falls from a positive margin to a nonpositive margin after
+  adding the local net pressure drop.
+
+This is deliberately still a local pressure-depth predicate.  It does not
+claim that positive pressure depths form a prefix, an interval family, or a
+global shape theorem.
+-/
+def SourcePressurePulse
+    (n : OddNat) (k r j : ℕ) : Prop :=
+  (SourcePressureMarginInt n k (r + (j - 1)) ≤ 0 ∧
+    0 <
+      SourcePressureMarginInt n k (r + (j - 1)) +
+        SourcePressureNetDropInt n k r (j - 1)) ∧
+    (0 < SourcePressureMarginInt n k (r + j) ∧
+      SourcePressureMarginInt n k (r + j) +
+        SourcePressureNetDropInt n k r j ≤ 0)
+
+/--
+Left-edge projection from a source-pressure pulse.
+-/
+theorem sourcePressurePulse_left
+    {n : OddNat} {k r j : ℕ}
+    (h : SourcePressurePulse n k r j) :
+    SourcePressureMarginInt n k (r + (j - 1)) ≤ 0 ∧
+      0 <
+        SourcePressureMarginInt n k (r + (j - 1)) +
+          SourcePressureNetDropInt n k r (j - 1) :=
+  h.1
+
+/--
+Right-edge projection from a source-pressure pulse.
+-/
+theorem sourcePressurePulse_right
+    {n : OddNat} {k r j : ℕ}
+    (h : SourcePressurePulse n k r j) :
+    0 < SourcePressureMarginInt n k (r + j) ∧
+      SourcePressureMarginInt n k (r + j) +
+        SourcePressureNetDropInt n k r j ≤ 0 :=
+  h.2
+
+/--
+Sign-change form of a local source-pressure pulse.
+
+This alias keeps the sign-profile reading available beside the net-drop
+reading in `SourcePressurePulse`.  It is useful when a later checkpoint wants
+only the two signs, without opening the integer balance sheet.
+-/
+def SourcePressureSignPulse
+    (n : OddNat) (k r j : ℕ) : Prop :=
+  SourcePressureSignChangeUp n k r (j - 1) ∧
+    SourcePressureSignChangeDown n k r j
+
+/--
+The named net-drop pulse is equivalent to the two sign changes.
+-/
+theorem sourcePressurePulse_iff_signPulse
+    (n : OddNat) (k r j : ℕ) :
+    SourcePressurePulse n k r j ↔
+      SourcePressureSignPulse n k r j := by
+  unfold SourcePressurePulse SourcePressureSignPulse
+  rw [sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses]
+  rw [sourcePressureSignChangeDown_iff_margin_pos_and_netDrop_falls]
+
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
index 53d6cc44..fe336a2f 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
@@ -4,7 +4,7 @@ Released under MIT license as described in the file LICENSE.
 Authors: D. and Wise Wolf.
 -/

-import DkMath.Collatz.PetalBridge.DriftBudget
+import DkMath.Collatz.PetalBridge.PressureDecay

 #print "file: DkMath.Collatz.PetalBridge.PressureFrontier"

@@ -82,89 +82,6 @@ def IsSourcePressureDepth
     (orbitWindowContinuationSiblingMassPow2 n k (r + j))
     (orbitWindowRetentionMassPow2 n k (r + j))

-/--
-Integer-valued source pressure margin at a single depth.
-
-The margin is positive exactly when source continuation occupies more than
-half of source retention.  It is intentionally integer-valued, because the
-natural-number subtraction would truncate negative margins and hide failures.
--/
-noncomputable def SourcePressureMarginInt
-    (n : OddNat) (k r : ℕ) : ℤ :=
-  (2 * orbitWindowContinuationSiblingMassPow2 n k r : ℤ) -
-    (orbitWindowRetentionMassPow2 n k r : ℤ)
-
-/--
-Integer-valued retention drop across adjacent pressure depths.
-
-The sign convention is `current - next`.  This is the convention used by the
-Python pressure scan and by the checkpoint-136 balance sheet.  Keeping it as
-an integer avoids truncation when a later experiment crosses a non-monotone
-edge.
--/
-noncomputable def SourceRetentionDropInt
-    (n : OddNat) (k r j : ℕ) : ℤ :=
-  (orbitWindowRetentionMassPow2 n k (r + j) : ℤ) -
-    (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ)
-
-/--
-Integer-valued continuation drop across adjacent pressure depths.
-
-This uses the same `current - next` convention as `SourceRetentionDropInt`.
-The continuation term appears with coefficient `2` in the source pressure
-margin, so the net pressure contribution is
-`retention_drop - 2 * continuation_drop`.
--/
-noncomputable def SourceContinuationDropInt
-    (n : OddNat) (k r j : ℕ) : ℤ :=
-  (orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) -
-    (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ)
-
-/--
-Integer-valued net pressure drop across adjacent pressure depths.
-
-This is only a name for the balance quantity
-`retention_drop - 2 * continuation_drop`.  Existing predicates keep their
-current API, while later zero-crossing theorems can refer to this single
-integer expression.
--/
-noncomputable def SourcePressureNetDropInt
-    (n : OddNat) (k r j : ℕ) : ℤ :=
-  SourceRetentionDropInt n k r j -
-    2 * SourceContinuationDropInt n k r j
-
-/--
-Adjacent source-pressure margin accounting identity.
-
-This is the checkpoint-136 balance sheet.  A positive pressure step is exactly
-the net effect of losing retention mass faster than twice the continuation
-mass across the same adjacent pressure-depth edge.  No global pressure-prefix
-or dominance theorem is asserted here.
--/
-theorem sourcePressureMarginStepDiff_eq
-    (n : OddNat) (k r j : ℕ) :
-    SourcePressureMarginInt n k (r + j + 1) -
-        SourcePressureMarginInt n k (r + j) =
-      SourcePressureNetDropInt n k r j := by
-  unfold SourcePressureMarginInt
-  unfold SourcePressureNetDropInt SourceRetentionDropInt SourceContinuationDropInt
-  ring
-
-/--
-Next adjacent source-pressure margin as current margin plus net pressure drop.
-
-This is the additive zero-crossing form of the checkpoint-136 balance sheet.
-It is still local to one adjacent pressure-depth edge.
--/
-theorem sourcePressureMargin_next_eq_current_add_netDrop
-    (n : OddNat) (k r j : ℕ) :
-    SourcePressureMarginInt n k (r + j + 1) =
-      SourcePressureMarginInt n k (r + j) +
-        SourcePressureNetDropInt n k r j := by
-  have h := sourcePressureMarginStepDiff_eq n k r j
-  rw [← h]
-  ring
-
 /--
 Selected source pressure is exactly positive source pressure margin.

@@ -328,43 +245,6 @@ theorem downClosed_iff_no_prefixFailure
     · exact hshallow
     · exact False.elim (hno j₁ j₂ hlt hj₂ ⟨hlt, hshallow, hdeep⟩)

-/--
-Upward sign change of the source-pressure margin between adjacent depths.
-
-This is a small building block for pressure-frontier and pressure-island
-classification.  It is stated directly in margin language because the
-checkpoint-125 correction is that pressure should be studied as a sign profile,
-not as raw carrier membership.
--/
-def SourcePressureSignChangeUp
-    (n : OddNat) (k r j : ℕ) : Prop :=
-  SourcePressureMarginInt n k (r + j) ≤ 0 ∧
-    0 < SourcePressureMarginInt n k (r + j + 1)
-
-/--
-Downward sign change of the source-pressure margin between adjacent depths.
-
-This is the right-edge companion to `SourcePressureSignChangeUp`: the current
-depth is positive, while the next adjacent pressure depth is nonpositive.
--/
-def SourcePressureSignChangeDown
-    (n : OddNat) (k r j : ℕ) : Prop :=
-  0 < SourcePressureMarginInt n k (r + j) ∧
-    SourcePressureMarginInt n k (r + j + 1) ≤ 0
-
-/--
-Named pressure-margin jump between adjacent pressure depths.
-
-Checkpoint 134 starts the thin `PressureDecayProfile` vocabulary here rather
-than introducing a full grid.  The predicate only compares adjacent pressure
-depths `r + j` and `r + j + 1`; it says nothing about time indices and does
-not assert that selected pressure depths form a prefix.
--/
-def SourcePressureMarginJumpUp
-    (n : OddNat) (k r j : ℕ) : Prop :=
-  SourcePressureMarginInt n k (r + j) <
-    SourcePressureMarginInt n k (r + j + 1)
-
 /--
 Retention mass strictly drops across adjacent pressure depths.

@@ -415,17 +295,6 @@ def SourcePressureJumpWithDecay
     SourceRetentionDropsAcross n k r j ∧
       SourceContinuationWeaklyDropsAcross n k r j

-/--
-Positive net integer drop across an adjacent pressure-depth edge.
-
-This is intentionally not named `RetentionDropDominant` yet.  The predicate is
-the algebraic quantity that actually appears in the margin-step identity:
-retention loss minus twice continuation loss.
--/
-def SourcePressureNetDropPositive
-    (n : OddNat) (k r j : ℕ) : Prop :=
-  0 < SourcePressureNetDropInt n k r j
-
 /--
 The first selected source-pressure depth.

@@ -785,65 +654,6 @@ theorem sourcePressureMarginJumpUp_of_localIsland_left
   sourcePressureMarginJumpUp_of_signChangeUp n k r (j - 1)
     (sourcePressureSignChangeUp_of_localIsland n k r j hisland)

-/--
-Strict adjacent margin jump is equivalent to positive integer step
-difference.
--/
-theorem sourcePressureMarginJumpUp_iff_stepDiff_pos
-    (n : OddNat) (k r j : ℕ) :
-    SourcePressureMarginJumpUp n k r j ↔
-      0 <
-        SourcePressureMarginInt n k (r + j + 1) -
-          SourcePressureMarginInt n k (r + j) := by
-  unfold SourcePressureMarginJumpUp
-  omega
-
-/--
-Positive net retention/continuation drop forces a named pressure-margin jump.
-
-This is the first Lean use of the checkpoint-136 balance sheet.  It remains a
-local adjacent-edge theorem; it does not claim any global prefix shape for
-selected pressure depths.
--/
-theorem sourcePressureMarginJumpUp_of_netDropPositive
-    (n : OddNat) (k r j : ℕ)
-    (h : SourcePressureNetDropPositive n k r j) :
-    SourcePressureMarginJumpUp n k r j := by
-  rw [sourcePressureMarginJumpUp_iff_stepDiff_pos]
-  unfold SourcePressureNetDropPositive at h
-  rw [sourcePressureMarginStepDiff_eq]
-  exact h
-
-/--
-A named pressure-margin jump gives positive net integer pressure drop.
-
-Together with `sourcePressureMarginJumpUp_of_netDropPositive`, this closes the
-local checkpoint-137 equivalence between adjacent margin jumps and the integer
-balance sheet.  This remains strictly local to one adjacent pressure-depth
-edge.
--/
-theorem sourcePressureNetDropPositive_of_marginJumpUp
-    (n : OddNat) (k r j : ℕ)
-    (h : SourcePressureMarginJumpUp n k r j) :
-    SourcePressureNetDropPositive n k r j := by
-  unfold SourcePressureNetDropPositive
-  rw [← sourcePressureMarginStepDiff_eq]
-  exact (sourcePressureMarginJumpUp_iff_stepDiff_pos n k r j).1 h
-
-/--
-Adjacent pressure-margin jump is exactly positive net pressure drop.
-
-This theorem is the stable local API for later pressure-decay work.  It should
-be preferred over introducing a global or dominance-sounding predicate until a
-specific downstream theorem requires that stronger vocabulary.
--/
-theorem sourcePressureMarginJumpUp_iff_netDropPositive
-    (n : OddNat) (k r j : ℕ) :
-    SourcePressureMarginJumpUp n k r j ↔
-      SourcePressureNetDropPositive n k r j :=
-  ⟨sourcePressureNetDropPositive_of_marginJumpUp n k r j,
-    sourcePressureMarginJumpUp_of_netDropPositive n k r j⟩
-
 /--
 An upward pressure sign change has positive net integer pressure drop.
 -/
@@ -865,24 +675,6 @@ theorem sourcePressureNetDropPositive_of_localIsland_left
   sourcePressureNetDropPositive_of_marginJumpUp n k r (j - 1)
     (sourcePressureMarginJumpUp_of_localIsland_left n k r j hisland)

-/--
-Upward source-pressure sign change as a local zero-crossing.
-
-The statement keeps the two axes separated: `j` is a pressure-depth edge, not a
-time index.  The theorem says that the next margin is positive exactly when
-the current nonpositive margin crosses zero after adding the local net pressure
-drop.
--/
-theorem sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses
-    (n : OddNat) (k r j : ℕ) :
-    SourcePressureSignChangeUp n k r j ↔
-      SourcePressureMarginInt n k (r + j) ≤ 0 ∧
-        0 <
-          SourcePressureMarginInt n k (r + j) +
-            SourcePressureNetDropInt n k r j := by
-  unfold SourcePressureSignChangeUp
-  rw [← sourcePressureMargin_next_eq_current_add_netDrop n k r j]
-
 /--
 A local pressure island gives the zero-crossing condition at its left edge.
 -/
@@ -915,23 +707,6 @@ theorem sourcePressureSignChangeDown_of_localIsland
         ((isSourcePressureDepth_iff_margin_pos n k r (j + 1)).2 hpos)
     omega

-/--
-Downward source-pressure sign change as a local falling condition.
-
-This is the right-edge companion to
-`sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses`: the current
-positive margin falls to a nonpositive next margin after adding the local net
-pressure drop.
--/
-theorem sourcePressureSignChangeDown_iff_margin_pos_and_netDrop_falls
-    (n : OddNat) (k r j : ℕ) :
-    SourcePressureSignChangeDown n k r j ↔
-      0 < SourcePressureMarginInt n k (r + j) ∧
-        SourcePressureMarginInt n k (r + j) +
-          SourcePressureNetDropInt n k r j ≤ 0 := by
-  unfold SourcePressureSignChangeDown
-  rw [← sourcePressureMargin_next_eq_current_add_netDrop n k r j]
-
 /--
 A local pressure island gives the falling condition at its right edge.
 -/
@@ -961,31 +736,6 @@ theorem sourcePressureLocalIsland_gives_crossing_pulse
   ⟨sourcePressureCrosses_of_localIsland_left n k r j hisland,
     sourcePressureFalls_of_localIsland_right n k r j hisland⟩

-/--
-Named local source-pressure pulse.
-
-`SourcePressurePulse n k r j` records the two adjacent pressure-depth edges
-around the selected depth `j`:
-
-* the left edge crosses upward from a nonpositive margin after adding the
-  local net pressure drop;
-* the right edge falls from a positive margin to a nonpositive margin after
-  adding the local net pressure drop.
-
-This is deliberately still a local pressure-depth predicate.  It does not
-claim that positive pressure depths form a prefix, an interval family, or a
-global shape theorem.
--/
-def SourcePressurePulse
-    (n : OddNat) (k r j : ℕ) : Prop :=
-  (SourcePressureMarginInt n k (r + (j - 1)) ≤ 0 ∧
-    0 <
-      SourcePressureMarginInt n k (r + (j - 1)) +
-        SourcePressureNetDropInt n k r (j - 1)) ∧
-    (0 < SourcePressureMarginInt n k (r + j) ∧
-      SourcePressureMarginInt n k (r + j) +
-        SourcePressureNetDropInt n k r j ≤ 0)
-
 /--
 A local pressure island is a named source-pressure pulse.
 -/
@@ -995,41 +745,6 @@ theorem sourcePressurePulse_of_localIsland
     SourcePressurePulse n k r j :=
   sourcePressureLocalIsland_gives_crossing_pulse n k r j hisland

-/--
-Left-edge projection from a source-pressure pulse.
--/
-theorem sourcePressurePulse_left
-    {n : OddNat} {k r j : ℕ}
-    (h : SourcePressurePulse n k r j) :
-    SourcePressureMarginInt n k (r + (j - 1)) ≤ 0 ∧
-      0 <
-        SourcePressureMarginInt n k (r + (j - 1)) +
-          SourcePressureNetDropInt n k r (j - 1) :=
-  h.1
-
-/--
-Right-edge projection from a source-pressure pulse.
--/
-theorem sourcePressurePulse_right
-    {n : OddNat} {k r j : ℕ}
-    (h : SourcePressurePulse n k r j) :
-    0 < SourcePressureMarginInt n k (r + j) ∧
-      SourcePressureMarginInt n k (r + j) +
-        SourcePressureNetDropInt n k r j ≤ 0 :=
-  h.2
-
-/--
-Sign-change form of a local source-pressure pulse.
-
-This alias keeps the sign-profile reading available beside the net-drop
-reading in `SourcePressurePulse`.  It is useful when a later checkpoint wants
-only the two signs, without opening the integer balance sheet.
--/
-def SourcePressureSignPulse
-    (n : OddNat) (k r j : ℕ) : Prop :=
-  SourcePressureSignChangeUp n k r (j - 1) ∧
-    SourcePressureSignChangeDown n k r j
-
 /--
 A local pressure island is also a pulse in sign-change language.
 -/
@@ -1040,17 +755,6 @@ theorem sourcePressureSignPulse_of_localIsland
   ⟨sourcePressureSignChangeUp_of_localIsland n k r j hisland,
     sourcePressureSignChangeDown_of_localIsland n k r j hisland⟩

-/--
-The named net-drop pulse is equivalent to the two sign changes.
--/
-theorem sourcePressurePulse_iff_signPulse
-    (n : OddNat) (k r j : ℕ) :
-    SourcePressurePulse n k r j ↔
-      SourcePressureSignPulse n k r j := by
-  unfold SourcePressurePulse SourcePressureSignPulse
-  rw [sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses]
-  rw [sourcePressureSignChangeDown_iff_margin_pos_and_netDrop_falls]
-
 /--
 Meaning-name alias for a positive pressure run.

diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-143.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-143.md
new file mode 100644
index 00000000..9e383570
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-143.md
@@ -0,0 +1,154 @@
+# Report Petal 143
+
+## Scope
+
+Checkpoint 143 performed the first import-safe split of the pressure-decay
+vocabulary.
+
+Created:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean
+```
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+No mathematical theorem names were changed.
+
+## Split policy used
+
+Moved to `PressureDecay`:
+
+```lean
+SourcePressureMarginInt
+
+SourceRetentionDropInt
+SourceContinuationDropInt
+SourcePressureNetDropInt
+SourcePressureNetDropPositive
+
+sourcePressureMarginStepDiff_eq
+sourcePressureMargin_next_eq_current_add_netDrop
+
+SourcePressureSignChangeUp
+SourcePressureSignChangeDown
+SourcePressureMarginJumpUp
+
+sourcePressureMarginJumpUp_iff_stepDiff_pos
+sourcePressureMarginJumpUp_of_netDropPositive
+sourcePressureNetDropPositive_of_marginJumpUp
+sourcePressureMarginJumpUp_iff_netDropPositive
+
+sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses
+sourcePressureSignChangeDown_iff_margin_pos_and_netDrop_falls
+
+SourcePressurePulse
+SourcePressureSignPulse
+sourcePressurePulse_left
+sourcePressurePulse_right
+sourcePressurePulse_iff_signPulse
+```
+
+Kept in `PressureFrontier`:
+
+```lean
+IsSourcePressureDepth
+SelectedPressurePrefix
+SourcePressurePrefixFailure
+SourcePressureFrontier
+SourcePressureLocalIsland
+SourcePressurePositiveBlock
+SourcePressureRun
+SourcePressureIntervalPulse
+```
+
+and all frontier/local-island-facing bridge theorems.
+
+## Why run/interval stayed in PressureFrontier
+
+`SourcePressureRun` is a meaning-name alias for
+`SourcePressurePositiveBlock`, and `SourcePressurePositiveBlock` depends on
+`IsSourcePressureDepth`.
+
+Moving run/interval in this checkpoint would require also moving the selected
+pressure-depth layer, which would make the split larger than requested.  So
+checkpoint 143 intentionally moved only the import-safe decay block and kept
+run/interval vocabulary in `PressureFrontier`.
+
+This preserves the intended dependency shape:
+
+```text
+DriftBudget
+  -> PressureDecay
+  -> PressureFrontier
+  -> Collision / parent aggregate
+```
+
+## Public API
+
+The parent aggregate was updated:
+
+```lean
+import DkMath.Collatz.PetalBridge.PressureDecay
+import DkMath.Collatz.PetalBridge.PressureFrontier
+```
+
+So users importing:
+
+```lean
+import DkMath.Collatz.PetalBridge
+```
+
+continue to see the moved declarations.
+
+## Python
+
+No Python changes were needed for this checkpoint.
+
+## Verification
+
+Commands run:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureDecay
+lake build DkMath.Collatz.PetalBridge.PressureFrontier
+lake build DkMath.Collatz.PetalBridge
+rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean
+rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+```
+
+Result:
+
+```text
+pass
+```
+
+The `rg` checks returned no matches in either split file.
+
+The build still reports the pre-existing unrelated warning:
+
+```text
+DkMath.NumberTheory.ZsigmondyCyclotomicResearch: declaration uses `sorry`
+```
+
+## Inference
+
+The first split is stable.  `PressureDecay` is now the lower layer for generic
+integer pressure-margin accounting, while `PressureFrontier` remains the
+frontier/island/run-facing layer.
+
+The next checkpoint can safely return to math:
+
+```text
+SourcePressureRunAddress
+SourcePressureIntervalPulseAddress
+thin boundary extraction for positive runs
+```
+
+If file pressure continues, the next possible split is not more decay, but a
+separate frontier/run-facing module above `PressureDecay`.
````
`````
