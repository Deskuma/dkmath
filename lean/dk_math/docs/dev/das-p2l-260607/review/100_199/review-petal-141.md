# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.*

gch: 3e2fb87f096b61a8d5b443b4da58686bbdc44ff9

## Report

Checkpoint 140 完了です。

[PressureFrontier.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean) に `SourcePressurePulse` を追加し、local island から pulse への橋、左右 projection、sign-change 版 `SourcePressureSignPulse` と同値補題まで入れました。これで「左で crossing、右で falling」の局所構造に安定名が付きました。

Python scan も更新し、pulse 観測を追加しました。生成物:

- [CSV](/python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_140_16383_k64_d12.csv)
- [summary](/python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_140_16383_k64_d12.md)
- [report-petal-140.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-140.md)

主要観測は `rows_with_local_pressure_pulse = 252`、`rows_with_local_island_to_pulse_failure = 0` です。

検証:

- `python3 -m py_compile ...` pass
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier` pass
- `lake build DkMath.Collatz.PetalBridge` pass
- `rg -n "\bsorry\b" .../PressureFrontier.lean` no hits
- `git diff --check` pass

既存の `ZsigmondyCyclotomicResearch` の `sorry` warning は今回範囲外の既存警告です。

## Review

## 状況分析

Checkpoint `140` は、前回までに得た crossing / falling 構造へ **`SourcePressurePulse` という安定名を与える checkpoint** として成功している。

Lean 側では `PressureFrontier.lean` に `SourcePressurePulse` が追加され、local island から pulse への橋、左右 projection、さらに sign-change 版の `SourcePressureSignPulse` と `sourcePressurePulse_iff_signPulse` まで入っている。これにより、local island は「左で crossing、右で falling」という局所構造として、net-drop 会計語彙と sign-profile 語彙の両方から読めるようになった。

Python 側でも pulse 観測が追加され、`rows_with_local_pressure_pulse = 252`、`rows_with_local_island_to_pulse_failure = 0` が出ている。これは scan 窓内で `SourcePressureLocalIsland -> SourcePressurePulse` の読みと矛盾がない、という確認になっている。

## レビュー

## 良い点

第一に、`SourcePressurePulse` の定義がよい。

今回の定義は、単なる符号パターンではなく、

```text
left edge:
  margin_jprev <= 0
  margin_jprev + netDrop_jprev > 0

right edge:
  margin_j > 0
  margin_j + netDrop_j <= 0
```

という **net-drop 会計を露出した pulse** になっている。これは、宇宙式保存法則語彙でいう「境界を跨ぐ局所保存会計 pulse」として非常に読みやすい。

第二に、`SourcePressureSignPulse` を併設したのが良い。

`SourcePressurePulse` は会計語彙、`SourcePressureSignPulse` は符号変化語彙じゃ。
そして `sourcePressurePulse_iff_signPulse` によって、この二つが Lean 上で行き来できる。

つまり、今後の証明では、

```text
会計で読むとき:
  SourcePressurePulse

符号プロファイルだけ見たいとき:
  SourcePressureSignPulse
```

と使い分けられる。これはかなり良い API じゃ。

第三に、local island から pulse への橋が自然に閉じている。

```text
SourcePressureLocalIsland
  -> SourcePressurePulse
```

が入ったことで、local island は「prefix を壊す例外」ではなく、局所 pulse として扱えるようになった。これは前回までの推論と一致している。

## 注意点

ここで注意すべきは、`SourcePressurePulse` はまだ **長さ 1 の singleton pulse** だという点じゃ。

今回の pulse は、

```text
nonpositive -> positive -> nonpositive
```

という一点島を表す。
一方、scan では positive block は長さ 1 だけではなく、長さ 2 以上も多数出ている。今回の report でも次 checkpoint 候補として、singleton island から positive pressure run / interval pulse へ拡張する方向が挙げられている。

つまり、次は `SourcePressurePulse` をすぐ大域 theorem に使うのではなく、

```text
singleton pulse
  -> positive run
  -> interval pulse
```

という順で拡張するのがよい。

## 解説

今の段階で、pressure-depth 方向の局所構造はかなり綺麗になった。

```text
margin_next = margin_current + netDrop
```

この保存会計式の上で、

```text
sign-change-up:
  current margin <= 0
  current margin + netDrop > 0

sign-change-down:
  current margin > 0
  current margin + netDrop <= 0
```

が成り立つ。

そして local island は、

```text
left edge:
  sign-change-up

center:
  positive margin

right edge:
  sign-change-down
```

として読める。

今回の `SourcePressurePulse` は、この一連の局所構造に名前を与えたものじゃ。
つまり、ここで「島」はついに、Lean の語彙として **pressure pulse** になった。

## 次の指示

Checkpoint `141` は、report の提案どおり **positive pressure run / interval pulse の薄い語彙**へ進むのが良い。

`PressureDecay.lean` への分割も近いが、今回 `SourcePressurePulse` が入った直後なので、まずはその一般化先となる `SourcePressureRun` を薄く置くのが自然じゃ。

ただし、既に `SourcePressurePositiveBlock` があるなら、新しい定義を重複させるより、まず alias または wrapper として扱うのがよい。

## Checkpoint 141 推奨内容

## 1. 既存 `SourcePressurePositiveBlock` を確認する

以前の checkpoint で `SourcePressurePositiveBlock` が入っているはずなので、まずそれを再利用する。

新しく `SourcePressureRun` を定義するなら、重複定義ではなく alias がよい。

```lean
def SourcePressureRun
    (n : OddNat) (k r a len : ℕ) : Prop :=
  SourcePressurePositiveBlock n k r a len
```

これにより、既存の positive block API を壊さず、より意味名として `Run` を使える。

## 2. run の左右境界条件を定義する

positive run を interval pulse として読むには、左 crossing と右 falling を分ける。

```lean
def SourcePressureRunHasLeftCrossing
    (n : OddNat) (k r a len : ℕ) : Prop :=
  SourcePressureSignChangeUp n k r (a - 1)
```

```lean
def SourcePressureRunHasRightFall
    (n : OddNat) (k r a len : ℕ) : Prop :=
  SourcePressureSignChangeDown n k r (a + len - 1)
```

ただし `a = 0` のとき `a - 1 = 0` になるので、ここは注意が必要じゃ。
pressure depth の開始を `r + a` と見る設計なら、`a > 0` を条件に入れるか、left crossing は optional にする必要がある。

安全には、まずこうするのがよい。

```lean
def SourcePressureRunHasLeftCrossing
    (n : OddNat) (k r a len : ℕ) : Prop :=
  0 < a ∧ SourcePressureSignChangeUp n k r (a - 1)
```

## 3. interval pulse を定義する

```lean
def SourcePressureIntervalPulse
    (n : OddNat) (k r a len : ℕ) : Prop :=
  SourcePressureRun n k r a len ∧
    SourcePressureRunHasLeftCrossing n k r a len ∧
      SourcePressureRunHasRightFall n k r a len
```

これはまだ「全 positive block は interval pulse」とは主張しない。
あくまで、run と両端 crossing/fall が揃った構造に名前を与えるだけじゃ。

## 4. singleton pulse との橋

`len = 1` の interval pulse と `SourcePressurePulse` の関係を将来狙う。

ただし、Checkpoint `141` では全部閉じなくてよい。
まず片方向だけでよい。

候補：

```lean
theorem sourcePressureIntervalPulse_of_localIsland
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j) :
    SourcePressureIntervalPulse n k r j 1 := by
  -- existing SourcePressurePositiveBlock singleton helper があれば使う
  -- なければ次 checkpoint に回す
```

これは既存 API 次第。無理なら、まず `SourcePressurePulse` と `SourcePressureSignPulse` から Run 側へ繋ぐ補題を後回しにしてよい。

## 一歩先ゆく推論

ここから見えている方向は、かなり美しい。

今までは local island を点として見ていた。
しかし positive block が長さを持つなら、それは

```text
left crossing
positive plateau
right falling
```

を持つ。

つまり、pressure-depth profile は、単なる点の集合ではなく、

```text
positive run の列
```

として扱える可能性がある。

ここまで行くと、`SourcePressurePrefix` が成り立たない理由も、単なる失敗ではなくなる。

```text
prefix が壊れる
```

のではなく、

```text
pulse / interval pulse が発生している
```

と読める。

これはかなり重要じゃ。
「prefix failure」を否定的に見るのではなく、「positive pressure pulse の発生」として肯定的な構造に変換できる。

## さらなる次の一手

Checkpoint `141` で interval vocabulary が薄く入ったら、Checkpoint `142` は二択。

## Route A: `PressureDecay.lean` へ分割

ここまで来ると `PressureFrontier.lean` はかなり育っている。
`SourcePressurePulse`、`NetDropInt`、crossing/falling、interval pulse まで入るなら、分割の価値が高い。

候補：

```text
DkMath.Collatz.PetalBridge.PressureDecay
```

移動対象候補：

```text
SourceRetentionDropInt
SourceContinuationDropInt
SourcePressureNetDropInt
SourcePressureNetDropPositive
SourcePressureMarginStepDiff_eq
sourcePressureMargin_next_eq_current_add_netDrop
sourcePressureMarginJumpUp_iff_netDropPositive
sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses
SourcePressureSignChangeDown
sourcePressureSignChangeDown_iff_margin_pos_and_netDrop_falls
SourcePressurePulse
SourcePressureSignPulse
```

local island 由来の bridge は依存関係次第で `PressureFrontier` 側に残してもよい。

## Route B: positive run extraction

既存の `SourcePressurePositiveBlock` から、

```text
left boundary
right boundary
run length
```

を取り出す補題へ進む。

これは数学的には面白いが、少し重い。
先に薄い interval vocabulary を置いてからが安全じゃ。

## 賢狼が試して欲しい実験補題

## 実験 A: run alias

```lean
def SourcePressureRun
    (n : OddNat) (k r a len : ℕ) : Prop :=
  SourcePressurePositiveBlock n k r a len
```

## 実験 B: left crossing condition

```lean
def SourcePressureRunHasLeftCrossing
    (n : OddNat) (k r a len : ℕ) : Prop :=
  0 < a ∧ SourcePressureSignChangeUp n k r (a - 1)
```

## 実験 C: right fall condition

```lean
def SourcePressureRunHasRightFall
    (n : OddNat) (k r a len : ℕ) : Prop :=
  SourcePressureSignChangeDown n k r (a + len - 1)
```

## 実験 D: interval pulse

```lean
def SourcePressureIntervalPulse
    (n : OddNat) (k r a len : ℕ) : Prop :=
  SourcePressureRun n k r a len ∧
    SourcePressureRunHasLeftCrossing n k r a len ∧
      SourcePressureRunHasRightFall n k r a len
```

## 実験 E: projection helpers

```lean
theorem sourcePressureIntervalPulse_run
    {n : OddNat} {k r a len : ℕ}
    (h : SourcePressureIntervalPulse n k r a len) :
    SourcePressureRun n k r a len :=
  h.1
```

```lean
theorem sourcePressureIntervalPulse_left
    {n : OddNat} {k r a len : ℕ}
    (h : SourcePressureIntervalPulse n k r a len) :
    SourcePressureRunHasLeftCrossing n k r a len :=
  h.2.1
```

```lean
theorem sourcePressureIntervalPulse_right
    {n : OddNat} {k r a len : ℕ}
    (h : SourcePressureIntervalPulse n k r a len) :
    SourcePressureRunHasRightFall n k r a len :=
  h.2.2
```

## Python 側の次観測

Python 側は、positive block / interval pulse の観測を少しだけ追加するとよい。

```text
rows_with_interval_pulse
rows_with_positive_block_without_left_crossing
rows_with_positive_block_without_right_fall
```

ただし `a = 0` の left boundary は扱いに注意。
depth scan が `r_start = 2` なら、多くの場合は `a > 0` と見られるが、Lean 側では自然数 subtraction の罠があるので、Python と Lean の index convention を report に明記した方がよい。

## 総括

Checkpoint `140` は成功じゃ。

これで local island は、

```text
SourcePressureLocalIsland
  -> SourcePressurePulse
  ↔ SourcePressureSignPulse
```

として安定名を得た。

つまり、local island はもう「例外」ではなく、

```text
局所 pressure pulse
```

になった。

次は、この pulse を singleton から interval へ拡張する段階じゃ。
`SourcePressureRun` / `SourcePressureIntervalPulse` を薄く置けば、positive block 全体を宇宙式保存会計の「圧力島の住所」として扱う準備ができる。

## Codex instructions

```text
Checkpoint 141:
Add thin interval vocabulary that generalizes a singleton SourcePressurePulse
to a positive pressure run / interval pulse.

Context:
  Checkpoint 140 added:
    SourcePressurePulse
    sourcePressurePulse_of_localIsland
    sourcePressurePulse_left
    sourcePressurePulse_right
    SourcePressureSignPulse
    sourcePressureSignPulse_of_localIsland
    sourcePressurePulse_iff_signPulse

  The local island is now a named crossing/falling pulse.

Primary goal:
  Add a small vocabulary for positive pressure runs and interval pulses.
  Keep it local to pressure-depth indices.
  Do not claim that all positive pressure shapes are prefixes.

Preferred Lean location:
  DkMath.Collatz.PetalBridge.PressureFrontier

Implementation guidance:
  1. Check whether SourcePressurePositiveBlock already exists.
     If it exists, define SourcePressureRun as a meaning-name alias:
       SourcePressureRun n k r a len :=
         SourcePressurePositiveBlock n k r a len

     Do not duplicate an equivalent block definition.

  2. Define:
       SourcePressureRunHasLeftCrossing

     Suggested safe definition:
       SourcePressureRunHasLeftCrossing n k r a len :=
         0 < a ∧ SourcePressureSignChangeUp n k r (a - 1)

     The 0 < a guard avoids silently treating a - 1 as 0.

  3. Define:
       SourcePressureRunHasRightFall

     Suggested definition:
       SourcePressureRunHasRightFall n k r a len :=
         SourcePressureSignChangeDown n k r (a + len - 1)

  4. Define:
       SourcePressureIntervalPulse

     Suggested definition:
       SourcePressureIntervalPulse n k r a len :=
         SourcePressureRun n k r a len ∧
           SourcePressureRunHasLeftCrossing n k r a len ∧
             SourcePressureRunHasRightFall n k r a len

  5. Add projection helpers:
       sourcePressureIntervalPulse_run
       sourcePressureIntervalPulse_left
       sourcePressureIntervalPulse_right

  6. Optional:
       If existing singleton positive-block helpers are readily available,
       try a theorem connecting SourcePressureLocalIsland to
       SourcePressureIntervalPulse n k r j 1.
       If this becomes nontrivial, leave it for the next checkpoint.

Optional Python:
  Add summary fields:
    rows_with_interval_pulse
    rows_with_positive_block_without_left_crossing
    rows_with_positive_block_without_right_fall

  Be careful with left boundary index a = 0.
  Record the depth/index convention in the generated report.

Verification:
  Run:
    lake build DkMath.Collatz.PetalBridge.PressureFrontier
    lake build DkMath.Collatz.PetalBridge
    python3 -m py_compile python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
    rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
    git diff --check

Do not:
  introduce Real.log
  claim a pressure prefix theorem
  define full ShapePressureGrid
  prove deep all-ones excursion implies positive block
  conflate time index i with pressure-depth index j
  perform a broad refactor in this checkpoint

Next checkpoint hint:
  After interval vocabulary is in place, consider splitting pressure-decay material into:
    DkMath.Collatz.PetalBridge.PressureDecay
  or proving singleton/interval connections for local islands.
```

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
index cccfa93c..868a900e 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
@@ -961,6 +961,96 @@ theorem sourcePressureLocalIsland_gives_crossing_pulse
   ⟨sourcePressureCrosses_of_localIsland_left n k r j hisland,
     sourcePressureFalls_of_localIsland_right n k r j hisland⟩

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
+A local pressure island is a named source-pressure pulse.
+-/
+theorem sourcePressurePulse_of_localIsland
+    (n : OddNat) (k r j : ℕ)
+    (hisland : SourcePressureLocalIsland n k r j) :
+    SourcePressurePulse n k r j :=
+  sourcePressureLocalIsland_gives_crossing_pulse n k r j hisland
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
+A local pressure island is also a pulse in sign-change language.
+-/
+theorem sourcePressureSignPulse_of_localIsland
+    (n : OddNat) (k r j : ℕ)
+    (hisland : SourcePressureLocalIsland n k r j) :
+    SourcePressureSignPulse n k r j :=
+  ⟨sourcePressureSignChangeUp_of_localIsland n k r j hisland,
+    sourcePressureSignChangeDown_of_localIsland n k r j hisland⟩
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
 /--
 Package a named margin jump and a strict retention drop.

diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-140.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-140.md
new file mode 100644
index 00000000..e457fcfc
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-140.md
@@ -0,0 +1,165 @@
+# Report Petal 140
+
+## Scope
+
+Checkpoint 140 named the local pressure island crossing/falling shape as a
+first-class Lean predicate:
+
+```lean
+SourcePressurePulse n k r j
+```
+
+The implementation stays inside the current pressure-depth vocabulary.  It
+does not introduce a pressure-prefix theorem, a shape grid, or any global
+interval theorem.
+
+## Lean changes
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+```
+
+Added:
+
+```lean
+def SourcePressurePulse
+theorem sourcePressurePulse_of_localIsland
+theorem sourcePressurePulse_left
+theorem sourcePressurePulse_right
+def SourcePressureSignPulse
+theorem sourcePressureSignPulse_of_localIsland
+theorem sourcePressurePulse_iff_signPulse
+```
+
+Interpretation:
+
+```text
+left edge:
+  margin_jprev <= 0
+  margin_jprev + netDrop_jprev > 0
+
+right edge:
+  margin_j > 0
+  margin_j + netDrop_j <= 0
+```
+
+This fixes the local island as a named pulse:
+
+```text
+nonpositive -> positive -> nonpositive
+```
+
+but expressed through the integer net-drop balance sheet rather than by
+claiming any global monotone pressure profile.
+
+## Python observation changes
+
+Updated:
+
+```text
+python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
+```
+
+Added row fields:
+
+```text
+local_pressure_pulse_positions
+local_pressure_pulse_count
+local_island_to_pulse_failure_count
+```
+
+Added summary fields:
+
+```text
+rows_with_local_pressure_pulse
+rows_with_local_island_to_pulse_failure
+```
+
+Generated:
+
+```text
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_140_16383_k64_d12.csv
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_140_16383_k64_d12.md
+```
+
+Main observed summary:
+
+```text
+rows: 8192
+rows with positive pressure depths: 4421
+rows with local islands: 252
+rows with sign-change-up positions: 404
+rows_with_sign_change_down: 4421
+rows_with_local_pressure_pulse: 252
+rows_with_local_island_to_pulse_failure: 0
+rows_with_local_island_right_fall_failure: 0
+rows_with_sign_change_up_iff_crossing_failure: 0
+rows_with_sign_change_down_iff_falling_failure: 0
+```
+
+The scan agrees with the Lean direction:
+
+```text
+SourcePressureLocalIsland -> SourcePressurePulse
+```
+
+and found no counterexample in the checkpoint-140 window.
+
+## Inference
+
+`SourcePressurePulse` is now the right unit of negotiation for the next layer.
+It is more precise than a raw local island because it exposes the two adjacent
+net-drop edges, and it is safer than a block theorem because it remains local.
+
+This suggests two next directions:
+
+1. Define a positive-run / interval-pulse vocabulary for longer blocks.
+2. Split the pressure-decay material into a smaller file, for example
+   `DkMath.Collatz.PetalBridge.PressureDecay`, if `PressureFrontier.lean`
+   continues to grow.
+
+The first direction is mathematically more useful.  The second is engineering
+cleanup and can wait unless the next checkpoint needs many more decay lemmas.
+
+## Verification
+
+Commands run:
+
+```text
+python3 -m py_compile python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
+lake build DkMath.Collatz.PetalBridge.PressureFrontier
+lake build DkMath.Collatz.PetalBridge
+python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py --max-n 16383 --steps 64 --r-start 2 --depth-len 12 --name-suffix _140_16383_k64_d12
+rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+git diff --check
+```
+
+Result:
+
+```text
+pass
+```
+
+The `rg` check returned no matches in `PressureFrontier.lean`.
+
+The build still reports the pre-existing unrelated warning:
+
+```text
+DkMath.NumberTheory.ZsigmondyCyclotomicResearch: declaration uses `sorry`
+```
+
+## Suggested next checkpoint
+
+Add the thin interval vocabulary that generalizes a pulse from a singleton
+island to a positive pressure run:
+
+```lean
+def SourcePressureRun
+def SourcePressureRunHasLeftCrossing
+def SourcePressureRunHasRightFall
+```
+
+Keep it local to pressure-depth indices and continue avoiding any unconditional
+pressure-prefix claim.
````
`````
