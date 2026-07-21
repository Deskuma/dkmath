# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.*

gch: ca4e95b24c9e7d03ba1d46d83b1f9d27b140095b

## Report

Checkpoint 141 完了です。

[PressureFrontier.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean) に interval vocabulary を追加しました。`SourcePressureRun` は既存 `SourcePressurePositiveBlock` の意味名 alias とし、`SourcePressureIntervalPulse` は「run + left crossing + right fall」の薄い構造として固定しています。`SourcePressureLocalIsland -> SourcePressureIntervalPulse ... 1` も通しました。

Python scan には interval pulse 観測を追加しました。生成物:

- [CSV](/python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_141_16383_k64_d12.csv)
- [summary](/python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_141_16383_k64_d12.md)
- [report-petal-141.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-141.md)

主要観測は `rows_with_interval_pulse = 404`、`rows_with_positive_block_without_left_crossing = 0`、`rows_with_positive_block_without_right_fall = 0` です。左境界は `start > r_start` の block だけ検査しています。

検証:

- `python3 -m py_compile ...` pass
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier` pass
- `lake build DkMath.Collatz.PetalBridge` pass
- `rg -n "\bsorry\b" .../PressureFrontier.lean` no hits
- `git diff --check` pass

既存の `ZsigmondyCyclotomicResearch` の `sorry` warning は今回範囲外です。

## Review

## 状況分析

Checkpoint `141` は、singleton の `SourcePressurePulse` を、positive pressure run / interval pulse へ拡張するための **薄い interval vocabulary** として成功している。

Lean 側では `PressureFrontier.lean` に、

```text id="zqxujd"
SourcePressureRun
SourcePressureRunHasLeftCrossing
SourcePressureRunHasRightFall
SourcePressureIntervalPulse
```

が追加された。特に `SourcePressureRun` は新しい重複定義ではなく、既存 `SourcePressurePositiveBlock` の意味名 alias として置かれている。これは良い判断じゃ。

さらに、`SourcePressureLocalIsland -> SourcePressureIntervalPulse n k r j 1` も通っている。これにより、local island は singleton pulse であると同時に、長さ 1 の interval pulse としても読めるようになった。

Python 側でも interval pulse 観測が追加され、`rows_with_interval_pulse = 404`、`rows_with_positive_block_without_left_crossing = 0`、`rows_with_positive_block_without_right_fall = 0` が出ている。左 crossing は `start > r_start` の block だけ検査するという index convention も明記されており、自然数 predecessor の罠を避けている。

## レビュー

## 良い点

第一に、`SourcePressureRun` を alias にしたのが良い。

```lean id="n5mz6m"
def SourcePressureRun
    (n : OddNat) (k r a len : ℕ) : Prop :=
  SourcePressurePositiveBlock n k r a len
```

ここで新しい block 定義を増やしていたら、後続で `PositiveBlock` 系補題と `Run` 系補題が二重管理になっていた。今回は既存構造を保ちつつ、意味名だけを追加しているので、API として安全じゃ。

第二に、left crossing に `0 < a` guard を入れたのが良い。

```lean id="y3jjlh"
def SourcePressureRunHasLeftCrossing
    (n : OddNat) (k r a _len : ℕ) : Prop :=
  0 < a ∧ SourcePressureSignChangeUp n k r (a - 1)
```

Lean の自然数では `0 - 1 = 0` になってしまうため、ここを guard なしで書くと、観測窓の左端で間違った意味になる。今回の設計はその罠をきちんと避けている。

第三に、`SourcePressureIntervalPulse` が薄い。

```text id="ly5m3m"
run
left crossing
right fall
```

だけを package しており、maximality、uniqueness、coverage はまだ主張していない。これは正しい。いまの段階では「正の run を interval pulse として読む語彙」を置く段階であって、「すべての positive shape を一意に分解する」段階ではない。

第四に、singleton bridge が通ったのが大きい。

```text id="6jj2ou"
SourcePressureLocalIsland n k r j
  -> SourcePressureIntervalPulse n k r j 1
```

これにより、

```text id="8znuw4"
local island
  -> SourcePressurePulse
  -> SourcePressureIntervalPulse length 1
```

という階層が見えるようになった。
これは、local pulse から interval pulse へ進む道が Lean 上でつながったということじゃ。

## 注意点

次の注意点は、`SourcePressureIntervalPulse` がまだ **positive run の住所語彙**であり、maximal run の抽出ではないことじゃ。

現在の定義では、

```text id="v7lg29"
run + left crossing + right fall
```

が揃っていれば interval pulse である。

しかし、これが「最大の positive block」であるかどうかはまだ言っていない。
たとえば将来、

```text id="clrq8h"
SourcePressureMaximalRun
SourcePressureRunStart
SourcePressureRunEnd
```

のような語彙を入れるまでは、interval pulse はあくまで「境界を持った positive run」として扱うのが安全じゃ。

もう一つの注意点は、`PressureFrontier.lean` がかなり育ってきたことじゃ。

Report でも次候補として `PressureDecay.lean` への分割が挙げられている。
ここまで来ると、数学的にはまだ進めたいが、実装保守上は一度分割しておく価値が高くなっている。

## 解説

ここまでの流れを整理すると、かなり綺麗な階層になっている。

```text id="5uvm3q"
SourcePressureLocalIsland:
  点としての孤立正 pressure

SourcePressurePulse:
  left crossing + right fall を持つ局所 pulse

SourcePressureRun:
  正 pressure が連続する有限 run

SourcePressureIntervalPulse:
  run + left crossing + right fall を持つ interval pulse
```

つまり、prefix failure は単なる失敗ではなくなってきた。

以前は、

```text id="yftb67"
positive pressure が prefix にならない
```

という否定的な観測だった。

今は、

```text id="6w6m9h"
positive pressure run が pulse / interval pulse として現れる
```

という肯定的な構造になっている。

これは宇宙式保存法則語彙で言えば、

```text id="ee41y3"
境界を跨ぐ局所 pulse が、深さ方向に有限区間として住所を持つ
```

という段階じゃ。

## 次の指示

Checkpoint `142` は、賢狼としては **Route B: thin interval-run extraction helpers** を推す。

理由は、`PressureDecay.lean` 分割も近いが、いま `SourcePressureIntervalPulse` を置いた直後なので、まずその API を少しだけ使いやすくしておくと、分割後も境界が明確になるからじゃ。

ただし、Checkpoint `143` では分割を真剣に考えたい。

## Checkpoint 142 推奨内容

## 1. interval pulse constructor from parts

すでに定義は conjunction なので、constructor theorem を置く。

```lean id="2y7ekq"
theorem sourcePressureIntervalPulse_of_run_boundaries
    (n : OddNat) (k r a len : ℕ)
    (hrun : SourcePressureRun n k r a len)
    (hleft : SourcePressureRunHasLeftCrossing n k r a len)
    (hright : SourcePressureRunHasRightFall n k r a len) :
    SourcePressureIntervalPulse n k r a len := by
  exact ⟨hrun, hleft, hright⟩
```

これは薄いが、以後の theorem が読みやすくなる。

## 2. interval pulse から sign-change を取り出す

`SourcePressureRunHasLeftCrossing` は `0 < a ∧ SourcePressureSignChangeUp ...` なので、sign-change-up だけを取り出す補題が欲しい。

```lean id="k78524"
theorem sourcePressureIntervalPulse_left_signChange
    {n : OddNat} {k r a len : ℕ}
    (h : SourcePressureIntervalPulse n k r a len) :
    SourcePressureSignChangeUp n k r (a - 1) :=
  (sourcePressureIntervalPulse_left h).2
```

右側も同様。

```lean id="i1rqxg"
theorem sourcePressureIntervalPulse_right_signChange
    {n : OddNat} {k r a len : ℕ}
    (h : SourcePressureIntervalPulse n k r a len) :
    SourcePressureSignChangeDown n k r (a + len - 1) :=
  sourcePressureIntervalPulse_right h
```

## 3. interval pulse の left guard を取り出す

```lean id="pqaxkg"
theorem sourcePressureIntervalPulse_left_pos
    {n : OddNat} {k r a len : ℕ}
    (h : SourcePressureIntervalPulse n k r a len) :
    0 < a :=
  (sourcePressureIntervalPulse_left h).1
```

これは自然数 predecessor を扱う後続で便利になる。

## 4. interval pulse から crossing/falling 条件を直接取り出す

sign-change theorem を通して、net-drop crossing / falling を取り出す補題も欲しい。

```lean id="j3unjp"
theorem sourcePressureIntervalPulse_left_crossing
    {n : OddNat} {k r a len : ℕ}
    (h : SourcePressureIntervalPulse n k r a len) :
    SourcePressureMarginInt n k (r + (a - 1)) ≤ 0 ∧
      0 <
        SourcePressureMarginInt n k (r + (a - 1)) +
          SourcePressureNetDropInt n k r (a - 1) :=
  (sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses
    n k r (a - 1)).1
    (sourcePressureIntervalPulse_left_signChange h)
```

右側。

```lean id="spv8ym"
theorem sourcePressureIntervalPulse_right_falling
    {n : OddNat} {k r a len : ℕ}
    (h : SourcePressureIntervalPulse n k r a len) :
    0 < SourcePressureMarginInt n k (r + (a + len - 1)) ∧
      SourcePressureMarginInt n k (r + (a + len - 1)) +
        SourcePressureNetDropInt n k r (a + len - 1) ≤ 0 :=
  (sourcePressureSignChangeDown_iff_margin_pos_and_netDrop_falls
    n k r (a + len - 1)).1
    (sourcePressureIntervalPulse_right_signChange h)
```

これで interval pulse は、sign profile でも net-drop 会計でもすぐ読める。

## 5. singleton bridge の projection wrappers は optional

既に `sourcePressureIntervalPulse_singleton_of_localIsland` があるので、今回は不要。
ただし、必要なら、

```text id="x4cimx"
local island -> interval pulse -> left crossing
local island -> interval pulse -> right falling
```

の wrapper を作ってもよいが、重複になりやすいので今回は控えめでよい。

## 一歩先ゆく推論

ここで interval pulse extraction helpers が入ると、次に見えてくるのは **positive block の保存会計住所**じゃ。

positive block は、単なる `List` や `range` の連続正値ではなく、

```text id="7cg3cl"
left boundary:
  outside -> inside

interior:
  positive pressure run

right boundary:
  inside -> outside
```

として読める。

これは、宇宙式の言葉にすると、

```text id="dohk88"
境界を跨いで現れ、
有限区間だけ保存状態が正に偏り、
再び境界外へ戻る
```

という finite pressure body じゃ。

ここまで来ると、positive pressure run は **圧力島の住所**になる。

次の大きな設計は、

```text id="xm0455"
SourcePressureAddress
SourcePressureRunAddress
SourcePressurePulseAddress
```

のような address vocabulary かもしれぬ。

ただし、まだ早い。
まず extraction helpers と分割が先じゃ。

## さらなる次の一手

Checkpoint `142` が通ったら、Checkpoint `143` は **`PressureDecay.lean` への分割**を推す。

分割対象は以下のように考えるとよい。

## PressureDecay.lean に移す候補

```text id="hl48b8"
SourceRetentionDropInt
SourceContinuationDropInt
SourcePressureNetDropInt
SourcePressureNetDropPositive

sourcePressureMarginStepDiff_eq
sourcePressureMargin_next_eq_current_add_netDrop

SourcePressureMarginJumpUp
sourcePressureMarginJumpUp_iff_stepDiff_pos
sourcePressureMarginJumpUp_of_netDropPositive
sourcePressureNetDropPositive_of_marginJumpUp
sourcePressureMarginJumpUp_iff_netDropPositive

SourcePressureSignChangeUp
SourcePressureSignChangeDown
sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses
sourcePressureSignChangeDown_iff_margin_pos_and_netDrop_falls

SourcePressurePulse
SourcePressureSignPulse
sourcePressurePulse_iff_signPulse

SourcePressureRun
SourcePressureIntervalPulse
```

## PressureFrontier.lean に残す候補

```text id="xljwki"
SourcePressureFrontier
SourcePressureLocalIsland
sourcePressureSignChangeUp_of_localIsland
sourcePressureSignChangeDown_of_localIsland
sourcePressurePulse_of_localIsland
sourcePressureIntervalPulse_singleton_of_localIsland
prefix / frontier / below 系
```

理由は、`LocalIsland` や `Frontier` は frontier 語彙であり、`PressureDecay` は margin/drop/crossing/pulse の一般語彙に寄せたいからじゃ。

ただし、依存関係次第では、`SourcePressureSignChangeUp` 自体は `PressureFrontier` に残した方が import が楽かもしれぬ。Codex には「最小移動、import cycle 回避」を強く指示するのが良い。

## 賢狼が試して欲しい実験補題

## 実験 A: constructor

```lean id="fqf4h2"
theorem sourcePressureIntervalPulse_of_run_boundaries
    (n : OddNat) (k r a len : ℕ)
    (hrun : SourcePressureRun n k r a len)
    (hleft : SourcePressureRunHasLeftCrossing n k r a len)
    (hright : SourcePressureRunHasRightFall n k r a len) :
    SourcePressureIntervalPulse n k r a len := by
  exact ⟨hrun, hleft, hright⟩
```

## 実験 B: left sign-change projection

```lean id="goi3gz"
theorem sourcePressureIntervalPulse_left_signChange
    {n : OddNat} {k r a len : ℕ}
    (h : SourcePressureIntervalPulse n k r a len) :
    SourcePressureSignChangeUp n k r (a - 1) :=
  (sourcePressureIntervalPulse_left h).2
```

## 実験 C: left positive index projection

```lean id="8gmrti"
theorem sourcePressureIntervalPulse_left_pos
    {n : OddNat} {k r a len : ℕ}
    (h : SourcePressureIntervalPulse n k r a len) :
    0 < a :=
  (sourcePressureIntervalPulse_left h).1
```

## 実験 D: right sign-change projection

```lean id="e2x57e"
theorem sourcePressureIntervalPulse_right_signChange
    {n : OddNat} {k r a len : ℕ}
    (h : SourcePressureIntervalPulse n k r a len) :
    SourcePressureSignChangeDown n k r (a + len - 1) :=
  sourcePressureIntervalPulse_right h
```

## 実験 E: left net-drop crossing projection

```lean id="iw1ms6"
theorem sourcePressureIntervalPulse_left_crossing
    {n : OddNat} {k r a len : ℕ}
    (h : SourcePressureIntervalPulse n k r a len) :
    SourcePressureMarginInt n k (r + (a - 1)) ≤ 0 ∧
      0 <
        SourcePressureMarginInt n k (r + (a - 1)) +
          SourcePressureNetDropInt n k r (a - 1) :=
  (sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses
    n k r (a - 1)).1
    (sourcePressureIntervalPulse_left_signChange h)
```

## 実験 F: right net-drop falling projection

```lean id="mwxzl2"
theorem sourcePressureIntervalPulse_right_falling
    {n : OddNat} {k r a len : ℕ}
    (h : SourcePressureIntervalPulse n k r a len) :
    0 < SourcePressureMarginInt n k (r + (a + len - 1)) ∧
      SourcePressureMarginInt n k (r + (a + len - 1)) +
        SourcePressureNetDropInt n k r (a + len - 1) ≤ 0 :=
  (sourcePressureSignChangeDown_iff_margin_pos_and_netDrop_falls
    n k r (a + len - 1)).1
    (sourcePressureIntervalPulse_right_signChange h)
```

## Python 側の次観測

Python 側はすでに interval pulse の主要観測が出ているので、今回は必須ではない。

追加するなら、projection に対応して以下を summary に出す程度でよい。

```text id="aq3o8x"
rows_with_interval_pulse_left_crossing_failure
rows_with_interval_pulse_right_falling_failure
```

期待値：

```text id="tdn00j"
0
```

ただし、Checkpoint `142` は Lean API 整備を主にした方がよい。

## 総括

Checkpoint `141` は成功じゃ。

これで、

```text id="k87e7r"
singleton pulse
  -> interval pulse
```

への拡張が始まった。

そして重要なのは、prefix failure が単なる失敗ではなく、

```text id="q5b82h"
positive pressure run / interval pressure pulse
```

として読み替えられるようになってきたことじゃ。

次は、`SourcePressureIntervalPulse` から左右境界や net-drop crossing/falling を取り出す補題を薄く整える。
その次に、`PressureDecay.lean` 分割へ進むのがよい。

## Codex instructions

```text id="oewl73"
Checkpoint 142:
Add thin extraction helpers for SourcePressureIntervalPulse.

Context:
  Checkpoint 141 added:
    SourcePressureRun
    SourcePressureRunHasLeftCrossing
    SourcePressureRunHasRightFall
    SourcePressureIntervalPulse
    sourcePressureIntervalPulse_run
    sourcePressureIntervalPulse_left
    sourcePressureIntervalPulse_right
    sourcePressureIntervalPulse_singleton_of_localIsland

  SourcePressureRun is a meaning-name alias for SourcePressurePositiveBlock.
  SourcePressureIntervalPulse packages:
    run + left crossing + right fall.

Primary goal:
  Make SourcePressureIntervalPulse easier to consume by adding small constructor
  and projection helpers.
  Keep the work local to pressure-depth indices.
  Do not add maximality, uniqueness, coverage, or prefix claims.

Preferred Lean location:
  DkMath.Collatz.PetalBridge.PressureFrontier

Implement:
  1. Constructor:
     sourcePressureIntervalPulse_of_run_boundaries

     Inputs:
       hrun   : SourcePressureRun n k r a len
       hleft  : SourcePressureRunHasLeftCrossing n k r a len
       hright : SourcePressureRunHasRightFall n k r a len

     Output:
       SourcePressureIntervalPulse n k r a len

  2. Projection:
     sourcePressureIntervalPulse_left_signChange

     Output:
       SourcePressureSignChangeUp n k r (a - 1)

  3. Projection:
     sourcePressureIntervalPulse_left_pos

     Output:
       0 < a

  4. Projection:
     sourcePressureIntervalPulse_right_signChange

     Output:
       SourcePressureSignChangeDown n k r (a + len - 1)

  5. Net-drop projection:
     sourcePressureIntervalPulse_left_crossing

     Output:
       SourcePressureMarginInt n k (r + (a - 1)) <= 0
       ∧
       0 <
         SourcePressureMarginInt n k (r + (a - 1))
           + SourcePressureNetDropInt n k r (a - 1)

  6. Net-drop projection:
     sourcePressureIntervalPulse_right_falling

     Output:
       0 < SourcePressureMarginInt n k (r + (a + len - 1))
       ∧
       SourcePressureMarginInt n k (r + (a + len - 1))
         + SourcePressureNetDropInt n k r (a + len - 1) <= 0

Optional Python:
  Only if convenient, add sanity summary fields:
    rows_with_interval_pulse_left_crossing_failure
    rows_with_interval_pulse_right_falling_failure

  Expected values:
    0
    0

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
  add maximality or uniqueness for runs
  perform a broad refactor in this checkpoint

Next checkpoint hint:
  After these extraction helpers are in place, strongly consider splitting
  pressure-decay material into:
    DkMath.Collatz.PetalBridge.PressureDecay
  with minimal movement and careful import-cycle avoidance.
```

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
index 868a900e..ce609a34 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
@@ -1051,6 +1051,98 @@ theorem sourcePressurePulse_iff_signPulse
   rw [sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses]
   rw [sourcePressureSignChangeDown_iff_margin_pos_and_netDrop_falls]

+/--
+Meaning-name alias for a positive pressure run.
+
+The underlying predicate is the already-existing
+`SourcePressurePositiveBlock`.  This alias marks the next reading layer:
+positive pressure depths may be studied as finite runs without asserting that
+all selected depths form a prefix.
+-/
+def SourcePressureRun
+    (n : OddNat) (k r a len : ℕ) : Prop :=
+  SourcePressurePositiveBlock n k r a len
+
+/--
+The left boundary of a positive pressure run crosses upward.
+
+The guard `0 < a` is part of the predicate: it prevents the address
+`a - 1` from silently collapsing to `0` at the left edge of the observation
+window.
+-/
+def SourcePressureRunHasLeftCrossing
+    (n : OddNat) (k r a _len : ℕ) : Prop :=
+  0 < a ∧ SourcePressureSignChangeUp n k r (a - 1)
+
+/--
+The right boundary of a positive pressure run falls downward.
+
+For a run beginning at `a` with length `len`, the last positive depth is
+`a + len - 1`, so the right fall is the sign change at that same depth edge.
+-/
+def SourcePressureRunHasRightFall
+    (n : OddNat) (k r a len : ℕ) : Prop :=
+  SourcePressureSignChangeDown n k r (a + len - 1)
+
+/--
+A finite interval pressure pulse.
+
+This packages the three local facts that later interval accounting needs:
+there is a positive run, its left boundary crosses upward, and its right
+boundary falls back to nonpositive pressure.  It remains an observation about
+pressure-depth indices only.
+-/
+def SourcePressureIntervalPulse
+    (n : OddNat) (k r a len : ℕ) : Prop :=
+  SourcePressureRun n k r a len ∧
+    SourcePressureRunHasLeftCrossing n k r a len ∧
+      SourcePressureRunHasRightFall n k r a len
+
+/-- The positive-run component of an interval pressure pulse. -/
+theorem sourcePressureIntervalPulse_run
+    {n : OddNat} {k r a len : ℕ}
+    (h : SourcePressureIntervalPulse n k r a len) :
+    SourcePressureRun n k r a len :=
+  h.1
+
+/-- The left-crossing component of an interval pressure pulse. -/
+theorem sourcePressureIntervalPulse_left
+    {n : OddNat} {k r a len : ℕ}
+    (h : SourcePressureIntervalPulse n k r a len) :
+    SourcePressureRunHasLeftCrossing n k r a len :=
+  h.2.1
+
+/-- The right-fall component of an interval pressure pulse. -/
+theorem sourcePressureIntervalPulse_right
+    {n : OddNat} {k r a len : ℕ}
+    (h : SourcePressureIntervalPulse n k r a len) :
+    SourcePressureRunHasRightFall n k r a len :=
+  h.2.2
+
+/--
+A local pressure island is an interval pulse of length one.
+
+This is the singleton bridge from checkpoint-140 pulses to checkpoint-141
+interval pulses.  It does not say that every positive run is isolated; it only
+packages the already-proved local island boundaries into the interval API.
+-/
+theorem sourcePressureIntervalPulse_singleton_of_localIsland
+    (n : OddNat) (k r j : ℕ)
+    (hisland : SourcePressureLocalIsland n k r j) :
+    SourcePressureIntervalPulse n k r j 1 := by
+  rcases hisland with ⟨hjpos, hsel, hprev_not, hnext_not⟩
+  constructor
+  · exact sourcePressurePositiveBlock_singleton n k r j hsel
+  constructor
+  · exact ⟨hjpos,
+      sourcePressureSignChangeUp_of_localIsland n k r j
+        ⟨hjpos, hsel, hprev_not, hnext_not⟩⟩
+  · unfold SourcePressureRunHasRightFall
+    have hidx : j + 1 - 1 = j := by omega
+    simpa [hidx] using
+      sourcePressureSignChangeDown_of_localIsland n k r j
+        ⟨hjpos, hsel, hprev_not, hnext_not⟩
+
 /--
 Package a named margin jump and a strict retention drop.

diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-141.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-141.md
new file mode 100644
index 00000000..0a43a61b
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-141.md
@@ -0,0 +1,183 @@
+# Report Petal 141
+
+## Scope
+
+Checkpoint 141 generalizes the singleton `SourcePressurePulse` vocabulary to a
+thin interval vocabulary for positive pressure runs.
+
+This checkpoint remains local to pressure-depth indices.  It does not claim a
+global pressure-prefix theorem and does not introduce a full pressure grid.
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
+def SourcePressureRun
+def SourcePressureRunHasLeftCrossing
+def SourcePressureRunHasRightFall
+def SourcePressureIntervalPulse
+
+theorem sourcePressureIntervalPulse_run
+theorem sourcePressureIntervalPulse_left
+theorem sourcePressureIntervalPulse_right
+theorem sourcePressureIntervalPulse_singleton_of_localIsland
+```
+
+`SourcePressureRun` is deliberately only a meaning-name alias for the existing
+`SourcePressurePositiveBlock`.  This avoids duplicating an equivalent block
+definition while giving later code a more interval-oriented name.
+
+The left crossing predicate includes the guard:
+
+```lean
+0 < a
+```
+
+This is intentional.  It prevents the predecessor address `a - 1` from
+silently collapsing at the left boundary.
+
+The new singleton bridge is:
+
+```lean
+SourcePressureLocalIsland n k r j
+  -> SourcePressureIntervalPulse n k r j 1
+```
+
+So the existing local island is now visible both as a singleton pulse and as
+an interval pulse of length one.
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
+interval_pulse_blocks
+interval_pulse_count
+positive_block_without_left_crossing_count
+positive_block_without_right_fall_count
+```
+
+Added summary fields:
+
+```text
+rows_with_interval_pulse
+rows_with_positive_block_without_left_crossing
+rows_with_positive_block_without_right_fall
+```
+
+Generated:
+
+```text
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_141_16383_k64_d12.csv
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_141_16383_k64_d12.md
+```
+
+Important convention:
+
+```text
+left crossing is checked only for blocks with start > r_start
+```
+
+If a positive block starts at the observed left boundary, the scan does not
+have the previous pressure depth, so it does not classify that case as a left
+crossing failure.
+
+Main observed summary:
+
+```text
+rows: 8192
+rows with positive pressure depths: 4421
+rows with local islands: 252
+rows_with_local_pressure_pulse: 252
+rows_with_interval_pulse: 404
+rows_with_positive_block_without_left_crossing: 0
+rows_with_positive_block_without_right_fall: 0
+rows_with_sign_change_up_iff_crossing_failure: 0
+rows_with_sign_change_down_iff_falling_failure: 0
+```
+
+The scan supports the intended reading:
+
+```text
+positive run with observable boundaries
+  = left crossing + positive plateau + right falling
+```
+
+within the checkpoint-141 observation window.
+
+## Inference
+
+`SourcePressureIntervalPulse` is now the better negotiation unit for longer
+positive pressure blocks.  The older prefix-failure language remains useful
+as an obstruction, but the constructive reading is now:
+
+```text
+prefix failure can indicate a pressure pulse / interval pulse
+```
+
+This reframes non-prefix behavior as positive structure rather than merely as
+failure of monotonicity.
+
+The current Lean API is intentionally thin.  It names the interval shape and
+gives projections, but it does not yet prove maximality, uniqueness, or
+coverage by runs.
+
+## Verification
+
+Commands run:
+
+```text
+python3 -m py_compile python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
+lake build DkMath.Collatz.PetalBridge.PressureFrontier
+lake build DkMath.Collatz.PetalBridge
+python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py --max-n 16383 --steps 64 --r-start 2 --depth-len 12 --name-suffix _141_16383_k64_d12
+rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
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
+Two routes are now reasonable.
+
+Route A: split the pressure-decay vocabulary into:
+
+```text
+DkMath.Collatz.PetalBridge.PressureDecay
+```
+
+Route B: add thin interval-run extraction helpers:
+
+```lean
+sourcePressureIntervalPulse_of_run_boundaries
+sourcePressureIntervalPulse_left_signChange
+sourcePressureIntervalPulse_right_signChange
+```
+
+I would do Route B first if the next checkpoint remains mathematical, and
+Route A first if file size starts blocking review.
````
`````
