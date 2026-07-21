# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.*

gch: 7ea458d8ddbc746887faa9ba2f5962287635205d

## Report

Checkpoint 142 完了です。

[PressureFrontier.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean) に `SourcePressureIntervalPulse` の consumer-side helper を追加しました。constructor、left/right sign-change projection、left guard、net-drop crossing/falling projection まで入っています。これで downstream は interval pulse を unfold せずに使えます。

Python scan には指定名の sanity summary を追加し、再生成しました。

- [CSV](/python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_142_16383_k64_d12.csv)
- [summary](/python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_142_16383_k64_d12.md)
- [report-petal-142.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-142.md)

主要観測は `rows_with_interval_pulse = 404`、`rows_with_interval_pulse_left_crossing_failure = 0`、`rows_with_interval_pulse_right_falling_failure = 0` です。

検証:

- `python3 -m py_compile ...` pass
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier` pass
- `lake build DkMath.Collatz.PetalBridge` pass
- `rg -n "\bsorry\b" .../PressureFrontier.lean` no hits
- `git diff --check` pass

次は指示どおりなら、`PressureDecay.lean` への import-safe split が自然です。

## Review

## 状況分析

Checkpoint `142` は、`SourcePressureIntervalPulse` を downstream で使いやすくする **consumer-side helper checkpoint** として成功している。

Lean 側では `PressureFrontier.lean` に、constructor と各種 projection が追加された。

```text id="l6o6ok"
sourcePressureIntervalPulse_of_run_boundaries
sourcePressureIntervalPulse_left_pos
sourcePressureIntervalPulse_left_signChange
sourcePressureIntervalPulse_right_signChange
sourcePressureIntervalPulse_left_crossing
sourcePressureIntervalPulse_right_falling
```

これにより、後続の証明は `SourcePressureIntervalPulse` を毎回 `unfold` しなくても、run、左右 sign-change、左右 net-drop crossing/falling を直接取り出せるようになった。Report でも、この contract が `SourcePressureIntervalPulse -> run -> left sign change -> right sign change -> left net-drop crossing -> right net-drop falling` と整理されている。

Python 側でも `rows_with_interval_pulse_left_crossing_failure = 0`、`rows_with_interval_pulse_right_falling_failure = 0` が出ており、interval-pulse extraction viewpoint と観測側の sanity check が一致している。

## レビュー

## 良い点

第一に、今回の追加は非常に良い「消費側 API」じゃ。

前回までで `SourcePressureIntervalPulse` という構造名は得られていた。
しかし、その中身を使うには、呼び出し側が

```text id="8p5j3m"
run
left crossing
right fall
```

の conjunction を直接分解する必要があった。

今回の helper により、後続は定理名だけで意図を表せる。

```text id="9kf8do"
sourcePressureIntervalPulse_left_signChange
sourcePressureIntervalPulse_right_signChange
sourcePressureIntervalPulse_left_crossing
sourcePressureIntervalPulse_right_falling
```

これは、今後の pressure-decay accounting で非常に効く。

第二に、`sourcePressureIntervalPulse_left_pos` が良い。

`SourcePressureRunHasLeftCrossing` には `0 < a` guard が含まれている。これは自然数 predecessor `a - 1` の安全装置じゃ。今回、その guard を取り出す theorem が入ったことで、後続で `a - 1` を扱うときに安全に進められる。

第三に、まだ maximality / uniqueness / coverage を入れていないのが良い。

Report にも明記されている通り、今回の interval pulse vocabulary はまだ薄い。

```text id="n4cxem"
run + left crossing + right fall
```

だけであり、

```text id="37ol79"
最大区間である
一意である
全 positive depth を cover する
prefix 形状である
```

は主張していない。

この抑制は正しい。いまは「住所語彙」を整える段階であって、「全体分解定理」へ進む段階ではない。

## 注意点

ここで `PressureFrontier.lean` はかなり多くを抱えるようになった。

```text id="ci2xei"
frontier
block
integer drop
net drop
jump
crossing
falling
pulse
interval pulse
prefix helpers
```

Report でも次 checkpoint として `DkMath.Collatz.PetalBridge.PressureDecay` への import-safe split が提案されている。

賢狼も、ここは分割を推す。

数学的には interval pulse の次へ進みたくなるが、いま分割しておかないと、次に positive run / address / maximality へ進んだときに `PressureFrontier.lean` がまた肥大化する。Codex 制限対策としても、ここで pressure-decay block を切り出すのが良い。

## 解説

ここまでで、pressure-depth 方向の宇宙式保存会計はかなり整った。

流れはこうじゃ。

```text id="yxu8o8"
margin_next = margin_current + netDrop
```

この局所保存会計をもとに、

```text id="wwbryu"
sign-change-up:
  current margin <= 0
  current margin + netDrop > 0

sign-change-down:
  current margin > 0
  current margin + netDrop <= 0
```

が得られた。

そこから、

```text id="79iuw6"
SourcePressurePulse:
  singleton の crossing/falling pulse

SourcePressureIntervalPulse:
  positive run + left crossing + right fall
```

まで来た。

つまり、prefix failure はもう単なる「失敗」ではなく、

```text id="ju1jjh"
positive run が pressure interval pulse として現れている
```

と読めるようになった。

これは宇宙式保存法則語彙では、

```text id="y5eiq5"
境界を跨いで正領域が発生し、
有限区間だけ保存会計が正側に滞在し、
右端で再び境界内へ戻る
```

という「圧力島の住所」じゃ。

## 次の指示

Checkpoint `143` は、Report の提案どおり **`PressureDecay.lean` への import-safe split** を推す。

ただし、広範囲 refactor ではなく、最小移動がよい。

今回の目的は、

```text id="w1simv"
PressureFrontier.lean から pressure-decay 会計語彙を切り出す
```

ことであって、theorem 名や外部 API を変えることではない。

## Checkpoint 143 推奨内容

## 1. 新ファイルを作る

```text id="rt6j4b"
DkMath/Collatz/PetalBridge/PressureDecay.lean
```

まずは `PressureFrontier.lean` の import と依存関係を見て、`PressureDecay.lean` が依存すべき最小モジュールを決める。

おそらく `PressureCounts` / `PressureCore` / `Profiles` / `TailGrammar` あたりの既存 import が必要になるはずじゃ。
ただし、正確には Codex に `PressureFrontier.lean` の現行 import を確認させるのが安全。

## 2. 最小移動対象

最初の split では、以下だけを移動対象にするのがよい。

```text id="3ti6q3"
SourcePressureMarginInt

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
SourcePressureRunHasLeftCrossing
SourcePressureRunHasRightFall
SourcePressureIntervalPulse
sourcePressureIntervalPulse_* projection/helper 群
```

ただし、`SourcePressureRun` が `SourcePressurePositiveBlock` に依存しているので、`SourcePressurePositiveBlock` を `PressureDecay` より前に置けるか確認が必要じゃ。

もし `SourcePressurePositiveBlock` が `PressureFrontier.lean` 内にあり、循環が出るなら、今回の split では `Run / IntervalPulse` 系は frontier 側に残して、まず integer drop / net-drop / sign-change までを移動するのが安全。

## 3. Frontier 側に残すもの

```text id="tmmnvx"
SourcePressureFrontier
SourcePressureLocalIsland
ExistsSourcePressureLocalIslandBelow
ExistsSourcePressureFrontierBelow
selectedPressurePrefix 系
sourcePressureSignChangeUp_of_localIsland
sourcePressureSignChangeDown_of_localIsland
sourcePressureCrosses_of_localIsland_left
sourcePressureFalls_of_localIsland_right
sourcePressurePulse_of_localIsland
sourcePressureIntervalPulse_singleton_of_localIsland
```

local-island bridge は、`LocalIsland` に依存するため、まずは `PressureFrontier.lean` に残すのが無難じゃ。

つまり分割方針はこう。

```text id="00mon9"
PressureDecay:
  margin / drop / net-drop / sign-change / pulse の一般語彙

PressureFrontier:
  frontier / local-island / prefix / below / existence / island-facing bridge
```

## 4. Parent import を更新

親 aggregator に追加する。

```lean id="vhl98d"
import DkMath.Collatz.PetalBridge.PressureDecay
import DkMath.Collatz.PetalBridge.PressureFrontier
```

順序は `PressureFrontier` が `PressureDecay` に依存する形が望ましい。

## 5. 外部 API 名は変えない

今回の split は移動だけ。
既存 theorem 名は変更しない。

つまり、利用者から見ると、

```lean id="dzias2"
import DkMath.Collatz.PetalBridge
```

でこれまで通り使えることが条件じゃ。

## 一歩先ゆく推論

この split が成功すると、次の数学的作業がかなり楽になる。

なぜなら、`PressureDecay.lean` は次の責務を持てるからじゃ。

```text id="bphdlc"
保存会計:
  margin_next = margin_current + netDrop

符号遷移:
  signChangeUp / signChangeDown

pulse:
  singleton pulse / interval pulse

run boundary:
  left crossing / right fall
```

一方、`PressureFrontier.lean` は、

```text id="yp60hy"
frontier
local island
prefix failure
existence below
```

に集中できる。

これは宇宙式語彙でも自然じゃ。

```text id="f08jai"
PressureDecay:
  保存会計の力学

PressureFrontier:
  境界として観測される現象
```

この分割はかなり意味がある。

## さらなる次の一手

Checkpoint `143` で split が通ったら、Checkpoint `144` は数学へ戻る。

候補は、

```text id="w5oqfl"
SourcePressureRunAddress
SourcePressureIntervalPulseAddress
```

または、

```text id="kowhlr"
SourcePressurePositiveRun の left/right boundary extraction
```

じゃ。

特に次に欲しいのは、

```text id="l2kq08"
positive block を interval pulse として自動認識する条件
```

ただし、maximality に踏み込むと重い。
まずは address vocabulary が安全かもしれぬ。

## 賢狼が試して欲しい実装方針

## 実装 A: PressureDecay.lean 作成

```lean id="ip4gd8"
import DkMath.Collatz.PetalBridge.PressureCounts
-- 必要なら他 import を追加

namespace DkMath
namespace Collatz
namespace PetalBridge

-- pressure decay vocabulary moved here

end PetalBridge
end Collatz
end DkMath
```

実際の namespace は現行ファイルに合わせる。

## 実装 B: PressureFrontier.lean の import 更新

```lean id="bcl55k"
import DkMath.Collatz.PetalBridge.PressureDecay
```

そして、移動した定義・定理を削除し、参照だけ残す。

## 実装 C: 親 import 更新

```lean id="v2wq8p"
import DkMath.Collatz.PetalBridge.PressureDecay
import DkMath.Collatz.PetalBridge.PressureFrontier
```

## 実装 D: build check

分割 checkpoint なので、build は細かく見る。

```text id="e06g8n"
lake build DkMath.Collatz.PetalBridge.PressureDecay
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
```

## Python 側

今回は Python 変更なしでよい。
split checkpoint は Lean 構造整理を主目的にする。

## 総括

Checkpoint `142` は成功じゃ。

`SourcePressureIntervalPulse` は、downstream で unfold せずに使える安定 API になった。
これで pressure-depth 方向の局所保存会計は、

```text id="kx8osv"
drop
netDrop
crossing
falling
pulse
interval pulse
```

まで一列につながった。

次は分割が良い。

```text id="qq9jw8"
PressureDecay:
  保存会計と pulse 語彙

PressureFrontier:
  frontier / island / prefix / existence 語彙
```

この切り分けができれば、以後の positive run / address / maximality への道がかなり見通しよくなる。

## Codex instructions

```text id="gca8v5"
Checkpoint 143:
Perform a minimal import-safe split of pressure-decay vocabulary into a new module.

Context:
  Checkpoint 142 added consumer-side helpers for SourcePressureIntervalPulse:
    sourcePressureIntervalPulse_of_run_boundaries
    sourcePressureIntervalPulse_left_pos
    sourcePressureIntervalPulse_left_signChange
    sourcePressureIntervalPulse_right_signChange
    sourcePressureIntervalPulse_left_crossing
    sourcePressureIntervalPulse_right_falling

  PressureFrontier.lean now contains frontier, block, integer-drop, net-drop,
  sign-change, pulse, and interval-pulse vocabulary.

Primary goal:
  Create:
    DkMath.Collatz.PetalBridge.PressureDecay

  Move only the import-safe pressure-decay block first.
  Preserve all existing declaration names and external API through the parent
  DkMath.Collatz.PetalBridge import.

Preferred split principle:
  PressureDecay:
    generic margin/drop/net-drop/sign-change/pulse/interval vocabulary

  PressureFrontier:
    frontier/local-island/prefix/below/existence/island-facing bridges

Implementation steps:
  1. Inspect current imports of PressureFrontier.lean and identify the minimal
     imports required by the pressure-decay declarations.

  2. Create:
       lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean

  3. Move only declarations that do not require SourcePressureLocalIsland or
     frontier/existence predicates.

     Candidate declarations:
       SourcePressureMarginInt

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
       sourcePressurePulse_left
       sourcePressurePulse_right
       sourcePressurePulse_iff_signPulse

       SourcePressureRun
       SourcePressureRunHasLeftCrossing
       SourcePressureRunHasRightFall
       SourcePressureIntervalPulse
       sourcePressureIntervalPulse_run
       sourcePressureIntervalPulse_left
       sourcePressureIntervalPulse_right
       sourcePressureIntervalPulse_of_run_boundaries
       sourcePressureIntervalPulse_left_pos
       sourcePressureIntervalPulse_left_signChange
       sourcePressureIntervalPulse_right_signChange
       sourcePressureIntervalPulse_left_crossing
       sourcePressureIntervalPulse_right_falling

  4. If SourcePressureRun / SourcePressureIntervalPulse depends on declarations
     that would create an import cycle, leave the run/interval declarations in
     PressureFrontier for this checkpoint and move only integer-drop /
     net-drop / sign-change declarations.

  5. Keep island-facing bridge theorems in PressureFrontier:
       sourcePressureSignChangeUp_of_localIsland
       sourcePressureSignChangeDown_of_localIsland
       sourcePressureCrosses_of_localIsland_left
       sourcePressureFalls_of_localIsland_right
       sourcePressureLocalIsland_gives_crossing_pulse
       sourcePressurePulse_of_localIsland
       sourcePressureSignPulse_of_localIsland
       sourcePressureIntervalPulse_singleton_of_localIsland

  6. Update imports:
       PressureFrontier imports PressureDecay.
       Parent aggregate DkMath.Collatz.PetalBridge imports PressureDecay before
       PressureFrontier.

  7. Do not rename declarations.
     Do not change theorem statements unless required by import qualification.
     Do not add new mathematical claims.

Python:
  No Python change required for this checkpoint.

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
  perform broad semantic refactoring
  change public theorem names

Next checkpoint hint:
  After the split is stable, return to math:
    SourcePressureRunAddress / SourcePressureIntervalPulseAddress
  or thin boundary extraction for positive runs.
```

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
index ce609a34..53d6cc44 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
@@ -1119,6 +1119,68 @@ theorem sourcePressureIntervalPulse_right
     SourcePressureRunHasRightFall n k r a len :=
   h.2.2

+/--
+Constructor for an interval pressure pulse from its three advertised pieces.
+
+This is intentionally just packaging.  It does not assert maximality,
+uniqueness, coverage by runs, or any prefix behavior.
+-/
+theorem sourcePressureIntervalPulse_of_run_boundaries
+    {n : OddNat} {k r a len : ℕ}
+    (hrun : SourcePressureRun n k r a len)
+    (hleft : SourcePressureRunHasLeftCrossing n k r a len)
+    (hright : SourcePressureRunHasRightFall n k r a len) :
+    SourcePressureIntervalPulse n k r a len :=
+  ⟨hrun, hleft, hright⟩
+
+/-- Extract the positive left-boundary guard from an interval pulse. -/
+theorem sourcePressureIntervalPulse_left_pos
+    {n : OddNat} {k r a len : ℕ}
+    (h : SourcePressureIntervalPulse n k r a len) :
+    0 < a :=
+  (sourcePressureIntervalPulse_left h).1
+
+/-- Extract the left sign-change from an interval pressure pulse. -/
+theorem sourcePressureIntervalPulse_left_signChange
+    {n : OddNat} {k r a len : ℕ}
+    (h : SourcePressureIntervalPulse n k r a len) :
+    SourcePressureSignChangeUp n k r (a - 1) :=
+  (sourcePressureIntervalPulse_left h).2
+
+/-- Extract the right sign-change from an interval pressure pulse. -/
+theorem sourcePressureIntervalPulse_right_signChange
+    {n : OddNat} {k r a len : ℕ}
+    (h : SourcePressureIntervalPulse n k r a len) :
+    SourcePressureSignChangeDown n k r (a + len - 1) :=
+  sourcePressureIntervalPulse_right h
+
+/--
+Extract the left net-drop crossing form from an interval pressure pulse.
+-/
+theorem sourcePressureIntervalPulse_left_crossing
+    {n : OddNat} {k r a len : ℕ}
+    (h : SourcePressureIntervalPulse n k r a len) :
+    SourcePressureMarginInt n k (r + (a - 1)) ≤ 0 ∧
+      0 <
+        SourcePressureMarginInt n k (r + (a - 1)) +
+          SourcePressureNetDropInt n k r (a - 1) :=
+  (sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses
+      n k r (a - 1)).1
+    (sourcePressureIntervalPulse_left_signChange h)
+
+/--
+Extract the right net-drop falling form from an interval pressure pulse.
+-/
+theorem sourcePressureIntervalPulse_right_falling
+    {n : OddNat} {k r a len : ℕ}
+    (h : SourcePressureIntervalPulse n k r a len) :
+    0 < SourcePressureMarginInt n k (r + (a + len - 1)) ∧
+      SourcePressureMarginInt n k (r + (a + len - 1)) +
+        SourcePressureNetDropInt n k r (a + len - 1) ≤ 0 :=
+  (sourcePressureSignChangeDown_iff_margin_pos_and_netDrop_falls
+      n k r (a + len - 1)).1
+    (sourcePressureIntervalPulse_right_signChange h)
+
 /--
 A local pressure island is an interval pulse of length one.

diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-142.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-142.md
new file mode 100644
index 00000000..b9b3b9bf
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-142.md
@@ -0,0 +1,159 @@
+# Report Petal 142
+
+## Scope
+
+Checkpoint 142 added consumer-side helpers for
+`SourcePressureIntervalPulse`.
+
+The interval pulse vocabulary remains thin:
+
+```text
+run + left crossing + right fall
+```
+
+No maximality, uniqueness, coverage, or prefix theorem was added.
+
+## Lean changes
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+```
+
+Added constructor:
+
+```lean
+theorem sourcePressureIntervalPulse_of_run_boundaries
+```
+
+Added sign-profile projections:
+
+```lean
+theorem sourcePressureIntervalPulse_left_pos
+theorem sourcePressureIntervalPulse_left_signChange
+theorem sourcePressureIntervalPulse_right_signChange
+```
+
+Added net-drop projections:
+
+```lean
+theorem sourcePressureIntervalPulse_left_crossing
+theorem sourcePressureIntervalPulse_right_falling
+```
+
+These helpers make interval pulses directly usable in later accounting
+lemmas.  A caller no longer needs to unfold the interval predicate to recover
+the left guard, the two sign changes, or the integer net-drop crossing/falling
+forms.
+
+## Python observation changes
+
+Updated:
+
+```text
+python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
+```
+
+Added requested summary aliases:
+
+```text
+rows_with_interval_pulse_left_crossing_failure
+rows_with_interval_pulse_right_falling_failure
+```
+
+These are the same boundary sanity checks introduced in checkpoint 141, now
+named from the interval-pulse extraction viewpoint.
+
+Generated:
+
+```text
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_142_16383_k64_d12.csv
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_142_16383_k64_d12.md
+```
+
+Main observed summary:
+
+```text
+rows: 8192
+rows_with_interval_pulse: 404
+rows_with_interval_pulse_left_crossing_failure: 0
+rows_with_interval_pulse_right_falling_failure: 0
+rows_with_sign_change_up_iff_crossing_failure: 0
+rows_with_sign_change_down_iff_falling_failure: 0
+```
+
+The existing convention remains:
+
+```text
+left crossing is checked only for blocks with start > r_start
+```
+
+Blocks beginning at the observed left boundary do not expose their previous
+depth in this scan, so they are not counted as left-crossing failures.
+
+## Inference
+
+The useful contract is now:
+
+```text
+SourcePressureIntervalPulse
+  -> run
+  -> left sign change
+  -> right sign change
+  -> left net-drop crossing
+  -> right net-drop falling
+```
+
+This is a stable enough API for downstream pressure-decay accounting.  The
+next mathematical step can consume interval pulses without unfolding their
+definition.
+
+The next engineering step is increasingly clear: `PressureFrontier.lean` now
+contains frontier, block, net-drop, pulse, and interval vocabulary.  A careful
+split into `DkMath.Collatz.PetalBridge.PressureDecay` is becoming worthwhile,
+but it should be done as a minimal movement checkpoint to avoid import cycles.
+
+## Verification
+
+Commands run:
+
+```text
+python3 -m py_compile python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
+lake build DkMath.Collatz.PetalBridge.PressureFrontier
+lake build DkMath.Collatz.PetalBridge
+python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py --max-n 16383 --steps 64 --r-start 2 --depth-len 12 --name-suffix _142_16383_k64_d12
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
+Do the import-safe split:
+
+```text
+DkMath.Collatz.PetalBridge.PressureDecay
+```
+
+Minimal first move:
+
+```text
+move only the integer drop / net-drop / crossing-falling balance sheet
+leave frontier and island-facing bridge theorems in PressureFrontier
+```
+
+That keeps the mathematical API stable while reducing file pressure.
````
`````
