# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.*

gch: d9b55895752b7e2fe297a58357d79334925214f8

## Report

実装完了です。

[PressureFrontier.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean) に、局所 pressure island の右端を扱う `SourcePressureSignChangeDown` と、右端 fall 条件への同値・導出補題を追加しました。これで local island は「左で上向き crossing、右で下向き falling」という crossing pulse として読めます。

Python 側の観測にも right-fall 検査を追加し、mod/深さ scan を再実行しました。結果は以下です。

- [CSV](/python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_139_16383_k64_d12.csv)
- [summary](/python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_139_16383_k64_d12.md)
- [report-petal-139.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-139.md)

検証結果:

- `python3 -m py_compile python/Collatz/PetalBridge/pressure_sign_pattern_scan.py` pass
- `lake build DkMath.Collatz.PetalBridge.PressureFrontier` pass
- `lake build DkMath.Collatz.PetalBridge` pass
- `rg "\bsorry\b" PressureFrontier.lean` no hits
- `git diff --check` pass

観測でも `local_island_right_fall_failure = 0`、`sign_change_down_iff_falling_failure = 0` でした。次は、この pulse を interval / block 的な「圧力島の住所」として扱う方向が自然です。

## Review

## 状況分析

Checkpoint `139` は、前回の zero-crossing theorem に対して、右端の **fall down** を追加し、local island を完全に **crossing pulse** として読めるところまで進めた checkpoint じゃ。

Lean 側では `PressureFrontier.lean` に `SourcePressureSignChangeDown` が追加され、local island の右端が downward sign-change であること、さらにそれが

```text
current margin > 0
current margin + net drop <= 0
```

という falling condition と同値であることが固定された。最後に `sourcePressureLocalIsland_gives_crossing_pulse` により、local island が「左で上向き crossing、右で下向き falling」を持つ局所 pulse として package された。

Python 側でも `local_island_right_fall_failure = 0`、`sign_change_down_iff_falling_failure = 0` が出ており、Lean の右端 theorem と scan の観測が一致している。

## レビュー

## 良い点

第一に、`SourcePressureSignChangeDown` の追加で、sign-change-up の片翼だけだった構造が双対化された。

```text
SourcePressureSignChangeUp:
  nonpositive -> positive

SourcePressureSignChangeDown:
  positive -> nonpositive
```

これで pressure-depth 方向の符号プロファイルを、上昇 edge と下降 edge の両方から扱えるようになった。

第二に、`sourcePressureSignChangeDown_of_localIsland` が良い。

local island は中央 depth が positive で、その左右が nonpositive という形なので、右端 `j -> j+1` は自然に sign-change-down になる。これが Lean で閉じたことで、local island は単なる定義上の符号パターンではなく、隣接 edge の変化として読めるようになった。

第三に、falling theorem が zero-crossing theorem と綺麗に対になる。

```text
up:
  current margin <= 0
  current margin + net drop > 0

down:
  current margin > 0
  current margin + net drop <= 0
```

これは非常に DkMath 的じゃ。
上昇も下降も、同じ保存会計式

```text
next margin = current margin + net drop
```

の上で、境界をどちら向きに跨ぐかの違いとして表現できている。

第四に、`sourcePressureLocalIsland_gives_crossing_pulse` が良い。

これで local island は、

```text
left edge:
  zero-crossing up

right edge:
  falling down
```

を同時に持つ **局所 pulse** として扱えるようになった。報告にもある通り、これは global prefix を主張せず、あくまで local adjacent-depth edge の構造として閉じている点が安全じゃ。

## 注意点

ここで注意すべきは、`SourcePressureLocalIsland` はまだ **長さ 1 の孤立 pulse** である、という点じゃ。

今回閉じたのは、

```text
nonpositive -> positive -> nonpositive
```

という一点島の構造じゃ。

一方で、Python scan では positive block length が `1` だけでなく、`2`, `3`, `4`, … まで出ている。今回の summary でも positive block length や sign-change-down の観測が出ており、`rows_with_sign_change_down=4421` は positive pressure depths を持つ行数と一致している。

つまり次の一般化対象は、

```text
local island:
  長さ 1 の pulse

positive block / positive run:
  長さ >= 1 の interval pulse
```

じゃ。

ここを急に大域定理にせず、まず「住所」や「区間」として扱うのがよい。

## 解説

前回の問いに絡めて言えば、今回でかなりはっきり **宇宙式保存法則語彙に乗った**。

今の pressure pulse は、こう読める。

```text
current margin:
  現在の境界状態

net drop:
  retention obstruction の減少と continuation loss の差分から生じる局所駆動量

next margin:
  保存会計を通した次の境界状態
```

そして基本式は、

```text
next margin = current margin + net drop
```

じゃ。

local island は、この式に沿って、

```text
左端:
  net drop が現在 margin を 0 の上へ押し上げる

右端:
  net drop が現在 margin を 0 以下へ戻す
```

という形になる。

つまり、local island は prefix を壊す「例外」ではなく、

```text
pressure-depth 方向の局所保存会計 pulse
```

として扱えるようになった。

これは大きい。
Collatz の pressure profile が単調な carrier ではなく、局所 pulse を含む sign profile である、という読みが Lean 側で支えられ始めている。報告でも「observed pressure is not a monotone carrier; it is a sign profile with local pulses」と整理されている。

## 次の指示

Checkpoint `140` は、賢狼としては **薄い `SourcePressurePulse` 語彙の追加**を推す。

`PressureDecay.lean` への分割もそろそろ自然だが、今回の theorem flow はまだ熱い。
まず `SourcePressureLocalIsland_gives_crossing_pulse` で得た構造に名前を与えるのが良い。

その後、Checkpoint `141` あたりで `PressureDecay.lean` へ分割するのが安全じゃ。

## Checkpoint 140 推奨内容

## 1. SourcePressurePulse を定義する

まずは長さ 1 の local pulse として定義する。

```lean
def SourcePressurePulse
    (n : OddNat) (k r j : ℕ) : Prop :=
  (SourcePressureMarginInt n k (r + (j - 1)) ≤ 0 ∧
    0 <
      SourcePressureMarginInt n k (r + (j - 1)) +
        SourcePressureNetDropInt n k r (j - 1)) ∧
  (0 < SourcePressureMarginInt n k (r + j) ∧
    SourcePressureMarginInt n k (r + j) +
      SourcePressureNetDropInt n k r j ≤ 0)
```

これは `sourcePressureLocalIsland_gives_crossing_pulse` の右辺に名前を付けたものじゃ。

## 2. local island から pulse を出す

```lean
theorem sourcePressurePulse_of_localIsland
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j) :
    SourcePressurePulse n k r j := by
  exact sourcePressureLocalIsland_gives_crossing_pulse n k r j hisland
```

定義が完全に一致すれば `exact` で通るはず。
通らなければ `unfold SourcePressurePulse` を挟む。

## 3. pulse から左 crossing / 右 falling を取り出す

```lean
theorem sourcePressurePulse_left
    (n : OddNat) (k r j : ℕ)
    (h : SourcePressurePulse n k r j) :
    SourcePressureMarginInt n k (r + (j - 1)) ≤ 0 ∧
      0 <
        SourcePressureMarginInt n k (r + (j - 1)) +
          SourcePressureNetDropInt n k r (j - 1) :=
  h.1
```

```lean
theorem sourcePressurePulse_right
    (n : OddNat) (k r j : ℕ)
    (h : SourcePressurePulse n k r j) :
    0 < SourcePressureMarginInt n k (r + j) ∧
      SourcePressureMarginInt n k (r + j) +
        SourcePressureNetDropInt n k r j ≤ 0 :=
  h.2
```

これは薄いが、次に positive run / interval pulse を作るときに便利になる。

## 4. sign-change 版の pulse も optional

もし余裕があれば、margin formula ではなく sign-change 述語だけで pulse を定義する alias もあり。

```lean
def SourcePressureSignPulse
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourcePressureSignChangeUp n k r (j - 1) ∧
    SourcePressureSignChangeDown n k r j
```

そして、

```lean
theorem sourcePressureSignPulse_of_localIsland
```

を出す。

ただし、今回の主語は保存会計語彙なので、まずは `SourcePressurePulse` を net drop crossing/falling で定義する方がよい。

## 5. Python は任意

Python 側はすでに right-fall sanity が十分出ている。
次にやるなら、pulse count を明示する程度でよい。

```text
rows_with_local_pressure_pulse
rows_with_local_island_iff_pulse_failure
```

ただし今回は Lean 側の vocabulary を優先でよい。

## 一歩先ゆく推論

この `SourcePressurePulse` が入ると、次に見えるのは **positive block の interval 化**じゃ。

local island は長さ 1 の pulse。

しかし positive block が長さ `m` のときは、

```text
left edge:
  sign-change-up / crossing

middle:
  positive plateau

right edge:
  sign-change-down / falling
```

になる。

つまり次の一般化は、

```text
SourcePressurePositiveRun
SourcePressurePulseInterval
```

のようなものになる。

ただし、いきなり interval をやると重い。
まず `SourcePressurePulse` で長さ 1 の構造を固定し、その後で positive block の住所系へ進むのがよい。

これはまさに報告にある「pulse を interval / block 的な圧力島の住所として扱う方向」と合っている。

## さらなる次の一手

Checkpoint `140` で `SourcePressurePulse` が入ったら、Checkpoint `141` は二択。

## Route A: `PressureDecay.lean` へ分割

ここまでで `PressureFrontier.lean` はかなり多くを抱えている。

```text
integer drops
net drop
margin step identity
jump equivalence
zero crossing
falling
pulse
frontier / island / prefix helpers
```

`PressureDecay.lean` を切るには十分じゃ。

ただし import 依存に注意する必要がある。
`SourcePressureLocalIsland` が `PressureFrontier` 側に残るなら、`PressureDecay` に移すものは純粋な margin / drop / sign-change の定義と theorem に絞るのがよい。

## Route B: positive run / interval pulse

数学的にはこちらが面白い。

```text
SourcePressurePositiveRun n k r a len
```

を定義し、

```text
left crossing
positive run
right falling
```

を持つ `SourcePressurePulseInterval` へ進める。

ただしこれは少し重いので、先に分割してからの方が安全かもしれぬ。

## 賢狼が試して欲しい実験補題

## 実験 A: pressure pulse definition

```lean
def SourcePressurePulse
    (n : OddNat) (k r j : ℕ) : Prop :=
  (SourcePressureMarginInt n k (r + (j - 1)) ≤ 0 ∧
    0 <
      SourcePressureMarginInt n k (r + (j - 1)) +
        SourcePressureNetDropInt n k r (j - 1)) ∧
  (0 < SourcePressureMarginInt n k (r + j) ∧
    SourcePressureMarginInt n k (r + j) +
      SourcePressureNetDropInt n k r j ≤ 0)
```

## 実験 B: local island gives pulse

```lean
theorem sourcePressurePulse_of_localIsland
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j) :
    SourcePressurePulse n k r j := by
  exact sourcePressureLocalIsland_gives_crossing_pulse n k r j hisland
```

必要なら：

```lean
  unfold SourcePressurePulse
  exact sourcePressureLocalIsland_gives_crossing_pulse n k r j hisland
```

## 実験 C: pulse left projection

```lean
theorem sourcePressurePulse_left
    (n : OddNat) (k r j : ℕ)
    (h : SourcePressurePulse n k r j) :
    SourcePressureMarginInt n k (r + (j - 1)) ≤ 0 ∧
      0 <
        SourcePressureMarginInt n k (r + (j - 1)) +
          SourcePressureNetDropInt n k r (j - 1) :=
  h.1
```

## 実験 D: pulse right projection

```lean
theorem sourcePressurePulse_right
    (n : OddNat) (k r j : ℕ)
    (h : SourcePressurePulse n k r j) :
    0 < SourcePressureMarginInt n k (r + j) ∧
      SourcePressureMarginInt n k (r + j) +
        SourcePressureNetDropInt n k r j ≤ 0 :=
  h.2
```

## 実験 E: sign pulse alias

これは optional。

```lean
def SourcePressureSignPulse
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourcePressureSignChangeUp n k r (j - 1) ∧
    SourcePressureSignChangeDown n k r j
```

## Python 側の次観測

今回は Python は控えめでよい。
追加するなら summary だけ。

```text
rows_with_local_pressure_pulse
rows_with_local_island_to_pulse_failure
```

期待値：

```text
rows_with_local_island_to_pulse_failure: 0
```

ただし Lean theorem が主なので、Python 追加は optional で十分じゃ。

## 総括

Checkpoint `139` は成功じゃ。

これで local island は、

```text
left:
  current margin <= 0
  current margin + net drop > 0

right:
  current margin > 0
  current margin + net drop <= 0
```

という **crossing pulse** として閉じた。

これは、宇宙式保存法則語彙で言えば、

```text
局所境界を上へ跨ぎ、
次の edge で再び境界内へ戻る保存会計 pulse
```

じゃ。

次はその構造に `SourcePressurePulse` という名前を与えるのがよい。
その後で `PressureDecay.lean` に切り出せば、数学的にも実装的にも綺麗になる。

## Codex instructions

```text
Checkpoint 140:
Add a thin SourcePressurePulse vocabulary for the local pressure island pulse.

Context:
  Checkpoint 139 added:
    SourcePressureSignChangeDown
    sourcePressureSignChangeDown_of_localIsland
    sourcePressureSignChangeDown_iff_margin_pos_and_netDrop_falls
    sourcePressureFalls_of_localIsland_right
    sourcePressureLocalIsland_gives_crossing_pulse

  The current local island story is:
    left edge:
      current margin <= 0
      current margin + net drop > 0
    right edge:
      current margin > 0
      current margin + net drop <= 0

Primary goal:
  Give this local crossing/falling structure a stable Lean name:
    SourcePressurePulse

Preferred Lean location:
  DkMath.Collatz.PetalBridge.PressureFrontier

Implement:
  1. Define:
     SourcePressurePulse n k r j

     Suggested definition:
       (SourcePressureMarginInt n k (r + (j - 1)) <= 0
        ∧ 0 <
          SourcePressureMarginInt n k (r + (j - 1))
            + SourcePressureNetDropInt n k r (j - 1))
       ∧
       (0 < SourcePressureMarginInt n k (r + j)
        ∧ SourcePressureMarginInt n k (r + j)
            + SourcePressureNetDropInt n k r j <= 0)

  2. Prove:
     sourcePressurePulse_of_localIsland

     It should follow directly from:
       sourcePressureLocalIsland_gives_crossing_pulse

  3. Prove projection helpers:
     sourcePressurePulse_left
     sourcePressurePulse_right

  4. Optional:
     Define SourcePressureSignPulse as:
       SourcePressureSignChangeUp n k r (j - 1)
       ∧ SourcePressureSignChangeDown n k r j

     Only add this if it stays very small.

Optional Python:
  Add summary fields:
    rows_with_local_pressure_pulse
    rows_with_local_island_to_pulse_failure

  Expected:
    rows_with_local_island_to_pulse_failure: 0

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
  After SourcePressurePulse is named, consider splitting pressure-decay material into:
    DkMath.Collatz.PetalBridge.PressureDecay
  or generalizing from local pulses to positive-run / interval pulses.
```

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
index 86da8e3d..cccfa93c 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
@@ -341,6 +341,17 @@ def SourcePressureSignChangeUp
   SourcePressureMarginInt n k (r + j) ≤ 0 ∧
     0 < SourcePressureMarginInt n k (r + j + 1)
 
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
 /--
 Named pressure-margin jump between adjacent pressure depths.
 
@@ -886,6 +897,70 @@ theorem sourcePressureCrosses_of_localIsland_left
       n k r (j - 1)).1
     (sourcePressureSignChangeUp_of_localIsland n k r j hisland)
 
+/--
+A local pressure island produces a downward sign change at its right edge.
+-/
+theorem sourcePressureSignChangeDown_of_localIsland
+    (n : OddNat) (k r j : ℕ)
+    (hisland : SourcePressureLocalIsland n k r j) :
+    SourcePressureSignChangeDown n k r j := by
+  rcases hisland with ⟨_hjpos, hsel, _hprev_not, hnext_not⟩
+  unfold SourcePressureSignChangeDown
+  constructor
+  · exact (isSourcePressureDepth_iff_margin_pos n k r j).1 hsel
+  · have hnotpos :
+        ¬ 0 < SourcePressureMarginInt n k (r + j + 1) := by
+      intro hpos
+      exact hnext_not
+        ((isSourcePressureDepth_iff_margin_pos n k r (j + 1)).2 hpos)
+    omega
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
+A local pressure island gives the falling condition at its right edge.
+-/
+theorem sourcePressureFalls_of_localIsland_right
+    (n : OddNat) (k r j : ℕ)
+    (hisland : SourcePressureLocalIsland n k r j) :
+    0 < SourcePressureMarginInt n k (r + j) ∧
+      SourcePressureMarginInt n k (r + j) +
+        SourcePressureNetDropInt n k r j ≤ 0 :=
+  (sourcePressureSignChangeDown_iff_margin_pos_and_netDrop_falls n k r j).1
+    (sourcePressureSignChangeDown_of_localIsland n k r j hisland)
+
+/--
+A local pressure island is a local crossing pulse: it crosses upward at the
+left edge and falls back down at the right edge.
+-/
+theorem sourcePressureLocalIsland_gives_crossing_pulse
+    (n : OddNat) (k r j : ℕ)
+    (hisland : SourcePressureLocalIsland n k r j) :
+    (SourcePressureMarginInt n k (r + (j - 1)) ≤ 0 ∧
+      0 <
+        SourcePressureMarginInt n k (r + (j - 1)) +
+          SourcePressureNetDropInt n k r (j - 1)) ∧
+      (0 < SourcePressureMarginInt n k (r + j) ∧
+        SourcePressureMarginInt n k (r + j) +
+          SourcePressureNetDropInt n k r j ≤ 0) :=
+  ⟨sourcePressureCrosses_of_localIsland_left n k r j hisland,
+    sourcePressureFalls_of_localIsland_right n k r j hisland⟩
+
 /--
 Package a named margin jump and a strict retention drop.
 
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-139.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-139.md
new file mode 100644
index 00000000..706735f5
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-139.md
@@ -0,0 +1,198 @@
+# Report Petal 139
+
+## Scope
+
+Checkpoint 139 added the right-edge fall side of a local source-pressure
+island.
+
+The result is still local to adjacent pressure-depth edges.  It does not claim
+that selected pressure depths are prefix-shaped and does not introduce a full
+pressure grid.
+
+## Lean Changes
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+```
+
+Added the downward sign-change predicate:
+
+```lean
+def SourcePressureSignChangeDown
+```
+
+Added the local-island right-edge bridge:
+
+```lean
+theorem sourcePressureSignChangeDown_of_localIsland
+```
+
+Added the falling form of the zero-crossing theorem:
+
+```lean
+theorem sourcePressureSignChangeDown_iff_margin_pos_and_netDrop_falls
+```
+
+Added local-island right-edge falling extraction:
+
+```lean
+theorem sourcePressureFalls_of_localIsland_right
+```
+
+Added the pulse packaging theorem:
+
+```lean
+theorem sourcePressureLocalIsland_gives_crossing_pulse
+```
+
+The local island now has both edges available:
+
+```text
+left edge:
+  current margin <= 0
+  and current margin + net drop > 0
+
+right edge:
+  current margin > 0
+  and current margin + net drop <= 0
+```
+
+This closes the immediate up/down local pulse shape without asserting anything
+about deeper global pressure structure.
+
+## Python Changes
+
+Updated:
+
+```text
+python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
+```
+
+Added row-level fields:
+
+```text
+sign_change_down_positions
+sign_change_down_count
+falling_matches_sign_change_down
+local_island_right_fall_failure_count
+sign_change_down_iff_falling_failure_count
+```
+
+Added summary fields:
+
+```text
+rows_with_sign_change_down
+rows_with_local_island_right_fall_failure
+rows_with_sign_change_down_iff_falling_failure
+```
+
+These mirror the Lean right-edge falling theorem at scan level.
+
+## Experiment
+
+Command:
+
+```bash
+python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py \
+  --max-n 16383 --steps 64 --r-start 2 --depth-len 12 \
+  --name-suffix _139_16383_k64_d12
+```
+
+Generated:
+
+```text
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_139_16383_k64_d12.csv
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_139_16383_k64_d12.md
+```
+
+Observed summary:
+
+```text
+rows: 8192
+rows with positive pressure depths: 4421
+rows with local islands: 252
+rows with sign-change-up positions: 404
+max positive depth count: 11
+max local island count: 1
+max sign-change-up count: 1
+largest margin jump: 12
+largest retention drop: 20
+largest continuation drop: 13
+largest retention drop minus 2 continuation drop: 10
+rows_with_margin_step_identity_failure: 0
+rows_with_net_drop_positive: 8089
+rows_with_margin_jump: 8089
+rows_with_margin_jump_iff_net_drop_failure: 0
+rows_with_crossing_identity_failure: 0
+rows_with_sign_change_up_iff_crossing_failure: 0
+rows_with_sign_change_down: 4421
+rows_with_local_island_right_fall_failure: 0
+rows_with_sign_change_down_iff_falling_failure: 0
+sign-change cause counts: retention_drop_dominant:404
+```
+
+The finite scan agrees with the Lean right-edge theorem:
+
+```text
+local island right edge -> sign-change-down
+sign-change-down iff current margin > 0 and current margin + net drop <= 0
+```
+
+## Inference
+
+The local pulse vocabulary is now justified:
+
+```text
+SourcePressureLocalIsland
+  -> left zero-crossing up
+  -> right fall down
+```
+
+This gives a compact local obstruction shape for the larger Collatz/Petal
+pressure story.  The observed pressure is not a monotone carrier; it is a sign
+profile with local pulses.
+
+## Suggested Next Checkpoint
+
+There are two good next moves:
+
+1. Engineering split:
+
+```text
+DkMath.Collatz.PetalBridge.PressureDecay
+```
+
+The pressure-decay block now includes integer drops, margin step identity,
+up/down crossing, local island pulse, and packaging theorems.  It is coherent
+enough to extract without changing theorem statements.
+
+2. Thin vocabulary:
+
+```lean
+def SourcePressurePulse
+```
+
+This could package the two local pulse edge conditions into one predicate.  If
+the next checkpoint keeps theorem work going, this is the smaller step.
+
+## Verification
+
+Passed:
+
+```text
+python3 -m py_compile python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
+lake build DkMath.Collatz.PetalBridge.PressureFrontier
+lake build DkMath.Collatz.PetalBridge
+rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+git diff --check
+```
+
+Notes:
+
+- `rg sorry` returned no hits in `PressureFrontier.lean`.
+- `lake build DkMath.Collatz.PetalBridge` still reports the pre-existing
+  project warning that
+  `DkMath.NumberTheory.ZsigmondyCyclotomicResearch` uses `sorry`; this
+  checkpoint did not touch that file.
````
`````
