# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.*

gch: ef3792c8a11dcd3292ea0e48d0e02a2235141cd7

## Report

checkpoint 138 を実装しました。

[PressureFrontier.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean) に `SourcePressureNetDropInt` を追加し、zero-crossing theorem を固定しました。

```lean
SourcePressureNetDropInt
sourcePressureMargin_next_eq_current_add_netDrop
sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses
sourcePressureCrosses_of_localIsland_left
```

これで局所構図はこうなりました。

```text
next margin = current margin + net drop
sign-change-up ↔ current margin <= 0 ∧ current margin + net drop > 0
```

Python scan 側も [pressure_sign_pattern_scan.py](/python/Collatz/PetalBridge/pressure_sign_pattern_scan.py) に crossing sanity fields を追加しました。生成物:

- [pressure_sign_pattern_scan_138_16383_k64_d12.csv](/python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_138_16383_k64_d12.csv)
- [pressure_sign_pattern_scan_138_16383_k64_d12.md](/python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_138_16383_k64_d12.md)
- [report-petal-138.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-138.md)

観測結果は `rows_with_crossing_identity_failure=0`、`rows_with_sign_change_up_iff_crossing_failure=0` です。

検証済み:

```text
python3 -m py_compile python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
git diff --check
```

`PressureFrontier.lean` に新規 `sorry` はありません。次は `SourcePressureSignChangeDown` と local-island 右端 fall を入れるか、`PressureDecay.lean` へ分割するかの分岐です。

## Review

## 状況分析

Checkpoint `138` は、前回の狙いどおり **source pressure の zero-crossing theorem** を閉じた checkpoint じゃ。

Lean 側では `PressureFrontier.lean` に `SourcePressureNetDropInt` が追加され、さらに

```text
next margin = current margin + net drop
```

を表す `sourcePressureMargin_next_eq_current_add_netDrop` と、主定理

```text
sign-change-up
  ↔ current margin <= 0 ∧ current margin + net drop > 0
```

を表す `sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses` が入った。加えて、local island の左端がこの zero-crossing 条件を満たすことも `sourcePressureCrosses_of_localIsland_left` として固定されている。

Python 側でも crossing sanity fields が追加され、`rows_with_crossing_identity_failure=0`、`rows_with_sign_change_up_iff_crossing_failure=0` が出ている。Lean の局所定理と Python の観測が綺麗に対応している。

ここまでで、PressureDecayProfile の局所構図はかなり完成してきた。

```text
integer balance:
  next margin = current margin + net drop

jump reading:
  margin jump ↔ net drop positive

zero-crossing reading:
  sign-change-up ↔ current nonpositive margin crosses above zero
```

## レビュー

## 良い点

第一に、`SourcePressureNetDropInt` を導入した判断が良い。

これまでは net drop が

```text
SourceRetentionDropInt n k r j - 2 * SourceContinuationDropInt n k r j
```

として毎回展開されていた。今回、これを `SourcePressureNetDropInt` として名前にしたことで、zero-crossing theorem の見通しが一気に良くなった。

これは単なる省略ではなく、数学的にも大事じゃ。
`SourcePressureNetDropInt` は、PressureDecayProfile における **局所駆動量**になった。

第二に、`SourcePressureNetDropPositive` の API 名を維持しつつ、内部定義を `SourcePressureNetDropInt` 経由にしたのが良い。

既存 theorem への影響を抑えつつ、今後の crossing / falling / pulse 系 theorem では `SourcePressureNetDropInt` を直接使える。これは安全な整理じゃ。

第三に、`sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses` は、これまでの流れの自然な到達点になっている。

以前は `sign-change-up` を、

```text
margin_j <= 0
margin_{j+1} > 0
```

という符号パターンとして見ていた。

今回からは、

```text
current margin <= 0
current margin + net drop > 0
```

と読める。
つまり、「符号が変わった」ではなく、「net drop によってゼロ境界を跨いだ」と言えるようになった。

第四に、local island の左端が zero-crossing 条件に接続されたのが大きい。

`sourcePressureCrosses_of_localIsland_left` によって、local island は単なる例外的符号パターンではなく、

```text
左端で zero-crossing up が起きる局所構造
```

として扱えるようになった。

## 注意点

次の注意点は、local island は左端だけではまだ完全には読めていない、という点じゃ。

今回閉じたのは、

```text
local island の左端:
  nonpositive -> positive
```

つまり上向き crossing じゃ。

しかし local island は本来、

```text
j - 1: nonpositive
j:     positive
j + 1: nonpositive
```

という局所山構造を持つ。

したがって、次に必要なのは右端。

```text
positive -> nonpositive
```

これを `SourcePressureSignChangeDown` として定義し、local island の右端が sign-change-down であることを出すと、local island が

```text
left crossing up + right falling down
```

として閉じる。

ここまで行けば、local island は「点」ではなく **pressure pulse** として扱える。

## 解説

いまの構図はこうじゃ。

まず、隣接 pressure-depth edge に対して、

```text
margin_next = margin_current + net_drop
```

がある。

そして sign-change-up は、

```text
margin_current <= 0
```

かつ、

```text
0 < margin_current + net_drop
```

である。

これは、current margin がゼロ以下にいたところへ、net drop が加わって、次の margin が正になったことを意味する。

つまり sign-change-up は、

```text
net drop が正である
```

だけでは足りない。

現在位置が深く負なら、少し正の net drop があってもゼロを超えない。
だから sign-change-up の本質は、

```text
net drop positive
```

ではなく、

```text
current margin + net drop が 0 を超える
```

ことじゃ。

この違いが重要じゃな。

だから `SourcePressureNetDropPositive` は margin jump の同値対象であり、`SourcePressureSignChangeUp` は zero-crossing の同値対象になる。今回その切り分けが Lean で定着した。

## 次の指示

Checkpoint `139` は、数学的には **right-edge fall theorem** を推す。

分割 `PressureDecay.lean` も候補ではあるが、今は theorem の流れが熱い。
local island を pulse として閉じるには、ここで `SourcePressureSignChangeDown` を入れるのが自然じゃ。

## Checkpoint 139 推奨内容

## 1. SourcePressureSignChangeDown を定義する

```lean
def SourcePressureSignChangeDown
    (n : OddNat) (k r j : ℕ) : Prop :=
  0 < SourcePressureMarginInt n k (r + j) ∧
    SourcePressureMarginInt n k (r + j + 1) ≤ 0
```

これは `SourcePressureSignChangeUp` の双対じゃ。

## 2. local island から右端 fall を出す

`SourcePressureLocalIsland` はすでに、

```text
0 < j
IsSourcePressureDepth n k r j
¬ IsSourcePressureDepth n k r (j - 1)
¬ IsSourcePressureDepth n k r (j + 1)
```

を持っているはずなので、margin equivalence を使えば右端が落ちる。

```lean
theorem sourcePressureSignChangeDown_of_localIsland
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j) :
    SourcePressureSignChangeDown n k r j := by
  rcases hisland with ⟨_hjpos, hsel, _hprev_not, hnext_not⟩
  unfold SourcePressureSignChangeDown
  constructor
  · exact (isSourcePressureDepth_iff_margin_pos n k r j).1 hsel
  · have hnotpos :
        ¬ 0 < SourcePressureMarginInt n k (r + (j + 1)) := by
      intro hpos
      exact hnext_not
        ((isSourcePressureDepth_iff_margin_pos n k r (j + 1)).2 hpos)
    omega
```

これは通る可能性が高い。

## 3. sign-change-down の zero-crossing-down theorem

次に、down 版の crossing theorem を置く。

```lean
theorem sourcePressureSignChangeDown_iff_margin_pos_and_netDrop_falls
    (n : OddNat) (k r j : ℕ) :
    SourcePressureSignChangeDown n k r j ↔
      0 < SourcePressureMarginInt n k (r + j) ∧
        SourcePressureMarginInt n k (r + j) +
          SourcePressureNetDropInt n k r j ≤ 0 := by
  unfold SourcePressureSignChangeDown
  rw [← sourcePressureMargin_next_eq_current_add_netDrop n k r j]
```

`rfl` 相当で閉じるか、必要なら `constructor` と `simp` で分ける。

## 4. local island の右端 fall crossing

```lean
theorem sourcePressureFalls_of_localIsland_right
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j) :
    0 < SourcePressureMarginInt n k (r + j) ∧
      SourcePressureMarginInt n k (r + j) +
        SourcePressureNetDropInt n k r j ≤ 0 :=
  (sourcePressureSignChangeDown_iff_margin_pos_and_netDrop_falls
    n k r j).1
    (sourcePressureSignChangeDown_of_localIsland n k r j hisland)
```

これが入ると、local island の左端と右端が両方 PressureDecay の crossing/falling として読める。

## 5. local island を pulse としてまとめる optional theorem

少しだけ余裕があれば、左右をまとめる theorem もあり。

```lean
theorem sourcePressureLocalIsland_gives_crossing_pulse
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j) :
    (SourcePressureMarginInt n k (r + (j - 1)) ≤ 0 ∧
      0 <
        SourcePressureMarginInt n k (r + (j - 1)) +
          SourcePressureNetDropInt n k r (j - 1)) ∧
    (0 < SourcePressureMarginInt n k (r + j) ∧
      SourcePressureMarginInt n k (r + j) +
        SourcePressureNetDropInt n k r j ≤ 0) := by
  constructor
  · exact sourcePressureCrosses_of_localIsland_left n k r j hisland
  · exact sourcePressureFalls_of_localIsland_right n k r j hisland
```

名前は長いので、まだ optional じゃ。

## 一歩先ゆく推論

今回の zero-crossing theorem により、local island の左端は

```text
margin <= 0
margin + netDrop > 0
```

として読めるようになった。

次に右端を入れると、

```text
margin > 0
margin + netDrop <= 0
```

になる。

つまり local island は、

```text
上へ跨ぐ edge
正の一点または正の短い block
下へ戻る edge
```

という pressure pulse になる。

これはかなり強い。

今まで local island は、prefix を壊す厄介な例外だった。
しかしこの読みでは、local island は例外ではなく、

```text
pressure-depth 方向の局所パルス
```

じゃ。

DkMath 的に言えば、

```text
retention obstruction が抜けて正へ跳ね、
次の depth で continuation support も落ちて戻る
```

という局所的な保存崩れ・再平衡として読める。

## さらなる次の一手

Checkpoint `139` で right-edge fall が閉じたら、Checkpoint `140` は二択。

## Route A: PressureDecay.lean へ分割

ここまでで `PressureFrontier.lean` は、frontier / island / prefix だけでなく、integer drop / net drop / crossing / falling も抱える。
`PressureDecay.lean` を切るには十分な量になっている。

移動候補：

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
```

ただし import order に注意。`SourcePressureLocalIsland` が `PressureFrontier` 側に残るなら、local-island wrappers は frontier 側に残すか、`PressureDecay` が `PressureFrontier` に依存するかを慎重に決める必要がある。

## Route B: positive block の pulse 列観測

local island が pulse として読めるなら、positive block も

```text
cross up
positive plateau
fall down
```

として読める可能性がある。

この場合、次の概念が見えてくる。

```text
SourcePressurePositiveRun
SourcePressurePulse
```

ただしこれは少し先でよい。
まずは `SignChangeDown` と local island right edge を閉じるのが先じゃ。

## 賢狼が試して欲しい実験補題

## 実験 A: sign-change-down definition

```lean
def SourcePressureSignChangeDown
    (n : OddNat) (k r j : ℕ) : Prop :=
  0 < SourcePressureMarginInt n k (r + j) ∧
    SourcePressureMarginInt n k (r + j + 1) ≤ 0
```

## 実験 B: local island gives sign-change-down

```lean
theorem sourcePressureSignChangeDown_of_localIsland
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j) :
    SourcePressureSignChangeDown n k r j := by
  rcases hisland with ⟨_hjpos, hsel, _hprev_not, hnext_not⟩
  unfold SourcePressureSignChangeDown
  constructor
  · exact (isSourcePressureDepth_iff_margin_pos n k r j).1 hsel
  · have hnotpos :
        ¬ 0 < SourcePressureMarginInt n k (r + (j + 1)) := by
      intro hpos
      exact hnext_not
        ((isSourcePressureDepth_iff_margin_pos n k r (j + 1)).2 hpos)
    omega
```

## 実験 C: sign-change-down zero-crossing theorem

```lean
theorem sourcePressureSignChangeDown_iff_margin_pos_and_netDrop_falls
    (n : OddNat) (k r j : ℕ) :
    SourcePressureSignChangeDown n k r j ↔
      0 < SourcePressureMarginInt n k (r + j) ∧
        SourcePressureMarginInt n k (r + j) +
          SourcePressureNetDropInt n k r j ≤ 0 := by
  unfold SourcePressureSignChangeDown
  rw [← sourcePressureMargin_next_eq_current_add_netDrop n k r j]
```

## 実験 D: local island right-edge fall

```lean
theorem sourcePressureFalls_of_localIsland_right
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j) :
    0 < SourcePressureMarginInt n k (r + j) ∧
      SourcePressureMarginInt n k (r + j) +
        SourcePressureNetDropInt n k r j ≤ 0 :=
  (sourcePressureSignChangeDown_iff_margin_pos_and_netDrop_falls
    n k r j).1
    (sourcePressureSignChangeDown_of_localIsland n k r j hisland)
```

## 実験 E: local island as pulse

```lean
theorem sourcePressureLocalIsland_gives_crossing_pulse
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j) :
    (SourcePressureMarginInt n k (r + (j - 1)) ≤ 0 ∧
      0 <
        SourcePressureMarginInt n k (r + (j - 1)) +
          SourcePressureNetDropInt n k r (j - 1)) ∧
    (0 < SourcePressureMarginInt n k (r + j) ∧
      SourcePressureMarginInt n k (r + j) +
        SourcePressureNetDropInt n k r j ≤ 0) := by
  constructor
  · exact sourcePressureCrosses_of_localIsland_left n k r j hisland
  · exact sourcePressureFalls_of_localIsland_right n k r j hisland
```

## Python 側の次観測

Python 側は optional でよい。
追加するなら right-edge fall sanity fields を入れる。

```text
rows_with_sign_change_down
rows_with_local_island_right_fall_failure
rows_with_sign_change_down_iff_falling_failure
```

期待値：

```text
rows_with_local_island_right_fall_failure: 0
rows_with_sign_change_down_iff_falling_failure: 0
```

ただし、今回の checkpoint では Lean theorem を優先してよい。
Python は必要なら追随で十分じゃ。

## 総括

Checkpoint `138` は成功じゃ。

これで、

```text
sign-change-up
  ↔ current margin <= 0
     and current margin + net drop > 0
```

が Lean に入った。

つまり、sign-change-up は完全に **zero-crossing by net drop** として読める。

次は右端。

```text
sign-change-down
  ↔ current margin > 0
     and current margin + net drop <= 0
```

を入れる。
これが通れば、local island は

```text
left crossing up
right falling down
```

を持つ pressure pulse として閉じる。

ここまで行くと、local island は「prefix を壊す例外」ではなく、構造的に説明可能な局所パルスになる。
次はそこじゃ。

## Codex instructions

```text
Checkpoint 139:
Add the right-edge fall side of the local pressure island.

Context:
  Checkpoint 138 added:
    SourcePressureNetDropInt
    sourcePressureMargin_next_eq_current_add_netDrop
    sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses
    sourcePressureCrosses_of_localIsland_left

  The current local story is:
    sign-change-up iff current margin <= 0 and current margin + net drop > 0.

Primary goal:
  Add the downward companion:
    sign-change-down iff current margin > 0 and current margin + net drop <= 0.
  Then connect local islands to the right-edge fall.

Preferred Lean location:
  DkMath.Collatz.PetalBridge.PressureFrontier

Implement:
  1. Define:
     SourcePressureSignChangeDown n k r j :=
       0 < SourcePressureMarginInt n k (r + j)
       ∧ SourcePressureMarginInt n k (r + j + 1) <= 0

  2. Prove:
     sourcePressureSignChangeDown_of_localIsland

     Use SourcePressureLocalIsland and isSourcePressureDepth_iff_margin_pos.
     The right neighbor non-selected condition should give nonpositive margin
     by contradiction plus omega.

  3. Prove:
     sourcePressureSignChangeDown_iff_margin_pos_and_netDrop_falls

     Expected statement:
       SourcePressureSignChangeDown n k r j ↔
         0 < SourcePressureMarginInt n k (r + j)
         ∧ SourcePressureMarginInt n k (r + j)
             + SourcePressureNetDropInt n k r j <= 0

     Suggested proof:
       unfold SourcePressureSignChangeDown
       rw [← sourcePressureMargin_next_eq_current_add_netDrop n k r j]
     If the goal does not close directly, split with constructor and simp/omega.

  4. Prove:
     sourcePressureFalls_of_localIsland_right

     Expected:
       A SourcePressureLocalIsland gives the falling condition at its right edge j.

  5. Optional theorem:
     sourcePressureLocalIsland_gives_crossing_pulse

     Expected:
       left edge:
         current margin <= 0 and current margin + net drop > 0
       right edge:
         current margin > 0 and current margin + net drop <= 0

Optional Python:
  Add summary fields:
    rows_with_sign_change_down
    rows_with_local_island_right_fall_failure
    rows_with_sign_change_down_iff_falling_failure

  Expected:
    rows_with_local_island_right_fall_failure: 0
    rows_with_sign_change_down_iff_falling_failure: 0

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
  After right-edge fall is closed, consider splitting the pressure-decay block into:
    DkMath.Collatz.PetalBridge.PressureDecay
  or defining a thin SourcePressurePulse vocabulary.
```

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
index 1fcb309e..86da8e3d 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
@@ -120,6 +120,19 @@ noncomputable def SourceContinuationDropInt
   (orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) -
     (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ)

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
 /--
 Adjacent source-pressure margin accounting identity.

@@ -132,10 +145,24 @@ theorem sourcePressureMarginStepDiff_eq
     (n : OddNat) (k r j : ℕ) :
     SourcePressureMarginInt n k (r + j + 1) -
         SourcePressureMarginInt n k (r + j) =
-      SourceRetentionDropInt n k r j -
-        2 * SourceContinuationDropInt n k r j := by
+      SourcePressureNetDropInt n k r j := by
   unfold SourcePressureMarginInt
-  unfold SourceRetentionDropInt SourceContinuationDropInt
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
   ring

 /--
@@ -386,9 +413,7 @@ retention loss minus twice continuation loss.
 -/
 def SourcePressureNetDropPositive
     (n : OddNat) (k r j : ℕ) : Prop :=
-  0 <
-    SourceRetentionDropInt n k r j -
-      2 * SourceContinuationDropInt n k r j
+  0 < SourcePressureNetDropInt n k r j

 /--
 The first selected source-pressure depth.
@@ -829,6 +854,38 @@ theorem sourcePressureNetDropPositive_of_localIsland_left
   sourcePressureNetDropPositive_of_marginJumpUp n k r (j - 1)
     (sourcePressureMarginJumpUp_of_localIsland_left n k r j hisland)

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
+A local pressure island gives the zero-crossing condition at its left edge.
+-/
+theorem sourcePressureCrosses_of_localIsland_left
+    (n : OddNat) (k r j : ℕ)
+    (hisland : SourcePressureLocalIsland n k r j) :
+    SourcePressureMarginInt n k (r + (j - 1)) ≤ 0 ∧
+      0 <
+        SourcePressureMarginInt n k (r + (j - 1)) +
+          SourcePressureNetDropInt n k r (j - 1) :=
+  (sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses
+      n k r (j - 1)).1
+    (sourcePressureSignChangeUp_of_localIsland n k r j hisland)
+
 /--
 Package a named margin jump and a strict retention drop.

diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-138.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-138.md
new file mode 100644
index 00000000..d039fbb7
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-138.md
@@ -0,0 +1,201 @@
+# Report Petal 138
+
+## Scope
+
+Checkpoint 138 closed the local zero-crossing theorem for
+`SourcePressureSignChangeUp`.
+
+The theorem remains strictly local to one adjacent pressure-depth edge.  It
+does not claim a global pressure prefix, does not introduce `Real.log`, and
+does not define a full pressure grid.
+
+## Lean Changes
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+```
+
+Added a named integer net-drop expression:
+
+```lean
+noncomputable def SourcePressureNetDropInt
+```
+
+`SourcePressureNetDropPositive` now reads through this expression:
+
+```lean
+def SourcePressureNetDropPositive
+    (n : OddNat) (k r j : Nat) : Prop :=
+  0 < SourcePressureNetDropInt n k r j
+```
+
+The old API name is preserved.  The definition is just cleaner for future
+zero-crossing and right-edge work.
+
+Added the additive margin theorem:
+
+```lean
+theorem sourcePressureMargin_next_eq_current_add_netDrop
+```
+
+Added the main zero-crossing theorem:
+
+```lean
+theorem sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses
+```
+
+This gives the local reading:
+
+```text
+sign-change-up
+  iff
+current margin <= 0
+and
+current margin + net drop > 0
+```
+
+Added local-island left-edge wrapper:
+
+```lean
+theorem sourcePressureCrosses_of_localIsland_left
+```
+
+## Python Changes
+
+Updated:
+
+```text
+python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
+```
+
+Added scan fields:
+
+```text
+current_margin
+net_drop
+current_margin_plus_net_drop
+next_margin
+crossing_matches_sign_change_up
+crossing_identity_failure_count
+sign_change_up_iff_crossing_failure_count
+```
+
+Added summary fields:
+
+```text
+rows_with_crossing_identity_failure
+rows_with_sign_change_up_iff_crossing_failure
+```
+
+These mirror the Lean zero-crossing theorem at scan level.
+
+## Experiment
+
+Command:
+
+```bash
+python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py \
+  --max-n 16383 --steps 64 --r-start 2 --depth-len 12 \
+  --name-suffix _138_16383_k64_d12
+```
+
+Generated:
+
+```text
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_138_16383_k64_d12.csv
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_138_16383_k64_d12.md
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
+sign-change cause counts: retention_drop_dominant:404
+```
+
+The finite scan agrees with the new Lean zero-crossing theorem:
+
+```text
+current_margin + net_drop = next_margin
+sign-change-up iff current_margin <= 0 and current_margin + net_drop > 0
+```
+
+## Inference
+
+The local pressure story is now a three-step chain:
+
+```text
+integer balance:
+  next margin = current margin + net drop
+
+jump reading:
+  margin jump iff net drop is positive
+
+zero-crossing reading:
+  sign-change-up iff current nonpositive margin crosses above zero
+```
+
+This is a cleaner interface than using the Python classification label
+`retention_drop_dominant` directly.  The Lean-facing term is
+`SourcePressureNetDropInt`, and the Lean-facing predicate is
+`SourcePressureNetDropPositive`.
+
+## Suggested Next Checkpoint
+
+Two natural next moves remain:
+
+1. Add `SourcePressureSignChangeDown` and the local-island right-edge fall.
+   This would complete the local island as left crossing up plus right crossing
+   down.
+
+2. Split the pressure-decay material into:
+
+```text
+DkMath.Collatz.PetalBridge.PressureDecay
+```
+
+The file is now carrying pressure margin, integer-drop accounting, zero
+crossing, frontier, island, and prefix helpers.  The split is not urgent, but
+the pressure-decay block has become cohesive enough to extract cleanly.
+
+If continuing theorem work first, the right-edge fall is the more mathematical
+next step.  If preparing for longer maintenance, the split is the cleaner
+engineering step.
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
