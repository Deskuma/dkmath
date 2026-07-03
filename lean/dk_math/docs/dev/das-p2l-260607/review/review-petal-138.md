# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.*

gch: fdfcc4b14085986b5ad0a8a84c697c5319187f70

## Report

checkpoint 137 を実装しました。

[PressureFrontier.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean) で局所同値を閉じました。

```lean
sourcePressureNetDropPositive_of_marginJumpUp
sourcePressureMarginJumpUp_iff_netDropPositive
sourcePressureNetDropPositive_of_signChangeUp
sourcePressureNetDropPositive_of_localIsland_left
sourcePressureJumpWithDecay_of_netDropPositive_of_decay
```

これで Lean 側の安定 API は次の形です。

```text
SourcePressureMarginJumpUp n k r j
  ↔ SourcePressureNetDropPositive n k r j
```

Python scan 側も [pressure_sign_pattern_scan.py](/python/Collatz/PetalBridge/pressure_sign_pattern_scan.py) に summary fields を追加しました。生成物:

- [pressure_sign_pattern_scan_137_16383_k64_d12.csv](/python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_137_16383_k64_d12.csv)
- [pressure_sign_pattern_scan_137_16383_k64_d12.md](/python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_137_16383_k64_d12.md)
- [report-petal-137.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-137.md)

観測では `rows_with_net_drop_positive=8089`, `rows_with_margin_jump=8089`, `rows_with_margin_jump_iff_net_drop_failure=0` でした。

検証済み:

```text
python3 -m py_compile python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
git diff --check
```

`PressureFrontier.lean` に新規 `sorry` はありません。次は zero-crossing theorem、つまり「現在 margin が非正で、現在 margin + net drop が正になる iff sign-change-up」を狙うのが自然です。

## Review

## 状況分析

Checkpoint `137` は、前回の狙いどおり **margin jump と net drop positive の局所同値**を閉じた checkpoint じゃ。

Lean 側では `PressureFrontier.lean` に以下が追加されている。

```text
sourcePressureNetDropPositive_of_marginJumpUp
sourcePressureMarginJumpUp_iff_netDropPositive
sourcePressureNetDropPositive_of_signChangeUp
sourcePressureNetDropPositive_of_localIsland_left
sourcePressureJumpWithDecay_of_netDropPositive_of_decay
```

これで安定 API は、

```text
SourcePressureMarginJumpUp n k r j
  ↔
SourcePressureNetDropPositive n k r j
```

になった。これは非常に大きい。`SourcePressureNetDropPositive` は checkpoint `136` で固定した整数会計量、つまり `0 < retention_drop - 2 * continuation_drop` なので、margin jump が完全に整数 drop balance と同値になったわけじゃ。

Python 側でも `rows_with_net_drop_positive=8089`、`rows_with_margin_jump=8089`、`rows_with_margin_jump_iff_net_drop_failure=0` が出ており、scan 側でも Lean theorem と対応する確認が取れている。

ここまでで、PressureDecayProfile は次の段階まで進んだ。

```text
Checkpoint 134:
  margin jump / retention drop / continuation weak drop の語彙

Checkpoint 135:
  jump with decay の packaging

Checkpoint 136:
  integer drop amount と margin step identity

Checkpoint 137:
  margin jump ↔ net drop positive
```

次は、報告にもある通り **zero-crossing theorem** が自然じゃ。

## レビュー

## 良い点

第一に、今回の同値化はかなり重要じゃ。

これまでは、

```text
net drop positive
  -> margin jump
```

だけだった。
今回、

```text
margin jump
  -> net drop positive
```

も閉じたことで、`SourcePressureMarginJumpUp` と `SourcePressureNetDropPositive` が局所的に同じものとして扱えるようになった。

つまり、以後は margin の符号変化を扱うときに、

```text
margin が上がった
```

と言ってもよいし、

```text
retention_drop - 2 * continuation_drop が正
```

と言ってもよい。
この二つが Lean 上で行き来できる。

第二に、`sourcePressureNetDropPositive_of_signChangeUp` が良い。

`sign-change-up` は、

```text
current margin <= 0
next margin > 0
```

なので、当然 margin jump を含む。
今回それが `net drop positive` へ接続された。

これで sign-change-up は、

```text
符号が上へ跨いだ
```

だけでなく、

```text
その辺では正味 drop が正である
```

とも読める。

第三に、`sourcePressureNetDropPositive_of_localIsland_left` が良い。

local island は pressure profile の孤立正領域じゃが、その左端が net drop positive edge として読めるようになった。これは、以前の観測

```text
local island は retention obstruction の急落で生じる
```

を Lean 側の局所構造へかなり近づけている。

第四に、`RetentionDropDominant` をまだ入れていないのが良い。

ここで `Dominant` という名前を使うこともできた。
しかし、今の安定名は `SourcePressureNetDropPositive`。これは数式そのものを表すので、後続の定理で安全に使える。

`Dominant` は説明語としては良いが、Lean API としてはまだ強すぎる。今はこのままでよい。

## 注意点

次に注意すべきは、**margin jump と sign-change-up は違う**という点じゃ。

今回閉じたのは、

```text
margin jump
  ↔
net drop positive
```

であって、

```text
sign-change-up
  ↔
net drop positive
```

ではない。

なぜなら、margin jump は単に

```text
margin_next > margin_current
```

だが、sign-change-up は

```text
margin_current <= 0
margin_next > 0
```

を要求するからじゃ。

したがって次の checkpoint では、

```text
net drop positive
```

だけでなく、

```text
current margin + net drop > 0
```

を使う必要がある。

これが zero-crossing theorem の本質じゃ。

## 解説

いまの構造はこう整理できる。

```text
margin_next - margin_current
  =
retention_drop - 2 * continuation_drop
```

そして今回、

```text
margin_next > margin_current
```

と

```text
0 < retention_drop - 2 * continuation_drop
```

が同値になった。

しかし、sign-change-up とは単なる増加ではない。

```text
margin_current <= 0
margin_next > 0
```

つまり、

```text
margin_current <= 0
```

かつ、

```text
0 < margin_current + (retention_drop - 2 * continuation_drop)
```

である。

ここで `margin_current + netDrop` は `margin_next` に等しい。
だから次に欲しいのは、この恒等式じゃ。

```text
margin_next =
  margin_current + retention_drop - 2 * continuation_drop
```

すでに `sourcePressureMarginStepDiff_eq` があるので、これは薄い補題として出せるはずじゃ。

そしてそれを使って、

```text
signChangeUp
  ↔
current margin <= 0
  ∧
0 < current margin + netDrop
```

を閉じる。

これで sign-change-up は完全に PressureDecayProfile の言葉で読めるようになる。

## 次の指示

Checkpoint `138` は **zero-crossing theorem** を狙うのがよい。

追加先は引き続き `PressureFrontier.lean` でよい。
ただし、ここまで来ると `PressureDecay` の語彙がかなり増えてきたので、Checkpoint `139` 以降では `PressureDecay.lean` 分割を考えてよい。

## Checkpoint 138 推奨内容

## 1. net drop expression の補助定義を入れるか検討

現状では `SourcePressureNetDropPositive` が直接、

```text
0 < SourceRetentionDropInt n k r j - 2 * SourceContinuationDropInt n k r j
```

を持っている。

zero-crossing theorem ではこの式を何度も使うので、補助定義があると読みやすい。

```lean
noncomputable def SourcePressureNetDropInt
    (n : OddNat) (k r j : ℕ) : ℤ :=
  SourceRetentionDropInt n k r j -
    2 * SourceContinuationDropInt n k r j
```

そのうえで、既存 `SourcePressureNetDropPositive` は将来的にこの形へ書き換えてもよい。

```lean
def SourcePressureNetDropPositive
    (n : OddNat) (k r j : ℕ) : Prop :=
  0 < SourcePressureNetDropInt n k r j
```

ただし既存 API を壊すのが嫌なら、今回は `SourcePressureNetDropInt` を追加するだけで、`SourcePressureNetDropPositive` の定義変更はしなくてもよい。

## 2. margin next equals current plus net drop

本命前の補助 theorem。

```lean
theorem sourcePressureMargin_next_eq_current_add_netDrop
    (n : OddNat) (k r j : ℕ) :
    SourcePressureMarginInt n k (r + j + 1) =
      SourcePressureMarginInt n k (r + j) +
        (SourceRetentionDropInt n k r j -
          2 * SourceContinuationDropInt n k r j) := by
  have h := sourcePressureMarginStepDiff_eq n k r j
  omega
```

`omega` で詰まるなら、`linarith` ではなく `ring` 系より `omega` の方が期待値は高いが、`Int` の等式なので必要なら次のように進める。

```lean
  rw [← h]
  ring
```

ただし実際の証明は Lean に合わせて調整でよい。

## 3. sign-change-up iff crossing by net drop

これが Checkpoint `138` の主定理。

```lean
theorem sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses
    (n : OddNat) (k r j : ℕ) :
    SourcePressureSignChangeUp n k r j ↔
      SourcePressureMarginInt n k (r + j) ≤ 0 ∧
        0 <
          SourcePressureMarginInt n k (r + j) +
            (SourceRetentionDropInt n k r j -
              2 * SourceContinuationDropInt n k r j) := by
  unfold SourcePressureSignChangeUp
  rw [← sourcePressureMargin_next_eq_current_add_netDrop n k r j]
  rfl
```

`rfl` で閉じない場合は、`constructor` で分ければよい。

## 4. sign-change-up iff current nonpositive and current plus netDrop positive, named version

もし `SourcePressureNetDropInt` を入れた場合は読みやすくなる。

```lean
theorem sourcePressureSignChangeUp_iff_margin_nonpos_and_netDropInt_crosses
    (n : OddNat) (k r j : ℕ) :
    SourcePressureSignChangeUp n k r j ↔
      SourcePressureMarginInt n k (r + j) ≤ 0 ∧
        0 <
          SourcePressureMarginInt n k (r + j) +
            SourcePressureNetDropInt n k r j := by
  unfold SourcePressureNetDropInt
  exact sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses n k r j
```

これは綺麗じゃ。

## 5. local island left edge crossing

local island から、左端で crossing が起きることも出せる。

```lean
theorem sourcePressureCrosses_of_localIsland_left
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j) :
    SourcePressureMarginInt n k (r + (j - 1)) ≤ 0 ∧
      0 <
        SourcePressureMarginInt n k (r + (j - 1)) +
          (SourceRetentionDropInt n k r (j - 1) -
            2 * SourceContinuationDropInt n k r (j - 1)) := by
  exact
    (sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses
      n k r (j - 1)).1
      (sourcePressureSignChangeUp_of_localIsland n k r j hisland)
```

これは local island を PressureDecayProfile にかなり強く接続する補題じゃ。

## 一歩先ゆく推論

Checkpoint `138` で zero-crossing が閉じると、local island は次の形で読める。

```text
left edge:
  current margin <= 0
  current margin + netDrop > 0

island center:
  margin > 0

right edge:
  next margin <= 0
```

つまり local island は、

```text
netDrop positive で上へ跨ぎ、
その後の edge で再び非正へ戻る局所山
```

として読める。

ここまで来ると、`SourcePressureLocalIsland` は符号パターンではなく、

```text
PressureDecay pulse
```

として扱えるようになる。

これは重要じゃ。
`local island` が「例外」ではなく、**pressure-depth direction における局所パルス**として意味を持ち始める。

この見方なら、次の観測は、

```text
local island の左端 netDrop
local island の右端 netDrop
```

の比較になる。

左端は positive。
右端はおそらく nonpositive または negative step になるはずじゃ。

## さらなる次の一手

Checkpoint `138` が通ったら、Checkpoint `139` は二択。

## Route A: right-edge fall theorem

local island の右端を decay profile で読む。

```text
local island:
  j is positive
  j-1 is nonpositive
  j+1 is nonpositive
```

左端は sign-change-up。
右端は sign-change-down 的なものじゃ。

新しい述語候補：

```lean
def SourcePressureSignChangeDown
    (n : OddNat) (k r j : ℕ) : Prop :=
  0 < SourcePressureMarginInt n k (r + j) ∧
    SourcePressureMarginInt n k (r + j + 1) ≤ 0
```

そして、

```text
local island -> signChangeDown at j
```

を出す。

さらに将来的には、

```text
signChangeDown iff current positive and current + netDrop <= 0
```

も出せる。

## Route B: split `PressureDecay.lean`

ここまで来ると、`PressureFrontier.lean` に frontier, island, decay, netDrop, crossing が混在し始める。
Checkpoint `139` か `140` では分割を検討してよい。

候補：

```text
DkMath/Collatz/PetalBridge/PressureDecay.lean
```

移動候補：

```text
SourceRetentionDropInt
SourceContinuationDropInt
SourcePressureNetDropPositive
SourcePressureNetDropInt
sourcePressureMarginStepDiff_eq
sourcePressureMarginJumpUp_iff_netDropPositive
zero-crossing theorem 群
```

ただし、Checkpoint `138` ではまだ refactor せず、zero-crossing を閉じるのを優先するのがよい。

## 賢狼が試して欲しい実験補題

## 実験 A: optional net drop int

```lean
noncomputable def SourcePressureNetDropInt
    (n : OddNat) (k r j : ℕ) : ℤ :=
  SourceRetentionDropInt n k r j -
    2 * SourceContinuationDropInt n k r j
```

## 実験 B: margin next equals current plus net drop

```lean
theorem sourcePressureMargin_next_eq_current_add_netDrop
    (n : OddNat) (k r j : ℕ) :
    SourcePressureMarginInt n k (r + j + 1) =
      SourcePressureMarginInt n k (r + j) +
        (SourceRetentionDropInt n k r j -
          2 * SourceContinuationDropInt n k r j) := by
  have h := sourcePressureMarginStepDiff_eq n k r j
  rw [← h]
  ring
```

## 実験 C: zero-crossing theorem

```lean
theorem sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses
    (n : OddNat) (k r j : ℕ) :
    SourcePressureSignChangeUp n k r j ↔
      SourcePressureMarginInt n k (r + j) ≤ 0 ∧
        0 <
          SourcePressureMarginInt n k (r + j) +
            (SourceRetentionDropInt n k r j -
              2 * SourceContinuationDropInt n k r j) := by
  unfold SourcePressureSignChangeUp
  rw [← sourcePressureMargin_next_eq_current_add_netDrop n k r j]
  rfl
```

## 実験 D: local island left crossing

```lean
theorem sourcePressureCrosses_of_localIsland_left
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j) :
    SourcePressureMarginInt n k (r + (j - 1)) ≤ 0 ∧
      0 <
        SourcePressureMarginInt n k (r + (j - 1)) +
          (SourceRetentionDropInt n k r (j - 1) -
            2 * SourceContinuationDropInt n k r (j - 1)) := by
  exact
    (sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses
      n k r (j - 1)).1
      (sourcePressureSignChangeUp_of_localIsland n k r j hisland)
```

## 実験 E: sign-change-down skeleton は次回候補

今回は入れなくてよいが、次に欲しくなる。

```lean
def SourcePressureSignChangeDown
    (n : OddNat) (k r j : ℕ) : Prop :=
  0 < SourcePressureMarginInt n k (r + j) ∧
    SourcePressureMarginInt n k (r + j + 1) ≤ 0
```

## Python 側の次観測

Python 側は今回、Lean 同値に対応する summary が十分に出ている。
次に追加するなら、zero-crossing 用の sanity fields。

```text
current_margin
net_drop
current_margin_plus_net_drop
next_margin
crossing_matches_sign_change_up
```

summary:

```text
rows_with_crossing_identity_failure: 0
rows_with_sign_change_up_iff_crossing_failure: 0
```

ただし、今回は Lean 側で zero-crossing theorem を閉じる方が主。Python 拡張は optional でよい。

## 総括

Checkpoint `137` は成功じゃ。

これで PressureDecayProfile の局所会計は、

```text
margin jump
  ↔ positive step difference
  ↔ positive net pressure drop
```

まで閉じた。

次は、

```text
sign-change-up
  ↔ current margin <= 0
     and current margin + netDrop > 0
```

を閉じる。
これは「margin が上がる」から一歩進んで、「ゼロ境界を跨ぐ」ことの定式化じゃ。

ここが通れば、local island の左端は完全に **PressureDecay zero-crossing** として読める。
いよいよ「島」が、ただの例外ではなく、局所的な圧力パルスとして扱えるようになる。

## Codex instructions

```text
Checkpoint 138:
Prove the local zero-crossing theorem for source pressure sign-change-up.

Context:
  Checkpoint 137 closed the local equivalence:
    SourcePressureMarginJumpUp n k r j
      ↔ SourcePressureNetDropPositive n k r j

  Existing relevant API:
    SourceRetentionDropInt
    SourceContinuationDropInt
    sourcePressureMarginStepDiff_eq
    SourcePressureNetDropPositive
    sourcePressureMarginJumpUp_iff_netDropPositive
    sourcePressureNetDropPositive_of_signChangeUp
    sourcePressureNetDropPositive_of_localIsland_left

Primary goal:
  Express SourcePressureSignChangeUp as a local zero-crossing condition:
    current margin is nonpositive,
    and current margin plus net drop is positive.

Preferred Lean location:
  DkMath.Collatz.PetalBridge.PressureFrontier

Implement:
  1. Optional helper definition:
     SourcePressureNetDropInt n k r j :=
       SourceRetentionDropInt n k r j
         - 2 * SourceContinuationDropInt n k r j

     Do not rewrite existing SourcePressureNetDropPositive unless it is painless.
     Keep API compatibility.

  2. Prove:
     sourcePressureMargin_next_eq_current_add_netDrop

     Expected statement:
       SourcePressureMarginInt n k (r + j + 1)
         =
       SourcePressureMarginInt n k (r + j)
         + (SourceRetentionDropInt n k r j
             - 2 * SourceContinuationDropInt n k r j)

     Suggested proof:
       have h := sourcePressureMarginStepDiff_eq n k r j
       rw [← h]
       ring

  3. Prove the main theorem:
     sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses

     Expected statement:
       SourcePressureSignChangeUp n k r j ↔
         SourcePressureMarginInt n k (r + j) ≤ 0 ∧
           0 <
             SourcePressureMarginInt n k (r + j)
               + (SourceRetentionDropInt n k r j
                   - 2 * SourceContinuationDropInt n k r j)

     Suggested proof:
       unfold SourcePressureSignChangeUp
       rw [← sourcePressureMargin_next_eq_current_add_netDrop n k r j]
       rfl
     If `rfl` does not close, split with constructor and simp.

  4. Prove:
     sourcePressureCrosses_of_localIsland_left

     Expected:
       A SourcePressureLocalIsland gives the zero-crossing condition at j - 1.

Optional Python:
  Add sanity fields:
    current_margin
    net_drop
    current_margin_plus_net_drop
    next_margin
    crossing_matches_sign_change_up

  Add summary:
    rows_with_crossing_identity_failure: 0
    rows_with_sign_change_up_iff_crossing_failure: 0

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
  After zero-crossing is closed, consider either:
    - SourcePressureSignChangeDown and right-edge local-island fall, or
    - splitting pressure-decay material into PetalBridge/PressureDecay.lean.
```

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
index 79280af8..1fcb309e 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
@@ -778,6 +778,57 @@ theorem sourcePressureMarginJumpUp_of_netDropPositive
   rw [sourcePressureMarginStepDiff_eq]
   exact h
 
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
+An upward pressure sign change has positive net integer pressure drop.
+-/
+theorem sourcePressureNetDropPositive_of_signChangeUp
+    (n : OddNat) (k r j : ℕ)
+    (h : SourcePressureSignChangeUp n k r j) :
+    SourcePressureNetDropPositive n k r j :=
+  sourcePressureNetDropPositive_of_marginJumpUp n k r j
+    (sourcePressureMarginJumpUp_of_signChangeUp n k r j h)
+
+/--
+A local pressure island has positive net integer pressure drop at its left
+edge.
+-/
+theorem sourcePressureNetDropPositive_of_localIsland_left
+    (n : OddNat) (k r j : ℕ)
+    (hisland : SourcePressureLocalIsland n k r j) :
+    SourcePressureNetDropPositive n k r (j - 1) :=
+  sourcePressureNetDropPositive_of_marginJumpUp n k r (j - 1)
+    (sourcePressureMarginJumpUp_of_localIsland_left n k r j hisland)
+
 /--
 Package a named margin jump and a strict retention drop.
 
@@ -845,6 +896,19 @@ theorem sourcePressureJumpWithDecay_of_signChangeUp_of_decay
   sourcePressureJumpWithDecay_of_parts n k r j
     (sourcePressureMarginJumpUp_of_signChangeUp n k r j hchange) hret hcont
 
+/--
+Positive net pressure drop plus the two order-theoretic decay observations
+packages as `SourcePressureJumpWithDecay`.
+-/
+theorem sourcePressureJumpWithDecay_of_netDropPositive_of_decay
+    (n : OddNat) (k r j : ℕ)
+    (hnet : SourcePressureNetDropPositive n k r j)
+    (hret : SourceRetentionDropsAcross n k r j)
+    (hcont : SourceContinuationWeaklyDropsAcross n k r j) :
+    SourcePressureJumpWithDecay n k r j :=
+  sourcePressureJumpWithDecay_of_parts n k r j
+    (sourcePressureMarginJumpUp_of_netDropPositive n k r j hnet) hret hcont
+
 /-- The empty selected-pressure prefix is always available. -/
 theorem selectedPressurePrefix_zero
     (n : OddNat) (k r len : ℕ) :
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-137.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-137.md
new file mode 100644
index 00000000..7a2dfb19
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-137.md
@@ -0,0 +1,196 @@
+# Report Petal 137
+
+## Scope
+
+Checkpoint 137 closed the local equivalence between an adjacent source-pressure
+margin jump and positive net integer pressure drop.
+
+This remains a local adjacent-depth theorem.  It does not introduce a pressure
+prefix theorem, a full grid, `Real.log`, or a named `RetentionDropDominant`
+predicate.
+
+## Lean Changes
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+```
+
+Added the reverse implication:
+
+```lean
+theorem sourcePressureNetDropPositive_of_marginJumpUp
+```
+
+Closed the local equivalence:
+
+```lean
+theorem sourcePressureMarginJumpUp_iff_netDropPositive
+```
+
+Added sign-change and local-island bridges:
+
+```lean
+theorem sourcePressureNetDropPositive_of_signChangeUp
+theorem sourcePressureNetDropPositive_of_localIsland_left
+```
+
+Added a packaging theorem from positive net drop plus the two decay predicates:
+
+```lean
+theorem sourcePressureJumpWithDecay_of_netDropPositive_of_decay
+```
+
+The stable local API is now:
+
+```text
+SourcePressureMarginJumpUp n k r j
+  iff
+SourcePressureNetDropPositive n k r j
+```
+
+where `SourcePressureNetDropPositive` is the exact integer balance quantity
+from checkpoint 136:
+
+```text
+0 < retention_drop - 2 * continuation_drop
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
+Added row-level counts:
+
+```text
+net_drop_positive_count
+margin_jump_count
+margin_jump_iff_net_drop_failure_count
+```
+
+Added summary fields:
+
+```text
+rows_with_net_drop_positive
+rows_with_margin_jump
+rows_with_margin_jump_iff_net_drop_failure
+```
+
+This mirrors the Lean equivalence at scan level.
+
+## Experiment
+
+Command:
+
+```bash
+python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py \
+  --max-n 16383 --steps 64 --r-start 2 --depth-len 12 \
+  --name-suffix _137_16383_k64_d12
+```
+
+Generated:
+
+```text
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_137_16383_k64_d12.csv
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_137_16383_k64_d12.md
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
+sign-change cause counts: retention_drop_dominant:404
+```
+
+The scan-level equality of row counts agrees with the Lean theorem:
+
+```text
+rows_with_net_drop_positive = rows_with_margin_jump
+rows_with_margin_jump_iff_net_drop_failure = 0
+```
+
+## Inference
+
+The pressure-decay layer now has an exact local algebraic surface:
+
+```text
+margin jump
+  <-> positive step difference
+  <-> positive net pressure drop
+```
+
+This means later proofs should not reason directly from the Python
+`retention_drop_dominant` label.  The Lean-facing object is now
+`SourcePressureNetDropPositive`.
+
+The next natural theorem is the zero-crossing statement mentioned by the
+review file:
+
+```text
+signChangeUp iff current margin is nonpositive
+  and current margin + net drop is positive
+```
+
+This would connect the local algebraic balance sheet to the sign-profile
+frontier/island vocabulary without asserting any global prefix shape.
+
+## Suggested Next Checkpoint
+
+Consider proving a theorem of the form:
+
+```lean
+sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses
+```
+
+The expected shape is:
+
+```text
+SourcePressureSignChangeUp n k r j
+  iff
+SourcePressureMarginInt n k (r + j) <= 0
+  and
+0 < SourcePressureMarginInt n k (r + j)
+      + (SourceRetentionDropInt n k r j
+          - 2 * SourceContinuationDropInt n k r j)
+```
+
+This should be treated as another local adjacent-edge theorem.
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
