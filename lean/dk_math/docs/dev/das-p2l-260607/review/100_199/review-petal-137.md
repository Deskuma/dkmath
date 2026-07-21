# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.*

gch: 798b1b0eb21ab68ae00ccae83a9a488e75469ee1

## Report

checkpoint 136 を実装しました。

[PressureFrontier.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean) に整数 drop 層を追加し、核心の隣接 margin 恒等式を Lean で固定しました。

```lean
SourceRetentionDropInt
SourceContinuationDropInt
sourcePressureMarginStepDiff_eq
sourcePressureMarginJumpUp_iff_stepDiff_pos
SourcePressureNetDropPositive
sourcePressureMarginJumpUp_of_netDropPositive
```

Python 側も [pressure_sign_pattern_scan.py](/python/Collatz/PetalBridge/pressure_sign_pattern_scan.py) に sanity fields を追加し、`rows_with_margin_step_identity_failure: 0` を出すようにしました。

生成物:

- [pressure_sign_pattern_scan_136_16383_k64_d12.csv](/python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_136_16383_k64_d12.csv)
- [pressure_sign_pattern_scan_136_16383_k64_d12.md](/python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_136_16383_k64_d12.md)
- [report-petal-136.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-136.md)

観測値は `rows=8192`, `sign-change-up=404`, `local-islands=252`, `largest margin jump=12`, `largest retention drop minus 2 continuation drop=10`, `rows_with_margin_step_identity_failure=0` です。

検証済み:

```text
python3 -m py_compile python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
git diff --check
```

`PressureFrontier.lean` に新規 `sorry` はありません。次は `SourcePressureMarginJumpUp ↔ SourcePressureNetDropPositive` を閉じるのが自然です。

## Review

## 状況分析

Checkpoint `136` は、かなり大きな節目じゃ。
前回まで Python 側で観測していた

```text
retention_drop_minus_2_continuation_drop
```

が、Lean 側で `SourceRetentionDropInt` / `SourceContinuationDropInt` として定義され、核心の隣接 margin 恒等式

```text
margin_next - margin_current =
  retention_drop - 2 * continuation_drop
```

として固定された。これは単なる wrapper ではなく、PressureDecayProfile の **整数会計層**が入ったということじゃ。

Python 側でも `margin_step_diff`, `retention_drop_minus_2_continuation_drop`, `margin_step_matches_net_drop`, `rows_with_margin_step_identity_failure` が追加され、`rows_with_margin_step_identity_failure: 0` が出ている。Lean の恒等式と Python の sanity check が一致した形じゃな。

別添の scan 結果でも、`rows=8192`, `sign-change-up=404`, `local-islands=252`, `rows_with_margin_step_identity_failure=0` が確認できる。positive block は最大長 `11`、sign-change cause は `retention_drop_dominant:404` で全件 retention-drop 側に分類されている。

ここまでで、以前の仮説はかなり形式化に近づいた。

```text
local island / sign-change-up は、
continuation が増えた現象ではなく、
retention obstruction が continuation decay の 2 倍を超えて落ちたことで、
margin が正方向へ跳ねた現象である。
```

## レビュー

## 良い点

第一に、`SourceRetentionDropInt` と `SourceContinuationDropInt` の符号規約が明確で良い。

```text
drop = current - next
```

これにより、

```text
retention_drop - 2 * continuation_drop
```

がそのまま `margin_next - margin_current` になる。ここで符号を間違えると後続の theorem が全部ねじれるので、docstring で規約を固定したのは正しい。

第二に、`sourcePressureMarginStepDiff_eq` が本当に核心じゃ。

```lean
theorem sourcePressureMarginStepDiff_eq
```

これは PressureDecayProfile の保存式に相当する。
以前は、

```text
margin jump
retention drop
continuation weak drop
```

が同じ edge に並んでいるだけだった。
しかし今回からは、

```text
margin jump amount =
  retention drop - 2 * continuation drop
```

として、三者が同一の整数会計に入った。

第三に、`SourcePressureNetDropPositive` という名前が良い。

まだ `RetentionDropDominant` と呼ばず、

```text
0 < retention_drop - 2 * continuation_drop
```

をそのまま表す名前にしている。
これは Lean 名として安全じゃ。`Dominant` は解釈名であり、`NetDropPositive` は数式名。いまの段階では数式名の方が強い。

第四に、Python 側の scan が Lean theorem の sanity check になっている。
`rows_with_margin_step_identity_failure: 0` は、Lean では当然の恒等式だが、Python 実装が同じ量を正しく読んでいるかの確認として有用じゃ。

## 注意点

ここでの注意点は、次に作る theorem の向きじゃ。

すでに実装済みなのは、

```text
SourcePressureNetDropPositive
  -> SourcePressureMarginJumpUp
```

じゃ。

次に閉じるべきは逆向き。

```text
SourcePressureMarginJumpUp
  -> SourcePressureNetDropPositive
```

これが閉じると、

```text
SourcePressureMarginJumpUp
  ↔ SourcePressureNetDropPositive
```

になる。

この equivalence が入ると、margin jump と net drop positive は完全に同義になる。
すると `signChangeUp` や `localIsland` も、margin jump 経由で net drop positive へ接続できる。

ただし、まだ global pressure prefix へ進むべきではない。
今回の恒等式は **adjacent pressure-depth edge** の局所会計であり、深さ全体の形状定理ではない。

## 解説

今の構造はこう整理できる。

```text
SourcePressureMarginInt(j)
  = 2 * continuation(j) - retention(j)
```

そして drop を

```text
retention_drop(j)
  = retention(j) - retention(j+1)

continuation_drop(j)
  = continuation(j) - continuation(j+1)
```

と読む。

このとき、

```text
margin(j+1) - margin(j)
  = retention_drop(j) - 2 * continuation_drop(j)
```

つまり、margin が上がる条件は、

```text
0 < retention_drop - 2 * continuation_drop
```

である。

これは local island の意味をかなり明確にする。

```text
retention_drop が大きい:
  retention obstruction が抜ける

continuation_drop が大きい:
  continuation support も失われる

retention_drop - 2 * continuation_drop が正:
  obstruction の抜け方が continuation loss を上回り、margin が上がる
```

だから、Python の `retention_drop_dominant` は単なる経験的ラベルではなく、Lean では `SourcePressureNetDropPositive` として読める段階に入った。
まだ名前は `Dominant` にしなくてよいが、数学的にはもうかなり近い。

## 次の指示

Checkpoint `137` は、報告にもある通り、まず

```text
SourcePressureMarginJumpUp
  ↔ SourcePressureNetDropPositive
```

を閉じるのが自然じゃ。

そのあと、`signChangeUp` / `localIsland` から `NetDropPositive` へ渡す bridge theorem を追加するとよい。

## Checkpoint 137 推奨内容

## 1. margin jump から net drop positive

```lean
theorem sourcePressureNetDropPositive_of_marginJumpUp
    (n : OddNat) (k r j : ℕ)
    (h : SourcePressureMarginJumpUp n k r j) :
    SourcePressureNetDropPositive n k r j := by
  unfold SourcePressureNetDropPositive
  rw [← sourcePressureMarginStepDiff_eq n k r j]
  exact (sourcePressureMarginJumpUp_iff_stepDiff_pos n k r j).1 h
```

これは今回の identity を逆向きに使うだけじゃ。

## 2. margin jump iff net drop positive

```lean
theorem sourcePressureMarginJumpUp_iff_netDropPositive
    (n : OddNat) (k r j : ℕ) :
    SourcePressureMarginJumpUp n k r j ↔
      SourcePressureNetDropPositive n k r j := by
  constructor
  · exact sourcePressureNetDropPositive_of_marginJumpUp n k r j
  · exact sourcePressureMarginJumpUp_of_netDropPositive n k r j
```

これで局所 margin jump と正味 drop positivity が完全に同値になる。

## 3. sign-change-up から net drop positive

```lean
theorem sourcePressureNetDropPositive_of_signChangeUp
    (n : OddNat) (k r j : ℕ)
    (h : SourcePressureSignChangeUp n k r j) :
    SourcePressureNetDropPositive n k r j :=
  sourcePressureNetDropPositive_of_marginJumpUp n k r j
    (sourcePressureMarginJumpUp_of_signChangeUp n k r j h)
```

## 4. local island 左端から net drop positive

```lean
theorem sourcePressureNetDropPositive_of_localIsland_left
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j) :
    SourcePressureNetDropPositive n k r (j - 1) :=
  sourcePressureNetDropPositive_of_marginJumpUp n k r (j - 1)
    (sourcePressureMarginJumpUp_of_localIsland_left n k r j hisland)
```

これはかなり重要。
local island の左端は、

```text
margin jump
```

であるだけでなく、

```text
net drop positive
```

でもある、と言える。

## 5. JumpWithDecay と net drop positive の wrapper

既存の `SourcePressureJumpWithDecay` は `MarginJumpUp ∧ retentionDrop ∧ continuationWeakDrop` なので、net drop positive から margin jump を復元できる。

```lean
theorem sourcePressureJumpWithDecay_of_netDropPositive_of_decay
    (n : OddNat) (k r j : ℕ)
    (hnet : SourcePressureNetDropPositive n k r j)
    (hret : SourceRetentionDropsAcross n k r j)
    (hcont : SourceContinuationWeaklyDropsAcross n k r j) :
    SourcePressureJumpWithDecay n k r j := by
  exact sourcePressureJumpWithDecay_of_parts n k r j
    (sourcePressureMarginJumpUp_of_netDropPositive n k r j hnet)
    hret
    hcont
```

これは現行 API を綺麗につなぐ。

## 一歩先ゆく推論

Checkpoint `137` で equivalence が閉じると、次に見えるのは **zero-crossing theorem** じゃ。

margin jump は、

```text
margin_next - margin_current > 0
```

に対応する。

しかし sign-change-up はもう少し強い。

```text
margin_current <= 0
and
margin_next > 0
```

つまり、

```text
margin_current <= 0
and
0 < margin_current + net_drop
```

が sign-change-up の本質になる。

したがって、Checkpoint `138` 以降で狙う形はこれ。

```lean
theorem sourcePressureSignChangeUp_iff_margin_nonpos_and_crossesByNetDrop
    ...
```

概念的には、

```text
SourcePressureSignChangeUp n k r j
  ↔
SourcePressureMarginInt n k (r + j) ≤ 0
  ∧
0 <
  SourcePressureMarginInt n k (r + j)
    + SourceRetentionDropInt n k r j
    - 2 * SourceContinuationDropInt n k r j
```

これはかなり強い。
sign-change-up を、単なる margin 符号変化ではなく、

```text
現在 margin + 正味 drop が 0 を超える
```

という crossing 条件に言い換えるものじゃ。

ここまで行くと、local island の左端は完全に PressureDecayProfile で説明できる。

## さらなる次の一手

Checkpoint `137` が通ったら、Checkpoint `138` は二択。

## Route A: crossing theorem

局所 sign-change-up の完全な decay 表現へ進む。

```text
signChangeUp
  ↔ current margin nonpositive and net drop crosses zero
```

これは理論的に美しい。

## Route B: split `PressureDecay.lean`

`PressureFrontier.lean` に pressure decay 語彙が増えてきたので、そろそろ分割を検討する。

候補：

```text
DkMath/Collatz/PetalBridge/PressureDecay.lean
```

移動候補：

```text
SourceRetentionDropInt
SourceContinuationDropInt
SourcePressureNetDropPositive
SourcePressureMarginStepDiff_eq
sourcePressureMarginJumpUp_iff_netDropPositive
SourcePressureJumpWithDecay
```

ただし、Checkpoint `137` ではまだ broad refactor しない方が良い。
まず equivalence を閉じてから、次に分割するのが安全じゃ。

## 賢狼が試して欲しい実験補題

## 実験 A: net drop positive from margin jump

```lean
theorem sourcePressureNetDropPositive_of_marginJumpUp
    (n : OddNat) (k r j : ℕ)
    (h : SourcePressureMarginJumpUp n k r j) :
    SourcePressureNetDropPositive n k r j := by
  unfold SourcePressureNetDropPositive
  rw [← sourcePressureMarginStepDiff_eq n k r j]
  exact (sourcePressureMarginJumpUp_iff_stepDiff_pos n k r j).1 h
```

## 実験 B: equivalence

```lean
theorem sourcePressureMarginJumpUp_iff_netDropPositive
    (n : OddNat) (k r j : ℕ) :
    SourcePressureMarginJumpUp n k r j ↔
      SourcePressureNetDropPositive n k r j := by
  constructor
  · exact sourcePressureNetDropPositive_of_marginJumpUp n k r j
  · exact sourcePressureMarginJumpUp_of_netDropPositive n k r j
```

## 実験 C: sign-change-up gives net drop positive

```lean
theorem sourcePressureNetDropPositive_of_signChangeUp
    (n : OddNat) (k r j : ℕ)
    (h : SourcePressureSignChangeUp n k r j) :
    SourcePressureNetDropPositive n k r j :=
  sourcePressureNetDropPositive_of_marginJumpUp n k r j
    (sourcePressureMarginJumpUp_of_signChangeUp n k r j h)
```

## 実験 D: local island left edge gives net drop positive

```lean
theorem sourcePressureNetDropPositive_of_localIsland_left
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j) :
    SourcePressureNetDropPositive n k r (j - 1) :=
  sourcePressureNetDropPositive_of_marginJumpUp n k r (j - 1)
    (sourcePressureMarginJumpUp_of_localIsland_left n k r j hisland)
```

## 実験 E: jump with decay from net drop positive

```lean
theorem sourcePressureJumpWithDecay_of_netDropPositive_of_decay
    (n : OddNat) (k r j : ℕ)
    (hnet : SourcePressureNetDropPositive n k r j)
    (hret : SourceRetentionDropsAcross n k r j)
    (hcont : SourceContinuationWeaklyDropsAcross n k r j) :
    SourcePressureJumpWithDecay n k r j := by
  exact sourcePressureJumpWithDecay_of_parts n k r j
    (sourcePressureMarginJumpUp_of_netDropPositive n k r j hnet)
    hret
    hcont
```

## Python 側の次観測

Python 側は、今回すでに sanity check が十分よく出ている。次に見るなら、`net_drop_positive` を summary で明示すると良い。

追加候補：

```text
rows_with_net_drop_positive
rows_with_margin_jump
rows_with_margin_jump_iff_net_drop_failure
```

期待値：

```text
rows_with_margin_jump_iff_net_drop_failure: 0
```

ただし、Lean で同値を閉じるなら Python 側は必須ではない。
今回は Lean 側の theorem close を優先してよい。

## 総括

Checkpoint `136` は成功じゃ。
PressureDecayProfile は、ついに観測語彙から整数会計へ進んだ。

```text
margin_next - margin_current =
  retention_drop - 2 * continuation_drop
```

この式が入ったことで、`retention_drop_dominant` は単なる Python ラベルではなく、Lean の `SourcePressureNetDropPositive` として読めるようになった。

次は、

```text
SourcePressureMarginJumpUp
  ↔ SourcePressureNetDropPositive
```

を閉じる。
そこまで行けば、local island / sign-change-up はすべて「net drop positive edge」として読める。

これはかなり大きな前進じゃ。

## Codex instructions

```text
Checkpoint 137:
Close the local equivalence between pressure margin jumps and positive net pressure drop.

Context:
  Checkpoint 136 added:
    SourceRetentionDropInt
    SourceContinuationDropInt
    sourcePressureMarginStepDiff_eq
    sourcePressureMarginJumpUp_iff_stepDiff_pos
    SourcePressureNetDropPositive
    sourcePressureMarginJumpUp_of_netDropPositive

  Python also reports:
    rows_with_margin_step_identity_failure: 0

Primary goal:
  Prove that a named adjacent pressure-margin jump is equivalent to positive
  net integer drop:
    SourcePressureMarginJumpUp n k r j
      ↔ SourcePressureNetDropPositive n k r j

Preferred Lean location:
  DkMath.Collatz.PetalBridge.PressureFrontier

Implement:
  1. Prove:
     sourcePressureNetDropPositive_of_marginJumpUp

     Suggested proof:
       unfold SourcePressureNetDropPositive
       rw [← sourcePressureMarginStepDiff_eq n k r j]
       exact (sourcePressureMarginJumpUp_iff_stepDiff_pos n k r j).1 h

  2. Prove:
     sourcePressureMarginJumpUp_iff_netDropPositive

  3. Prove:
     sourcePressureNetDropPositive_of_signChangeUp

  4. Prove:
     sourcePressureNetDropPositive_of_localIsland_left

  5. Prove:
     sourcePressureJumpWithDecay_of_netDropPositive_of_decay

Optional Python:
  Add summary fields:
    rows_with_net_drop_positive
    rows_with_margin_jump
    rows_with_margin_jump_iff_net_drop_failure

  Expected:
    rows_with_margin_jump_iff_net_drop_failure: 0

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
  After this equivalence is closed, consider a zero-crossing theorem:
    signChangeUp iff current margin is nonpositive and current margin plus net drop is positive.
```

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
index 33e283a4..79280af8 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
@@ -94,6 +94,50 @@ noncomputable def SourcePressureMarginInt
   (2 * orbitWindowContinuationSiblingMassPow2 n k r : ℤ) -
     (orbitWindowRetentionMassPow2 n k r : ℤ)

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
+      SourceRetentionDropInt n k r j -
+        2 * SourceContinuationDropInt n k r j := by
+  unfold SourcePressureMarginInt
+  unfold SourceRetentionDropInt SourceContinuationDropInt
+  ring
+
 /--
 Selected source pressure is exactly positive source pressure margin.

@@ -333,6 +377,19 @@ def SourcePressureJumpWithDecay
     SourceRetentionDropsAcross n k r j ∧
       SourceContinuationWeaklyDropsAcross n k r j

+/--
+Positive net integer drop across an adjacent pressure-depth edge.
+
+This is intentionally not named `RetentionDropDominant` yet.  The predicate is
+the algebraic quantity that actually appears in the margin-step identity:
+retention loss minus twice continuation loss.
+-/
+def SourcePressureNetDropPositive
+    (n : OddNat) (k r j : ℕ) : Prop :=
+  0 <
+    SourceRetentionDropInt n k r j -
+      2 * SourceContinuationDropInt n k r j
+
 /--
 The first selected source-pressure depth.

@@ -692,6 +749,35 @@ theorem sourcePressureMarginJumpUp_of_localIsland_left
   sourcePressureMarginJumpUp_of_signChangeUp n k r (j - 1)
     (sourcePressureSignChangeUp_of_localIsland n k r j hisland)

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
 /--
 Package a named margin jump and a strict retention drop.

diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-136.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-136.md
new file mode 100644
index 00000000..2937b90a
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-136.md
@@ -0,0 +1,197 @@
+# Report Petal 136
+
+## Scope
+
+Checkpoint 136 fixed the integer accounting layer for the Collatz pressure
+frontier work.
+
+The main result is local and adjacent-depth only:
+
+```text
+margin_next - margin_current =
+  retention_drop - 2 * continuation_drop
+```
+
+No global pressure-prefix theorem, no `Real.log`, no full grid, and no named
+`RetentionDropDominant` predicate were introduced.
+
+## Lean Changes
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+```
+
+Added integer-valued drop definitions:
+
+```lean
+noncomputable def SourceRetentionDropInt
+noncomputable def SourceContinuationDropInt
+```
+
+Both use the same sign convention:
+
+```text
+drop = current_depth_mass - next_depth_mass
+```
+
+Added the adjacent margin-step identity:
+
+```lean
+theorem sourcePressureMarginStepDiff_eq
+```
+
+Added the bridge from a strict margin comparison to a positive integer step:
+
+```lean
+theorem sourcePressureMarginJumpUp_iff_stepDiff_pos
+```
+
+Added a safe local net-drop predicate:
+
+```lean
+def SourcePressureNetDropPositive
+```
+
+and the first theorem using the balance sheet:
+
+```lean
+theorem sourcePressureMarginJumpUp_of_netDropPositive
+```
+
+The comments in source code now spell out that this is an adjacent-edge
+balance sheet, not a global selected-pressure shape theorem.
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
+margin_step_diff
+retention_drop_minus_2_continuation_drop
+margin_step_matches_net_drop
+margin_step_identity_failure_count
+```
+
+Added summary field:
+
+```text
+rows_with_margin_step_identity_failure
+```
+
+This gives an external sanity check for the same identity now proved in Lean.
+
+## Experiment
+
+Command:
+
+```bash
+python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py \
+  --max-n 16383 --steps 64 --r-start 2 --depth-len 12 \
+  --name-suffix _136_16383_k64_d12
+```
+
+Generated:
+
+```text
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_136_16383_k64_d12.csv
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_136_16383_k64_d12.md
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
+sign-change cause counts: retention_drop_dominant:404
+```
+
+The Python scan and the Lean theorem now agree on the exact local accounting
+identity.  The scan still sees all sign-change-up rows in this finite window as
+`retention_drop_dominant`, but that remains experimental classification only.
+
+## Inference
+
+The balance sheet changes the next design question.
+
+Before checkpoint 136, a margin jump and the two decay observations were only
+packaged together.  After checkpoint 136, a margin jump can be read exactly as
+positive net drop:
+
+```text
+retention_drop - 2 * continuation_drop > 0
+```
+
+This suggests that the next Lean layer should avoid global claims and instead
+build local equivalences around `SourcePressureNetDropPositive`.
+
+Possible next theorem surface:
+
+```lean
+theorem sourcePressureNetDropPositive_of_marginJumpUp
+theorem sourcePressureMarginJumpUp_iff_netDropPositive
+theorem sourcePressureJumpWithDecay_of_netDropPositive_of_decay
+```
+
+The first two are likely thin consequences of
+`sourcePressureMarginStepDiff_eq` and
+`sourcePressureMarginJumpUp_iff_stepDiff_pos`.
+
+## Suggested Next Checkpoint
+
+Checkpoint 137 should consider closing the equivalence:
+
+```text
+SourcePressureMarginJumpUp n k r j
+  iff
+SourcePressureNetDropPositive n k r j
+```
+
+Then, if useful, add wrappers connecting:
+
+```text
+sign-change-up
+local-island-left-edge
+net-drop-positive
+jump-with-decay
+```
+
+Keep `RetentionDropDominant` out of Lean until the exact predicate and its
+intended use are unavoidable.
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
