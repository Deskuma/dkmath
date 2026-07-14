# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.*

gch: e6a1d9d8b55217ccc5ce231f401e1a839b43e725

## Report

checkpoint 135 を実装しました。

主な変更は [PressureFrontier.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean) で、`SourcePressureJumpWithDecay` と以下の薄い wrapper theorem を追加しています。

- `sourcePressureJumpWithRetentionDrop_of_parts`
- `sourcePressureJumpWithRetentionDrop_of_signChangeUp_of_retentionDrop`
- `sourcePressureJumpWithRetentionDrop_of_localIsland_left_of_retentionDrop`
- `sourcePressureJumpWithDecay_of_parts`
- `sourcePressureJumpWithDecay_of_signChangeUp_of_decay`

Python scan 側では [pressure_sign_pattern_scan.py](/python/Collatz/PetalBridge/pressure_sign_pattern_scan.py) に `retention_drop_minus_2_continuation_drop` 系の観測値を追加し、sign-change/local-island の PressureDecay 詳細を全行出すようにしました。

生成物:

- [pressure_sign_pattern_scan_135_16383_k64_d12.csv](/python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_135_16383_k64_d12.csv)
- [pressure_sign_pattern_scan_135_16383_k64_d12.md](/python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_135_16383_k64_d12.md)
- [report-petal-135.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-135.md)

観測サマリは `rows=8192`, `sign-change-up=404`, `local-islands=252`, `largest margin jump=12`, `largest retention drop=20`, `largest continuation drop=13`, `largest retention drop minus 2 continuation drop=10` でした。sign-change-up はこの窓では全て `retention_drop_dominant` に分類されています。

検証済み:

```text
python3 -m py_compile python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
git diff --check
```

`PressureFrontier.lean` に新規 `sorry` はありません。次は report に書いた通り、`SourceRetentionDropInt` / `SourceContinuationDropInt` と margin step identity を Lean 側で固定するのが自然です。

## Review

## 状況分析

Checkpoint `135` は、前回の方針どおり **PressureDecayProfile の薄い wrapper 層**として綺麗に閉じている。

Lean 側では `PressureFrontier.lean` に `SourcePressureJumpWithDecay` が追加され、さらに以下の wrapper theorem が入った。

```text
sourcePressureJumpWithRetentionDrop_of_parts
sourcePressureJumpWithRetentionDrop_of_signChangeUp_of_retentionDrop
sourcePressureJumpWithRetentionDrop_of_localIsland_left_of_retentionDrop
sourcePressureJumpWithDecay_of_parts
sourcePressureJumpWithDecay_of_signChangeUp_of_decay
```

これらは、既にある観測を「同じ adjacent pressure-depth edge 上の情報」として束ねるだけで、まだ quantitative dominance を主張していない。これは非常に良い抑制じゃ。

Python 側では `pressure_sign_pattern_scan.py` に `retention_drop_minus_2_continuation_drop` 系の観測値が追加され、`_135_16383_k64_d12` の大きめ scan が実行された。結果は `rows=8192`, `sign-change-up=404`, `local-islands=252`, `largest margin jump=12`, `largest retention drop=20`, `largest continuation drop=13`, `largest retention drop minus 2 continuation drop=10`。この窓では sign-change-up が全件 `retention_drop_dominant` に分類されている。

つまり、今の到達点はこうじゃ。

```text
Checkpoint 134:
  margin jump / retention drop / continuation weak drop の語彙を導入

Checkpoint 135:
  それらを同じ pressure-depth edge 上の observation として package

Checkpoint 136:
  いよいよ integer drop amount と margin step identity へ進む段階
```

## レビュー

## 良い点

第一に、`SourcePressureJumpWithDecay` の粒度がちょうど良い。

```lean
def SourcePressureJumpWithDecay
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourcePressureMarginJumpUp n k r j ∧
    SourceRetentionDropsAcross n k r j ∧
      SourceContinuationWeaklyDropsAcross n k r j
```

これはまだ「原因」を断定しない。
ただ、

```text
margin が上がる
retention が厳密に落ちる
continuation が弱く落ちる
```

を同じ辺に束ねるだけじゃ。

したがって、Python の `retention_drop_dominant` を Lean に先取りせず、次の整数恒等式へ進むための安全な足場になっている。

第二に、wrapper theorem 群がよい。

特に、

```text
signChangeUp + retentionDrop
  -> SourcePressureJumpWithRetentionDrop

signChangeUp + retentionDrop + continuationWeakDrop
  -> SourcePressureJumpWithDecay
```

という形は、今後 `SourcePressureMarginStepDiff_eq` のような恒等式を入れたあとに、そのまま原因分析へ接続できる。

第三に、Python 側で `retention_drop_minus_2_continuation_drop` を出したのが重要じゃ。

これは次の恒等式そのものに対応している。

```text
margin_next - margin_current
  = retention_drop - 2 * continuation_drop
```

つまり、Python の観測値が、次に Lean で固定すべき algebraic identity の右辺になった。
ここまで来ると、観測と形式化の噛み合わせがかなり良い。

## 注意点

ここで一番大事なのは、次に `Dominant` を急がないことじゃ。

Python では `retention_drop_dominant` が全件で出ている。だが、Lean で `SourcePressureRetentionDropDominant` のような名前を入れる前に、まず以下を固定する必要がある。

```text
SourceRetentionDropInt
SourceContinuationDropInt
sourcePressureMarginStepDiff_eq
```

この順番が重要じゃ。

いきなり dominance predicate を入れると、「分類名」は得られるが、「なぜ margin jump になるのか」の構造がまだ薄い。
先に整数差分の恒等式を入れれば、dominance は自然に生える。

## 解説

現在の pressure margin は、既存定義から概念的にこう読める。

```text
margin = 2 * continuation - retention
```

ここで adjacent depth に対して、

```text
retention_drop = retention_current - retention_next
continuation_drop = continuation_current - continuation_next
```

と定義する。

すると、

```text
margin_next - margin_current
  = retention_drop - 2 * continuation_drop
```

になる。

これは今回の Python field、

```text
retention_drop_minus_2_continuation_drop
```

と一致する。
つまり、Python で見えている `retention_drop_dominant` は、形式的には

```text
2 * continuation_drop < retention_drop
```

であり、それは

```text
0 < margin_next - margin_current
```

すなわち margin jump を生む。

この恒等式が Lean に入ると、今までの物語はこう締まる。

```text
local island
  -> left-edge sign-change-up
  -> margin jump
  -> margin_next - margin_current > 0
  -> retention_drop - 2 * continuation_drop > 0
```

ここまで来て初めて、`retention_drop_dominant` を Lean 名として入れる資格が出る。

## 次の指示

Checkpoint `136` は、報告にもある通り、**integer-valued drop definitions と margin step identity** を狙うのが自然じゃ。

追加先は、まずは `PressureFrontier.lean` でよい。
ただし、今回の identity まで入ったら、次 checkpoint 以降で `PressureDecay.lean` を新設するか判断するのが良い。

## Checkpoint 136 推奨内容

## 1. retention drop の整数定義

```lean
noncomputable def SourceRetentionDropInt
    (n : OddNat) (k r j : ℕ) : ℤ :=
  (orbitWindowRetentionMassPow2 n k (r + j) : ℤ) -
    (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ)
```

## 2. continuation drop の整数定義

```lean
noncomputable def SourceContinuationDropInt
    (n : OddNat) (k r j : ℕ) : ℤ :=
  (orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) -
    (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ)
```

ここで drop は `current - next` と読む。
この convention は report-petal-135 でも明示されているので、それに合わせる。

## 3. margin step difference identity

本命 theorem。

```lean
theorem sourcePressureMarginStepDiff_eq
    (n : OddNat) (k r j : ℕ) :
    SourcePressureMarginInt n k (r + j + 1) -
      SourcePressureMarginInt n k (r + j)
      =
    SourceRetentionDropInt n k r j -
      2 * SourceContinuationDropInt n k r j := by
  unfold SourcePressureMarginInt
  unfold SourceRetentionDropInt SourceContinuationDropInt
  ring
```

これはおそらく `ring` で落ちる。
ただし `Nat` から `Int` への coercion と `2 * ...` の形で詰まる場合は、`ring_nf` の方が強いかもしれない。

## 4. margin jump iff positive step diff

次に薄く便利な補題。

```lean
theorem sourcePressureMarginJumpUp_iff_stepDiff_pos
    (n : OddNat) (k r j : ℕ) :
    SourcePressureMarginJumpUp n k r j ↔
      0 <
        SourcePressureMarginInt n k (r + j + 1) -
          SourcePressureMarginInt n k (r + j) := by
  unfold SourcePressureMarginJumpUp
  omega
```

これは今後の dominance への橋になる。

## 5. dominance はまだ theorem にしないか、薄い名前だけ

もし入れるなら、最小限こう。

```lean
def SourceRetentionDropDominatesContinuationDrop
    (n : OddNat) (k r j : ℕ) : Prop :=
  2 * SourceContinuationDropInt n k r j <
    SourceRetentionDropInt n k r j
```

ただし、これは optional にしてよい。
賢狼としては、Checkpoint `136` では定義だけ、もしくはまだ入れない方を推す。

入れるなら、次の theorem まで軽く通す。

```lean
theorem sourcePressureMarginJumpUp_of_retentionDropDominates
    (n : OddNat) (k r j : ℕ)
    (hdom : SourceRetentionDropDominatesContinuationDrop n k r j) :
    SourcePressureMarginJumpUp n k r j := by
  rw [sourcePressureMarginJumpUp_iff_stepDiff_pos]
  rw [sourcePressureMarginStepDiff_eq]
  unfold SourceRetentionDropDominatesContinuationDrop at hdom
  omega
```

ここまで通るなら `Dominates` を入れてもよい。
通らないなら、Checkpoint `137` に回す。

## 一歩先ゆく推論

ここから構造がかなり明確になる。

これまでの観測は、

```text
retention_drop_dominant rows が多い
```

だった。

Checkpoint `136` で identity が入ると、それは単なる観測分類ではなく、

```text
retention_drop - 2 * continuation_drop
  = margin_jump amount
```

という保存式になる。

つまり、pressure decay は次の形で読める。

```text
retention_drop:
  margin を押し上げる力

continuation_drop:
  margin を押し下げる力の半分ではなく、係数 2 で効く減衰項

retention_drop - 2 * continuation_drop:
  net pressure jump
```

ここが実に面白い。

`margin = 2C - R` なので、continuation は値としては 2 倍効いている。
しかし drop で見ると、continuation が落ちることは margin を下げる。
一方、retention が落ちることは margin を上げる。

だから local island は、

```text
continuation が増えた現象
```

ではなく、

```text
retention obstruction が急に抜けた現象
```

として説明できる。

これは DkMath 的にはかなり綺麗じゃ。

```text
Retention:
  障壁 / 抵抗 / 残留質量

Continuation:
  継続供給 / carrier support

Margin jump:
  障壁の急落と継続供給の減衰差
```

## さらなる次の一手

Checkpoint `136` が成功したら、Checkpoint `137` でやるべきことは明確じゃ。

## 1. dominance predicate

```lean
def SourceRetentionDropDominatesContinuationDrop
    (n : OddNat) (k r j : ℕ) : Prop :=
  2 * SourceContinuationDropInt n k r j <
    SourceRetentionDropInt n k r j
```

## 2. dominance gives margin jump

```lean
theorem sourcePressureMarginJumpUp_of_retentionDropDominates
    (n : OddNat) (k r j : ℕ)
    (hdom : SourceRetentionDropDominatesContinuationDrop n k r j) :
    SourcePressureMarginJumpUp n k r j := by
  rw [sourcePressureMarginJumpUp_iff_stepDiff_pos]
  rw [sourcePressureMarginStepDiff_eq]
  unfold SourceRetentionDropDominatesContinuationDrop at hdom
  omega
```

## 3. sign-change-up iff nonpositive/current and dominance-like positive step

これは少し重いが、将来の形としてはこう。

```text
margin_current <= 0
and
retention_drop dominates continuation_drop enough to cross zero
  -> sign-change-up
```

つまり、単なる margin jump ではなく、ゼロ境界を跨ぐ条件じゃ。

```text
0 < margin_current + retention_drop - 2 * continuation_drop
```

この形まで来ると、local island の左端を完全に decay balance として読める。

## 賢狼が試して欲しい実験補題

## 実験 A: retention drop int

```lean
noncomputable def SourceRetentionDropInt
    (n : OddNat) (k r j : ℕ) : ℤ :=
  (orbitWindowRetentionMassPow2 n k (r + j) : ℤ) -
    (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ)
```

## 実験 B: continuation drop int

```lean
noncomputable def SourceContinuationDropInt
    (n : OddNat) (k r j : ℕ) : ℤ :=
  (orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) -
    (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ)
```

## 実験 C: margin step identity

```lean
theorem sourcePressureMarginStepDiff_eq
    (n : OddNat) (k r j : ℕ) :
    SourcePressureMarginInt n k (r + j + 1) -
      SourcePressureMarginInt n k (r + j)
      =
    SourceRetentionDropInt n k r j -
      2 * SourceContinuationDropInt n k r j := by
  unfold SourcePressureMarginInt
  unfold SourceRetentionDropInt SourceContinuationDropInt
  ring
```

## 実験 D: jump iff positive step diff

```lean
theorem sourcePressureMarginJumpUp_iff_stepDiff_pos
    (n : OddNat) (k r j : ℕ) :
    SourcePressureMarginJumpUp n k r j ↔
      0 <
        SourcePressureMarginInt n k (r + j + 1) -
          SourcePressureMarginInt n k (r + j) := by
  unfold SourcePressureMarginJumpUp
  omega
```

## 実験 E: positive net drop gives jump

`Dominant` 名を避けるなら、まずは net positive の名前にする。

```lean
def SourcePressureNetDropPositive
    (n : OddNat) (k r j : ℕ) : Prop :=
  0 < SourceRetentionDropInt n k r j -
    2 * SourceContinuationDropInt n k r j
```

```lean
theorem sourcePressureMarginJumpUp_of_netDropPositive
    (n : OddNat) (k r j : ℕ)
    (hnet : SourcePressureNetDropPositive n k r j) :
    SourcePressureMarginJumpUp n k r j := by
  rw [sourcePressureMarginJumpUp_iff_stepDiff_pos]
  rw [sourcePressureMarginStepDiff_eq]
  exact hnet
```

この名前は `Dominant` より安全じゃ。
あとから `SourceRetentionDropDominatesContinuationDrop` を alias にしてもよい。

## Python 側の次観測

Python 側は、すでに `retention_drop_minus_2_continuation_drop` を出している。
次は、Lean theorem と対応させるために、以下の列名を明確にするのがよい。

```text
margin_step_diff
retention_drop_minus_2_continuation_drop
margin_step_matches_net_drop
```

期待値：

```text
margin_step_matches_net_drop:
  all True
```

さらに summary にこれを入れる。

```text
rows_with_margin_step_identity_failure:
  0
```

これは Python 側の sanity check であり、Lean の `sourcePressureMarginStepDiff_eq` と対応する。

## 総括

Checkpoint `135` は成功じゃ。

今回で、PressureDecayProfile は

```text
margin jump
retention drop
continuation weak drop
jump with decay
```

を同じ edge 上で扱えるようになった。

次は整数差分。

```text
retention_drop = retention_current - retention_next
continuation_drop = continuation_current - continuation_next
```

を Lean に入れ、

```text
margin_next - margin_current =
  retention_drop - 2 * continuation_drop
```

を閉じる。

これが通れば、Python の `retention_drop_dominant` は、いよいよ Lean の構造へ昇格できる。
ここはかなり重要な checkpoint になる。

## Codex instructions

```text
Checkpoint 136:
Introduce integer-valued pressure-drop accounting and prove the adjacent margin-step identity.

Context:
  Checkpoint 135 added thin wrapper predicates/theorems:
    SourcePressureJumpWithDecay
    sourcePressureJumpWithRetentionDrop_of_parts
    sourcePressureJumpWithRetentionDrop_of_signChangeUp_of_retentionDrop
    sourcePressureJumpWithRetentionDrop_of_localIsland_left_of_retentionDrop
    sourcePressureJumpWithDecay_of_parts
    sourcePressureJumpWithDecay_of_signChangeUp_of_decay

  Python now reports:
    retention_drop_minus_2_continuation_drop

Primary goal:
  Formalize the integer balance sheet:
    margin_next - margin_current =
      retention_drop - 2 * continuation_drop

Preferred Lean location:
  DkMath.Collatz.PetalBridge.PressureFrontier

  If the file becomes too large after this checkpoint, propose a follow-up split:
    DkMath.Collatz.PetalBridge.PressureDecay
  but do not perform a broad refactor in this checkpoint.

Implement:
  1. Define integer-valued retention drop:
     SourceRetentionDropInt n k r j :=
       (orbitWindowRetentionMassPow2 n k (r + j) : ℤ)
       - (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ)

  2. Define integer-valued continuation drop:
     SourceContinuationDropInt n k r j :=
       (orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ)
       - (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ)

  3. Prove the adjacent margin-step identity:
     sourcePressureMarginStepDiff_eq:
       SourcePressureMarginInt n k (r + j + 1)
         - SourcePressureMarginInt n k (r + j)
       =
       SourceRetentionDropInt n k r j
         - 2 * SourceContinuationDropInt n k r j

     Suggested proof:
       unfold SourcePressureMarginInt
       unfold SourceRetentionDropInt SourceContinuationDropInt
       ring
     If coercions block `ring`, try `ring_nf`.

  4. Prove:
     sourcePressureMarginJumpUp_iff_stepDiff_pos:
       SourcePressureMarginJumpUp n k r j ↔
         0 <
           SourcePressureMarginInt n k (r + j + 1)
             - SourcePressureMarginInt n k (r + j)

  5. Optional safe predicate:
     SourcePressureNetDropPositive n k r j :=
       0 < SourceRetentionDropInt n k r j
         - 2 * SourceContinuationDropInt n k r j

  6. If the optional predicate is added, prove:
     sourcePressureMarginJumpUp_of_netDropPositive

Naming caution:
  Do not introduce `RetentionDropDominant` yet unless the exact dominance
  predicate is needed and proved through the margin-step identity.
  Prefer `NetDropPositive` for this checkpoint.

Python:
  Add or verify sanity fields:
    margin_step_diff
    retention_drop_minus_2_continuation_drop
    margin_step_matches_net_drop

  Add summary:
    rows_with_margin_step_identity_failure: 0

  Re-run:
    python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py \
      --max-n 16383 --steps 64 --r-start 2 --depth-len 12 \
      --name-suffix _136_16383_k64_d12

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
  perform a broad refactor
```

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
index 861db9f4..33e283a4 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
@@ -319,6 +319,20 @@ def SourcePressureJumpWithRetentionDrop
   SourcePressureMarginJumpUp n k r j ∧
     SourceRetentionDropsAcross n k r j
 
+/--
+Observed pressure jump with both retention and continuation decay information.
+
+Checkpoint 135 keeps this as a thin packaging predicate.  It still avoids any
+quantitative dominance claim; it only records that the margin jumps upward,
+retention strictly drops, and continuation weakly drops across the same
+adjacent pressure-depth edge.
+-/
+def SourcePressureJumpWithDecay
+    (n : OddNat) (k r j : ℕ) : Prop :=
+  SourcePressureMarginJumpUp n k r j ∧
+    SourceRetentionDropsAcross n k r j ∧
+      SourceContinuationWeaklyDropsAcross n k r j
+
 /--
 The first selected source-pressure depth.
 
@@ -678,6 +692,73 @@ theorem sourcePressureMarginJumpUp_of_localIsland_left
   sourcePressureMarginJumpUp_of_signChangeUp n k r (j - 1)
     (sourcePressureSignChangeUp_of_localIsland n k r j hisland)
 
+/--
+Package a named margin jump and a strict retention drop.
+
+This checkpoint-135 wrapper is deliberately non-quantitative: it does not say
+that the retention drop dominates the continuation drop.  It only records that
+both observations are attached to the same adjacent pressure-depth edge.
+-/
+theorem sourcePressureJumpWithRetentionDrop_of_parts
+    (n : OddNat) (k r j : ℕ)
+    (hjump : SourcePressureMarginJumpUp n k r j)
+    (hret : SourceRetentionDropsAcross n k r j) :
+    SourcePressureJumpWithRetentionDrop n k r j :=
+  ⟨hjump, hret⟩
+
+/--
+An upward sign change plus a strict retention drop packages as a
+pressure-jump-with-retention-drop witness.
+-/
+theorem sourcePressureJumpWithRetentionDrop_of_signChangeUp_of_retentionDrop
+    (n : OddNat) (k r j : ℕ)
+    (hchange : SourcePressureSignChangeUp n k r j)
+    (hret : SourceRetentionDropsAcross n k r j) :
+    SourcePressureJumpWithRetentionDrop n k r j :=
+  sourcePressureJumpWithRetentionDrop_of_parts n k r j
+    (sourcePressureMarginJumpUp_of_signChangeUp n k r j hchange) hret
+
+/--
+A local pressure island left edge plus a strict retention drop packages as a
+pressure-jump-with-retention-drop witness.
+-/
+theorem sourcePressureJumpWithRetentionDrop_of_localIsland_left_of_retentionDrop
+    (n : OddNat) (k r j : ℕ)
+    (hisland : SourcePressureLocalIsland n k r j)
+    (hret : SourceRetentionDropsAcross n k r (j - 1)) :
+    SourcePressureJumpWithRetentionDrop n k r (j - 1) :=
+  sourcePressureJumpWithRetentionDrop_of_parts n k r (j - 1)
+    (sourcePressureMarginJumpUp_of_localIsland_left n k r j hisland) hret
+
+/--
+Package the three thin pressure-decay observations for the same edge.
+
+This is the source-code signpost for the next refinement: once integer drop
+amounts are introduced, this predicate should be the order-theoretic input
+side of the identity
+`margin_next - margin_current = retention_drop - 2 * continuation_drop`.
+-/
+theorem sourcePressureJumpWithDecay_of_parts
+    (n : OddNat) (k r j : ℕ)
+    (hjump : SourcePressureMarginJumpUp n k r j)
+    (hret : SourceRetentionDropsAcross n k r j)
+    (hcont : SourceContinuationWeaklyDropsAcross n k r j) :
+    SourcePressureJumpWithDecay n k r j :=
+  ⟨hjump, hret, hcont⟩
+
+/--
+An upward sign change plus retention/continuation decay packages as a
+pressure-jump-with-decay witness.
+-/
+theorem sourcePressureJumpWithDecay_of_signChangeUp_of_decay
+    (n : OddNat) (k r j : ℕ)
+    (hchange : SourcePressureSignChangeUp n k r j)
+    (hret : SourceRetentionDropsAcross n k r j)
+    (hcont : SourceContinuationWeaklyDropsAcross n k r j) :
+    SourcePressureJumpWithDecay n k r j :=
+  sourcePressureJumpWithDecay_of_parts n k r j
+    (sourcePressureMarginJumpUp_of_signChangeUp n k r j hchange) hret hcont
+
 /-- The empty selected-pressure prefix is always available. -/
 theorem selectedPressurePrefix_zero
     (n : OddNat) (k r len : ℕ) :
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-135.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-135.md
new file mode 100644
index 00000000..109ba8d1
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-135.md
@@ -0,0 +1,183 @@
+# Report Petal 135
+
+## Scope
+
+Checkpoint 135 continued the thin `PressureDecayProfile` layer in
+`DkMath.Collatz.PetalBridge.PressureFrontier`.
+
+The Lean side still avoids quantitative dominance.  The new API only packages
+already available observations across the same adjacent pressure-depth edge:
+
+- margin jump upward,
+- retention mass strictly drops,
+- continuation mass weakly drops.
+
+This keeps the proof surface ready for the next integer-drop identity without
+claiming `RetentionDropDominant` in Lean yet.
+
+## Lean Changes
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+```
+
+Added thin predicate:
+
+```lean
+def SourcePressureJumpWithDecay
+    (n : OddNat) (k r j : Nat) : Prop :=
+  SourcePressureMarginJumpUp n k r j ∧
+    SourceRetentionDropsAcross n k r j ∧
+      SourceContinuationWeaklyDropsAcross n k r j
+```
+
+Added wrapper theorems:
+
+```lean
+sourcePressureJumpWithRetentionDrop_of_parts
+sourcePressureJumpWithRetentionDrop_of_signChangeUp_of_retentionDrop
+sourcePressureJumpWithRetentionDrop_of_localIsland_left_of_retentionDrop
+sourcePressureJumpWithDecay_of_parts
+sourcePressureJumpWithDecay_of_signChangeUp_of_decay
+```
+
+The source comments now explicitly mark the next refinement point:
+
+```text
+margin_next - margin_current =
+  retention_drop - 2 * continuation_drop
+```
+
+with the convention that the future integer drops should be read as
+`current - next`.
+
+## Python Changes
+
+Updated:
+
+```text
+python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
+```
+
+Added a numeric scan field:
+
+```text
+max_retention_drop_minus_2_continuation_drop
+```
+
+and included per sign-change detail:
+
+```text
+retention_drop_minus_2_continuation_drop
+```
+
+The PressureDecay sections now emit all observed rows:
+
+- all sign-change-up rows with pressure-decay details,
+- all local-island rows with left-edge decay details.
+
+## Experiment
+
+Command:
+
+```bash
+python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py \
+  --max-n 16383 --steps 64 --r-start 2 --depth-len 12 \
+  --name-suffix _135_16383_k64_d12
+```
+
+Generated:
+
+```text
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_135_16383_k64_d12.csv
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_135_16383_k64_d12.md
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
+sign-change cause counts: retention_drop_dominant:404
+```
+
+The large scan again shows that every sign-change-up row in this window is
+classified by the experimental rule as `retention_drop_dominant`.  This is
+still observational Python data, not a Lean theorem.
+
+## Inference
+
+The useful next move is not a dominance predicate yet.  The stronger and more
+structural target is the integer accounting identity:
+
+```text
+margin_next - margin_current =
+  retention_drop - 2 * continuation_drop
+```
+
+Given
+
+```text
+margin_j = 2 * continuation_j - retention_j
+retention_drop = retention_j - retention_next
+continuation_drop = continuation_j - continuation_next
+```
+
+the identity is algebraic:
+
+```text
+(2 * continuation_next - retention_next)
+  - (2 * continuation_j - retention_j)
+= retention_drop - 2 * continuation_drop
+```
+
+That identity should become the checkpoint-136 bridge.  It converts the
+current order-only predicates into an exact integer balance sheet and explains
+why the Python `retention_drop_minus_2_continuation_drop` field numerically
+matches the observed margin jump.
+
+## Suggested Next Checkpoint
+
+Introduce integer-valued drop definitions, probably in the same
+`PressureFrontier` file unless the layer grows large enough to split:
+
+```lean
+def SourceRetentionDropInt
+def SourceContinuationDropInt
+```
+
+Then prove the local adjacent-depth identity for `SourcePressureMarginInt`.
+
+Only after that identity is in Lean should the project decide whether to name a
+dominance predicate such as `RetentionDropDominant`.
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
