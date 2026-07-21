# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.*

gch: c3d4a9cf8ac90b5dde8b7ab95ed2f4f469b0902f

## Report

Checkpoint 134 を完了しました。

Lean 側は [PressureFrontier.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean) に薄い PressureDecay vocabulary を追加しました。`SourcePressureMarginJumpUp`, `SourceRetentionDropsAcross`, `SourceContinuationWeaklyDropsAcross`, `SourcePressureJumpWithRetentionDrop` と、`signChangeUp` / `localIsland` から margin jump へ渡す bridge theorem を入れています。`Dominant` はまだ Lean 名には入れていません。

Python 側は `pressure_sign_pattern_scan.py` に PressureDecay section と CSV detail fields を追加し、`_134_8191_k64` の観測結果を生成しました。

新規 report:
[report-petal-134.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-134.md)

確認済み:

- `lake build DkMath.Collatz.PetalBridge.PressureFrontier`
- `lake build DkMath.Collatz.PetalBridge`
- `python3 -m py_compile python/Collatz/PetalBridge/pressure_sign_pattern_scan.py`
- `git diff --check`
- `PressureFrontier.lean` に新規 `sorry` なし

生成結果:

- `python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_134_8191_k64.csv`
- `python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_134_8191_k64.md`

## Review

## 状況分析

うむ。Checkpoint `134` は、前回の指示どおり **PressureDecayProfile の薄い開始**として成功している。

Lean 側では `PressureFrontier.lean` に、`SourcePressureMarginJumpUp`、`SourceRetentionDropsAcross`、`SourceContinuationWeaklyDropsAcross`、`SourcePressureJumpWithRetentionDrop` が追加された。さらに `signChangeUp` と `localIsland` から named margin jump へ渡す bridge theorem も入っている。重要なのは、ここで **Dominant** という名前をまだ Lean 側に入れていないことじゃ。Python 側では `retention_drop_dominant` という分類を使っているが、Lean 側ではまだ定量的不等式を形式化していないため、この抑制は正しい。

Python 側では `pressure_sign_pattern_scan.py` に PressureDecay section と詳細 CSV fields が追加され、`_134_8191_k64` の観測結果が生成されている。代表例として、`n=6247` の sign-change では retention が `12 -> 6`、continuation が `6 -> 4`、margin が `0 -> 2` に跳ねており、`n=1567` の local-island でも retention の落ち方が大きく見えている。

つまり今回で、

```text
sign-change-up
  -> margin jump

local island
  -> left-edge margin jump

pressure jump with retention drop
  -> thin PressureDecay vocabulary
```

が Lean と Python の両方で揃った。

## レビュー

## 良い点

第一に、今回の Lean 追加はとても薄く、しかも意味が強い。

`SourcePressureMarginJumpUp` は、隣接 pressure depth `r+j` から `r+j+1` で margin が増えるというだけの述語じゃ。これは pressure prefix も、global monotonicity も、ShapePressureGrid も主張していない。したがって、今後の実験結果に応じて安全に再利用できる。

第二に、retention / continuation の drop を **Nat subtraction ではなく比較述語**にしたのが良い。

```lean
def SourceRetentionDropsAcross
def SourceContinuationWeaklyDropsAcross
```

これはかなり安全じゃ。`Nat` の差は切り捨てが絡むので、最初から `retention_drop := current - next` のように定義すると後で証明が重くなる。今回のように、

```text
retention_next < retention_current
continuation_next <= continuation_current
```

としておけば、まず order-theoretic な薄い層として使える。

第三に、`SourcePressureJumpWithRetentionDrop` の名前が良い。

ここで `RetentionDropDominant` と呼んでしまうと、Python の分類ラベルを Lean theorem として先取りしてしまう。今回の名前は、

```text
margin jumps up
and retention strictly drops
```

だけを主張する。
これは現在の形式化段階にぴったりじゃ。

第四に、Python report がかなり有用になった。

sign-change-up rows と local-island rows で、margin / retention / continuation の前後値が見えるようになった。これにより、単なる `cause_label` ではなく、人間が実際に「なぜ margin が跳ねたか」を確認できる。

## 注意点

次に気をつけるべきは、**Dominance を Lean に上げるタイミング**じゃ。

Python では `retention_drop_dominant` が全件で出ている。しかし Lean 側でそれを定義するには、少なくとも次のどちらかが必要になる。

```text
1. integer-valued drop amount
2. margin step difference identity
```

特に本命は、

```text
margin_next - margin_current
  = 2 * continuation_change - retention_change
```

という形の差分恒等式じゃ。
これがないまま `Dominant` を定義すると、名前だけが強くなり、数学的にはまだ薄いままになってしまう。

したがって、Checkpoint `135` では Route B の「integer-valued drop expression」へいきなり進むより、まず Route A の薄い wrapper を閉じるのが良い。

## 解説

今回の進展で、local island の読みがかなり明確になった。

以前は local island を、

```text
深い continuation channel が突然強くなる現象
```

と見る可能性もあった。
しかし今回の pressure-decay details では、代表例で continuation も減っている。ただし retention の減り方がより大きいため、相対的に margin が正へ跳ねている。

つまり、現時点の読みはこうじゃ。

```text
local island:
  continuation が増える現象ではなく、
  retention が急落することで、
  2 * continuation - retention が正へ転じる現象
```

これは重要じゃ。

なぜなら、positive block と local island が別の機構に分かれて見えるからじゃ。

```text
positive block:
  deep residual all-ones excursion による continuation support

local island / sign-change-up:
  adjacent pressure depths における retention / continuation の減衰差
```

ここまで来ると、次の大構造はやはり二枚構成になる。

```text
ResidualAllOnesProfile:
  time axis 上の深い all-ones excursion

PressureDecayProfile:
  pressure-depth axis 上の retention / continuation decay
```

まだ `ShapePressureGrid` ではない。
その前に、この二枚をそれぞれ薄く固めるのが正着じゃ。

## 次の指示

Checkpoint `135` は **Route A を推す**。

つまり、今回入った薄い語彙を使って、次の wrapper / bridge を足す。

```text
strict retention drop + margin jump
  -> named pressure-decay observation

local island
  -> pressure jump with retention drop
```

ただし、後者は retention drop が既存 theorem から証明できる場合に限る。
もし `orbitWindowRetentionMassPow2` の反単調性から local island 左端で strict retention drop がすぐ出ないなら、無理に閉じない。まずは sign-change-up/local-island と margin jump の named bridge まででよい。

## Checkpoint 135 推奨内容

## 1. Pressure jump with retention drop constructor

すでに定義があるので、constructor theorem を置く。

```lean
theorem sourcePressureJumpWithRetentionDrop_of_jump_of_retentionDrop
    (n : OddNat) (k r j : ℕ)
    (hjump : SourcePressureMarginJumpUp n k r j)
    (hdrop : SourceRetentionDropsAcross n k r j) :
    SourcePressureJumpWithRetentionDrop n k r j := by
  exact ⟨hjump, hdrop⟩
```

これは軽いが、後続で使いやすい。

## 2. Sign-change-up plus retention drop

```lean
theorem sourcePressureJumpWithRetentionDrop_of_signChangeUp_of_retentionDrop
    (n : OddNat) (k r j : ℕ)
    (hsgn : SourcePressureSignChangeUp n k r j)
    (hdrop : SourceRetentionDropsAcross n k r j) :
    SourcePressureJumpWithRetentionDrop n k r j := by
  exact ⟨sourcePressureMarginJumpUp_of_signChangeUp n k r j hsgn, hdrop⟩
```

これは現在の vocabulary を自然につなぐ。

## 3. Local island plus retention drop at left edge

もし retention drop を別途仮定にするなら、これは確実に通る。

```lean
theorem sourcePressureJumpWithRetentionDrop_of_localIsland_left_of_retentionDrop
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j)
    (hdrop : SourceRetentionDropsAcross n k r (j - 1)) :
    SourcePressureJumpWithRetentionDrop n k r (j - 1) := by
  exact ⟨sourcePressureMarginJumpUp_of_localIsland_left n k r j hisland, hdrop⟩
```

ここでは `localIsland -> retention drop` を主張しない。
あくまで、local island と retention drop が揃ったら named observation にまとめる。

## 4. Continuation weak drop を含む observation

Python の cause 判定に近づける準備として、次のような薄い predicate を置いてもよい。

```lean
def SourcePressureJumpWithDecay
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourcePressureMarginJumpUp n k r j ∧
    SourceRetentionDropsAcross n k r j ∧
    SourceContinuationWeaklyDropsAcross n k r j
```

名前は `Dominant` ではなく `WithDecay` が安全じゃ。

constructor:

```lean
theorem sourcePressureJumpWithDecay_of_parts
    (n : OddNat) (k r j : ℕ)
    (hjump : SourcePressureMarginJumpUp n k r j)
    (hret : SourceRetentionDropsAcross n k r j)
    (hcont : SourceContinuationWeaklyDropsAcross n k r j) :
    SourcePressureJumpWithDecay n k r j := by
  exact ⟨hjump, hret, hcont⟩
```

## 5. Python 側は 1 本追加 scan

Python は今回 `8191/k64` を出している。
次は同じ PressureDecay details を `16383/k64/d12` にも出すのが良い。

```text
--max-n 16383 --steps 64 --r-start 2 --depth-len 12 --name-suffix _135_16383_k64_d12
```

これで、前回の大きめ scan に対して pressure-decay details の代表例も取れる。

## 一歩先ゆく推論

次の本命は、まだ `Dominant` 定義ではなく、**margin step decomposition** じゃ。

いまある margin は、概念的には

```text
margin(j) = 2 * continuation(j) - retention(j)
```

であるはず。

ならば次に欲しいのは、

```text
margin(j+1) - margin(j)
```

を retention / continuation の変化で書くことじゃ。

これが閉じると、

```text
retention drop が margin jump を作る
```

という説明が、観測ラベルではなく algebraic identity になる。

ただし、これは `ℤ` と `ℕ` の境界が絡むので、Checkpoint `135` ではまだ早いかもしれぬ。
Checkpoint `136` 以降で狙うのが良い。

## さらなる次の一手

Checkpoint `135` で thin wrapper が閉じたら、Checkpoint `136` は次のどちらか。

## Route B1: integer drop amount

```lean
def SourceRetentionDropInt
    (n : OddNat) (k r j : ℕ) : ℤ :=
  (orbitWindowRetentionMassPow2 n k (r + j) : ℤ) -
    (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ)
```

```lean
def SourceContinuationDropInt
    (n : OddNat) (k r j : ℕ) : ℤ :=
  (orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) -
    (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ)
```

これを入れると、Python の `retention_drop` / `continuation_drop` と Lean が一致しやすくなる。

## Route B2: margin step identity

```lean
theorem sourcePressureMarginStepDiff_eq
    (n : OddNat) (k r j : ℕ) :
    SourcePressureMarginInt n k (r + j + 1) -
      SourcePressureMarginInt n k (r + j)
      =
    2 * SourceContinuationDropInt n k r j -
      SourceRetentionDropInt n k r j := by
  -- statement may need sign adjustment depending on definitions
  sorry
```

ただし、符号向きは慎重に確認する必要がある。

もし drop を

```text
current - next
```

で定義するなら、概念的には

```text
margin_next - margin_current
  = retention_drop - 2 * continuation_drop
```

になる可能性が高い。

実際、

```text
margin = 2C - R
```

なら、

```text
margin_next - margin_current
  = 2(C_next - C_current) - (R_next - R_current)
```

ここで、

```text
retention_drop = R_current - R_next
continuation_drop = C_current - C_next
```

と置けば、

```text
margin_next - margin_current
  = retention_drop - 2 * continuation_drop
```

じゃ。

これはとても大事。
Python の `retention_drop > 2 * continuation_drop` は、まさに margin jump を意味する。

ここまで来ると、`Dominant` を Lean に入れる準備が整う。

## 賢狼が試して欲しい実験補題

## 実験 A: constructor for jump with retention drop

```lean
theorem sourcePressureJumpWithRetentionDrop_of_parts
    (n : OddNat) (k r j : ℕ)
    (hjump : SourcePressureMarginJumpUp n k r j)
    (hdrop : SourceRetentionDropsAcross n k r j) :
    SourcePressureJumpWithRetentionDrop n k r j := by
  exact ⟨hjump, hdrop⟩
```

## 実験 B: sign-change-up plus retention drop

```lean
theorem sourcePressureJumpWithRetentionDrop_of_signChangeUp_of_retentionDrop
    (n : OddNat) (k r j : ℕ)
    (hsgn : SourcePressureSignChangeUp n k r j)
    (hdrop : SourceRetentionDropsAcross n k r j) :
    SourcePressureJumpWithRetentionDrop n k r j := by
  exact ⟨sourcePressureMarginJumpUp_of_signChangeUp n k r j hsgn, hdrop⟩
```

## 実験 C: local island left edge plus retention drop

```lean
theorem sourcePressureJumpWithRetentionDrop_of_localIsland_left_of_retentionDrop
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j)
    (hdrop : SourceRetentionDropsAcross n k r (j - 1)) :
    SourcePressureJumpWithRetentionDrop n k r (j - 1) := by
  exact ⟨sourcePressureMarginJumpUp_of_localIsland_left n k r j hisland, hdrop⟩
```

## 実験 D: jump with full weak decay

```lean
def SourcePressureJumpWithDecay
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourcePressureMarginJumpUp n k r j ∧
    SourceRetentionDropsAcross n k r j ∧
    SourceContinuationWeaklyDropsAcross n k r j
```

```lean
theorem sourcePressureJumpWithDecay_of_parts
    (n : OddNat) (k r j : ℕ)
    (hjump : SourcePressureMarginJumpUp n k r j)
    (hret : SourceRetentionDropsAcross n k r j)
    (hcont : SourceContinuationWeaklyDropsAcross n k r j) :
    SourcePressureJumpWithDecay n k r j := by
  exact ⟨hjump, hret, hcont⟩
```

## 実験 E: sign-change-up with full weak decay

```lean
theorem sourcePressureJumpWithDecay_of_signChangeUp_of_decay
    (n : OddNat) (k r j : ℕ)
    (hsgn : SourcePressureSignChangeUp n k r j)
    (hret : SourceRetentionDropsAcross n k r j)
    (hcont : SourceContinuationWeaklyDropsAcross n k r j) :
    SourcePressureJumpWithDecay n k r j := by
  exact ⟨sourcePressureMarginJumpUp_of_signChangeUp n k r j hsgn, hret, hcont⟩
```

## Python 側の次観測

次は `_135_16383_k64_d12` を出して、PressureDecay details の代表例を増やす。

```text
python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py \
  --max-n 16383 --steps 64 --r-start 2 --depth-len 12 \
  --name-suffix _135_16383_k64_d12
```

見たい項目：

```text
largest_margin_jump
largest_retention_drop
largest_continuation_drop
largest_retention_drop_minus_2_continuation_drop
all sign-change-up rows with cause
all local-island rows with left-edge decay details
```

特に、

```text
retention_drop - 2 * continuation_drop
```

を追加するとよい。
これは将来の Lean theorem `margin_next - margin_current` と直結する。

## 総括

Checkpoint `134` は成功じゃ。

今回で、PressureDecayProfile はまだ薄いながらも、

```text
margin jump
retention drop
continuation weak drop
jump with retention drop
```

という語彙を得た。

次は、これらを少しだけつなぐ wrapper theorem を足す。
まだ quantitative dominance は入れない。

賢狼の推奨はこれ。

```text
Checkpoint 135:
  Thin wrappers for pressure-decay observations.

Checkpoint 136:
  Integer drop amounts and margin-step identity.

Checkpoint 137:
  Only then define retention-drop dominance.
```

ここまで順序を守れば、Python の `retention_drop_dominant` が、ちゃんと Lean の構造定理へ昇格できる。

## Codex instructions

```text
Checkpoint 135:
Continue the thin PressureDecayProfile layer.

Context:
  Checkpoint 134 added:
    SourcePressureMarginJumpUp
    SourceRetentionDropsAcross
    SourceContinuationWeaklyDropsAcross
    SourcePressureJumpWithRetentionDrop
    sourcePressureMarginJumpUp_of_signChangeUp
    sourcePressureMarginJumpUp_of_localIsland_left

Primary goal:
  Add lightweight wrapper theorems that package existing observations.
  Do not introduce quantitative dominance yet.

Preferred Lean location:
  DkMath.Collatz.PetalBridge.PressureFrontier

Implement:
  1. Constructor theorem:
     sourcePressureJumpWithRetentionDrop_of_parts

  2. Bridge theorem:
     sourcePressureJumpWithRetentionDrop_of_signChangeUp_of_retentionDrop

  3. Bridge theorem:
     sourcePressureJumpWithRetentionDrop_of_localIsland_left_of_retentionDrop

  4. Optional thin predicate:
     SourcePressureJumpWithDecay :=
       SourcePressureMarginJumpUp
       ∧ SourceRetentionDropsAcross
       ∧ SourceContinuationWeaklyDropsAcross

  5. If added, prove:
     sourcePressureJumpWithDecay_of_parts
     sourcePressureJumpWithDecay_of_signChangeUp_of_decay

Python:
  Run a larger PressureDecay-detail scan:
    python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py \
      --max-n 16383 --steps 64 --r-start 2 --depth-len 12 \
      --name-suffix _135_16383_k64_d12

  Add or report:
    largest_margin_jump
    largest_retention_drop
    largest_continuation_drop
    largest_retention_drop_minus_2_continuation_drop
    all sign-change-up rows with pressure-decay details
    all local-island rows with left-edge decay details

  If convenient, add a numeric field:
    retention_drop_minus_2_continuation_drop

Verification:
  Run:
    lake build DkMath.Collatz.PetalBridge.PressureFrontier
    lake build DkMath.Collatz.PetalBridge
    python3 -m py_compile python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
    git diff --check

Do not:
  introduce Real.log
  claim a pressure prefix theorem
  define full ShapePressureGrid
  define RetentionDropDominant in Lean yet
  prove deep all-ones excursion implies positive block
  conflate time index i with pressure-depth index j

Next checkpoint hint:
  Checkpoint 136 should consider integer-valued drop amounts:
    SourceRetentionDropInt
    SourceContinuationDropInt
  and the margin step identity:
    margin_next - margin_current =
      retention_drop - 2 * continuation_drop
```

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
index c56af501..861db9f4 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
@@ -270,6 +270,55 @@ def SourcePressureSignChangeUp
   SourcePressureMarginInt n k (r + j) ≤ 0 ∧
     0 < SourcePressureMarginInt n k (r + j + 1)

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
+Retention mass strictly drops across adjacent pressure depths.
+
+This is intentionally a comparison predicate instead of a natural-number
+subtraction.  The experimental scan reports numeric drops, but the Lean API
+keeps the first pressure-decay layer order-theoretic.
+-/
+def SourceRetentionDropsAcross
+    (n : OddNat) (k r j : ℕ) : Prop :=
+  orbitWindowRetentionMassPow2 n k (r + j + 1) <
+    orbitWindowRetentionMassPow2 n k (r + j)
+
+/--
+Continuation mass weakly drops across adjacent pressure depths.
+
+The weak form is the safe default for checkpoint 134: it records monotone
+decay across the adjacent pressure depths without claiming a quantitative
+dominance relation.
+-/
+def SourceContinuationWeaklyDropsAcross
+    (n : OddNat) (k r j : ℕ) : Prop :=
+  orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) ≤
+    orbitWindowContinuationSiblingMassPow2 n k (r + j)
+
+/--
+Observed pressure jump equipped with a strict retention drop.
+
+The name deliberately avoids "dominant": dominance in the Python scan uses
+the quantitative inequality `retention_drop > 2 * continuation_drop`, which is
+not part of this thin Lean predicate yet.
+-/
+def SourcePressureJumpWithRetentionDrop
+    (n : OddNat) (k r j : ℕ) : Prop :=
+  SourcePressureMarginJumpUp n k r j ∧
+    SourceRetentionDropsAcross n k r j
+
 /--
 The first selected source-pressure depth.

@@ -569,6 +618,15 @@ theorem sourcePressureMargin_lt_of_signChangeUp
   rcases h with ⟨hle, hpos⟩
   omega

+/--
+An upward sign change is a named pressure-margin jump.
+-/
+theorem sourcePressureMarginJumpUp_of_signChangeUp
+    (n : OddNat) (k r j : ℕ)
+    (h : SourcePressureSignChangeUp n k r j) :
+    SourcePressureMarginJumpUp n k r j :=
+  sourcePressureMargin_lt_of_signChangeUp n k r j h
+
 /--
 A local pressure island produces an upward sign change at its left edge.
 -/
@@ -607,6 +665,19 @@ theorem sourcePressureMargin_lt_of_localIsland_left
   sourcePressureMargin_lt_of_signChangeUp n k r (j - 1)
     (sourcePressureSignChangeUp_of_localIsland n k r j hisland)

+/--
+A local pressure island gives a named pressure-margin jump at its left edge.
+
+This is the checkpoint-134 vocabulary version of
+`sourcePressureMargin_lt_of_localIsland_left`.
+-/
+theorem sourcePressureMarginJumpUp_of_localIsland_left
+    (n : OddNat) (k r j : ℕ)
+    (hisland : SourcePressureLocalIsland n k r j) :
+    SourcePressureMarginJumpUp n k r (j - 1) :=
+  sourcePressureMarginJumpUp_of_signChangeUp n k r (j - 1)
+    (sourcePressureSignChangeUp_of_localIsland n k r j hisland)
+
 /-- The empty selected-pressure prefix is always available. -/
 theorem selectedPressurePrefix_zero
     (n : OddNat) (k r len : ℕ) :
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-134.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-134.md
new file mode 100644
index 00000000..8eed2cbc
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-134.md
@@ -0,0 +1,252 @@
+# Report Petal 134
+
+## Scope
+
+Checkpoint 134 starts the thin `PressureDecayProfile` layer after the
+`DkMath.Collatz.PetalBridge` refactor.
+
+No package docs were synchronized.  The durable explanation was placed in Lean
+docstrings and source comments, following the current rule that source comments
+are the active synchronization surface.
+
+## Lean Changes
+
+File:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+```
+
+Added named margin-jump vocabulary:
+
+```lean
+def SourcePressureMarginJumpUp
+```
+
+Added weak pressure-decay predicates:
+
+```lean
+def SourceRetentionDropsAcross
+def SourceContinuationWeaklyDropsAcross
+```
+
+These avoid natural-number subtraction.  They are comparison predicates over
+adjacent pressure depths:
+
+```text
+retention_next < retention_current
+continuation_next <= continuation_current
+```
+
+Added a combined observation predicate:
+
+```lean
+def SourcePressureJumpWithRetentionDrop
+```
+
+The name deliberately avoids `Dominant`.  The Python scan uses a quantitative
+cause label, but this Lean predicate only packages:
+
+```text
+margin jumps up
+retention strictly drops
+```
+
+Added bridge theorems:
+
+```lean
+theorem sourcePressureMarginJumpUp_of_signChangeUp
+theorem sourcePressureMarginJumpUp_of_localIsland_left
+```
+
+The existing theorem
+
+```lean
+sourcePressureMargin_lt_of_localIsland_left
+```
+
+remains the raw inequality form.  The new theorem is only the named predicate
+version for future pressure-decay work.
+
+## Python Changes
+
+File:
+
+```text
+python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
+```
+
+Added two CSV fields:
+
+```text
+sign_change_pressure_decay_details
+local_island_pressure_decay_details
+```
+
+Added a `PressureDecay` summary section:
+
+```text
+PressureDecay: Sign-Change-Up Rows
+PressureDecay: Local-Island Rows
+```
+
+The sign-change rows now expose:
+
+```text
+j
+margin_j
+margin_next
+margin_jump
+retention_j
+retention_next
+retention_drop
+continuation_j
+continuation_next
+continuation_drop
+cause
+```
+
+The local-island rows now expose:
+
+```text
+n
+island_depth
+left_edge_j
+margin_left
+margin_island
+margin_right
+retention_left
+retention_island
+retention_right
+continuation_left
+continuation_island
+continuation_right
+```
+
+This keeps the time axis and pressure-depth axis separate.  It does not assert
+that a local island is caused by any single global condition.
+
+## Experiment
+
+Generated a checkpoint-specific scan:
+
+```text
+python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py \
+  --max-n 8191 --steps 64 --r-start 2 --depth-len 10 \
+  --name-suffix _134_8191_k64
+```
+
+Outputs:
+
+```text
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_134_8191_k64.csv
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_134_8191_k64.md
+```
+
+Summary:
+
+```text
+rows: 4096
+rows with positive pressure depths: 2170
+rows with local islands: 91
+rows with sign-change-up positions: 137
+max positive depth count: 10
+max local island count: 1
+max sign-change-up count: 1
+sign-change cause counts: retention_drop_dominant:137
+```
+
+Representative sign-change pressure-decay row:
+
+```text
+n=6247:
+  j=4
+  margin_j=0
+  margin_next=2
+  margin_jump=2
+  retention_j=12
+  retention_next=6
+  retention_drop=6
+  continuation_j=6
+  continuation_next=4
+  continuation_drop=2
+  cause=retention_drop_dominant
+```
+
+Representative local-island pressure-decay row:
+
+```text
+n=1567:
+  island_depth=3
+  left_edge_j=2
+  margin_left=-2
+  margin_island=1
+  margin_right=0
+  retention_left=8
+  retention_island=3
+  retention_right=2
+  continuation_left=3
+  continuation_island=2
+  continuation_right=1
+```
+
+## Inference
+
+The new Lean vocabulary matches the current experimental resolution:
+
+```text
+sign-change-up -> margin jump
+local island -> left-edge margin jump
+```
+
+The retention/continuation observations are now visible in Python, but Lean
+does not yet formalize the quantitative dominance inequality
+
+```text
+retention_drop > 2 * continuation_drop
+```
+
+That restraint is intentional.  The next useful step is to decide whether the
+dominance relation should be formalized as an integer inequality or kept as a
+computed classification layer for a few more checkpoints.
+
+## Verification
+
+Commands run:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureFrontier
+lake build DkMath.Collatz.PetalBridge
+python3 -m py_compile python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
+git diff --check
+```
+
+No new `sorry` was found in:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
+```
+
+## Next Candidate
+
+Checkpoint 135 has two clean options.
+
+Route A:
+
+```text
+Add theorem wrappers that turn a strict retention drop plus a suitable
+continuation weak drop into a named pressure-decay observation.
+```
+
+This remains thin and avoids dominance.
+
+Route B:
+
+```text
+Introduce an integer-valued retention/continuation drop expression, then define
+SourcePressureRetentionDropDominatesContinuationDrop only when the exact
+inequality is ready.
+```
+
+Route B is more expressive, but it should not be started unless the reviewer
+wants the quantitative cause label moved from Python into Lean.
````
`````
