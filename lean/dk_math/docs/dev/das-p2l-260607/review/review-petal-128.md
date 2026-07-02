# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 70f0558d1428a04b6c76c6dbeaf877e7a291644f

## Report

checkpoint 127 を実装しました。

`PetalBridge` に window residual shape 層を追加しました。新規定義は [orbitWindowResidualShape](/lean/dk_math/DkMath/Collatz/PetalBridge.lean:133)、`orbitWindowResidualShapeSeq`、`orbitWindowFirstFailedPow2Depth` です。主定理として [orbitWindowResidualShape_eq_oddOrbitLabel_succ](/lean/dk_math/DkMath/Collatz/PetalBridge.lean:4714) を閉じ、有限窓で「抽出された residual shape = 次の odd label」を固定しました。

追加で、residual shape sequence が shifted label sequence と一致する補題、window raw factorization、first failed depth の remainder 非零も入れています。これで finite window は `label_i -> raw -> height -> residualShape -> label_{i+1}` の有限力学として読めます。

おまけとして pressure 側に [SourcePressureSignChangeUp](/lean/dk_math/DkMath/Collatz/PetalBridge.lean:6901)、frontier から sign-change を得る補題、[SourcePressureLocalIsland](/lean/dk_math/DkMath/Collatz/PetalBridge.lean:7002) も追加しました。これは prefix 主張ではなく、margin sign pattern 分類の足場です。

ドキュメントは README、126 doc、PetalBridge guide/status を更新し、新規に [Collatz-WindowResidualShape-127.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-WindowResidualShape-127.md:1) と [report-petal-127.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-127.md:1) を作成しました。

検証:
`lake build DkMath.Collatz.PetalBridge`
`lake build DkMath.Collatz.Collatz2K26`
no-sorry 検索、diff check、末尾空白チェックも通過。既存依存の `ZsigmondyCyclotomicResearch` の `sorry` warning は今回範囲外です。

## Review

## 状況分析

うむ。checkpoint `127` は、かなり綺麗に Route A を閉じている。
今回の中心は、pointwise で閉じていた

```text
RawGnomonResidualShape n.val = (T n).val
```

を、有限窓へ持ち上げたことじゃ。

新しく `orbitWindowResidualShape`, `orbitWindowResidualShapeSeq`, `orbitWindowFirstFailedPow2Depth` が入り、主定理 `orbitWindowResidualShape_eq_oddOrbitLabel_succ` によって、有限窓で「抽出された residual shape が次の odd label である」ことが固定された。さらに window raw factorization と first failed depth の remainder 非零も入っているため、finite window を `label_i -> raw -> height -> residualShape -> label_{i+1}` の有限力学として読めるようになった。

これは大きい。
これで Collatz.PetalBridge は単なる height / residue / count の観測面ではなく、**residual-shape extraction の有限力学面**になった。

## レビュー

## 良い点

第一に、`orbitWindowResidualShape_eq_oddOrbitLabel_succ` が非常に重要じゃ。

```lean
theorem orbitWindowResidualShape_eq_oddOrbitLabel_succ
    (n : OddNat) (i : ℕ) :
    orbitWindowResidualShape n i = oddOrbitLabel n (i + 1)
```

これにより、`orbitWindowResidualShape` は単なる派生観測値ではなく、次の軌道ラベルそのものになった。
つまり有限窓は、

```text
label_0, label_1, label_2, ...
```

という列であると同時に、

```text
residual_0, residual_1, residual_2, ...
```

の列でもある。

第二に、`orbitWindow_rawGnomonStep_factor` が良い。

```lean
RawGnomonStep (oddOrbitLabel n i) =
  2 ^ orbitWindowHeight n i * orbitWindowResidualShape n i
```

これは各 window index において、raw gnomon step が「2進整列深度」と「残差形状」に分解されることを示す。
これで `height` は単なる数え上げではなく、残差形状を取り出すための抽出指数になった。

第三に、`orbitWindow_firstFailed_remainder_ne_zero` が入ったことで、window 各点で first failed depth が明確になった。これは、今後「どこまで一色線に整列し、どこから残差形状が見えるか」を finite window 上で観測する入口になる。

第四に、pressure 側の追加が控えめなのも良い。`SourcePressureSignChangeUp`, `sourcePressureSignChangeUp_of_frontier_pos`, `SourcePressureLocalIsland` は入っているが、まだ prefix theorem には進んでいない。これは正しい。pressure はまだ sign pattern の分類段階であり、monotonicity を主張する段階ではない。

## 注意点

次の注意点は、residual-shape sequence API がまだ薄いことじゃ。

`orbitWindowResidualShapeSeq` は定義されたが、height sequence と同じように使うための list helper がまだ不足している。レポートでも次 checkpoint 候補として、

```lean
orbitWindowResidualShapeSeq_length
orbitWindowResidualShapeSeq_get?_eq_some
orbitWindowResidualShapeSeq_take_length
orbitWindowResidualShapeSeq_take_get?_eq_some
```

が挙げられている。

ここを整えると、後続の pressure island / frontier / block の定理で、residual shape profile を参照しやすくなる。

## 解説

ここまでで、Collatz の accelerated odd window は次の形で固定された。

```text
label_i
  -> RawGnomonStep label_i
  -> orbitWindowHeight n i
  -> orbitWindowResidualShape n i
  -> label_{i+1}
```

この流れの意味はこうじゃ。

`label_i` は現在の奇数残差形状。
そこへ奇数グノモン層を足して `RawGnomonStep` を作る。
その raw 値がどれだけ \(2^h\) に整列するかを `orbitWindowHeight` で評価する。
整列分を取り除いたものが `orbitWindowResidualShape`。
そしてそれが、次の `label_{i+1}` になる。

つまり、コラッツ軌道は「数が増えたり減ったりする列」ではなく、

```text
奇数グノモン補正
2進整列評価
残差形状抽出
次形状への更新
```

の有限反復として読める。

この言い換えは、今後かなり効く。
なぜなら pressure margin は、単に residue count の話ではなく、

```text
有限窓内の residual shape が、
どの channel に残り、
どの channel へ継続し、
どの深さで retention に勝つか
```

という話に昇格するからじゃ。

## 次の指示

次 checkpoint は、レポート推奨どおり **Route A をもう一段進める**のが良い。

つまり、`orbitWindowResidualShapeSeq` を height sequence と同じくらい扱いやすくする。

## Checkpoint 128 推奨内容

### 1. residual-shape sequence の length

```lean
theorem orbitWindowResidualShapeSeq_length
    (n : OddNat) (k : ℕ) :
    (orbitWindowResidualShapeSeq n k).length = k := by
  unfold orbitWindowResidualShapeSeq
  simp
```

これは軽いが重要。
後で `get?` や `take` を使うときの土台になる。

### 2. residual-shape sequence の get? 補題

```lean
theorem orbitWindowResidualShapeSeq_get?_eq_some
    (n : OddNat) (k i : ℕ)
    (hi : i < k) :
    (orbitWindowResidualShapeSeq n k).get? i =
      some (orbitWindowResidualShape n i) := by
  unfold orbitWindowResidualShapeSeq
  simp [List.get?_map, hi]
```

Lean の `List.get?` API によっては `simp` だけで閉じる可能性がある。
詰まる場合は、既存の `orbitWindowHeightSeq_get?_eq_some` があるか探して、それに合わせるのが良い。

### 3. shifted label としての get? 補題

`orbitWindowResidualShapeSeq_eq_shifted_oddOrbitLabels` を使い、

```lean
theorem orbitWindowResidualShapeSeq_get?_eq_some_shifted_label
    (n : OddNat) (k i : ℕ)
    (hi : i < k) :
    (orbitWindowResidualShapeSeq n k).get? i =
      some (oddOrbitLabel n (i + 1)) := by
  rw [orbitWindowResidualShapeSeq_eq_shifted_oddOrbitLabels]
  -- use List.get?_map / hi
  sorry
```

これは、residual profile が shifted label profile であることを list API でも使えるようにする補題じゃ。

### 4. take length

```lean
theorem orbitWindowResidualShapeSeq_take_length
    (n : OddNat) (k m : ℕ) :
    ((orbitWindowResidualShapeSeq n k).take m).length = min m k := by
  rw [List.length_take]
  rw [orbitWindowResidualShapeSeq_length]
```

### 5. take get? 補題

```lean
theorem orbitWindowResidualShapeSeq_take_get?_eq_some
    (n : OddNat) (k m i : ℕ)
    (hi : i < m)
    (hik : i < k) :
    ((orbitWindowResidualShapeSeq n k).take m).get? i =
      some (orbitWindowResidualShape n i) := by
  -- use List.get?_take and orbitWindowResidualShapeSeq_get?_eq_some
  sorry
```

これは少し API 探索が必要かもしれない。
難しければ、まず `get?` 本体だけで十分じゃ。

## 一歩先ゆく推論

ここから先は、residual shape profile と pressure sign profile を接続する段階に入る。

現状では、

```text
height profile
residual-shape profile
pressure-margin profile
```

が別々に存在している。

次に欲しいのは、この三つを同じ window index 上で並べることじゃ。

```text
i:
  label_i
  height_i
  residual_i = label_{i+1}
  first_failed_depth_i
  pressure_margin_depth_j
```

ここで注意すべきは、`i` と `j` が別軸であること。

`i` は orbit window の時間方向。
`j` は pressure depth の解像度方向。

つまり、次に現れる本物の構造は二次元じゃ。

```text
time index i
depth index j
```

ここを混ぜると危ない。
逆に、ここを整理できれば非常に強い。

賢狼の推論では、今後の本命はこうなる。

```text
ResidualShapeWindow:
  時間方向の形状遷移

PressureSignProfile:
  深さ方向の margin 符号列

ShapePressureGrid:
  時間 i × 深さ j の有限観測格子
```

この `ShapePressureGrid` 的な構造ができると、Collatz の「相対スケール調整」がかなり見やすくなる。

## さらなる次の一手

checkpoint 128 で residual-shape list API を整えたら、checkpoint 129 では pressure sign-pattern classification に戻るのが良い。

ただし、いきなり `SourcePressureIsland` を巨大にしない。
まずは軽い margin equivalence から。

### `SourcePressureLocalIsland` の margin 同値

既に predicate はあるので、次は margin 版。

```lean
theorem sourcePressureLocalIsland_iff_margin
    (n : OddNat) (k r j : ℕ) :
    SourcePressureLocalIsland n k r j ↔
      0 < j ∧
        0 < SourcePressureMarginInt n k (r + j) ∧
        SourcePressureMarginInt n k (r + (j - 1)) ≤ 0 ∧
        SourcePressureMarginInt n k (r + (j + 1)) ≤ 0 := by
  unfold SourcePressureLocalIsland
  constructor
  · intro h
    rcases h with ⟨hj, hsel, hprev_not, hnext_not⟩
    constructor
    · exact hj
    constructor
    · exact (isSourcePressureDepth_iff_margin_pos n k r j).1 hsel
    constructor
    · have hnotpos :
          ¬ 0 < SourcePressureMarginInt n k (r + (j - 1)) := by
        intro hpos
        exact hprev_not ((isSourcePressureDepth_iff_margin_pos n k r (j - 1)).2 hpos)
      omega
    · have hnotpos :
          ¬ 0 < SourcePressureMarginInt n k (r + (j + 1)) := by
        intro hpos
        exact hnext_not ((isSourcePressureDepth_iff_margin_pos n k r (j + 1)).2 hpos)
      omega
  · intro h
    rcases h with ⟨hj, hpos, hprev_nonpos, hnext_nonpos⟩
    constructor
    · exact hj
    constructor
    · exact (isSourcePressureDepth_iff_margin_pos n k r j).2 hpos
    constructor
    · intro hprev
      have hp := (isSourcePressureDepth_iff_margin_pos n k r (j - 1)).1 hprev
      omega
    · intro hnext
      have hp := (isSourcePressureDepth_iff_margin_pos n k r (j + 1)).1 hnext
      omega
```

これは `sourcePressurePrefixFailure_iff_margin` や `sourcePressureFrontier_iff_margin` と同じ型なので、通る可能性が高い。

### `SourcePressureSignChangeUp` と frontier の逆向きは慎重に

`sourcePressureSignChangeUp_of_frontier_pos` はすでにある。
しかし逆向き、

```text
signChangeUp -> frontier
```

は一般には言えない。
なぜなら、それ以前に別の positive margin がある可能性があるからじゃ。

必要なら条件付きで、

```lean
def NoPositivePressureBefore
    (n : OddNat) (k r j : ℕ) : Prop :=
  ∀ i, i < j → ¬ IsSourcePressureDepth n k r i
```

を置いてから、

```lean
theorem sourcePressureFrontier_of_signChangeUp_of_noPositiveBefore
```

を作る方が安全じゃ。

## 賢狼が試して欲しい実験補題

## 実験 A: residual-shape seq length

```lean
theorem orbitWindowResidualShapeSeq_length
    (n : OddNat) (k : ℕ) :
    (orbitWindowResidualShapeSeq n k).length = k := by
  unfold orbitWindowResidualShapeSeq
  simp
```

## 実験 B: residual-shape seq get?

```lean
theorem orbitWindowResidualShapeSeq_get?_eq_some
    (n : OddNat) (k i : ℕ)
    (hi : i < k) :
    (orbitWindowResidualShapeSeq n k).get? i =
      some (orbitWindowResidualShape n i) := by
  unfold orbitWindowResidualShapeSeq
  -- Try simp first.
  simp [hi]
```

もし `simp [hi]` で閉じなければ、既存の height sequence 補題を検索して同じ proof style を使う。

## 実験 C: residual-shape seq get? shifted

```lean
theorem orbitWindowResidualShapeSeq_get?_eq_some_shifted_label
    (n : OddNat) (k i : ℕ)
    (hi : i < k) :
    (orbitWindowResidualShapeSeq n k).get? i =
      some (oddOrbitLabel n (i + 1)) := by
  rw [orbitWindowResidualShapeSeq_eq_shifted_oddOrbitLabels]
  simp [hi]
```

## 実験 D: take length

```lean
theorem orbitWindowResidualShapeSeq_take_length
    (n : OddNat) (k m : ℕ) :
    ((orbitWindowResidualShapeSeq n k).take m).length = min m k := by
  rw [List.length_take]
  rw [orbitWindowResidualShapeSeq_length]
```

## 実験 E: take get?

```lean
theorem orbitWindowResidualShapeSeq_take_get?_eq_some
    (n : OddNat) (k m i : ℕ)
    (hi : i < m)
    (hik : i < k) :
    ((orbitWindowResidualShapeSeq n k).take m).get? i =
      some (orbitWindowResidualShape n i) := by
  -- Try:
  rw [List.get?_take]
  · exact orbitWindowResidualShapeSeq_get?_eq_some n k i hik
  · exact hi
```

Lean の `List.get?_take` の形が違う可能性があるので、詰まれば theorem 名探索。

## 実験 F: first failed depth sequence

```lean
noncomputable def orbitWindowFirstFailedPow2DepthSeq
    (n : OddNat) (k : ℕ) : List ℕ :=
  (List.range k).map (orbitWindowFirstFailedPow2Depth n)
```

```lean
theorem orbitWindowFirstFailedPow2DepthSeq_length
    (n : OddNat) (k : ℕ) :
    (orbitWindowFirstFailedPow2DepthSeq n k).length = k := by
  unfold orbitWindowFirstFailedPow2DepthSeq
  simp
```

## 実験 G: first failed depth equals height + 1 in window

```lean
theorem orbitWindowFirstFailedPow2Depth_eq_height_add_one
    (n : OddNat) (i : ℕ) :
    orbitWindowFirstFailedPow2Depth n i = orbitWindowHeight n i + 1 := by
  unfold orbitWindowFirstFailedPow2Depth FirstFailedPow2Depth
  rw [orbitWindowHeight_eq_rawGnomonHeight_oddOrbitLabel]
```

これはかなり良い補題じゃ。
`first failed depth` が window height の単なる `+1` であることを window 側で固定できる。

## 実験 H: local island margin equivalence

```lean
theorem sourcePressureLocalIsland_iff_margin
    (n : OddNat) (k r j : ℕ) :
    SourcePressureLocalIsland n k r j ↔
      0 < j ∧
        0 < SourcePressureMarginInt n k (r + j) ∧
        SourcePressureMarginInt n k (r + (j - 1)) ≤ 0 ∧
        SourcePressureMarginInt n k (r + (j + 1)) ≤ 0 := by
  -- same proof pattern as sourcePressureFrontier_iff_margin
  sorry
```

## Python 側の次観測

checkpoint 128 では、Python summary に residual-shape sequence の統計を追加するとよい。

```text
residual_shape_seq
shifted_label_seq
residual_eq_shifted_labels
first_failed_depth_seq
height_seq
first_failed_eq_height_plus_one
```

pressure 側はまだ巨大 CSV にせず、summary でよい。

```text
positive_depths
positive_blocks
local_islands
sign_change_up_positions
first_frontier_depth
frontier_margin
first_failure_pair
margin_jump
retention_drop
continuation_drop
```

特に見たいのは、

```text
local_islands がどの程度あるか
positive block は連続区間になりやすいか
frontier 後に positive が継続するか
sign-change-up が単発か連鎖か
```

## 次の指示まとめ

Codex への次指示はこうじゃ。

```text
Checkpoint 128:
Prefer Route A one more time.

Goal:
  Make residual-shape sequence as ergonomic as height sequence.

Implement:
  orbitWindowResidualShapeSeq_length
  orbitWindowResidualShapeSeq_get?_eq_some
  orbitWindowResidualShapeSeq_get?_eq_some_shifted_label
  orbitWindowResidualShapeSeq_take_length
  orbitWindowResidualShapeSeq_take_get?_eq_some

Also add:
  orbitWindowFirstFailedPow2DepthSeq
  orbitWindowFirstFailedPow2DepthSeq_length
  orbitWindowFirstFailedPow2Depth_eq_height_add_one

If time permits:
  sourcePressureLocalIsland_iff_margin

Do not:
  introduce Real.log
  claim pressure prefix
  add heavy island/block theory before Python classification
```

## 総括

checkpoint `127` は成功じゃ。
Route A の流れは、

```text
pointwise residual shape = T
window residual shape = next odd label
residual-shape sequence = shifted label sequence
```

まで来た。

次は residual-shape sequence API を整える。
ここが整えば、height profile と residual-shape profile を同じ水準で扱えるようになる。

その後に pressure sign pattern へ戻れば、単なる margin 列ではなく、

```text
residual-shape finite dynamics 上の pressure island / frontier
```

として定義できる。

この順番が良い。
急がず、形状列の API を一段固めるのが次の正着じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index a3a30391..323808b9 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -123,6 +123,34 @@ form of the sequence summed by `sumS`.
 noncomputable def orbitWindowHeightSeq (n : OddNat) (k : ℕ) : List ℕ :=
   (List.range k).map (orbitWindowHeight n)
 
+/--
+Residual shape extracted at the `i`-th accelerated Collatz odd-state label.
+
+This is a window-level lift of `RawGnomonResidualShape`; the low-level gnomon
+vocabulary stays in `GnomonEvaluation`, while this definition records the
+finite-window observation.
+-/
+noncomputable def orbitWindowResidualShape (n : OddNat) (i : ℕ) : ℕ :=
+  RawGnomonResidualShape (oddOrbitLabel n i)
+
+/--
+The ordered residual-shape profile observed in the first `k` accelerated
+Collatz states.
+
+Checkpoint 127 reads the orbit window as a finite chain of residual-shape
+extractions.
+-/
+noncomputable def orbitWindowResidualShapeSeq (n : OddNat) (k : ℕ) : List ℕ :=
+  (List.range k).map (orbitWindowResidualShape n)
+
+/--
+First failed power-of-two alignment depth at the `i`-th observed odd label.
+
+This is the window-level version of `FirstFailedPow2Depth`.
+-/
+noncomputable def orbitWindowFirstFailedPow2Depth (n : OddNat) (i : ℕ) : ℕ :=
+  FirstFailedPow2Depth (oddOrbitLabel n i)
+
 /--
 The first `k` accelerated Collatz odd-state labels are pairwise separated.
 
@@ -4677,6 +4705,59 @@ theorem oddOrbitLabel_succ_eq_T_iterateT
   unfold oddOrbitLabel
   rw [iterateT_succ_eq_T_iterateT]
 
+/--
+The residual shape extracted at index `i` is the next odd orbit label.
+
+This is the checkpoint-127 window lift of
+`rawGnomonResidualShape_eq_T_val`.
+-/
+theorem orbitWindowResidualShape_eq_oddOrbitLabel_succ
+    (n : OddNat) (i : ℕ) :
+    orbitWindowResidualShape n i = oddOrbitLabel n (i + 1) := by
+  unfold orbitWindowResidualShape oddOrbitLabel
+  rw [rawGnomonResidualShape_eq_T_val (iterateT i n)]
+  rw [iterateT_succ_eq_T_iterateT]
+
+/--
+The residual-shape sequence is exactly the shifted odd-label sequence.
+
+This records that a finite orbit window is a chain of residual-shape
+extractions.
+-/
+theorem orbitWindowResidualShapeSeq_eq_shifted_oddOrbitLabels
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidualShapeSeq n k =
+      (List.range k).map (fun i => oddOrbitLabel n (i + 1)) := by
+  unfold orbitWindowResidualShapeSeq
+  apply List.map_congr_left
+  intro i _hi
+  exact orbitWindowResidualShape_eq_oddOrbitLabel_succ n i
+
+/--
+Window-level raw gnomon factorization.
+
+At each observed label, the raw gnomon step decomposes into the observed
+window height and the residual shape that becomes the next label.
+-/
+theorem orbitWindow_rawGnomonStep_factor
+    (n : OddNat) (i : ℕ) :
+    RawGnomonStep (oddOrbitLabel n i) =
+      2 ^ orbitWindowHeight n i * orbitWindowResidualShape n i := by
+  rw [orbitWindowHeight_eq_rawGnomonHeight_oddOrbitLabel]
+  unfold orbitWindowResidualShape oddOrbitLabel
+  exact rawGnomonStep_eq_pow_height_mul_residualShape (iterateT i n)
+
+/--
+The first failed depth in the finite window has nonzero raw gnomon remainder.
+-/
+theorem orbitWindow_firstFailed_remainder_ne_zero
+    (n : OddNat) (i : ℕ) :
+    RawGnomonRemainderAtDepth
+        (oddOrbitLabel n i)
+        (orbitWindowFirstFailedPow2Depth n i) ≠ 0 := by
+  unfold orbitWindowFirstFailedPow2Depth oddOrbitLabel
+  exact rawGnomonRemainderAtDepth_firstFailed_ne_zero (iterateT i n)
+
 /--
 Label-sequence transition from the `3 mod 8` height-one channel.
 
@@ -6809,6 +6890,19 @@ theorem downClosed_iff_no_prefixFailure
     · exact hshallow
     · exact False.elim (hno j₁ j₂ hlt hj₂ ⟨hlt, hshallow, hdeep⟩)
 
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
 /--
 The first selected source-pressure depth.
 
@@ -6869,6 +6963,49 @@ theorem sourcePressurePrefixFailure_of_frontier_pos
     · exact hfront.2 0 hj
     · exact hfront.1
 
+/--
+A positive frontier produces an upward sign change at the previous depth.
+
+This is a local margin view of
+`sourcePressurePrefixFailure_of_frontier_pos`.
+-/
+theorem sourcePressureSignChangeUp_of_frontier_pos
+    (n : OddNat) (k r j : ℕ)
+    (hfront : SourcePressureFrontier n k r j)
+    (hj : 0 < j) :
+    SourcePressureSignChangeUp n k r (j - 1) := by
+  unfold SourcePressureSignChangeUp
+  have hprev_not : ¬ IsSourcePressureDepth n k r (j - 1) := by
+    exact hfront.2 (j - 1) (Nat.sub_lt hj Nat.zero_lt_one)
+  have hprev_nonpos :
+      SourcePressureMarginInt n k (r + (j - 1)) ≤ 0 := by
+    have hnotpos :
+        ¬ 0 < SourcePressureMarginInt n k (r + (j - 1)) := by
+      intro hpos
+      exact hprev_not
+        ((isSourcePressureDepth_iff_margin_pos n k r (j - 1)).2 hpos)
+    omega
+  have hj_pos :
+      0 < SourcePressureMarginInt n k (r + j) :=
+    (isSourcePressureDepth_iff_margin_pos n k r j).1 hfront.1
+  constructor
+  · exact hprev_nonpos
+  · have hidx : r + (j - 1) + 1 = r + j := by omega
+    simpa [hidx] using hj_pos
+
+/--
+Local isolated positive source-pressure depth.
+
+This is deliberately only a predicate.  Margin equivalences and count theorems
+should be added after numerical scans show which island shapes actually matter.
+-/
+def SourcePressureLocalIsland
+    (n : OddNat) (k r j : ℕ) : Prop :=
+  0 < j ∧
+    IsSourcePressureDepth n k r j ∧
+    ¬ IsSourcePressureDepth n k r (j - 1) ∧
+    ¬ IsSourcePressureDepth n k r (j + 1)
+
 /-- The empty selected-pressure prefix is always available. -/
 theorem selectedPressurePrefix_zero
     (n : OddNat) (k r len : ℕ) :
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index ffe4a645..abc040f3 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -142,6 +142,9 @@ OrbitWindow
 oddOrbitLabel
 orbitWindowHeight
 orbitWindowHeightSeq
+orbitWindowResidualShape
+orbitWindowResidualShapeSeq
+orbitWindowFirstFailedPow2Depth
 orbitWindowResidueCountPow2
 orbitWindowResidueCountPow2Tail
 sourcePow2Distribution_total
@@ -153,6 +156,8 @@ SourcePressureMarginInt
 SourcePressurePrefixFailure
 SourcePressureSelectedSetDownClosed
 SourcePressureFrontier
+SourcePressureSignChangeUp
+SourcePressureLocalIsland
 ```
 
 The central No.100 layer is:
@@ -209,6 +214,7 @@ docs/Collatz-ContinuationNesting-123.md
 docs/Collatz-PressureMargin-124.md
 docs/Collatz-GnomonEvaluation-125.md
 docs/Collatz-GnomonResidualShape-126.md
+docs/Collatz-WindowResidualShape-127.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-GnomonResidualShape-126.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-GnomonResidualShape-126.md
index 9728c161..c633dacb 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-GnomonResidualShape-126.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-GnomonResidualShape-126.md
@@ -149,3 +149,34 @@ continuation drop
 
 The recommended next checkpoint depends on whether the reviewer wants more
 shape dynamics or more pressure-profile classification.
+
+## Checkpoint 127 Follow-up
+
+Checkpoint 127 takes the recommended shape-dynamics route.
+
+New window names:
+
+```lean
+orbitWindowResidualShape
+orbitWindowResidualShapeSeq
+orbitWindowFirstFailedPow2Depth
+```
+
+Main theorem:
+
+```lean
+orbitWindowResidualShape_eq_oddOrbitLabel_succ
+```
+
+Meaning:
+
+```text
+residual shape extracted at window index i
+  = odd label at window index i+1
+```
+
+This lifts the pointwise residual-shape bridge into finite orbit windows.  See:
+
+```text
+Collatz-WindowResidualShape-127.md
+```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index 9940b949..de72734e 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -106,6 +106,45 @@ connects the ordered list back to the accumulated Collatz height:
 (orbitWindowHeightSeq n k).sum = sumS n k
 ```
 
+### `orbitWindowResidualShape`
+
+```lean
+orbitWindowResidualShape n i
+```
+
+This is the residual shape extracted from the `i`-th observed odd label:
+
+```text
+RawGnomonResidualShape (oddOrbitLabel n i)
+```
+
+Checkpoint 127 proves:
+
+```lean
+orbitWindowResidualShape_eq_oddOrbitLabel_succ
+```
+
+meaning:
+
+```text
+orbitWindowResidualShape n i = oddOrbitLabel n (i+1)
+```
+
+So the finite window can be read as a residual-shape chain.
+
+### `orbitWindowResidualShapeSeq`
+
+```lean
+orbitWindowResidualShapeSeq n k
+```
+
+This is the ordered list of residual shapes extracted in the first `k`
+positions.  It agrees with the shifted odd-label list by:
+
+```lean
+orbitWindowResidualShapeSeq_eq_shifted_oddOrbitLabels
+```
+
 ## Separation And Collision
 
 The bridge includes a finite split:
@@ -207,6 +246,17 @@ sourcePressurePrefixFailure_of_frontier_pos
 depth.  It is a first-positive-margin statement, not a claim that later depths
 continue as a prefix.
 
+Checkpoint 127 adds:
+
+```lean
+SourcePressureSignChangeUp
+sourcePressureSignChangeUp_of_frontier_pos
+SourcePressureLocalIsland
+```
+
+These are observation predicates for margin sign profiles.  They should be
+used to classify pressure islands before proposing any new monotonicity theorem.
+
 ## Residue Counts
 
 Named residue counts exist for low layers:
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 8735df6b..60aaeef4 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -116,6 +116,8 @@ OrbitWindow n k = Finset.range k
 oddOrbitLabel n i = the natural value of iterateT i n
 orbitWindowHeight n i = v2 (3 * oddOrbitLabel n i + 1)
 orbitWindowHeightSeq n k = the ordered list of the first k height labels
+orbitWindowResidualShape n i = residual shape extracted from oddOrbitLabel n i
+orbitWindowResidualShapeSeq n k = ordered residual-shape profile
 ```
 
 Checkpoint 125 adds the pressure-obstruction surface:
@@ -157,6 +159,25 @@ So a window height can now be read as:
 RawGnomonHeight of the observed odd label
 ```
 
+Checkpoint 127 lifts residual shape extraction to windows:
+
+```lean
+orbitWindowResidualShape_eq_oddOrbitLabel_succ
+orbitWindowResidualShapeSeq_eq_shifted_oddOrbitLabels
+orbitWindow_rawGnomonStep_factor
+orbitWindow_firstFailed_remainder_ne_zero
+```
+
+The finite window now supports the reading:
+
+```text
+label_i
+  -> RawGnomonStep
+  -> orbitWindowHeight
+  -> orbitWindowResidualShape
+  -> label_{i+1}
+```
+
 The first theorem set is deliberately thin:
 
 ```lean
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-WindowResidualShape-127.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-WindowResidualShape-127.md
new file mode 100644
index 00000000..d73369f2
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-WindowResidualShape-127.md
@@ -0,0 +1,176 @@
+# Collatz Window Residual Shape - Checkpoint 127
+
+Checkpoint 127 lifts the pointwise residual-shape bridge to finite orbit
+windows.
+
+Checkpoint 126 proved:
+
+```text
+RawGnomonResidualShape n.val = (T n).val
+```
+
+Checkpoint 127 turns this into a window statement:
+
+```text
+the residual shape extracted at index i is the odd label at index i+1
+```
+
+## New Window Vocabulary
+
+```lean
+orbitWindowResidualShape
+orbitWindowResidualShapeSeq
+orbitWindowFirstFailedPow2Depth
+```
+
+The definitions are window-level lifts:
+
+```text
+orbitWindowResidualShape n i
+  = RawGnomonResidualShape (oddOrbitLabel n i)
+
+orbitWindowResidualShapeSeq n k
+  = map orbitWindowResidualShape over List.range k
+
+orbitWindowFirstFailedPow2Depth n i
+  = FirstFailedPow2Depth (oddOrbitLabel n i)
+```
+
+These definitions deliberately live in `PetalBridge`, because they depend on
+the finite window label `oddOrbitLabel`.  The low-level arithmetic remains in
+`GnomonEvaluation`.
+
+## Main Theorem
+
+```lean
+orbitWindowResidualShape_eq_oddOrbitLabel_succ
+```
+
+Meaning:
+
+```text
+orbitWindowResidualShape n i = oddOrbitLabel n (i + 1)
+```
+
+This is the core checkpoint-127 result.  The finite orbit window is now a chain
+of residual-shape extractions:
+
+```text
+label_i
+  -> raw gnomon step
+  -> power-of-two alignment height
+  -> residual shape
+  -> label_{i+1}
+```
+
+## Sequence Bridge
+
+```lean
+orbitWindowResidualShapeSeq_eq_shifted_oddOrbitLabels
+```
+
+Meaning:
+
+```text
+residual shape profile over k indices
+  = shifted odd-label profile over k indices
+```
+
+This will be the natural starting point for later finite statistics on
+residual shapes.
+
+## Window Factorization
+
+```lean
+orbitWindow_rawGnomonStep_factor
+```
+
+At each window index:
+
+```text
+RawGnomonStep (oddOrbitLabel n i)
+  = 2 ^ orbitWindowHeight n i * orbitWindowResidualShape n i
+```
+
+This is the finite-window version of the pointwise factorization from
+checkpoint 126.
+
+## First Failed Depth
+
+```lean
+orbitWindow_firstFailed_remainder_ne_zero
+```
+
+At each observed odd label, the first failed power-of-two depth has nonzero
+remainder.  The window therefore carries both:
+
+```text
+alignment depth:
+  orbitWindowHeight n i
+
+first failed depth:
+  orbitWindowFirstFailedPow2Depth n i
+```
+
+## Pressure Sign Pattern Starter
+
+Checkpoint 127 also adds the first thin sign-pattern predicates:
+
+```lean
+SourcePressureSignChangeUp
+sourcePressureSignChangeUp_of_frontier_pos
+SourcePressureLocalIsland
+```
+
+These do not prove any pressure-prefix theorem.  They simply name local
+features of the margin profile:
+
+```text
+sign change up:
+  margin(j) <= 0 and margin(j+1) > 0
+
+local island:
+  depth j is positive, but j-1 and j+1 are not selected
+```
+
+The next pressure checkpoint should be driven by numerical classification of
+margin profiles, not by an assumed monotonicity law.
+
+## Next Work
+
+Two natural next directions remain.
+
+### Residual Shape Statistics
+
+Build counts or profiles over:
+
+```text
+orbitWindowResidualShapeSeq
+orbitWindowFirstFailedPow2Depth
+```
+
+Possible names:
+
+```lean
+orbitWindowResidualShapeSeq_length
+orbitWindowResidualShapeSeq_get?_eq_some
+orbitWindowFirstFailedDepthSeq
+```
+
+### Pressure Pattern Classification
+
+Use Python summary scans to classify:
+
+```text
+first_frontier_depth
+frontier_margin
+positive_depths
+positive_blocks
+local_islands
+first_failure_pair
+margin_jump
+retention_drop
+continuation_drop
+```
+
+Then add only the predicates that survive as useful theorem interfaces.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-127.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-127.md
new file mode 100644
index 00000000..4f669171
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-127.md
@@ -0,0 +1,210 @@
+# Report Petal 127
+
+## Summary
+
+Checkpoint 127 lifts the pointwise residual-shape theorem into finite orbit
+windows.
+
+Checkpoint 126 closed:
+
+```text
+RawGnomonResidualShape n.val = (T n).val
+```
+
+Checkpoint 127 closes:
+
+```text
+orbitWindowResidualShape n i = oddOrbitLabel n (i + 1)
+```
+
+So a finite Collatz observation window can now be read as a finite chain of
+residual-shape extractions.
+
+## Code Changes
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+New window definitions:
+
+```lean
+orbitWindowResidualShape
+orbitWindowResidualShapeSeq
+orbitWindowFirstFailedPow2Depth
+```
+
+New window bridge theorems:
+
+```lean
+orbitWindowResidualShape_eq_oddOrbitLabel_succ
+orbitWindowResidualShapeSeq_eq_shifted_oddOrbitLabels
+orbitWindow_rawGnomonStep_factor
+orbitWindow_firstFailed_remainder_ne_zero
+```
+
+The key theorem is:
+
+```lean
+orbitWindowResidualShape_eq_oddOrbitLabel_succ
+```
+
+Meaning:
+
+```text
+the residual shape extracted from the current odd label is the next odd label
+```
+
+## Pressure Additions
+
+Checkpoint 127 also adds thin sign-pattern vocabulary:
+
+```lean
+SourcePressureSignChangeUp
+sourcePressureSignChangeUp_of_frontier_pos
+SourcePressureLocalIsland
+```
+
+This is intentionally modest.  These are observation predicates, not a pressure
+prefix theorem.
+
+The added theorem:
+
+```lean
+sourcePressureSignChangeUp_of_frontier_pos
+```
+
+shows that a positive frontier gives a local upward margin sign change at the
+previous depth.
+
+## Mathematical Reading
+
+The finite window now has the following verified structure at every index:
+
+```text
+label_i
+  -> RawGnomonStep label_i
+  -> orbitWindowHeight n i
+  -> orbitWindowResidualShape n i
+  -> label_{i+1}
+```
+
+The raw factorization theorem states:
+
+```text
+RawGnomonStep (label_i)
+  = 2 ^ orbitWindowHeight n i * orbitWindowResidualShape n i
+```
+
+Thus `PetalBridge` is no longer only a height/residue observation surface.  It
+now exposes the actual finite residual-shape dynamics of the accelerated
+Collatz orbit.
+
+## Documentation Changes
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/README.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-GnomonResidualShape-126.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+```
+
+Added:
+
+```text
+lean/dk_math/DkMath/Collatz/docs/Collatz-WindowResidualShape-127.md
+```
+
+## Verification
+
+Commands run:
+
+```text
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath.Collatz.Collatz2K26
+rg -n "\bsorry\b" touched Collatz Lean files
+git diff --check -- tracked touched files
+rg -n "[ \t]$" new files
+```
+
+All passed.  No new `sorry` was introduced in `PetalBridge.lean` or
+`GnomonEvaluation.lean`.
+
+The usual unrelated dependency warning may still appear when replaying
+`PetalBridge` dependencies:
+
+```text
+DkMath.NumberTheory.ZsigmondyCyclotomicResearch declaration uses sorry
+```
+
+## Inference
+
+The Route A chain is now:
+
+```text
+pointwise residual shape = T
+window residual shape = next odd label
+residual-shape sequence = shifted label sequence
+```
+
+This suggests that the next shape-dynamics checkpoint should add ordered
+profile helpers analogous to the existing height-profile helpers:
+
+```lean
+orbitWindowResidualShapeSeq_length
+orbitWindowResidualShapeSeq_get?_eq_some
+orbitWindowResidualShapeSeq_take_get?_eq_some
+```
+
+These would make residual-shape windows as ergonomic as height windows.
+
+## Suggested Next Checkpoint
+
+Two natural routes remain.
+
+### Route A: residual-shape sequence API
+
+Add list API:
+
+```lean
+orbitWindowResidualShapeSeq_length
+orbitWindowResidualShapeSeq_get?_eq_some
+orbitWindowResidualShapeSeq_take_length
+orbitWindowResidualShapeSeq_take_get?_eq_some
+```
+
+This is low risk and would mirror the established `orbitWindowHeightSeq` API.
+
+### Route B: pressure sign-pattern classification
+
+Use Python summaries to decide which predicates deserve theorem support:
+
+```text
+positive blocks
+local islands
+first frontier depth
+margin jump
+retention drop
+continuation drop
+```
+
+If continuing Route B in Lean, the next safe theorem is likely a margin
+equivalence for `SourcePressureLocalIsland`.
+
+## Recommendation
+
+Prefer Route A for one more checkpoint.
+
+Reason:
+
+```text
+The finite window now has residual-shape dynamics, but it still lacks the list
+helper API that made height profiles useful.
+```
+
+After the residual-shape list API exists, pressure-island statements can refer
+to a richer window surface rather than only to margins.
````
`````
