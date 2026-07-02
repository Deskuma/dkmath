# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 5bf6f3c2b3a999cadd16f404faa09614d5f46527

## Report

checkpoint 126 を実装しました。

Route A を優先して、[GnomonEvaluation.lean](/lean/dk_math/DkMath/Collatz/GnomonEvaluation.lean:222) に `RawGnomonResidualShape = (T n).1` を固定しました。そこから `rawGnomonResidualShape_odd`、完全分解 `RawGnomonStep = 2^height * residualShape`、`height + 1` で割れない補題、first failed depth の remainder 非零まで閉じています。

`PetalBridge` 側には、[orbitWindowHeight_eq_rawGnomonHeight_oddOrbitLabel](/lean/dk_math/DkMath/Collatz/PetalBridge.lean:170) を追加し、window height を gnomon alignment height として読めるようにしました。さらに Route B の軽い入口として [SourcePressureFrontier](/lean/dk_math/DkMath/Collatz/PetalBridge.lean:6819)、margin 同値、frontier から prefix failure を作る補題も入れています。

ドキュメントは `README`、`Collatz-GnomonEvaluation-125.md`、PetalBridge guide/status を更新し、新規に [Collatz-GnomonResidualShape-126.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-GnomonResidualShape-126.md:1) と [report-petal-126.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-126.md:1) を作成しました。

検証済み:
`lake build DkMath.Collatz.GnomonEvaluation`
`lake build DkMath.Collatz.PetalBridge`
`lake build DkMath.Collatz.Collatz2K26`

今回触った Collatz Lean ファイルに新規 `sorry` はありません。既存依存の `ZsigmondyCyclotomicResearch` の warning は今回範囲外です。

## Review

## 状況分析

うむ。今回の `review-petal-127.md` は、内容としては **checkpoint 126 の実装レビュー**じゃな。
前回こちらが提案した Route A、つまり `RawGnomonResidualShape` を既存の accelerated map `T` に接続する作業が、きれいに閉じている。

一番大きい成果はこれ。

```lean
rawGnomonResidualShape_eq_T_val
```

これにより、checkpoint 125 で導入した

```text
奇数グノモン補正
  -> 2進整列評価
  -> residual shape 抽出
```

という新語彙が、単なる説明ではなく、既存の `T` と形式的に同一化された。さらに `rawGnomonResidualShape_odd`、完全分解 `RawGnomonStep = 2^height * residualShape`、`height + 1` で割れない補題、first failed depth の remainder 非零まで閉じている。

つまり、これで Collatz の odd step は Lean 上でこう読める。

```text
RawGnomonStep:
  奇数グノモン補正後の raw 値

RawGnomonHeight:
  2^h への整列深度

RawGnomonResidualShape:
  2進整列分を除去した次の奇数形状

T:
  その residual shape を次状態として扱う既存 accelerated map
```

ここまで来ると、かなり強い。
いまや `GnomonEvaluation` は「比喩」ではなく、Collatz accelerated dynamics の正式な別表現になった。

## レビュー

## 良い点

第一に、`rawGnomonResidualShape_eq_T_val` が `rfl` 近くで閉じているのが非常に良い。これは、設計が既存定義と自然に一致していたことを意味する。無理に作った橋ではなく、元から同じ構造だったものに名前を与えた形じゃ。

第二に、`rawGnomonStep_eq_pow_height_mul_residualShape` が入ったことで、

```text
raw = 2^height * residual
```

という完全分解が得られた。これにより、`height` は単なる観測値ではなく、raw 形状から residual shape を抽出する分解係数になった。

第三に、

```lean
two_pow_succ_rawGnomonHeight_not_dvd
rawGnomonRemainderAtDepth_firstFailed_ne_zero
```

が入ったことで、alignment boundary が片側ではなく両側から閉じた。

つまり、

```text
j <= height:
  remainder = 0

j = height + 1:
  remainder != 0
```

が Lean で固定された。これは「first failed depth」という名前に実体を与えている。

第四に、`PetalBridge` 側の

```lean
orbitWindowHeight_eq_rawGnomonHeight_oddOrbitLabel
```

が良い。これで finite window の height 観測も、点ごとの gnomon alignment height として読めるようになった。

第五に、Route B を広げすぎず、`SourcePressureFrontier` だけを追加したのも良い判断じゃ。frontier は「最初の正 margin」であり、prefix theorem ではない。この線引きが今後かなり重要になる。

## 注意点

次に気をつけるべきことは、`SourcePressureFrontier` を入れたからといって、まだ pressure island の分類ができたわけではない、という点じゃ。

現在あるのは、

```text
frontier:
  first positive margin
```

まで。

まだ無いのは、

```text
island:
  正 margin が孤立している

block:
  正 margin が連続区間を作る

prefix:
  0 から m まで全部正

gap:
  正 margin の後に非正 margin が戻る
```

という符号列の形状分類じゃ。

だから次 checkpoint でいきなり「pressure はこう動く」と言わず、まず residual-shape window profile を作るのが正しい。

## 解説

今回の checkpoint 126 で、Collatz の一段はこう完全に整理された。

```text
1. odd label n を見る

2. OddGnomonLayer n = 2n+1 を足す

3. RawGnomonStep n = n + (2n+1) = 3n+1 を得る

4. RawGnomonHeight n = v2(raw) で 2進整列深度を測る

5. RawGnomonResidualShape n = raw / 2^height を抽出する

6. その residual shape が、既存の T n の値そのものになる
```

ここで本質的なのは、`T` が「謎の Collatz 加速写像」ではなくなったことじゃ。

`T` は、

```text
グノモン補正後に、
2進整列分を除去して残った形状
```

である。

この読みを window に持ち上げると、軌道はこうなる。

```text
oddOrbitLabel n 0
  -> residual shape
  -> oddOrbitLabel n 1
  -> residual shape
  -> oddOrbitLabel n 2
  -> ...
```

つまり、軌道とは **residual shape extraction の反復列** じゃ。

この見方が入ると、`PetalBridge` の pressure/margin も単なる residue count ではなく、

```text
residual shape window の中で、
どの channel が retention に勝っているか
```

として読める。

## 次の指示

次 checkpoint は、レポートの推奨通り **Direction A を優先**でよい。

つまり次は、

```text
pointwise residual shape
```

を

```text
window residual shape profile
```

へ持ち上げる。

## Checkpoint 127 推奨内容

### 1. `orbitWindowResidualShape` を定義する

候補は `PetalBridge` 側。理由は `oddOrbitLabel` と finite window に依存するためじゃ。

```lean
noncomputable def orbitWindowResidualShape
    (n : OddNat) (i : ℕ) : ℕ :=
  RawGnomonResidualShape (oddOrbitLabel n i)
```

ただし、`oddOrbitLabel n i` がすでに `ℕ` ならこのままでよい。
もし `OddNat` なら `.1` を調整する。

### 2. window residual shape は次の odd label と一致する

本命 theorem。

```lean
theorem orbitWindowResidualShape_eq_oddOrbitLabel_succ
    (n : OddNat) (i : ℕ) :
    orbitWindowResidualShape n i = oddOrbitLabel n (i + 1) := by
  unfold orbitWindowResidualShape
  -- use rawGnomonResidualShape_eq_T_val
  -- use oddOrbitLabel / iterateT definitions
  sorry
```

これは非常に重要じゃ。

これが通ると、

```text
window の i 番目で抽出された residual shape が、
window の i+1 番目の odd label である
```

が固定される。

つまり、軌道窓は `ResidualShape` の連鎖になる。

### 3. `orbitWindowResidualShapeSeq` を定義する

```lean
noncomputable def orbitWindowResidualShapeSeq
    (n : OddNat) (k : ℕ) : List ℕ :=
  (List.range k).map (fun i => orbitWindowResidualShape n i)
```

既存の `orbitWindowHeightSeq` が `List` なのか `Finset` なのかに合わせる。

### 4. residual shape seq と shifted label seq の一致

```lean
theorem orbitWindowResidualShapeSeq_eq_tail_labels
    (n : OddNat) (k : ℕ) :
    orbitWindowResidualShapeSeq n k =
      (List.range k).map (fun i => oddOrbitLabel n (i + 1)) := by
  -- ext i / simp using orbitWindowResidualShape_eq_oddOrbitLabel_succ
  sorry
```

これはまず軽くて良い。

### 5. `orbitWindowHeight` と `orbitWindowResidualShape` の raw 分解

次に、window 版の完全分解を作る。

```lean
theorem orbitWindow_rawGnomonStep_factor
    (n : OddNat) (i : ℕ) :
    RawGnomonStep (oddOrbitLabel n i) =
      2 ^ orbitWindowHeight n i * orbitWindowResidualShape n i := by
  rw [orbitWindowHeight_eq_rawGnomonHeight_oddOrbitLabel]
  unfold orbitWindowResidualShape
  -- use rawGnomonStep_eq_pow_height_mul_residualShape
  -- may need OddNat wrapper for oddOrbitLabel
  sorry
```

型の都合で `oddOrbitLabel n i` から `OddNat` が必要になるなら、既存の `iterateT i n` を使う形に変更する。

## 一歩先ゆく推論

ここからさらに一歩先では、`pressure` の主語を次のように変えられる。

旧：

```text
retention と continuation の count 比較
```

新：

```text
residual shape window において、
浅い carrier に保持される形状と、
深い channel に継続する形状の margin 比較
```

このためには、まず window 内で

```text
label_i
height_i
residual_i = label_{i+1}
```

がそろっている必要がある。

checkpoint 126 で点wise には閉じた。
checkpoint 127 では window で閉じる。

その後、checkpoint 128 で pressure island へ進めるのがよい。

## さらなる次の一手

checkpoint 128 候補は、pressure sign-pattern classification じゃ。

定義候補は三つ。

### `SourcePressurePositiveBlock`

```lean
def SourcePressurePositiveBlock
    (n : OddNat) (k r a len : ℕ) : Prop :=
  0 < len ∧
    ∀ j, a ≤ j → j < a + len → IsSourcePressureDepth n k r j
```

これは「正 margin の連続区間」。

### `SourcePressureLocalIsland`

```lean
def SourcePressureLocalIsland
    (n : OddNat) (k r j : ℕ) : Prop :=
  0 < j ∧
    IsSourcePressureDepth n k r j ∧
    ¬ IsSourcePressureDepth n k r (j - 1) ∧
    ¬ IsSourcePressureDepth n k r (j + 1)
```

これは「孤立正 margin」。

### `SourcePressureSignChangeUp`

```lean
def SourcePressureSignChangeUp
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourcePressureMarginInt n k (r + j) ≤ 0 ∧
    0 < SourcePressureMarginInt n k (r + j + 1)
```

これは frontier / island の基本部品として使いやすい。

この三つのうち、最初に入れるなら `SourcePressureSignChangeUp` が軽い。
`LocalIsland` は `j - 1` が絡むので少し面倒。`PositiveBlock` は便利だが、後で境界条件が増える。

## 賢狼が試して欲しい実験補題

## 実験 A: window residual shape

```lean
noncomputable def orbitWindowResidualShape
    (n : OddNat) (i : ℕ) : ℕ :=
  RawGnomonResidualShape (oddOrbitLabel n i)
```

## 実験 B: residual shape equals next label

```lean
theorem orbitWindowResidualShape_eq_oddOrbitLabel_succ
    (n : OddNat) (i : ℕ) :
    orbitWindowResidualShape n i = oddOrbitLabel n (i + 1) := by
  unfold orbitWindowResidualShape
  -- likely:
  -- rw [rawGnomonResidualShape_eq_T_val]
  -- unfold oddOrbitLabel
  -- simp [Function.iterate_succ]
  sorry
```

もし `Function.iterate_succ` の向きで詰まるなら、既存の `oddOrbitLabel_succ` 系 theorem を探す方がよい。

## 実験 C: residual shape sequence

```lean
noncomputable def orbitWindowResidualShapeSeq
    (n : OddNat) (k : ℕ) : List ℕ :=
  (List.range k).map (fun i => orbitWindowResidualShape n i)
```

## 実験 D: residual shape seq equals shifted labels

```lean
theorem orbitWindowResidualShapeSeq_eq_shifted_oddOrbitLabels
    (n : OddNat) (k : ℕ) :
    orbitWindowResidualShapeSeq n k =
      (List.range k).map (fun i => oddOrbitLabel n (i + 1)) := by
  unfold orbitWindowResidualShapeSeq
  apply List.map_congr_left
  intro i hi
  exact orbitWindowResidualShape_eq_oddOrbitLabel_succ n i
```

必要なら `List.map_congr_left` の代わりに `simp` で。

## 実験 E: window raw factorization

```lean
theorem orbitWindow_rawGnomonStep_factor
    (n : OddNat) (i : ℕ) :
    RawGnomonStep (oddOrbitLabel n i) =
      2 ^ orbitWindowHeight n i * orbitWindowResidualShape n i := by
  rw [orbitWindowHeight_eq_rawGnomonHeight_oddOrbitLabel]
  unfold orbitWindowResidualShape
  -- use rawGnomonStep_eq_pow_height_mul_residualShape
  -- if needed, rewrite oddOrbitLabel n i as (Function.iterate T i n).1
  sorry
```

型が合わない場合は、以下の `OddNat` 版にする。

```lean
theorem orbitWindow_rawGnomonStep_factor_iterateT
    (n : OddNat) (i : ℕ) :
    RawGnomonStep ((Function.iterate T i n).1) =
      2 ^ orbitWindowHeight n i *
        RawGnomonResidualShape ((Function.iterate T i n).1) := by
  rw [orbitWindowHeight_eq_rawGnomonHeight_oddOrbitLabel]
  -- unfold oddOrbitLabel if needed
  exact rawGnomonStep_eq_pow_height_mul_residualShape
    (Function.iterate T i n)
```

## 実験 F: first failed depth window lift

```lean
noncomputable def orbitWindowFirstFailedPow2Depth
    (n : OddNat) (i : ℕ) : ℕ :=
  FirstFailedPow2Depth (oddOrbitLabel n i)
```

```lean
theorem orbitWindow_firstFailed_remainder_ne_zero
    (n : OddNat) (i : ℕ) :
    RawGnomonRemainderAtDepth
        (oddOrbitLabel n i)
        (orbitWindowFirstFailedPow2Depth n i) ≠ 0 := by
  unfold orbitWindowFirstFailedPow2Depth
  -- use rawGnomonRemainderAtDepth_firstFailed_ne_zero on iterateT i n
  sorry
```

## 実験 G: sign-change-up

Route B 用に軽い predicate。

```lean
def SourcePressureSignChangeUp
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourcePressureMarginInt n k (r + j) ≤ 0 ∧
    0 < SourcePressureMarginInt n k (r + j + 1)
```

frontier から sign-change が得られるのは、`j = frontier - 1` の形になるため、まずは単独定義でよい。

## 実験 H: local island

```lean
def SourcePressureLocalIsland
    (n : OddNat) (k r j : ℕ) : Prop :=
  0 < j ∧
    IsSourcePressureDepth n k r j ∧
    ¬ IsSourcePressureDepth n k r (j - 1) ∧
    ¬ IsSourcePressureDepth n k r (j + 1)
```

margin 版は後でよい。まず predicate だけ。

## Python 側の次観測

checkpoint 127 では Python 側にも window residual shape を入れる。

```text
label_i
raw_i
height_i
residual_i
label_succ_i
residual_eq_label_succ
first_failed_depth_i
first_failed_remainder_i
```

ここで `residual_eq_label_succ` は常に true のはず。
Lean theorem と Python 観測が一致する確認列じゃ。

pressure 側は、次に以下を追加。

```text
first_frontier_depth
frontier_margin
positive_depths
positive_blocks
local_islands
first_failure_pair
margin_jump
retention_drop
continuation_drop
```

ただし、巨大 CSV は不要。summary markdown に統計だけでよい。

## 次の指示まとめ

Codex への次指示はこうじゃ。

```text
Checkpoint 127:
Prefer Direction A.

Goal:
  Lift residual-shape bridge from pointwise dynamics to finite orbit windows.

Implement:
  orbitWindowResidualShape
  orbitWindowResidualShapeSeq
  orbitWindowResidualShape_eq_oddOrbitLabel_succ
  orbitWindowResidualShapeSeq_eq_shifted_oddOrbitLabels
  orbitWindow_rawGnomonStep_factor
  orbitWindowFirstFailedPow2Depth
  orbitWindow_firstFailed_remainder_ne_zero

Then, if time permits:
  SourcePressureSignChangeUp
  SourcePressureLocalIsland

Do not:
  introduce Real.log
  claim pressure prefix
  put low-level gnomon vocabulary back into PetalBridge except window lifts
```

## 総括

checkpoint 126 は成功。
`RawGnomonResidualShape = T` が閉じたことで、新しいグノモン視座は既存 Collatz core と完全に接続された。

次は自然に、

```text
pointwise residual shape
  -> window residual shape
```

へ進む。

ここが閉じると、`PetalBridge` の有限窓は単なる label/height の列ではなく、

```text
奇数グノモン補正
2進整列評価
residual shape 抽出
次ラベルへの更新
```

の有限力学として読めるようになる。

その後に pressure island / frontier / sign pattern の分類へ戻ればよい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/GnomonEvaluation.lean b/lean/dk_math/DkMath/Collatz/GnomonEvaluation.lean
index ef44f577..7c24f423 100644
--- a/lean/dk_math/DkMath/Collatz/GnomonEvaluation.lean
+++ b/lean/dk_math/DkMath/Collatz/GnomonEvaluation.lean
@@ -204,4 +204,92 @@ theorem rawGnomonRemainderAtDepth_eq_zero_of_le_height
     dvd_trans (pow_dvd_pow 2 hj) htop
   exact Nat.dvd_iff_mod_eq_zero.mp hdiv
 
+/--
+The residual shape is exactly the natural value of the existing accelerated
+Collatz map.
+
+This closes the checkpoint-126 bridge:
+
+```text
+RawGnomonStep      = existing `threeNPlusOne`
+RawGnomonHeight    = existing `s`
+RawGnomonResidualShape = existing `(T n).1`
+```
+
+After this theorem, the new gnomon vocabulary is not merely explanatory; it is
+definitionally connected to the core accelerated odd-state dynamics.
+-/
+theorem rawGnomonResidualShape_eq_T_val
+    (n : OddNat) :
+    RawGnomonResidualShape n.1 = (T n).1 := by
+  unfold RawGnomonResidualShape RawGnomonHeight T
+  rw [rawGnomonStep_eq_threeNPlusOne]
+  rfl
+
+/--
+The residual shape is odd.
+
+The proof intentionally uses `rawGnomonResidualShape_eq_T_val`: oddness is
+already carried by the `OddNat` result of `T`, so we do not duplicate the
+`padicValNat` maximality proof here.
+-/
+theorem rawGnomonResidualShape_odd
+    (n : OddNat) :
+    RawGnomonResidualShape n.1 % 2 = 1 := by
+  rw [rawGnomonResidualShape_eq_T_val n]
+  exact (T n).2
+
+/--
+The raw gnomon step factors into its visible power-of-two alignment and its
+residual shape.
+
+This is the multiplicative counterpart of the residual-shape bridge.
+-/
+theorem rawGnomonStep_eq_pow_height_mul_residualShape
+    (n : OddNat) :
+    RawGnomonStep n.1 =
+      2 ^ RawGnomonHeight n.1 * RawGnomonResidualShape n.1 := by
+  unfold RawGnomonResidualShape
+  have hdiv : 2 ^ RawGnomonHeight n.1 ∣ RawGnomonStep n.1 := by
+    unfold RawGnomonHeight
+    simpa [v2] using
+      (pow_padicValNat_dvd (p := 2) (n := RawGnomonStep n.1))
+  exact (Nat.mul_div_cancel' hdiv).symm
+
+/--
+The next power after the alignment height does not divide the raw gnomon step.
+
+This is the formal "first failed depth" boundary: height is maximal.
+-/
+theorem two_pow_succ_rawGnomonHeight_not_dvd
+    (n : OddNat) :
+    ¬ 2 ^ (RawGnomonHeight n.1 + 1) ∣ RawGnomonStep n.1 := by
+  have hpos : RawGnomonStep n.1 ≠ 0 := by
+    rw [rawGnomonStep_eq_three_mul_add_one]
+    omega
+  unfold RawGnomonHeight
+  simpa [v2] using
+    (pow_succ_padicValNat_not_dvd hpos)
+
+/--
+At the first failed depth, the raw gnomon remainder is nonzero.
+
+Together with `rawGnomonRemainderAtDepth_eq_zero_of_le_height`, this pins down
+the exact boundary:
+
+```text
+j <= height     -> remainder = 0
+j = height + 1  -> remainder != 0
+```
+-/
+theorem rawGnomonRemainderAtDepth_firstFailed_ne_zero
+    (n : OddNat) :
+    RawGnomonRemainderAtDepth n.1 (FirstFailedPow2Depth n.1) ≠ 0 := by
+  unfold RawGnomonRemainderAtDepth FirstFailedPow2Depth
+  intro h
+  have hdiv :
+      2 ^ (RawGnomonHeight n.1 + 1) ∣ RawGnomonStep n.1 :=
+    Nat.dvd_iff_mod_eq_zero.mpr h
+  exact two_pow_succ_rawGnomonHeight_not_dvd n hdiv
+
 end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index d37dd9a1..a3a30391 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -6,6 +6,7 @@ Authors: D. and Wise Wolf.
 
 import DkMath.Collatz.Accelerated
 import DkMath.Collatz.Shift
+import DkMath.Collatz.GnomonEvaluation
 import DkMath.Petal.RangeFamily
 
 #print "file: DkMath.Collatz.PetalBridge"
@@ -159,6 +160,20 @@ Raw height agrees with the existing Collatz observation `s` on odd states.
 theorem rawHeightLabel_eq_s (n : OddNat) :
     rawHeightLabel n.1 = s n := rfl
 
+/--
+Window height is the raw gnomon alignment height of the observed odd label.
+
+This is the PetalBridge lift of the checkpoint-126 residual-shape vocabulary:
+the finite window still uses `orbitWindowHeight`, but it can now be read as
+`RawGnomonHeight` pointwise.
+-/
+theorem orbitWindowHeight_eq_rawGnomonHeight_oddOrbitLabel
+    (n : OddNat) (i : ℕ) :
+    orbitWindowHeight n i =
+      RawGnomonHeight (oddOrbitLabel n i) := by
+  unfold orbitWindowHeight rawHeightLabel RawGnomonHeight
+  rw [rawGnomonStep_eq_three_mul_add_one]
+
 /--
 The window height is the existing Collatz observation `s` applied to the
 corresponding accelerated state.
@@ -6794,6 +6809,66 @@ theorem downClosed_iff_no_prefixFailure
     · exact hshallow
     · exact False.elim (hno j₁ j₂ hlt hj₂ ⟨hlt, hshallow, hdeep⟩)
 
+/--
+The first selected source-pressure depth.
+
+This is a frontier, not a prefix theorem.  It says that `j` is selected and all
+shallower depths are not selected.  Later work can decide whether the selected
+set continues, stops, or forms an island after this frontier.
+-/
+def SourcePressureFrontier
+    (n : OddNat) (k r j : ℕ) : Prop :=
+  IsSourcePressureDepth n k r j ∧
+    ∀ i, i < j → ¬ IsSourcePressureDepth n k r i
+
+/--
+Frontier in margin language.
+
+The first selected depth is exactly the first positive source-pressure margin.
+-/
+theorem sourcePressureFrontier_iff_margin
+    (n : OddNat) (k r j : ℕ) :
+    SourcePressureFrontier n k r j ↔
+      0 < SourcePressureMarginInt n k (r + j) ∧
+        ∀ i, i < j → SourcePressureMarginInt n k (r + i) ≤ 0 := by
+  constructor
+  · intro h
+    constructor
+    · exact (isSourcePressureDepth_iff_margin_pos n k r j).1 h.1
+    · intro i hi
+      have hnot := h.2 i hi
+      have hnotpos :
+          ¬ 0 < SourcePressureMarginInt n k (r + i) := by
+        intro hpos
+        exact hnot ((isSourcePressureDepth_iff_margin_pos n k r i).2 hpos)
+      omega
+  · intro h
+    constructor
+    · exact (isSourcePressureDepth_iff_margin_pos n k r j).2 h.1
+    · intro i hi hsel
+      have hpos :
+          0 < SourcePressureMarginInt n k (r + i) :=
+        (isSourcePressureDepth_iff_margin_pos n k r i).1 hsel
+      have hle := h.2 i hi
+      omega
+
+/--
+A positive frontier after depth `0` produces a concrete prefix-failure witness.
+
+This is the bridge from the frontier reading back to the checkpoint-125
+obstruction predicate.
+-/
+theorem sourcePressurePrefixFailure_of_frontier_pos
+    (n : OddNat) (k r j : ℕ)
+    (hfront : SourcePressureFrontier n k r j)
+    (hj : 0 < j) :
+    SourcePressurePrefixFailure n k r 0 j := by
+  constructor
+  · exact hj
+  · constructor
+    · exact hfront.2 0 hj
+    · exact hfront.1
+
 /-- The empty selected-pressure prefix is always available. -/
 theorem selectedPressurePrefix_zero
     (n : OddNat) (k r len : ℕ) :
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index 8f6ca449..ffe4a645 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -120,6 +120,11 @@ sum_odd_eq_square
 square_add_eq_square_add_gnomon_sum
 rawGnomonHeight_eq_s
 rawGnomonRemainderAtDepth_eq_zero_of_le_height
+rawGnomonResidualShape_eq_T_val
+rawGnomonResidualShape_odd
+rawGnomonStep_eq_pow_height_mul_residualShape
+two_pow_succ_rawGnomonHeight_not_dvd
+rawGnomonRemainderAtDepth_firstFailed_ne_zero
 ```
 
 This file is intentionally integer-valued.  It does not introduce
@@ -147,6 +152,7 @@ orbitWindowRetentionMass_split
 SourcePressureMarginInt
 SourcePressurePrefixFailure
 SourcePressureSelectedSetDownClosed
+SourcePressureFrontier
 ```
 
 The central No.100 layer is:
@@ -202,6 +208,7 @@ docs/Collatz-SelectedPressureDepths-122.md
 docs/Collatz-ContinuationNesting-123.md
 docs/Collatz-PressureMargin-124.md
 docs/Collatz-GnomonEvaluation-125.md
+docs/Collatz-GnomonResidualShape-126.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-GnomonEvaluation-125.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-GnomonEvaluation-125.md
index 899d6195..4d186f27 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-GnomonEvaluation-125.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-GnomonEvaluation-125.md
@@ -162,3 +162,45 @@ continuation_drop
 
 The Lean side now has a place to store those observations as exact predicates,
 without pretending that pressure selection is automatically prefix-shaped.
+
+## Checkpoint 126 Follow-up
+
+Checkpoint 126 closes the first residual-shape bridge.
+
+New theorem:
+
+```lean
+rawGnomonResidualShape_eq_T_val
+```
+
+The residual shape is now formally identical to the value of the existing
+accelerated map:
+
+```text
+RawGnomonResidualShape n.val = (T n).val
+```
+
+Additional consequences:
+
+```lean
+rawGnomonResidualShape_odd
+rawGnomonStep_eq_pow_height_mul_residualShape
+two_pow_succ_rawGnomonHeight_not_dvd
+rawGnomonRemainderAtDepth_firstFailed_ne_zero
+```
+
+The exact alignment boundary is now:
+
+```text
+j <= RawGnomonHeight n:
+  remainder at depth j is zero
+
+j = RawGnomonHeight n + 1:
+  remainder is nonzero
+```
+
+See:
+
+```text
+Collatz-GnomonResidualShape-126.md
+```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-GnomonResidualShape-126.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-GnomonResidualShape-126.md
new file mode 100644
index 00000000..9728c161
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-GnomonResidualShape-126.md
@@ -0,0 +1,151 @@
+# Collatz Gnomon Residual Shape - Checkpoint 126
+
+Checkpoint 126 closes the first Route A bridge from the new gnomon vocabulary
+back to the existing accelerated Collatz map.
+
+Checkpoint 125 introduced:
+
+```text
+RawGnomonStep n = n + (2n+1)
+RawGnomonHeight n = v2 (RawGnomonStep n)
+RawGnomonResidualShape n = RawGnomonStep n / 2^height
+```
+
+Checkpoint 126 proves that this residual shape is exactly the value already
+computed by the accelerated odd map `T`.
+
+## Main Bridge
+
+```lean
+rawGnomonResidualShape_eq_T_val
+```
+
+Meaning:
+
+```text
+RawGnomonResidualShape n.val = (T n).val
+```
+
+This is the important closure point.  The gnomon vocabulary is no longer only
+an explanation of the old Collatz step.  It is formally the same residual odd
+state used by the existing accelerated dynamics.
+
+## Consequences
+
+Oddness is inherited from `T`:
+
+```lean
+rawGnomonResidualShape_odd
+```
+
+The raw gnomon step decomposes into alignment height times residual shape:
+
+```lean
+rawGnomonStep_eq_pow_height_mul_residualShape
+```
+
+The alignment height is maximal:
+
+```lean
+two_pow_succ_rawGnomonHeight_not_dvd
+```
+
+Therefore the first failed depth has nonzero remainder:
+
+```lean
+rawGnomonRemainderAtDepth_firstFailed_ne_zero
+```
+
+Together with the checkpoint-125 theorem
+
+```lean
+rawGnomonRemainderAtDepth_eq_zero_of_le_height
+```
+
+the boundary is now exact:
+
+```text
+j <= height:
+  RawGnomonRemainderAtDepth n j = 0
+
+j = height + 1:
+  RawGnomonRemainderAtDepth n j != 0
+```
+
+## Window Lift
+
+`PetalBridge` also receives the pointwise lift:
+
+```lean
+orbitWindowHeight_eq_rawGnomonHeight_oddOrbitLabel
+```
+
+Meaning:
+
+```text
+orbitWindowHeight n i
+  = RawGnomonHeight (oddOrbitLabel n i)
+```
+
+This keeps `PetalBridge` as a finite observation surface while allowing every
+height observation to be read through the gnomon/alignment vocabulary.
+
+## Pressure Frontier
+
+Route B starts with a small, safe predicate:
+
+```lean
+SourcePressureFrontier
+sourcePressureFrontier_iff_margin
+sourcePressurePrefixFailure_of_frontier_pos
+```
+
+This is not a pressure-prefix theorem.
+
+It says:
+
+```text
+frontier = first positive margin
+```
+
+If the frontier is at a positive depth, it immediately yields a
+`SourcePressurePrefixFailure` from depth `0` to that frontier depth.
+
+The distinction is important:
+
+```text
+frontier:
+  first positive margin
+
+prefix:
+  all depths up to a bound are positive
+
+island:
+  positive margin appears without prefix behavior
+```
+
+Checkpoint 126 only fixes the frontier and its margin reading.  It does not
+claim that selected depths are prefix-shaped.
+
+## Next Work
+
+The next Route A extension is to expose residual-shape window profiles:
+
+```text
+orbitWindowResidualShape
+orbitWindowResidualShapeSeq
+```
+
+The next Route B extension is to classify pressure sign patterns:
+
+```text
+SourcePressureLocalIsland
+SourcePressureIsland
+first failure pair
+margin jump
+retention drop
+continuation drop
+```
+
+The recommended next checkpoint depends on whether the reviewer wants more
+shape dynamics or more pressure-profile classification.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index 93f32912..9940b949 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -195,6 +195,18 @@ Use these names when selected depths form a non-prefix sign pattern.  Such a
 case is not an error in the model: it means that a deeper residual-shape
 channel has positive margin while a shallower one does not.
 
+Checkpoint 126 adds the first frontier predicate:
+
+```lean
+SourcePressureFrontier
+sourcePressureFrontier_iff_margin
+sourcePressurePrefixFailure_of_frontier_pos
+```
+
+`SourcePressureFrontier n k r j` means that `j` is the first selected pressure
+depth.  It is a first-positive-margin statement, not a claim that later depths
+continue as a prefix.
+
 ## Residue Counts
 
 Named residue counts exist for low layers:
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 4867b67e..8735df6b 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -129,6 +129,9 @@ sourcePressurePrefixFailure_iff_margin
 not_selectedPressurePrefix_of_prefixFailure
 SourcePressureSelectedSetDownClosed
 downClosed_iff_no_prefixFailure
+SourcePressureFrontier
+sourcePressureFrontier_iff_margin
+sourcePressurePrefixFailure_of_frontier_pos
 ```
 
 These names deliberately avoid the unsafe assumption that selected pressure
@@ -141,6 +144,19 @@ depths are always prefix-shaped.  Pressure is the margin sign condition
 and this sign can become positive at a deeper depth while remaining
 nonpositive at a shallower depth.
 
+Checkpoint 126 also connects the finite window height to the low-level gnomon
+alignment vocabulary:
+
+```lean
+orbitWindowHeight_eq_rawGnomonHeight_oddOrbitLabel
+```
+
+So a window height can now be read as:
+
+```text
+RawGnomonHeight of the observed odd label
+```
+
 The first theorem set is deliberately thin:
 
 ```lean
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-126.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-126.md
new file mode 100644
index 00000000..2e8cbf78
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-126.md
@@ -0,0 +1,246 @@
+# Report Petal 126
+
+## Summary
+
+Checkpoint 126 prioritizes Route A:
+
+```text
+Connect the new gnomon residual-shape vocabulary to the existing accelerated
+Collatz map.
+```
+
+The main theorem is:
+
+```lean
+rawGnomonResidualShape_eq_T_val
+```
+
+This proves that the checkpoint-125 residual shape is exactly the natural value
+of the existing accelerated map `T`.
+
+## Code Changes
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/GnomonEvaluation.lean
+```
+
+New Route A theorems:
+
+```lean
+rawGnomonResidualShape_eq_T_val
+rawGnomonResidualShape_odd
+rawGnomonStep_eq_pow_height_mul_residualShape
+two_pow_succ_rawGnomonHeight_not_dvd
+rawGnomonRemainderAtDepth_firstFailed_ne_zero
+```
+
+The exact reading is now:
+
+```text
+RawGnomonStep = 2^RawGnomonHeight * RawGnomonResidualShape
+RawGnomonResidualShape = T value
+RawGnomonResidualShape is odd
+height + 1 is the first non-dividing power-of-two depth
+```
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+New window lift:
+
+```lean
+orbitWindowHeight_eq_rawGnomonHeight_oddOrbitLabel
+```
+
+New Route B starter predicates/theorems:
+
+```lean
+SourcePressureFrontier
+sourcePressureFrontier_iff_margin
+sourcePressurePrefixFailure_of_frontier_pos
+```
+
+## Mathematical Result
+
+Checkpoint 125 established:
+
+```text
+j <= height -> raw remainder at depth j is zero
+```
+
+Checkpoint 126 adds:
+
+```text
+j = height + 1 -> raw remainder at depth j is nonzero
+```
+
+So the alignment boundary is no longer just a one-sided observation.  It is now
+exact:
+
+```text
+RawGnomonHeight is the last fully aligned power-of-two depth.
+FirstFailedPow2Depth is the first depth where the residual odd shape appears.
+```
+
+This is stronger than a narrative reading of the Collatz step.  The shape
+extraction is connected to the actual accelerated map and to a precise
+divisibility boundary.
+
+## Pressure Result
+
+Route B was not expanded into islands yet.  Instead, a small safe predicate was
+added:
+
+```lean
+SourcePressureFrontier
+```
+
+It means:
+
+```text
+the first depth whose source pressure margin is positive
+```
+
+The margin theorem:
+
+```lean
+sourcePressureFrontier_iff_margin
+```
+
+states:
+
+```text
+frontier j
+  <-> margin(j) > 0 and every shallower margin is <= 0
+```
+
+If `0 < j`, the frontier produces a concrete prefix failure:
+
+```lean
+sourcePressurePrefixFailure_of_frontier_pos
+```
+
+This keeps the checkpoint-125 correction intact:
+
+```text
+frontier is not prefix
+first positive margin is not all-positive prefix
+```
+
+## Documentation Changes
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/README.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-GnomonEvaluation-125.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+```
+
+Added:
+
+```text
+lean/dk_math/DkMath/Collatz/docs/Collatz-GnomonResidualShape-126.md
+```
+
+## Verification
+
+Commands run:
+
+```text
+lake build DkMath.Collatz.GnomonEvaluation
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath.Collatz.Collatz2K26
+rg -n "\bsorry\b" touched Collatz Lean files
+git diff --check -- tracked touched files
+rg -n "[ \t]$" new files
+```
+
+All passed.  The `sorry` search found no new `sorry` in
+`GnomonEvaluation.lean` or `PetalBridge.lean`.
+
+The usual unrelated dependency warning can still appear when replaying
+`PetalBridge` dependencies:
+
+```text
+DkMath.NumberTheory.ZsigmondyCyclotomicResearch declaration uses sorry
+```
+
+## Inference
+
+The residual shape route is now strong enough to support two next directions.
+
+### Direction A: residual-shape window profiles
+
+Define finite window profiles for residual shapes:
+
+```lean
+noncomputable def orbitWindowResidualShape
+noncomputable def orbitWindowResidualShapeSeq
+```
+
+Likely theorem:
+
+```lean
+orbitWindowResidualShape_eq_oddOrbitLabel_succ
+```
+
+Meaning:
+
+```text
+the residual shape extracted from oddOrbitLabel n i is oddOrbitLabel n (i+1)
+```
+
+This would turn the pointwise `RawGnomonResidualShape = T` bridge into a window
+dynamics theorem.
+
+### Direction B: pressure sign-pattern classification
+
+The next safe pressure predicates are:
+
+```lean
+SourcePressureLocalIsland
+SourcePressureIsland
+FirstSourcePressureFailurePair
+```
+
+But they should be driven by Python classification first:
+
+```text
+first_failure_pair
+margin_jump
+retention_drop
+continuation_drop
+first_frontier_depth
+is_island
+```
+
+## Recommended Next Checkpoint
+
+Prefer Direction A first:
+
+```text
+orbitWindowResidualShape
+orbitWindowResidualShapeSeq
+residual shape at index i equals odd label at i+1
+```
+
+Reason:
+
+```text
+PetalBridge pressure profiles observe finite orbit windows.
+The residual-shape bridge should therefore be lifted from one point to the
+whole window before adding heavier pressure-island terminology.
+```
+
+After that, return to pressure islands with better semantics:
+
+```text
+an island is a positive-margin event in the residual-shape window profile
+```
````
`````
