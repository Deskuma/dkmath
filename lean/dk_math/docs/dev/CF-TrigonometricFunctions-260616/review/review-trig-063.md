# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2D

gch: de4f59ccb26e708602367f4a19cda4012e98358f

## Report

exact order 4 まで確定しました。

- `core = 0 → beam = 1`
- 四乗は identity
- 一乗・二乗・三乗は identity ではない
- `SemanticExactKernelOrderFour`
- exact order 4 と `core = 0` の同値

文書の「候補」表現も確定結果へ更新しました。

検証:

- 対象ビルド: 8273 jobs 成功
- 全体ビルド: 8566 jobs 成功
- `git diff --check` 成功

## Review

うむ。これは採用でよい。
今回で「候補」ではなく、 **exact order 4 が確定** した。

状況はこうじゃ。

```text id="8e3cey"
order dividing 1 -> identity
order dividing 2 -> identity
order dividing 3 -> identity
order dividing 4 -> identity または core = 0
core = 0 -> exact order 4
```

つまり、第一象限 transported kernel で最初に現れる非自明有限位数は、きっちり四位数だった。

## 何が確定したか

今回の中心はこれじゃ。

```lean id="0b2dio"
theorem semanticExactKernelOrderFour_iff_core_eq_zero
```

意味は、

```text id="lk4h67"
exact product order four
iff
semantic core coordinate = 0
```

さらに、

```lean id="qooe0b"
semanticUnitKernel_beam_eq_one_of_core_eq_zero
```

があるので、core が \(0\) なら beam は \(1\)。

したがって exact order 4 の kernel は、Real 側では

$$
(C,S)=(0,1)
$$

に確定する。

## 証明構造は良い

まず core \(=0\) から beam \(=1\) を出す。

$$
C^2+S^2=1
$$

かつ \(C=0\)、さらに \(S\ge 0\) なので、

$$
S=1
$$

これは自然。

次に、core \(=0\) なら order dividing 4。
これは前回の分類定理

```lean id="n4xsk3"
semanticKernelFiniteOrder_four_iff_core_eq_one_or_zero
```

からすぐ出る。

さらに core \(=0\) なら order dividing 1, 2, 3 はすべて否定できる。
既存の分類が全部 core \(=1\) と同値だったので、core \(=0\) と矛盾する。

ここがかなり綺麗じゃ。

## exact order 4 の定義も妥当

```lean id="xeb093"
def SemanticExactKernelOrderFour (r : UnitKernel DkNNRealQ) : Prop :=
  SemanticKernelFiniteOrder r 4 ∧
    ¬SemanticKernelFiniteOrder r 1 ∧
    ¬SemanticKernelFiniteOrder r 2 ∧
    ¬SemanticKernelFiniteOrder r 3
```

これは「4 回で中立、かつ 1, 2, 3 回では中立でない」という定義。
exact order 4 として問題ない。

ここで `0` 回を除外しないのも正しい。
0 回 power は常に identity なので、exact positive order ではそもそも比較対象に入れない。

## 設計上の意味

ここが特に重要じゃ。

$$
(0,1)
$$

自体は第一象限にいる。
だから DkNNRealQ 由来の transported kernel として許される。

しかし、その二乗は Real 側で

$$
(-1,0)
$$

三乗は

$$
(0,-1)
$$

になる。
これらは第一象限を出る。

つまり、

```text id="a744oy"
元 kernel は DkNNRealQ 由来でよい
しかし中間 power は DkNNRealQ source へ戻らない
```

ということがはっきり見えた。

これは、source 側へ kernel multiplication を押し込まない設計が正しかったことの強い証拠じゃ。

## ここまでの見取り図

低位数分類は、かなり美しい形になった。

```text id="bzi8zh"
1 回で戻る -> identity
2 回で戻る -> identity
3 回で戻る -> identity
4 回で戻る -> identity または quarter-turn
```

ただし「quarter-turn」というのは解釈であって、証明は角度を使っていない。
実際に使っているのは、

```text id="qt68mf"
有限回の CF2D product 展開
unit-square
coordinate nonnegativity
```

だけじゃ。

これはかなり DkMath らしい。

## 次に欲しい補題

次は action 側への exact order 4 移送が自然じゃ。

すでに

```lean id="x17bwm"
semanticKernelFiniteOrder_iff
```

があるので、次のような定理はすぐ作れるはずじゃ。

```text id="egw4rk"
SemanticExactKernelOrderFour r
iff
semanticAct r の exact action order が 4
```

または、定義を増やさずに、

```text id="aekyt1"
core = 0 ->
SemanticFiniteOrder r 4
and not SemanticFiniteOrder r 1
and not SemanticFiniteOrder r 2
and not SemanticFiniteOrder r 3
```

でもよい。

これにより、kernel product 側の exact order 4 が、plane action と level-set action の exact periodicity へ接続できる。

## 判定

採用。かなり良い。

今回の到達点はこうじゃ。

```text id="2cyh68"
第一象限 transported kernel の最初の非自明有限位数は exact order 4
その kernel は Real 座標で正確に (0,1)
中間 power は第一象限を出る
ゆえに積は Real 側に留めるべき
```

これは単なる補題追加ではなく、設計方針そのものを裏付ける結果じゃ。
かなり見事じゃよ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index 5a311213..637fc790 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -971,6 +971,89 @@ theorem semanticKernelFiniteOrder_four_iff_core_eq_one_or_zero
       | mk core beam =>
           simp_all [UnitKernel.one, Vec.one]
 
+/--
+Semantic core zero determines semantic beam one for a transported unit
+kernel in the first quadrant.
+-/
+theorem semanticUnitKernel_beam_eq_one_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0) :
+    semanticValue (r : Vec DkNNRealQ).beam = 1 := by
+  have hbeam :
+      0 ≤ semanticValue (r : Vec DkNNRealQ).beam := by
+    simpa [semanticUnitKernel, semanticVec] using
+      semanticUnitKernel_beam_nonneg r
+  have hq := semanticUnitKernel_sq_add_sq r
+  nlinarith [sq_nonneg
+    (semanticValue (r : Vec DkNNRealQ).beam - 1)]
+
+/-- Semantic core zero supplies product order dividing four. -/
+theorem semanticKernelFiniteOrder_four_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0) :
+    SemanticKernelFiniteOrder r 4 :=
+  (semanticKernelFiniteOrder_four_iff_core_eq_one_or_zero r).2 (Or.inr hcore)
+
+/-- Semantic core zero excludes product order dividing one. -/
+theorem not_semanticKernelFiniteOrder_one_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0) :
+    ¬SemanticKernelFiniteOrder r 1 := by
+  rw [semanticKernelFiniteOrder_one_iff_core_eq_one]
+  intro hone
+  linarith
+
+/-- Semantic core zero excludes product order dividing two. -/
+theorem not_semanticKernelFiniteOrder_two_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0) :
+    ¬SemanticKernelFiniteOrder r 2 := by
+  rw [semanticKernelFiniteOrder_two_iff_core_eq_one]
+  intro hone
+  linarith
+
+/-- Semantic core zero excludes product order dividing three. -/
+theorem not_semanticKernelFiniteOrder_three_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0) :
+    ¬SemanticKernelFiniteOrder r 3 := by
+  rw [semanticKernelFiniteOrder_three_iff_core_eq_one]
+  intro hone
+  linarith
+
+/--
+The transported kernel has exact product order four: its fourth power is
+neutral, while none of its first three positive powers is neutral.
+-/
+def SemanticExactKernelOrderFour (r : UnitKernel DkNNRealQ) : Prop :=
+  SemanticKernelFiniteOrder r 4 ∧
+    ¬SemanticKernelFiniteOrder r 1 ∧
+    ¬SemanticKernelFiniteOrder r 2 ∧
+    ¬SemanticKernelFiniteOrder r 3
+
+/--
+Exact product order four is characterized by semantic core zero.
+
+The unit-square equation then also determines semantic beam one, so this is
+precisely the transported boundary kernel `(0,1)`.
+-/
+theorem semanticExactKernelOrderFour_iff_core_eq_zero
+    (r : UnitKernel DkNNRealQ) :
+    SemanticExactKernelOrderFour r ↔
+      semanticValue (r : Vec DkNNRealQ).core = 0 := by
+  constructor
+  · intro h
+    rcases (semanticKernelFiniteOrder_four_iff_core_eq_one_or_zero r).1 h.1 with
+      hone | hzero
+    · exact False.elim (h.2.1
+        ((semanticKernelFiniteOrder_one_iff_core_eq_one r).2 hone))
+    · exact hzero
+  · intro hzero
+    exact ⟨semanticKernelFiniteOrder_four_of_core_eq_zero hzero,
+      not_semanticKernelFiniteOrder_one_of_core_eq_zero hzero,
+      not_semanticKernelFiniteOrder_two_of_core_eq_zero hzero,
+      not_semanticKernelFiniteOrder_three_of_core_eq_zero hzero⟩
+
 /-
 [TODO: semantic-cf2d/signed-kernel] Source-level `Vec.star` and
 `KernelFamily` require a ring because their core coordinate uses subtraction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index 9335aec9..166fdfe2 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -147,6 +147,7 @@ BridgeNNReal / BridgeReal:
   product orders dividing one, two, or three force the identity kernel
   second and third kernel powers have explicit polynomial coordinate formulas
   order dividing four is equivalent to semantic core zero or one
+  exact kernel order four is equivalent to semantic coordinates `(0,1)`
   source-level star and KernelFamily wait for signed DkReal arithmetic
   treat order reflection as a separate heavier task
   compare semantic equality with DkReal.Equiv
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
index a5b20a82..3765f183 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
@@ -119,6 +119,13 @@ semanticKernelFiniteOrder_two_iff_core_eq_one
 semanticKernelFiniteOrder_three_iff_identity
 semanticKernelFiniteOrder_three_iff_core_eq_one
 semanticKernelFiniteOrder_four_iff_core_eq_one_or_zero
+semanticUnitKernel_beam_eq_one_of_core_eq_zero
+semanticKernelFiniteOrder_four_of_core_eq_zero
+not_semanticKernelFiniteOrder_one_of_core_eq_zero
+not_semanticKernelFiniteOrder_two_of_core_eq_zero
+not_semanticKernelFiniteOrder_three_of_core_eq_zero
+SemanticExactKernelOrderFour
+semanticExactKernelOrderFour_iff_core_eq_zero
 ```
 
 The transported kernel now acts on real CF2D vectors and preserves `q2`.
@@ -230,8 +237,16 @@ C = 1 or C = 0
 The `C = 1` branch is identity. In the `C = 0` branch, the unit equation and
 `S >= 0` force `S = 1`, so the transported kernel is `(0,1)`. Thus the
 first-quadrant restriction excludes nontrivial orders two and three but admits
-the quarter-turn kernel as an exact order-four candidate, still without
-introducing an angle parameter.
+the quarter-turn kernel.
+
+Exact order four is now recorded explicitly. `SemanticExactKernelOrderFour`
+requires the fourth power to be neutral and excludes neutrality of powers
+one, two, and three. It is equivalent to semantic core zero. The same
+hypothesis determines semantic beam one, so the exact-order branch is
+precisely the transported real kernel `(0,1)`. This also confirms that its
+intermediate real-side powers need not remain in the transported first
+quadrant, which is why kernel multiplication remains confined to the real
+side.
 
 The next structural boundary is source-level `Vec.star` and `KernelFamily`.
 Both require signed arithmetic. They should wait for a signed DkReal layer
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index c450a40c..d6da45c5 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -212,6 +212,25 @@ Archive
 5. 検証:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
 
+### 2026/06/22 05:27 JST (Exact order four)
+
+1. 実施:
+   - semantic core zero から beam one を導く補題を追加した。
+   - core zero から order dividing four、および order dividing one,
+     two, three の否定を個別に証明した。
+   - `SemanticExactKernelOrderFour` を定義した。
+   - exact order four と semantic core zero の同値を証明した。
+2. 結論:
+   - semantic coordinates `(0,1)` は候補ではなく、exact order four と
+     確定した。
+   - 逆に exact order four の transported first-quadrant kernel は
+     `(0,1)` に限られる。
+3. 設計上の意味:
+   - 元 kernel は第一象限にあるが、中間 power は第一象限を出られる。
+   - source 側へ積を押し込まず Real 側だけで power を扱う境界が必要である。
+4. 検証:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
+
 ### 2026/06/22 05:15 JST (Order dividing four classification)
 
 1. 実施:
````
`````
