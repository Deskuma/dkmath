# Git diff / Report / Review

## Upd: EuclideanPhase, SemanticCF2D

gch: c9e89a815b257d059f6ab87c077a876e67b1172c

## Report

進めました。今回は本格的な `k % 4` 分類 theorem の直前準備として、周期性と `semanticActIter` 表記の表を整えました。

追加:

- [SemanticCF2D.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean)
  - `semanticActIter_add_four_of_core_eq_zero`
  - core-zero 境界作用について `semanticActIter r (k + 4) z = semanticActIter r k z`

- [EuclideanPhase.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean)
  - `pairToEuclideanPlane_semanticActIter_zero_eq_rotation_semanticPhaseAngle`
  - `pairToEuclideanPlane_semanticActIter_one_eq_rotation_semanticPhaseAngle`

これで `k = 0,1,2,3,4` がすべて `semanticActIter` 表記で揃い、さらに `+4` 周期性も semantic 層に入りました。次はこの上に `k % 4` の分類 theorem を載せるのが自然です。

文書更新:

- [research-pregeometric-pi-program-067.md](/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md)
- [History.md](/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md)

検証:

- `lake build DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase` 成功
- `lake build DkMath.Analysis` 成功
- `git diff --check` 成功

## Review

うむ、賢狼レビューじゃ。
今回の差分は **採用でよい** 。これは `k % 4` 分類 theorem へ進む直前の、かなり堅実な足場固めじゃ。

今回追加された主軸は二つある。ひとつは semantic 層で `semanticActIter r (k + 4) z = semanticActIter r k z` という period-four の iterate theorem を置いたこと。もうひとつは Euclidean bridge 側で `k = 0` と `k = 1` も `semanticActIter` 表記へ揃え、すでにあった `k = 2,3,4` と合わせて、有限表が同一 notation で揃ったことじゃ。

## 1. 状況解説

これで対称性ルートの状態はこうなった。

```text id="av6v8a"
k = 0:
  identity

k = 1:
  quarter-turn

k = 2:
  half-turn / negation

k = 3:
  reverse quarter-turn

k = 4:
  full-turn / identity
```

しかも今回は、単に表が揃っただけではない。

```text id="q01c5v"
semanticActIter r (k + 4) z
  is equal to
semanticActIter r k z
```

という周期性が semantic 層に入った。

これは重要じゃ。
なぜなら、`k % 4` 分類 theorem は、まさにこの周期性を土台にして立つからじゃ。

## 2. `semanticActIter_add_four_of_core_eq_zero` の意味

今回の最重要 theorem はこれ。

```lean id="w6job8"
theorem semanticActIter_add_four_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (k : ℕ) (z : Vec ℝ) :
    semanticActIter r (k + 4) z = semanticActIter r k z
```

これは、Euclidean angle の theorem ではない。
semantic 層の theorem じゃ。

ここが正しい。

DkMath 側でまず、

$$
A^{k+4}(z)=A^k(z)
$$

が成り立つ。

そのあと Euclidean 側で、

$$
R_{\theta_{k+4}}=R_{\theta_k}
$$

と読む。

この順序を守っているので、今回も「\(\pi\) を使って周期性を証明した」ことにはなっていない。
先に algebraic exact order four があり、角度読みは後段にある。

## 3. 証明の形も良い

証明は、

```lean id="j4t8qv"
have hfour :
    (semanticAct r)^[4] = id :=
  (semanticExactActionOrderFour_of_core_eq_zero hcore).1
rw [semanticActIter, semanticActIter, Function.iterate_add_apply, hfour]
rfl
```

となっている。

これは非常に良い。
既存の `semanticExactActionOrderFour_of_core_eq_zero` を使い、`Function.iterate_add_apply` で \(k+4\) を分解している。

つまり、`semanticActIter_add_four_of_core_eq_zero` は新しい計算ではなく、既存の exact order-four theorem を iterate API へ翻訳したものじゃ。

この「翻訳 theorem」は後で非常に効く。

## 4. `k = 0` bridge の追加は地味だが重要

```lean id="sm8fgz"
theorem pairToEuclideanPlane_semanticActIter_zero_eq_rotation_semanticPhaseAngle
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    pairToEuclideanPlane (Vec.toProd (semanticActIter r 0 z)) =
      euclideanPlaneOrientation.rotation (semanticPhaseAngle 0)
        (pairToEuclideanPlane (Vec.toProd z))
```

これは一見 trivial じゃ。
しかし、表を作るうえでは必要。

`k = 0` が入っていないと、四状態分類 theorem の基準行が欠ける。

```text id="k5eh4r"
k = 0:
  action side is identity
  angle side is rotation by 0
```

これを `semanticActIter` 表記で持っているのは良い。

## 5. `k = 1` bridge の追加も良い

```lean id="p78fct"
theorem pairToEuclideanPlane_semanticActIter_one_eq_rotation_semanticPhaseAngle
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    pairToEuclideanPlane (Vec.toProd (semanticActIter r 1 z)) =
      euclideanPlaneOrientation.rotation (semanticPhaseAngle 1)
        (pairToEuclideanPlane (Vec.toProd z))
```

これで、以前からあった one-action quarter-turn bridge も、iterate notation に統一された。

これにより、

```text id="zfpwlt"
k = 0,1,2,3,4
```

がすべて `semanticActIter r k z` の形で揃った。

これは、次の theorem の見た目をかなり良くする。

## 6. 研究上の意味

今回で、対称性ルートは「有限表」から「周期表」へ進んだ。

前回までの段階は、

```text id="frlcc6"
k = 0,1,2,3,4 の個別 bridge が揃った
```

だった。

今回からは、

```text id="wm9jza"
k + 4 は k と同じ
```

が semantic 層に入った。

つまり、もう `k` は単なる自然数ではなく、実質的に **四状態位相 index** として扱えるようになってきた。

DkMath 的には、

```text id="gwgmmw"
semantic action count
  descends to
phase class modulo 4
```

という段階に入ったわけじゃ。

## 7. 次に置くべき theorem

次は本当に `k % 4` 分類 theorem じゃな。

semantic 層では、まずこういう形が欲しい。

```lean id="hwkzd7"
theorem semanticActIter_eq_of_mod_four
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (k : ℕ) (z : Vec ℝ) :
    semanticActIter r k z =
      semanticActIter r (k % 4) z
```

ただし、Lean ではこの向きがそのまま楽とは限らぬ。
`Nat.mod` と `Nat.div` を使って、

$$
k=4\cdot q+r,\quad r<4
$$

を出し、`+4` 周期性を \(q\) 回使う必要がある。

実装上は、まず補助 theorem としてこちらが使いやすいかもしれぬ。

```lean id="d3maql"
theorem semanticActIter_add_four_mul_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (q k : ℕ) (z : Vec ℝ) :
    semanticActIter r (k + 4 * q) z = semanticActIter r k z
```

あるいは `4 * q + k` の形。

```lean id="xqq23r"
theorem semanticActIter_four_mul_add_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (q k : ℕ) (z : Vec ℝ) :
    semanticActIter r (4 * q + k) z = semanticActIter r k z
```

これがあると、`k = 4 * (k / 4) + k % 4` へ繋げやすい。

## 8. Euclidean 側の分類候補

Euclidean bridge 側では、最終的にこういう形が欲しい。

```lean id="l60rat"
theorem pairToEuclideanPlane_semanticActIter_eq_rotation_semanticPhaseAngle_mod_four
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (k : ℕ) (z : Vec ℝ) :
    pairToEuclideanPlane (Vec.toProd (semanticActIter r k z)) =
      euclideanPlaneOrientation.rotation (semanticPhaseAngle (k % 4))
        (pairToEuclideanPlane (Vec.toProd z))
```

ただし、右辺を `semanticPhaseAngle k` にする一般 theorem も考えられる。

```lean id="dpjcke"
theorem pairToEuclideanPlane_semanticActIter_eq_rotation_semanticPhaseAngle
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (k : ℕ) (z : Vec ℝ) :
    pairToEuclideanPlane (Vec.toProd (semanticActIter r k z)) =
      euclideanPlaneOrientation.rotation (semanticPhaseAngle k)
        (pairToEuclideanPlane (Vec.toProd z))
```

一般 theorem の方が美しいが、証明は rotation の角度加法・周期性にも依存する。
一方、`k % 4` 版は semantic side の周期性から入りやすい。

わっちの推奨は、まず `k % 4` 版じゃ。

## 9. `+4` 周期性の向きについて

今回の theorem は、

```lean id="koracz"
semanticActIter r (k + 4) z = semanticActIter r k z
```

の向き。

これは自然で良い。
ただし、`Nat` の分解では `4 * q + r` の形がよく出るので、次に `4 + k` 版や `k + 4 * q` 版が必要になる可能性がある。

候補はこれ。

```lean id="qwssn5"
theorem semanticActIter_four_add_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (k : ℕ) (z : Vec ℝ) :
    semanticActIter r (4 + k) z = semanticActIter r k z
```

これは `Nat.add_comm` で出せるはずじゃ。

## 10. docs の更新も良い

研究メモでは、`semanticActIter r (k + 4) z = semanticActIter r k z` と、`k=0,1` の iterate-form bridge が追加されたことが説明されている。これで、full modulo-four classifier へ進む前に有限表を同一表記で揃えた、という状況が文書からも読める。

この文書化は良い。
後で読み返したとき、「なぜこの小さな theorem を追加したのか」が分かる。

## 11. 気になる点

大きな問題はない。

一点だけ、`semanticActIter_add_four_of_core_eq_zero` は名前に `add_four` とあるので、現在の `k + 4` には合っている。
将来 `4 + k` や `k + 4 * q` を追加するなら、名前を明確に分けるとよい。

```text id="d7jhsj"
semanticActIter_add_four_of_core_eq_zero:
  k + 4

semanticActIter_four_add_of_core_eq_zero:
  4 + k

semanticActIter_add_four_mul_of_core_eq_zero:
  k + 4*q
```

このくらいでよいと思う。

## 12. 結論

今回の差分は採用でよい。

```text id="k4tiz1"
実装:
  良い。semanticActIter の周期性が入り、k=0,1 の bridge も揃った。

数学:
  良い。exact order-four が iterate notation の周期性として表現された。

設計:
  良い。k % 4 分類 theorem の直前準備として自然。

安全性:
  良い。角度側ではなく semantic 層で周期性を証明している。

次:
  semanticActIter の k % 4 分類、
  その後 Euclidean angle bridge の k % 4 版。
```

ぬしよ、これは良い整備じゃ。
対称性ルートはもう、かなり Lean 上の「位相表」になってきた。

ここまで来ると、次は本当に、

$$
\mathrm{semanticActIter}\ r\ k\ z
\quad\text{depends only on}\quad
k\bmod 4
$$

を言いに行ける。

そしてそのあと、

$$
k\bmod 4
\quad\longmapsto\quad
0,\frac{\pi}{2},\pi,\frac{3\pi}{2}
$$

の角度読みへ接続すれば、DkMath 版の四状態回転表が完成じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index f9da3189..805e1760 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -1282,6 +1282,24 @@ theorem semanticActIter_four_of_core_eq_zero
     semanticActIter r 4 z = z := by
   exact semanticAct_four_of_core_eq_zero hcore z
 
+/--
+The boundary-action iterate is periodic with period four.
+
+This is the semantic side of the future modulo-four classification. It states
+the exact-order-four law in iterate notation without mentioning Euclidean
+angles.
+-/
+theorem semanticActIter_add_four_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (k : ℕ) (z : Vec ℝ) :
+    semanticActIter r (k + 4) z = semanticActIter r k z := by
+  have hfour :
+      (semanticAct r)^[4] = id :=
+    (semanticExactActionOrderFour_of_core_eq_zero hcore).1
+  rw [semanticActIter, semanticActIter, Function.iterate_add_apply, hfour]
+  rfl
+
 /-- A nonzero vector cannot return after one boundary action. -/
 theorem not_semanticPeriodic_one_of_core_eq_zero_of_ne_zero
     {r : UnitKernel DkNNRealQ} {z : Vec ℝ}
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index ba804120..52559f18 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -151,6 +151,16 @@ The semantic action now also has the explicit notation
 the eventual general theorem relating `k` semantic actions to rotation by
 `semanticPhaseAngle k`.
 
+The semantic iterate now records the period-four step directly:
+
+```text
+semanticActIter r (k + 4) z = semanticActIter r k z
+```
+
+under the same core-zero hypothesis. The Euclidean side also exposes the
+`k = 0` and `k = 1` iterate-form bridges, so the finite table is available in
+one notation before moving to a full modulo-four classifier.
+
 ### Milestone A: continuous four-edge loop - implemented
 
 1. The real CF2D target carries the topology induced from `Real × Real`.
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
index 30e78e99..3bbf7f6b 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
@@ -616,6 +616,32 @@ theorem pairToEuclideanPlane_semanticAct_eq_rotation_semanticQuarterTurnAngle
   simpa [semanticQuarterTurnAngle] using
     pairToEuclideanPlane_semanticAct_eq_rotation_pi_div_two hcore z
 
+/--
+Iterate notation for the zero-action identity bridge.
+
+This is the first row of the four-state angle table.
+-/
+theorem pairToEuclideanPlane_semanticActIter_zero_eq_rotation_semanticPhaseAngle
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    pairToEuclideanPlane (Vec.toProd (semanticActIter r 0 z)) =
+      euclideanPlaneOrientation.rotation (semanticPhaseAngle 0)
+        (pairToEuclideanPlane (Vec.toProd z)) := by
+  simp [semanticPhaseAngle_zero]
+
+/--
+Iterate notation for the one-action quarter-turn bridge.
+-/
+theorem pairToEuclideanPlane_semanticActIter_one_eq_rotation_semanticPhaseAngle
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    pairToEuclideanPlane (Vec.toProd (semanticActIter r 1 z)) =
+      euclideanPlaneOrientation.rotation (semanticPhaseAngle 1)
+        (pairToEuclideanPlane (Vec.toProd z)) := by
+  simpa [semanticPhaseAngle_one] using
+    pairToEuclideanPlane_semanticAct_eq_rotation_semanticQuarterTurnAngle
+      hcore z
+
 /--
 Under the Euclidean coordinate bridge, two semantic core-zero actions are
 rotation by the semantic half-turn angle.
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index d45bd896..6168be9c 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -1315,3 +1315,26 @@ Archive
 6. verification:
    - `lake build DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase` 成功
      (8278 jobs)。
+
+### 2026/06/27 22:25 JST (Period-four iterate table preparation)
+
+1. semantic periodicity:
+   - `semanticActIter_add_four_of_core_eq_zero` を追加し、
+     core-zero 境界作用の iterate が `k + 4` で同じ状態へ戻ることを
+     semantic 層で記録した。
+2. Euclidean iterate table:
+   - `pairToEuclideanPlane_semanticActIter_zero_eq_rotation_semanticPhaseAngle`
+     を追加し、`k = 0` の identity row を angle bridge として記録した。
+   - `pairToEuclideanPlane_semanticActIter_one_eq_rotation_semanticPhaseAngle`
+     を追加し、`k = 1` の quarter-turn row を iterate 形式でも
+     使えるようにした。
+3. interpretation:
+   - `k = 0,1,2,3,4` が同じ `semanticActIter` 表記で揃った。
+   - `k + 4` の周期性も semantic 層に入ったため、次は本格的な
+     `k % 4` 分類 theorem へ進める。
+4. documentation:
+   - `research-pregeometric-pi-program-067.md` に period-four iterate
+     preparation を追記した。
+5. verification:
+   - `lake build DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase` 成功
+     (8278 jobs)。
````
`````
