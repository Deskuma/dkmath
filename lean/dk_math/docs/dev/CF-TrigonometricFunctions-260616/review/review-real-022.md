# Git diff / Report / Review

## Upd: Analysis.DkReal.Arithmetic

gch: d1031769e7d555b19a50f6010a3986b393695aff

## Report

レビュー指摘を確認し、次段階まで実装しました。

[Arithmetic.lean](/lean/dk_math/DkMath/Analysis/DkReal/Arithmetic.lean:88) に interval-level の十法則を追加しています。

- 加法の結合・交換・左右単位元
- 非負乗法の結合・交換・左右単位元
- 左右分配則

`DkReal` の生の等号や typeclass instance は導入していません。一般符号乗法も、端点の `min/max` が必要になるため保留しています。

同値関係は、区間交差・近似間距離の消失・将来の実数評価値という候補が同義とは未証明なので、次の設計課題として文書化しました。

検証結果:

- `lake build DkMath.Analysis DkMath` 成功
- 十法則すべての存在を確認
- DkReal 層に `noncomputable` なし
- `git diff --check` 成功

## Review

うむ、今回の差分も **合格** じゃ。
前回のレビューで「まだ typeclass instance は早い。まず interval-level の法則を積むべき」と言った、その通りの段階を実装しておる。

今回の成果はこうじゃな。

```text id="epx8pb"
DkReal.Arithmetic:
  加法・非負乗法の stagewise 十法則を追加

方針:
  DkReal の生の構造体等号は使わない
  Add / Mul / Semiring instance もまだ入れない
  各 n 段の観測区間が一致する、という形で止める
```

これは正しい。

## 1. 今回閉じたもの

追加された十法則は、ちょうど今の `DkReal` に必要な **観測段階の半環法則** じゃ。

```lean id="xp52al"
add_assoc_interval
add_comm_interval
add_zero_interval
zero_add_interval
mulNonneg_assoc_interval
mulNonneg_comm_interval
mulNonneg_one_interval
one_mulNonneg_interval
left_distrib_interval
right_distrib_interval
```

数学的には、これは `DkReal` そのものの等式ではなく、各段の有理区間で

$$
I_n(x+y)=I_n(y+x)
$$

や

$$
I_n(x(y+z))=I_n(xy+xz)
$$

を示している状態じゃ。

これは「同じ実数を表している」ではなく、もっと強い場合もある。つまり、 **同じ近似段で同じ区間が出る** という観測一致じゃな。

## 2. 方針がよい

今回、`Add` や `Mul` の typeclass instance を入れていないのは正しい。

理由は、`DkReal` は構造体としては

```lean id="ps2ime"
interval : ℕ → GapInterval
nested : ...
width_tends_zero : ...
```

を持つので、同じ極限値を表す別々の近似列が、生の Lean 構造体等号では一致しない可能性があるからじゃ。

つまり今はまだ、

```text id="kqpj5d"
観測区間列として同じ
極限実数として同じ
将来 eval した値が同じ
```

のどれを `DkReal` の等価性にするか決めていない。

ここで無理に semiring instance を入れると、あとで同値関係を選び直すときに API が重くなる。
したがって今回のように、まず

```lean id="jiolp9"
(...).interval n = (...).interval n
```

の形で十法則を保存するのは、かなり安全な進め方じゃ。

## 3. 加法法則レビュー

加法は一般 `DkReal` に対して閉じている。

```lean id="trfspy"
add x y
```

は stagewise に Minkowski sum を取る構造だった。加法は符号制約なしで端点ごとに順序保存されるので、

```lean id="l9msqb"
zero_add_interval
add_comm_interval
add_assoc_interval
```

は自然に `GapInterval.ext` と `simp` で閉じる。

これは問題なし。
加法については、次に `DkReal` の同値関係を選んだあと、そのまま quotient / setoid 上の加法へ持ち上げる候補になる。

## 4. 非負乗法法則レビュー

非負乗法についても、現段階では正しい。

`mulNonneg` は、非負区間でのみ

$$
[a,b]\cdot[c,d]=[ac,bd]
$$

を採用できる。
これが成り立つのは、乗法が非負領域で各変数について単調だからじゃ。

今回の法則はすべてその前提を明示している。

```lean id="7znuhh"
mulNonneg_assoc_interval
mulNonneg_comm_interval
mulNonneg_one_interval
one_mulNonneg_interval
left_distrib_interval
right_distrib_interval
```

特に `mulNonneg_assoc_interval` では、左側の積 `mulNonneg x y hx hy` が非負であることを

```lean id="vhob96"
nonnegative_mulNonneg hx hy
```

で供給している。
これは良い。証明引数が長くなるが、設計としては正しい。

## 5. 分配則も良い

左右分配則は、非負性の保存を使っている。

左分配は、

```lean id="db6gdz"
mulNonneg x (add y z) hx (nonnegative_add hy hz)
```

右辺は、

```lean id="4l3vtn"
add (mulNonneg x y hx hy) (mulNonneg x z hx hz)
```

になっている。

これは stagewise endpoint では通常の有理数分配法則そのものじゃ。
`GapInterval.ext` 後に `simp [add, addApprox, mulNonneg, mulNonnegApprox, mul_add]` で落ちるのは自然。

右分配も同様に `add_mul` で閉じている。
この段階で、非負演算の半環的骨格はかなり見えてきた。

## 6. 文書更新も正しい

文書で、これらの法則が **finite observation stage** の法則であり、生の `DkReal` 等号ではないと明記したのは重要じゃ。

この区別は、今後外向けに説明するときもかなり効く。

```text id="9clv5e"
今あるもの:
  各近似段の区間演算が半環法則を満たす

まだないもの:
  DkReal の同値関係上の半環構造
```

この説明が入ったので、過大主張になっていない。

## 7. 現在の数学的位置

ここまでで、`DkReal` は次の段階にいる。

$$
\boxed{\text{非負 }DkReal\text{ は、観測段階で半環法則を満たす。}}
$$

より正確には、

```text id="p1o47f"
DkReal:
  加法で閉じる

Nonnegative DkReal:
  加法で閉じる
  乗法で閉じる
  自然数冪で閉じる
  各段の区間に対して半環の十法則が成立
```

ただし、まだ

$$
x=y
$$

をどう読むかが決まっていないので、Lean の正式な `Semiring` ではない。
この慎重さは正しい。

## 8. 次の設計課題

次は本当に同値関係の設計じゃ。

候補は三つある。

```text id="d42f0h"
1. Persistent intersection
   十分先の区間が常に交差する

2. Vanishing separation
   2 つの近似区間の距離が 0 に収束する

3. Future eval equality
   DkReal → ℝ の評価値が等しい
```

わっちの直感では、Route B の計算可能性を保つなら、まずは 2 が扱いやすい。

区間間距離を

$$
dist(I_n,J_n)
$$

のように定義し、それが 0 に収束するなら同値、という形じゃな。

ただし、実装コストを考えるなら、先に `GapInterval` の距離を作る必要がある。
例えば閉区間同士の分離幅を

```lean id="om13wu"
max (I.lo - J.hi) (J.lo - I.hi) 0
```

のように置く案がある。これは一般符号や順序で少し重くなるので、急がず設計でよい。

## 9. 小さな注意点

一つだけ注意するなら、`simp` が今後強くなりすぎる可能性がある。

今の interval-level simp は良いが、将来 `add_interval` や `mulNonneg_interval` と組み合わさると、`simp` が深く展開しすぎる場合がある。
現時点では問題ない。もし後で遅くなったら、`simp` 補題の粒度を調整すればよい。

また、`mulNonneg` は非負 quadrant 限定であることを今後も名前で守るべきじゃ。一般乗法を実装するときは、同名にせず、

```lean id="qyf3r3"
mulInterval
mulGeneral
mul
```

のように別設計にするのが安全じゃ。

## 10. 最終判定

今回の差分は **合格** じゃ。

```text id="qis0nw"
良い点:
  interval-level の十法則を追加
  生の DkReal 等号を避けている
  typeclass instance をまだ導入していない
  同値関係の未確定性を文書化している
  noncomputable 不使用を維持

残る課題:
  DkReal の同値関係
  同値に対する add / mulNonneg の congruence
  将来の ordered semiring API
  一般符号区間乗法
```

うむ。これは堅い進み方じゃ。
`DkReal` はいま、 **観測段階の非負計算可能半環核** まで来た。次に必要なのは、「同じ値を表す」とは何かを決めることじゃな。ここを決めれば、演算はすでにかなりの部分が待機しておる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Arithmetic.lean b/lean/dk_math/DkMath/Analysis/DkReal/Arithmetic.lean
index 8f6d8d8f..52f57cd6 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/Arithmetic.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Arithmetic.lean
@@ -85,6 +85,32 @@ theorem add_zero_interval (x : DkMath.Analysis.DkReal) (n : ℕ) :
     (add x (DkMath.Analysis.DkReal.ofRat 0)).interval n = x.interval n := by
   apply GapInterval.ext <;> simp [add, addApprox]
 
+/-!
+## Additive interval laws
+
+These laws deliberately compare the interval observed at each stage. They do
+not identify two `DkReal` structures whose approximation sequences merely
+represent the same limiting real number.
+-/
+
+/-- Embedded zero is a left identity at every approximation stage. -/
+@[simp]
+theorem zero_add_interval (x : DkMath.Analysis.DkReal) (n : ℕ) :
+    (add (DkMath.Analysis.DkReal.ofRat 0) x).interval n = x.interval n := by
+  apply GapInterval.ext <;> simp [add, addApprox]
+
+/-- Addition is commutative at every approximation stage. -/
+theorem add_comm_interval
+    (x y : DkMath.Analysis.DkReal) (n : ℕ) :
+    (add x y).interval n = (add y x).interval n := by
+  apply GapInterval.ext <;> simp [add, addApprox, add_comm]
+
+/-- Addition is associative at every approximation stage. -/
+theorem add_assoc_interval
+    (x y z : DkMath.Analysis.DkReal) (n : ℕ) :
+    (add (add x y) z).interval n = (add x (add y z)).interval n := by
+  apply GapInterval.ext <;> simp [add, addApprox, add_assoc]
+
 /-!
 ## II. Multiplication on the nonnegative quadrant
 
@@ -238,4 +264,64 @@ theorem mulNonneg_one_interval
       = x.interval n := by
   apply GapInterval.ext <;> simp [mulNonneg, mulNonnegApprox]
 
+/-!
+## III. Nonnegative semiring laws at the interval level
+
+Proof arguments witness that endpoint multiplication is valid on the
+nonnegative quadrant. The conclusions concern only rational endpoints, so
+proof irrelevance removes any dependence on how those witnesses were obtained.
+-/
+
+/-- Embedded one is a left identity for nonnegative multiplication stagewise. -/
+@[simp]
+theorem one_mulNonneg_interval
+    (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
+    (mulNonneg (DkMath.Analysis.DkReal.ofRat 1) x
+        (nonnegative_ofRat zero_le_one) hx).interval n
+      = x.interval n := by
+  apply GapInterval.ext <;> simp [mulNonneg, mulNonnegApprox]
+
+/-- Nonnegative multiplication is commutative at every approximation stage. -/
+theorem mulNonneg_comm_interval
+    (x y : DkMath.Analysis.DkReal) (hx : Nonnegative x) (hy : Nonnegative y)
+    (n : ℕ) :
+    (mulNonneg x y hx hy).interval n
+      = (mulNonneg y x hy hx).interval n := by
+  apply GapInterval.ext <;> simp [mulNonneg, mulNonnegApprox, mul_comm]
+
+/-- Nonnegative multiplication is associative at every approximation stage. -/
+theorem mulNonneg_assoc_interval
+    (x y z : DkMath.Analysis.DkReal)
+    (hx : Nonnegative x) (hy : Nonnegative y) (hz : Nonnegative z)
+    (n : ℕ) :
+    (mulNonneg (mulNonneg x y hx hy) z
+        (nonnegative_mulNonneg hx hy) hz).interval n
+      =
+    (mulNonneg x (mulNonneg y z hy hz)
+        hx (nonnegative_mulNonneg hy hz)).interval n := by
+  apply GapInterval.ext <;>
+    simp [mulNonneg, mulNonnegApprox, mul_assoc]
+
+/-- Nonnegative multiplication distributes over addition from the left stagewise. -/
+theorem left_distrib_interval
+    (x y z : DkMath.Analysis.DkReal)
+    (hx : Nonnegative x) (hy : Nonnegative y) (hz : Nonnegative z)
+    (n : ℕ) :
+    (mulNonneg x (add y z) hx (nonnegative_add hy hz)).interval n
+      =
+    (add (mulNonneg x y hx hy) (mulNonneg x z hx hz)).interval n := by
+  apply GapInterval.ext <;>
+    simp [add, addApprox, mulNonneg, mulNonnegApprox, mul_add]
+
+/-- Nonnegative multiplication distributes over addition from the right stagewise. -/
+theorem right_distrib_interval
+    (x y z : DkMath.Analysis.DkReal)
+    (hx : Nonnegative x) (hy : Nonnegative y) (hz : Nonnegative z)
+    (n : ℕ) :
+    (mulNonneg (add x y) z (nonnegative_add hx hy) hz).interval n
+      =
+    (add (mulNonneg x z hx hz) (mulNonneg y z hy hz)).interval n := by
+  apply GapInterval.ext <;>
+    simp [add, addApprox, mulNonneg, mulNonnegApprox, add_mul]
+
 end DkMath.Analysis.DkReal
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index a40cd97a..0f418873 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -54,7 +54,8 @@ DkMath.Analysis.DkReal.PowBound
   finite-sum gapGN bounds and the completed nonnegative power map
 
 DkMath.Analysis.DkReal.Arithmetic
-  computable interval addition and nonnegative multiplication
+  computable interval addition, nonnegative multiplication, and stagewise
+  semiring laws
 
 DkMath.Analysis.DkReal
   public entry point for the computable approximation layer
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md b/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
index 3030bf6f..ccbc20b9 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
@@ -139,3 +139,38 @@ restriction; multiplication currently remains on the nonnegative quadrant so
 that endpoint multiplication is order preserving. These operations establish
 the computational core needed for a future nonnegative ordered-semiring API,
 before introducing a semantic map to Mathlib's `Real`.
+
+## Nonnegative Computable Semiring Core
+
+The arithmetic layer now proves the expected semiring laws at every finite
+observation stage:
+
+```lean
+add_assoc_interval
+add_comm_interval
+add_zero_interval
+zero_add_interval
+mulNonneg_assoc_interval
+mulNonneg_comm_interval
+mulNonneg_one_interval
+one_mulNonneg_interval
+left_distrib_interval
+right_distrib_interval
+```
+
+These statements identify the rational intervals produced at a fixed stage.
+They do not use the raw structure equality of `DkReal`. This distinction is
+essential: two different nested interval sequences may eventually represent
+the same real number without being definitionally equal as Lean structures.
+
+Consequently, no `Add`, `Mul`, or semiring typeclass instance is introduced
+yet. The implementation has a computable nonnegative semiring core at the
+observation level, but a formal algebraic structure should wait until the
+representation equivalence has been chosen and its congruence properties have
+been proved.
+
+Candidate equivalence principles include persistent interval intersection,
+vanishing separation between two approximations, or equality after a future
+evaluation map into Mathlib's `Real`. These formulations are not
+interchangeable by definition, so selecting one is a mathematical design
+decision rather than a routine API addition.
````
`````
