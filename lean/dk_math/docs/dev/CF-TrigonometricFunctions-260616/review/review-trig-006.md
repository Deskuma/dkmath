# Git diff / Report / Review

## Upd: CF2D.Failure

gch: cbe2a9b3f7419b3cdd026c3021c482184d912ad0

## Report

次段階まで仕上げました。

[Basic.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean) に `UnitKernel.ext`, `UnitKernel.act_one`, `UnitKernel.act_star` を追加し、単位核の積が作用の合成として読めるようにしました。

[Failure.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Failure.lean) は符号パターンを拡張しています。既存の `badStarPlus` の `+4abxy` に加えて、`badStarMinus` の `-4abxy`、さらに別の保存パターン `starPlusMinus` と `q2_starPlusMinus` を追加しました。docs も [Rotation2D-Implementation.md](/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md) に反映済みです。

検証はすべて成功しています。

```text
lake build DkMath.CosmicFormula.Rotation.CF2D.Basic
lake build DkMath.CosmicFormula.Rotation.CF2D.Failure
lake build DkMath.CosmicFormula.Rotation
lake build DkMath
git diff --check
```

## Review

## 現在差分レビュー

これは **採用でよい** 。
今回の `cbe2a9...` は、前回の `Failure` 拡張としてかなり筋が良い。

今回の更新で、`CF2D` は次の段階へ進んだ。

```text
UnitKernel.star
  単位核の積

UnitKernel.act_star
  単位核の積は作用の合成として読める

Failure.lean
  符号パターンごとの保存 / 非保存を明示
```

これで、単に「正しい核なら保存される」だけでなく、 **どの符号配置なら保存され、どの符号配置なら残差が出るか** が見えるようになった。

## 1. `UnitKernel.act_star` の意味

今回の一番安定した追加はこれじゃ。

$$
\operatorname{act}(r\star s,z)=\operatorname{act}(r,\operatorname{act}(s,z))
$$

Lean では、

```lean
UnitKernel.act_star :
  act (star r s) z = act r (act s z)
```

じゃな。

これは非常に重要。
これで `UnitKernel.star` は単なる閉包演算ではなく、 **作用の合成を表す積** になった。

つまり、

```text
核を掛けてから作用する
=
順番に作用する
```

が立った。

これにより、`UnitKernel` は完全に「回転核の代数面」として読める。

## 2. `UnitKernel.ext` の追加も良い

`UnitKernel` は証明フィールドを持つ構造体なので、そのまま等式を扱うと面倒になりやすい。

今回、

```lean
UnitKernel.ext :
  (r : Vec R) = (s : Vec R) -> r = s
```

を追加したのは正解じゃ。

これで今後、

```lean
apply UnitKernel.ext
```

として、値側の `Vec` 等式だけを示せばよくなる。

この補題が入ったので、次にかなり自然な wrapper theorem を置ける。

```lean
theorem KernelFamily.kernel_zero_one (F : KernelFamily T R) :
    F.kernel 0 = UnitKernel.one R := by
  apply UnitKernel.ext
  exact F.kernel_zero
```

```lean
theorem KernelFamily.kernel_add_star (F : KernelFamily T R) (t s : T) :
    F.kernel (t + s) = UnitKernel.star (F.kernel t) (F.kernel s) := by
  apply UnitKernel.ext
  simpa [UnitKernel.star_val] using F.kernel_add t s
```

これは次に入れてよい。
`KernelFamily` が本当に

$$
T\to UnitKernel
$$

への準同型として読めるようになる。

## 3. 符号パターン分類が見えてきた

今回の `Failure.lean` 拡張はとても良い。

二成分積を、ざっくり

$$
(ax \pm by,\; ay \pm bx)
$$

の符号パターンで見ると、四通りある。

```text
(ax - by, ay + bx)
  正しい Vec.star
  残差 0

(ax + by, ay - bx)
  starPlusMinus
  残差 0

(ax + by, ay + bx)
  badStarPlus
  残差 +4abxy

(ax - by, ay - bx)
  badStarMinus
  残差 -4abxy
```

つまり、保存条件はこうじゃ。

$$
\boxed{
\text{二つの Beam 交差項の符号が反対なら保存される}
}
$$

同じ符号なら、

$$
+4abxy
$$

または

$$
-4abxy
$$

が残る。

これはかなり明快な分類になった。

## 4. `starPlusMinus` の扱いは少し注意

`starPlusMinus` は (q2) を保存する。
これは重要じゃ。

ただし、ここで一つだけ理論上の注意がある。

`starPlusMinus` は、選択済みの `UnitKernel.star` と同じ意味での「核積」として扱うより、 **共役核による作用** として読む方が自然じゃ。

もし

$$
\operatorname{conj}(a,b)=(a,-b)
$$

と置くと、

$$
\operatorname{starPlusMinus}(r,z)=\operatorname{star}(\operatorname{conj}(r),z)
$$

になる。

実際、

$$
\operatorname{star}((a,-b),(x,y))=(ax+by,;ay-bx)
$$

じゃ。

だから `starPlusMinus` は「もう一つの保存する世界」ではあるが、独立した主積というより、

```text
正しい star に、左側の共役を入れた保存作用
```

と読める。

ここは次に整理すると、かなり綺麗になる。

## 5. 次に入れるなら `Vec.conj`

次の一手はこれが良い。

```lean
def Vec.conj [Neg R] (z : Vec R) : Vec R :=
  ⟨z.core, -z.beam⟩
```

欲しい補題は、

```lean
@[simp]
theorem Vec.conj_core ...
```

```lean
@[simp]
theorem Vec.conj_beam ...
```

```lean
theorem Vec.q2_conj [CommRing R] (z : Vec R) :
    q2 (conj z) = q2 z := by
  cases z
  simp [q2, conj]
  ring
```

そして本命。

```lean
theorem Vec.starPlusMinus_eq_star_conj_left [CommRing R] (r z : Vec R) :
    starPlusMinus r z = star (conj r) z := by
  cases r
  cases z
  simp [starPlusMinus, star, conj]
```

これを入れると、`starPlusMinus` の意味がかなり安定する。

```text
Vec.star
  通常向きの保存作用

Vec.starPlusMinus
  共役核による保存作用

badStarPlus / badStarMinus
  交差 Beam が相殺されず、残差が出る作用
```

という整理になる。

## 6. docs の方向性も良い

docs に `UnitKernel.act_star` と sign pattern の説明を追記したのは良い判断じゃ。

特に、

```text
The cancellation in Vec.q2_star and Vec.q2_starPlusMinus depends on opposite signs in the two beam cross terms.
```

この読みは正しい。

ただ、今後 `Vec.conj` を入れるなら、docs には次の一文を足すとさらに良い。

```text
The plus-minus preserving pattern is the usual star action by the conjugated left kernel.
```

つまり、

$$
\operatorname{starPlusMinus}(r,z)=\operatorname{star}(\overline r,z)
$$

じゃな。

この一文で、`starPlusMinus` がただの謎の別保存核ではなくなる。

## 7. 今回の理論的到達点

ここまでで見えたことは大きい。

最初は、

$$
Q((a,b)\star(x,y))=Q(a,b)Q(x,y)
$$

だけだった。

しかし今は、

```text
なぜ保存されるのか
なぜ壊れるのか
どの符号なら保存されるのか
保存する別符号は何者なのか
```

まで見え始めている。

つまり、`CF2D` はもう単なる三角関数証明ではない。

$$
\boxed{
二成分平方質量を保存する符号構造の分類入口
}
$$

になっている。

## 8. 次作業の推奨順

いま偏角・GN 比・和ゲージへ行くとまた広がりすぎる。
ここはまだ `CF2D` の安定層を固めるのがよい。

推奨順はこれ。

```text
1. KernelFamily.kernel_zero_one を追加
2. KernelFamily.kernel_add_star を追加
3. Vec.conj を追加
4. Vec.q2_conj を追加
5. Vec.starPlusMinus_eq_star_conj_left を追加
6. docs に「starPlusMinus は共役核作用」と追記
```

これで今回の sign-pattern 拡張は、かなり綺麗に閉じる。

## 9. 採用判断

評価はこうじゃ。

```text
実装品質:
  良好

数学的意味:
  大きい

懸念:
  starPlusMinus は「別の主積」ではなく「共役核作用」と読む方が安全

採用:
  採用でよい

次作業:
  KernelFamily の UnitKernel.star wrapper と Vec.conj 整理
```

## 10. まとめ

今回の更新で、保存核の姿がはっきりした。

$$
(ax-by,\;ay+bx)
$$

だけが偶然うまくいったのではない。

本質は、

$$
\boxed{
Beam 交差項が反対符号で出て相殺されること
}
$$

じゃ。

同符号なら残差が出る。

$$
+4abxy
$$

または

$$
-4abxy
$$

反対符号なら保存される。

そして、もう一つの保存パターンは、正しい `star` に共役を入れたものとして読める。

これはかなり綺麗じゃ。
`CF2D.Failure` という名前の中に、実は「失敗だけでなく、保存核分類の芽」が入り始めておる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean
index fcb1dbf5..1edc4999 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean
@@ -162,6 +162,15 @@ instance [Semiring R] : Coe (UnitKernel R) (Vec R) :=
 theorem coe_q2 [Semiring R] (r : UnitKernel R) : Vec.q2 (r : Vec R) = 1 :=
   r.q2_eq_one
 
+@[ext]
+theorem ext [Semiring R] {r s : UnitKernel R} (h : (r : Vec R) = (s : Vec R)) : r = s := by
+  cases r with
+  | mk rv hr =>
+      cases s with
+      | mk sv hs =>
+          cases h
+          rfl
+
 /-- The neutral unit kernel `(1,0)`. -/
 def one (R : Type u) [CommRing R] : UnitKernel R :=
   ⟨Vec.one R, by simp [Vec.q2, Vec.one]⟩
@@ -212,6 +221,17 @@ theorem star_comm [CommRing R] (r s : UnitKernel R) : star r s = star s r := by
 def act [CommRing R] (r : UnitKernel R) (z : Vec R) : Vec R :=
   Vec.star (r : Vec R) z
 
+@[simp]
+theorem act_one [CommRing R] (z : Vec R) : act (one R) z = z := by
+  simp [act, one]
+
+theorem act_star [CommRing R] (r s : UnitKernel R) (z : Vec R) :
+    act (star r s) z = act r (act s z) := by
+  change Vec.star ((star r s : UnitKernel R) : Vec R) z
+      = Vec.star (r : Vec R) (Vec.star (s : Vec R) z)
+  rw [star_val]
+  exact Vec.star_assoc (r : Vec R) (s : Vec R) z
+
 @[simp]
 theorem act_core [CommRing R] (r : UnitKernel R) (z : Vec R) :
     (act r z).core = (r : Vec R).core * z.core - (r : Vec R).beam * z.beam := rfl
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Failure.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Failure.lean
index d2b490ed..20e20bf8 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Failure.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Failure.lean
@@ -11,10 +11,10 @@ import DkMath.CosmicFormula.Rotation.CF2D.Basic
 /-!
 # Failure examples for the CF2D rotation kernel
 
-This file records what breaks when the sign pattern of the two-component kernel
-is changed.  The correct kernel cancels the opposite beam terms.  The plus-plus
-kernel leaves a residual `4 * a * b * x * y`, so it does not preserve `q2` in
-general.
+This file records what happens when the sign pattern of the two-component
+kernel is changed.  The correct kernel cancels the opposite beam terms.  Some
+nearby sign patterns preserve `q2`; others leave a residual
+`± 4 * a * b * x * y`.
 -/
 
 namespace DkMath
@@ -62,10 +62,69 @@ theorem q2_badStarPlus_eq_q2_mul_add_residual [CommRing R] (r z : Vec R) :
       | mk x y =>
           simpa [q2] using q2_badStarPlus (R := R) a b x y
 
+/--
+A second wrong sign pattern.
+
+Here both beam cross terms have the negative sign, so the residual is
+`-4 * a * b * x * y`.
+-/
+def badStarMinus [Ring R] (r z : Vec R) : Vec R :=
+  ⟨r.core * z.core - r.beam * z.beam,
+    r.core * z.beam - r.beam * z.core⟩
+
+@[simp]
+theorem badStarMinus_core [Ring R] (r z : Vec R) :
+    (badStarMinus r z).core = r.core * z.core - r.beam * z.beam := rfl
+
+@[simp]
+theorem badStarMinus_beam [Ring R] (r z : Vec R) :
+    (badStarMinus r z).beam = r.core * z.beam - r.beam * z.core := rfl
+
+theorem q2_badStarMinus [CommRing R] (a b x y : R) :
+    q2 (badStarMinus (Vec.mk a b) (Vec.mk x y))
+      = (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) - 4 * a * b * x * y := by
+  simp [q2, badStarMinus]
+  ring
+
+theorem q2_badStarMinus_eq_q2_mul_sub_residual [CommRing R] (r z : Vec R) :
+    q2 (badStarMinus r z) = q2 r * q2 z - 4 * r.core * r.beam * z.core * z.beam := by
+  cases r with
+  | mk a b =>
+      cases z with
+      | mk x y =>
+          simpa [q2] using q2_badStarMinus (R := R) a b x y
+
+/--
+The plus-minus sign pattern also preserves `q2`.
+
+It is a nearby preserving kernel, distinct from the chosen `Vec.star` sign
+convention.  Recording it keeps the failure file from implying that every sign
+change necessarily breaks square-mass preservation.
+-/
+def starPlusMinus [Ring R] (r z : Vec R) : Vec R :=
+  ⟨r.core * z.core + r.beam * z.beam,
+    r.core * z.beam - r.beam * z.core⟩
+
+@[simp]
+theorem starPlusMinus_core [Ring R] (r z : Vec R) :
+    (starPlusMinus r z).core = r.core * z.core + r.beam * z.beam := rfl
+
+@[simp]
+theorem starPlusMinus_beam [Ring R] (r z : Vec R) :
+    (starPlusMinus r z).beam = r.core * z.beam - r.beam * z.core := rfl
+
+theorem q2_starPlusMinus [CommRing R] (r z : Vec R) :
+    q2 (starPlusMinus r z) = q2 r * q2 z := by
+  cases r with
+  | mk a b =>
+      cases z with
+      | mk x y =>
+          simp [q2, starPlusMinus]
+          ring
+
 end Vec
 
 end CF2D
 end Rotation
 end CosmicFormula
 end DkMath
-
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md b/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md
index 9c9c5802..fd8fd71e 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md
@@ -83,6 +83,9 @@ UnitKernel.star r s
 UnitKernel.star_val :
   (UnitKernel.star r s : Vec R) = Vec.star (r : Vec R) (s : Vec R)
 
+UnitKernel.ext :
+  (r : Vec R) = (s : Vec R) -> r = s
+
 UnitKernel.star_one :
   UnitKernel.star r (UnitKernel.one R) = r
 
@@ -95,10 +98,19 @@ UnitKernel.star_assoc :
 
 UnitKernel.star_comm :
   UnitKernel.star r s = UnitKernel.star s r
+
+UnitKernel.act_one :
+  UnitKernel.act (UnitKernel.one R) z = z
+
+UnitKernel.act_star :
+  UnitKernel.act (UnitKernel.star r s) z
+    = UnitKernel.act r (UnitKernel.act s z)
 ```
 
 These lemmas make the unit kernels available as the abstract rotation-kernel
 surface, while the underlying product remains the same `Vec.star` calculation.
+The `act_star` theorem is the action law: multiplying kernels and then acting
+is the same as acting successively.
 
 ## Level Sets
 
@@ -206,9 +218,28 @@ Vec.q2_badStarPlus_eq_q2_mul_add_residual :
     = Vec.q2 r * Vec.q2 z + 4 * r.core * r.beam * z.core * z.beam
 ```
 
-This separates the preservation kernel from a superficially similar but
-non-preserving kernel.  The cancellation in `Vec.q2_star` depends on the
-opposite signs in the two beam cross terms.
+The minus-minus variant leaves the opposite residual:
+
+```lean
+Vec.badStarMinus (a,b) (x,y) = (a*x - b*y, a*y - b*x)
+
+Vec.q2_badStarMinus_eq_q2_mul_sub_residual :
+  Vec.q2 (Vec.badStarMinus r z)
+    = Vec.q2 r * Vec.q2 z - 4 * r.core * r.beam * z.core * z.beam
+```
+
+The plus-minus variant preserves square mass:
+
+```lean
+Vec.starPlusMinus (a,b) (x,y) = (a*x + b*y, a*y - b*x)
+
+Vec.q2_starPlusMinus :
+  Vec.q2 (Vec.starPlusMinus r z) = Vec.q2 r * Vec.q2 z
+```
+
+This separates the preservation kernels from superficially similar
+non-preserving kernels.  The cancellation in `Vec.q2_star` and
+`Vec.q2_starPlusMinus` depends on opposite signs in the two beam cross terms.
 
 ## Additive Group Layer
 
````
`````
