# Git diff / Report / Review

## Upd: CF2D

gch: d9d233c190200541bb2149247322ca44813e4f56

## Report

次段階まで仕上げました。

[Basic.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean) に `Vec.conj`, `Vec.q2_conj` を追加しました。二成分共役で square mass が保存される形です。

[Trig.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean) には `KernelFamily.kernel_zero_one` と `KernelFamily.kernel_add_star` を追加し、`KernelFamily` が `UnitKernel.one/star` への準同型として読める wrapper を整えました。

[Failure.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Failure.lean) には `Vec.starPlusMinus_eq_star_conj_left` を追加し、plus-minus 保存パターンを「共役した左核による通常 `Vec.star`」として整理しました。docs も更新済みです。

検証済みです。

```text
lake build DkMath.CosmicFormula.Rotation.CF2D.Basic
lake build DkMath.CosmicFormula.Rotation.CF2D.Failure
lake build DkMath.CosmicFormula.Rotation.CF2D.Trig
lake build DkMath.CosmicFormula.Rotation
lake build DkMath
git diff --check
```

## Review

## 現在差分レビュー

これは **採用でよい** 。
今回の `d9d233c...` は、前回こちらで提案した整理がほぼそのまま綺麗に入っておる。

今回の意味は三つじゃ。

```text
1. Vec.conj により、二成分共役が Basic 層へ入った
2. KernelFamily が UnitKernel.one/star への準同型として読めるようになった
3. starPlusMinus が「別の主積」ではなく「共役左核による通常 star」と整理された
```

かなり安定層らしい更新じゃ。

## 1. `Vec.conj` は正しい位置に入った

`Vec.conj` を `Failure.lean` ではなく `Basic.lean` に入れたのは正解じゃ。

$$
\operatorname{conj}(x,y)=(x,-y)
$$

であり、

$$
Q(\operatorname{conj}(z))=Q(z)
$$

これは失敗例のためだけではなく、二成分平方質量そのものの基本対称性じゃ。

つまり、共役は `Failure` の補助道具ではなく、`CF2D.Basic` の基礎構造である、という判断が良い。

## 2. `KernelFamily.kernel_zero_one` / `kernel_add_star` は重要

これで `KernelFamily` は、単なる `Vec` 等式で合成則を持つ構造から、

$$
F(0)=1
$$

$$
F(t+s)=F(t)\star F(s)
$$

を満たす `UnitKernel` への写像として読めるようになった。

つまり、

$$
F:T\to UnitKernel
$$

という準同型的な見方が明示された。

これは後で docs や設計資料を書くときにも効く。
`kernel_add` は実装都合の `Vec` 値等式、`kernel_add_star` は数学的に読むための wrapper、という役割分担になった。

ここはかなり良い整理じゃ。

## 3. `starPlusMinus_eq_star_conj_left` が効いている

今回の核心はこれじゃ。

$$
\operatorname{starPlusMinus}(r,z)=\operatorname{star}(\operatorname{conj}(r),z)
$$

これにより、plus-minus 保存パターンは「第二の主積」ではなく、

```text
通常 star に、共役した左核を入れたもの
```

として説明できるようになった。

これは大きい。

符号パターン分類はこう整理できる。

```text
star:
  (ax - by, ay + bx)
  通常保存核

starPlusMinus:
  (ax + by, ay - bx)
  共役左核による通常保存核

badStarPlus:
  (ax + by, ay + bx)
  残差 +4abxy

badStarMinus:
  (ax - by, ay - bx)
  残差 -4abxy
```

つまり本質は、

$$
\boxed{
保存する符号パターンは、通常 star とその共役左核作用で説明できる。
}
$$

になった。

これは `Failure.lean` の名前とは裏腹に、保存核分類の入口になっておる。

## 4. ここで見えた構造

ここまで来ると、`CF2D.Basic` はほとんど複素数的な代数核を持っている。

$$
z=(x,y)
$$

$$
\overline z=(x,-y)
$$

$$
Q(z)=x^2+y^2
$$

$$
Q(\overline z)=Q(z)
$$

そして通常 star は、複素数積の実部・虚部と同型的に振る舞う。

ただし、まだ「複素数」とは呼ばず、

```text
二成分平方質量を保存する宇宙式核
```

として置いているのがよい。

既存概念に寄せすぎず、Lean では純代数として閉じている。

## 5. 軽い注意点

ブロッカーではないが、一つだけ意識しておくとよい。

`UnitKernel.star` は可換なので、`KernelFamily.kernel_add_star` によって、任意の `t s` について

$$
F(t+s)=F(s+t)
$$

が値として導ける。

つまり、現在の `KernelFamily` は `[AddMonoid T]` で受けているが、像は可換化される。
角度パラメータは普通 `[AddCommMonoid]` や `[AddCommGroup]` なので問題はないが、docs に将来、

```text
The target unit-kernel product is commutative, so a KernelFamily only records the commutative image of the additive parameter.
```

くらいを書いてもよい。

今すぐ型を変える必要はない。
現状維持でよい。

## 6. 次に自然な補題

次は `Vec.conj` 周りをもう少し閉じるとよい。

候補はこのあたりじゃ。

```lean
@[simp]
theorem Vec.conj_conj [Ring R] (z : Vec R) :
    Vec.conj (Vec.conj z) = z := by
  cases z
  simp [Vec.conj]
```

```lean
theorem Vec.conj_star [CommRing R] (r z : Vec R) :
    Vec.conj (Vec.star r z) = Vec.star (Vec.conj r) (Vec.conj z) := by
  cases r
  cases z
  simp [Vec.conj, Vec.star]
  ring
```

そして一番おいしいのはこれ。

```lean
theorem Vec.star_conj_self [CommRing R] (z : Vec R) :
    Vec.star z (Vec.conj z) = Vec.mk (Vec.q2 z) 0 := by
  cases z
  simp [Vec.star, Vec.conj, Vec.q2]
  ring
```

```lean
theorem Vec.conj_star_self [CommRing R] (z : Vec R) :
    Vec.star (Vec.conj z) z = Vec.mk (Vec.q2 z) 0 := by
  cases z
  simp [Vec.star, Vec.conj, Vec.q2]
  ring
```

これはかなり重要じゃ。

$$
z\star\overline z=(Q(z),0)
$$

が出る。

つまり、共役は平方質量を core 側へ回収する操作になる。

## 7. その次は UnitKernel の逆元読み

`Vec.star_conj_self` が入ると、単位核では

$$
r\star\overline r=(1,0)
$$

が出る。

つまり共役は単位核の逆元として読める。

候補：

```lean
def UnitKernel.conj [CommRing R] (r : UnitKernel R) : UnitKernel R :=
  ⟨Vec.conj (r : Vec R), by
    rw [Vec.q2_conj, UnitKernel.coe_q2]⟩
```

```lean
@[simp]
theorem UnitKernel.star_conj [CommRing R] (r : UnitKernel R) :
    UnitKernel.star r (UnitKernel.conj r) = UnitKernel.one R := by
  apply UnitKernel.ext
  -- Vec.star_conj_self と r.q2_eq_one で閉じる
```

```lean
@[simp]
theorem UnitKernel.conj_star [CommRing R] (r : UnitKernel R) :
    UnitKernel.star (UnitKernel.conj r) r = UnitKernel.one R := by
  apply UnitKernel.ext
  -- 同様
```

これで `UnitKernel` は、可換モノイドから一段進んで、実質的に「逆元を持つ保存核面」として読める。

ただし Lean の `Group` instance にするのはまだ後でよい。
まずは theorem として置くだけで十分じゃ。

## 8. 推奨次作業

次はこの順がよい。

```text
1. Vec.conj_conj
2. Vec.conj_star
3. Vec.star_conj_self
4. Vec.conj_star_self
5. UnitKernel.conj
6. UnitKernel.star_conj
7. UnitKernel.conj_star
8. docs に「共役は単位核の逆元として働く」と追記
```

ここまでで `CF2D.Basic` の安定層はかなり閉じる。

そのあとに、必要なら `Failure.lean` の符号分類表を docs に明示してもよい。

## 9. 採用判断

```text
実装品質:
  良好

数学的意味:
  大きい

設計判断:
  Vec.conj を Basic に置いたのは正しい
  starPlusMinus を共役左核作用として整理したのも正しい

懸念:
  特になし
  AddMonoid T の像が可換化される点だけ docs に軽く触れてもよい

採用:
  採用でよい

次作業:
  共役と star の基本補題、UnitKernel.conj
```

## 10. まとめ

今回の更新で、`CF2D` の符号パターンはかなり整理された。

$$
(ax+by,\;ay-bx)
$$

は謎の別保存核ではなく、

$$
\operatorname{star}(\overline r,z)
$$

だった。

そして共役は、

$$
Q(\overline z)=Q(z)
$$

を満たす平方質量保存操作として `Basic` に昇格した。

ここまで来ると次の主題は明確じゃ。

$$
\boxed{
共役は、単位核における逆元である。
}
$$

これを Lean で閉じれば、`CF2D` の代数核はかなり美しく完成する。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean
index 1edc4999..d21f29b6 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean
@@ -136,6 +136,21 @@ theorem star_comm [CommRing R] (r z : Vec R) : star r z = star z r := by
           simp [star]
           constructor <;> ring

+/-- Conjugation flips the beam coordinate and keeps the core coordinate. -/
+def conj [Neg R] (z : Vec R) : Vec R :=
+  ⟨z.core, -z.beam⟩
+
+@[simp]
+theorem conj_core [Neg R] (z : Vec R) : (conj z).core = z.core := rfl
+
+@[simp]
+theorem conj_beam [Neg R] (z : Vec R) : (conj z).beam = -z.beam := rfl
+
+theorem q2_conj [CommRing R] (z : Vec R) : q2 (conj z) = q2 z := by
+  cases z with
+  | mk x y =>
+      simp [q2, conj]
+
 end Vec

 /-- A map preserves the two-component square mass. -/
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Failure.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Failure.lean
index 20e20bf8..b9f301e7 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Failure.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Failure.lean
@@ -122,6 +122,15 @@ theorem q2_starPlusMinus [CommRing R] (r z : Vec R) :
           simp [q2, starPlusMinus]
           ring

+theorem starPlusMinus_eq_star_conj_left [CommRing R] (r z : Vec R) :
+    starPlusMinus r z = star (conj r) z := by
+  cases r with
+  | mk a b =>
+      cases z with
+      | mk x y =>
+          simp [starPlusMinus, star, conj]
+          ring
+
 end Vec

 end CF2D
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean
index 577bef6b..fa21b75b 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean
@@ -59,6 +59,11 @@ theorem kernel_zero (F : KernelFamily T R) :
     ((F.kernel 0 : UnitKernel R) : Vec R) = Vec.one R :=
   F.map_zero

+theorem kernel_zero_one (F : KernelFamily T R) :
+    F.kernel 0 = UnitKernel.one R := by
+  apply UnitKernel.ext
+  exact F.kernel_zero
+
 @[simp]
 theorem C_zero (F : KernelFamily T R) : F.C 0 = 1 := by
   have h := congrArg Vec.core F.kernel_zero
@@ -107,6 +112,11 @@ theorem kernel_add (F : KernelFamily T R) (t s : T) :
           (((F.kernel s : UnitKernel R) : Vec R)) :=
   F.map_add t s

+theorem kernel_add_star (F : KernelFamily T R) (t s : T) :
+    F.kernel (t + s) = UnitKernel.star (F.kernel t) (F.kernel s) := by
+  apply UnitKernel.ext
+  simpa using F.kernel_add t s
+
 /--
 Core addition law:
 `C(t+s) = C(t) * C(s) - S(t) * S(s)`.
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md b/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md
index fd8fd71e..008a82f7 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md
@@ -48,6 +48,18 @@ This is proved by polynomial expansion with `ring`, over an arbitrary
 commutative ring.  No trigonometric functions, circle facts, angle facts, or
 metric-space facts are used.

+The basic two-component conjugation is:
+
+```lean
+Vec.conj z = (z.core, -z.beam)
+
+Vec.q2_conj :
+  Vec.q2 (Vec.conj z) = Vec.q2 z
+```
+
+It is used to identify the second preserving sign pattern as the ordinary
+`Vec.star` action by a conjugated left kernel.
+
 ## Unit Kernels and Rotation Reading

 `UnitKernel R` packages a vector whose square mass is `1`:
@@ -143,6 +155,12 @@ KernelFamily.S F t
 The formal identities are:

 ```lean
+KernelFamily.kernel_zero_one :
+  F.kernel 0 = UnitKernel.one R
+
+KernelFamily.kernel_add_star :
+  F.kernel (t + s) = UnitKernel.star (F.kernel t) (F.kernel s)
+
 KernelFamily.C_sq_add_S_sq :
   F.C t ^ 2 + F.S t ^ 2 = 1

@@ -235,11 +253,16 @@ Vec.starPlusMinus (a,b) (x,y) = (a*x + b*y, a*y - b*x)

 Vec.q2_starPlusMinus :
   Vec.q2 (Vec.starPlusMinus r z) = Vec.q2 r * Vec.q2 z
+
+Vec.starPlusMinus_eq_star_conj_left :
+  Vec.starPlusMinus r z = Vec.star (Vec.conj r) z
 ```

 This separates the preservation kernels from superficially similar
 non-preserving kernels.  The cancellation in `Vec.q2_star` and
 `Vec.q2_starPlusMinus` depends on opposite signs in the two beam cross terms.
+The plus-minus preserving pattern is not treated as a second primary product:
+it is the usual `Vec.star` action by the conjugated left kernel.

 ## Additive Group Layer

````
`````
