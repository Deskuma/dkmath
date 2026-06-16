# Git diff / Report / Review

## Upd: CosmicFormula.Rotation.CF2D.Trig

gch: f61f7667117da3c9b92800466f3c72cd96551159

## Report

次段階として、review の第一候補だった `KernelFamily` の零元対応を入れました。

変更内容:

- [Trig.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean:35) の `KernelFamily` を `[Add T]` から `[AddMonoid T]` に強化
- `map_zero` を追加して、保存単位核族が `0` を中立核 `(1,0)` に送ることを明示
- `KernelFamily.C_zero : F.C 0 = 1`
- `KernelFamily.S_zero : F.S 0 = 0`
- [Rotation2D-Implementation.md](/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md:82) も新 API に更新

確認:

- `lake build DkMath.CosmicFormula.Rotation.CF2D.Trig` 成功
- `lake build DkMath.CosmicFormula.Rotation` 成功
- `lake build DkMath` 成功
- `git diff --check` 成功

## Review

## 1. 総評

うむ、 **良い更新** じゃ。
今回の `KernelFamily` の `[Add] → [AddMonoid]` 強化と `map_zero` 追加は、前段の抽象三角座標 (C,S) を「加法族」から **零元を持つ単位核族** へ昇格させる自然な一手じゃな。

これで、

$$
C(0)=1,\qquad S(0)=0
$$

が Lean 上で定理名を持った。
つまり、宇宙式版三角関数の初期条件が正式に固定されたわけじゃ。

## 2. 数学的な意味

前回までの `KernelFamily` は、

$$
R(t+s)=R(t)\star R(s)
$$

だけを持つ構造だった。

今回、

$$
R(0)=(1,0)
$$

を追加したことで、これは単なる二項合成則ではなく、

```text
時間 0 では何もしない
```

という単位核の意味を持つようになった。

よって、

$$
R(0)=(C(0),S(0))=(1,0)
$$

から、

$$
C(0)=1,\qquad S(0)=0
$$

が出る。

これは既存の (\cos 0=1,\sin 0=0) を使っていない。
保存単位核族の零元条件から出している。ここが DkMath 的にきれいじゃ。

## 3. 実装判断

`[AddMonoid T]` は最小限として妥当じゃ。

今欲しいのは、

```lean
0 : T
t + s
```

なので、`AddMonoid` で十分。
まだ負元は不要なので `[AddGroup T]` へ急ぐ必要はない。

`map_zero` を `UnitKernel` の等式ではなく、

```lean
((kernel 0 : UnitKernel R) : Vec R) = Vec.one R
```

としているのも良い判断じゃ。
`UnitKernel` は証明フィールドを持つ構造なので、値としての `Vec` に落として比較する方が扱いやすい。

## 4. Review

ブロッカーは見当たらぬ。
この差分は通してよいと思う。

気になる点は docs の Lean snippet だけじゃ。

docs では概念的にこう書かれている。

```lean
map_zero : kernel 0 = Vec.one R
```

しかし実コードでは型を合わせるために coercion を入れている。

```lean
map_zero : ((kernel 0 : UnitKernel R) : Vec R) = Vec.one R
```

`map_add` も同様に、実際には `UnitKernel R` から `Vec R` へ落として比較している。
ドキュメントが「概念図」なら問題ないが、実装資料としては、ここは実コードに寄せた方が後で混乱が少ない。

## 5. 次の自然な一手

次は二方向ある。

まず安全な小補題として、

$$
C(t+0)=C(t),\qquad S(t+0)=S(t)
$$

$$
C(0+t)=C(t),\qquad S(0+t)=S(t)
$$

が `simp` で落ちるか確認し、必要なら theorem 化するのがよい。

ただし、これは `C_add`, `S_add`, `C_zero`, `S_zero` からほぼ自動で出るはずじゃ。

その次の本命は `[AddGroup T]` 版の拡張じゃな。

$$
R(-t)
$$

を扱えるようにすれば、

$$
C(-t)=C(t),\qquad S(-t)=-S(t)
$$

へ進める。
ここまで来ると、抽象三角座標の代数層はかなり三角関数らしくなる。

## 6. 結論

今回の更新は、

```text
保存単位核族
  + 加法合成
  + 零元対応
  → 抽象三角座標の初期条件
```

を Lean 上で固定したものじゃ。

評価は **採用でよい** 。
修正推奨は docs の snippet を実コード型に合わせる程度じゃな。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean
index 1127baed..ac6fab25 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean
@@ -26,20 +26,21 @@ namespace Rotation
 namespace CF2D

 /--
-An additive family of square-mass-one kernels.
+An additive-monoid family of square-mass-one kernels.

 The parameter type `T` can later be instantiated by `ℝ`, `ℤ`, a formal time
 monoid, or another additive parameter space. Continuity or analytic structure is
 deliberately not part of this algebraic layer.
 -/
-structure KernelFamily (T : Type u) (R : Type v) [Add T] [CommRing R] where
+structure KernelFamily (T : Type u) (R : Type v) [AddMonoid T] [CommRing R] where
   kernel : T → UnitKernel R
+  map_zero : ((kernel 0 : UnitKernel R) : Vec R) = Vec.one R
   map_add : ∀ t s, ((kernel (t + s) : UnitKernel R) : Vec R)
     = Vec.star ((kernel t : UnitKernel R) : Vec R) ((kernel s : UnitKernel R) : Vec R)

 namespace KernelFamily

-variable {T : Type u} {R : Type v} [Add T] [CommRing R]
+variable {T : Type u} {R : Type v} [AddMonoid T] [CommRing R]

 /-- Core coordinate of a unit-kernel family. -/
 def C (F : KernelFamily T R) (t : T) : R :=
@@ -54,6 +55,20 @@ theorem kernel_q2 (F : KernelFamily T R) (t : T) :
     Vec.q2 (((F.kernel t : UnitKernel R) : Vec R)) = 1 :=
   UnitKernel.coe_q2 (F.kernel t)

+theorem kernel_zero (F : KernelFamily T R) :
+    ((F.kernel 0 : UnitKernel R) : Vec R) = Vec.one R :=
+  F.map_zero
+
+@[simp]
+theorem C_zero (F : KernelFamily T R) : F.C 0 = 1 := by
+  have h := congrArg Vec.core F.kernel_zero
+  simpa [C, Vec.one] using h
+
+@[simp]
+theorem S_zero (F : KernelFamily T R) : F.S 0 = 0 := by
+  have h := congrArg Vec.beam F.kernel_zero
+  simpa [S, Vec.one] using h
+
 /--
 The basic identity for the coordinate functions:
 `C(t)^2 + S(t)^2 = 1`.
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md b/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md
index d957a87a..891a2c20 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md
@@ -82,11 +82,12 @@ the conserved square mass.

 ## Coordinate Functions

-`Trig.lean` defines an abstract additive family of unit kernels:
+`Trig.lean` defines an abstract additive-monoid family of unit kernels:

 ```lean
-structure KernelFamily (T R : Type u) [Add T] [CommRing R] where
+structure KernelFamily (T : Type u) (R : Type v) [AddMonoid T] [CommRing R] where
   kernel : T -> UnitKernel R
+  map_zero : kernel 0 = Vec.one R
   map_add : forall t s,
     kernel (t + s) = Vec.star (kernel t) (kernel s)
 ```
@@ -104,6 +105,12 @@ The formal identities are:
 KernelFamily.C_sq_add_S_sq :
   F.C t ^ 2 + F.S t ^ 2 = 1

+KernelFamily.C_zero :
+  F.C 0 = 1
+
+KernelFamily.S_zero :
+  F.S 0 = 0
+
 KernelFamily.C_add :
   F.C (t + s) = F.C t * F.C s - F.S t * F.S s

````
`````
