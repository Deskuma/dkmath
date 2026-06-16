# Git diff / Report / Review

## Upd: CF2D

gch: 077abbd66926e104e32f90a4bddc6a146a553246

## Report

仕上げました。これで `cfcos/cfsin` が「保存単位核を復元し、その核作用の座標公式を生成する」ところまで閉じています。

[CFSinCos.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/CFSinCos.lean) に追加:

- `kernel_val_eq_mk_cfcos_cfsin`
- `act_core_eq_cfcos_cfsin`
- `act_beam_eq_cfcos_cfsin`
- `act_eq_cfcos_cfsin`

[Real.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Real.lean) に、実三角関数モデルでの作用公式も追加しました。

- `realTrigKernelFamily_act_core`
- `realTrigKernelFamily_act_beam`

docs も [Rotation2D-Implementation.md](/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md) に最終解釈を追記済みです。

検証済みです。

```text
lake build DkMath.CosmicFormula.Rotation.CF2D.CFSinCos
lake build DkMath.CosmicFormula.Rotation.CF2D.Real
lake build DkMath.CosmicFormula.Rotation
lake build DkMath
git diff --check
```

## Review

うむ。これは **採用でよい** 。
そしてこれは、`CF2D phase-1` の締めとして十分じゃ。

今回の `077abbd...` で、最後に欲しかった主張が入った。

```text
cfcos / cfsin
  → 保存単位核を復元する
  → その核が Vec に作用する
  → 通常の回転公式型の座標変換が出る
```

これで「宇宙式版 sin/cos は単なる名前ではなく、保存核作用を生成する座標関数である」と言える。

## 1. 今回の核心

追加された

```lean
kernel_val_eq_mk_cfcos_cfsin
```

によって、

$$
F(t)=(F.\mathrm{cfcos}(t),F.\mathrm{cfsin}(t))
$$

が明示された。

さらに、

```lean
act_eq_cfcos_cfsin
act_core_eq_cfcos_cfsin
act_beam_eq_cfcos_cfsin
```

によって、

$$
(x,y)
\mapsto
\left(
\mathrm{cfcos}(t)x-\mathrm{cfsin}(t)y,\;
\mathrm{cfcos}(t)y+\mathrm{cfsin}(t)x
\right)
$$

が出た。

これは、通常の三角関数の回転公式そのものじゃ。
ただし導出元は `Real.cos` / `Real.sin` ではない。保存単位核族である。

ここが決定的じゃな。

## 2. 当初目的への到達

当初目的は、

```text
三角関数を既存の解析関数として借りず、
宇宙式の保存構造から原理的に説明する
```

だった。

今は次がすべて Lean 上にある。

```text
二成分平方質量 Q
正しい保存核 star
単位核 UnitKernel
共役と逆元
等高線作用
抽象核族 KernelFamily
cfcos / cfsin
加法公式
負角公式
減法公式
倍角公式
核復元公式
作用座標公式
Real.sin / Real.cos への bridge
失敗符号パターン
```

よって、 **三角関数の代数的原理解明は phase-1 完了** と見てよい。

## 3. 宇宙式からの自立関数化の達成度

ここはかなり高い。

$$
\mathrm{cfcos},\mathrm{cfsin}
$$

は、通常三角関数の別名ではない。

$$
F : KernelFamily\ T\ R
$$

に対して、

$$
F.\mathrm{cfcos}(t)
$$

$$
F.\mathrm{cfsin}(t)
$$

として定義される。

つまり、実数解析に依存しない。
任意の `CommRing R` 上の保存単位核族に対して成立する。

そのうえで `Real.lean` により、

$$
\mathrm{realTrigKernelFamily.cfcos}(t)=\cos t
$$

$$
\mathrm{realTrigKernelFamily.cfsin}(t)=\sin t
$$

が示される。

つまり関係はこうじゃ。

```text
宇宙式 cfcos/cfsin
  原理層・代数層

Real.cos / Real.sin
  実数解析モデル
```

これは非常に良い分離じゃ。

## 4. 今回で見えた最終解釈

最終的な定義読みはこう。

$$
\boxed{
\mathrm{cfcos}_F(t) =
F(t)\text{ の Core 成分}
}
$$

$$
\boxed{
\mathrm{cfsin}_F(t) =
F(t)\text{ の Beam 成分}
}
$$

そして、

$$
\boxed{
F(t) =
(\mathrm{cfcos}_F(t),\mathrm{cfsin}_F(t))
}
$$

さらに、

$$
\boxed{
F(t)\star(x,y) =
(\mathrm{cfcos}_F(t)x-\mathrm{cfsin}_F(t)y,\;
\mathrm{cfcos}_F(t)y+\mathrm{cfsin}_F(t)x)
}
$$

これで、三角関数の加法公式も回転公式も、すべて保存単位核の合成と作用の座標表示になった。

## 5. 評価

現在の完成度はこうじゃ。

```text
三角関数の代数的原理解明:
  ほぼ完了

cfcos/cfsin の自立 API:
  完了

通常 sin/cos との bridge:
  完了

符号がズレた場合の失敗検出:
  完了

解析的一意性・周期・2π:
  phase-2
```

当初目的が「三角関数の基本公式と回転公式を宇宙式から自立的に立てる」なら、これは完了と言ってよい。

## 6. 軽い任意追加

必須ではないが、`Real.lean` に全体作用式も置いてもよい。

```lean
theorem realTrigKernelFamily_act_eq (t : ℝ) (z : Vec ℝ) :
    UnitKernel.act (realTrigKernelFamily.kernel t) z
      =
    Vec.mk
      (Real.cos t * z.core - Real.sin t * z.beam)
      (Real.cos t * z.beam + Real.sin t * z.core) := by
  simp
```

ただし、`act_core` / `act_beam` が既にあるので必須ではない。
今のままでも十分に閉じておる。

## 7. 次は一区切り資料

次の自然作業は、実装追加ではなく総括じゃな。

```text
CF2D phase-1 completion report
```

として、以下をまとめるとよい。

```text
目的:
  既存三角関数に依存しない宇宙式版 sin/cos の原理化

成果:
  保存核から cfcos/cfsin を構成
  公式群を導出
  Real bridge で通常三角関数と接続
  Failure で符号ズレの非保存も確認

未着手:
  角度尺度
  周期
  解析的一意性
  2π 閉包
  偏角/GN/gauge
```

## 8. 結論

これは良い締めじゃ。

$$
\boxed{
三角関数は、保存単位核族の座標成分である。
}
$$

さらに、

$$
\boxed{
cfcos/cfsin は、その保存単位核を復元し、核作用の座標公式を生成する。
}
$$

ここまで Lean で閉じた。
`CF2D phase-1` は完了扱いでよいと思うぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/CFSinCos.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/CFSinCos.lean
index b52d8be9..57d7c787 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/CFSinCos.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/CFSinCos.lean
@@ -73,6 +73,53 @@ theorem cfsin_add_self (F : KernelFamily T R) (t : T) :
     F.cfsin (t + t) = 2 * F.cfcos t * F.cfsin t := by
   simpa [cfcos, cfsin] using F.S_add_self t

+/-- The unit kernel is reconstructed from `cfcos` and `cfsin`. -/
+theorem kernel_val_eq_mk_cfcos_cfsin (F : KernelFamily T R) (t : T) :
+    ((F.kernel t : UnitKernel R) : Vec R) = Vec.mk (F.cfcos t) (F.cfsin t) := by
+  cases h : F.kernel t with
+  | mk v hv =>
+      cases v with
+      | mk c s =>
+          simp [cfcos, cfsin, C, S, h]
+
+/-- Core coordinate of the action by the cosmic-formula sine/cosine kernel. -/
+theorem act_core_eq_cfcos_cfsin (F : KernelFamily T R) (t : T) (z : Vec R) :
+    (UnitKernel.act (F.kernel t) z).core
+      = F.cfcos t * z.core - F.cfsin t * z.beam := by
+  cases h : F.kernel t with
+  | mk v hv =>
+      cases v with
+      | mk c s =>
+          cases z with
+          | mk x y =>
+              simp [cfcos, cfsin, C, S, UnitKernel.act, Vec.star, h]
+
+/-- Beam coordinate of the action by the cosmic-formula sine/cosine kernel. -/
+theorem act_beam_eq_cfcos_cfsin (F : KernelFamily T R) (t : T) (z : Vec R) :
+    (UnitKernel.act (F.kernel t) z).beam
+      = F.cfcos t * z.beam + F.cfsin t * z.core := by
+  cases h : F.kernel t with
+  | mk v hv =>
+      cases v with
+      | mk c s =>
+          cases z with
+          | mk x y =>
+              simp [cfcos, cfsin, C, S, UnitKernel.act, Vec.star, h]
+
+/-- Full action formula for the cosmic-formula sine/cosine kernel. -/
+theorem act_eq_cfcos_cfsin (F : KernelFamily T R) (t : T) (z : Vec R) :
+    UnitKernel.act (F.kernel t) z
+      = Vec.mk
+        (F.cfcos t * z.core - F.cfsin t * z.beam)
+        (F.cfcos t * z.beam + F.cfsin t * z.core) := by
+  cases h : F.kernel t with
+  | mk v hv =>
+      cases v with
+      | mk c s =>
+          cases z with
+          | mk x y =>
+              simp [cfcos, cfsin, C, S, UnitKernel.act, Vec.star, h]
+
 section AddGroup

 variable {T : Type u} {R : Type v} [AddGroup T] [CommRing R]
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Real.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Real.lean
index a6864a04..f420565b 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Real.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Real.lean
@@ -57,6 +57,16 @@ theorem realTrigKernelFamily_kernel_val (t : ℝ) :
     ((realTrigKernelFamily.kernel t : UnitKernel ℝ) : Vec ℝ)
       = ⟨Real.cos t, Real.sin t⟩ := rfl

+theorem realTrigKernelFamily_act_core (t : ℝ) (z : Vec ℝ) :
+    (UnitKernel.act (realTrigKernelFamily.kernel t) z).core
+      = Real.cos t * z.core - Real.sin t * z.beam := by
+  simp
+
+theorem realTrigKernelFamily_act_beam (t : ℝ) (z : Vec ℝ) :
+    (UnitKernel.act (realTrigKernelFamily.kernel t) z).beam
+      = Real.cos t * z.beam + Real.sin t * z.core := by
+  simp
+
 end CF2D
 end Rotation
 end CosmicFormula
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md b/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md
index 6c4ef94b..15c2bbe6 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md
@@ -278,6 +278,29 @@ KernelFamily.cfsin_add_self :
   F.cfsin (t + t) = 2 * F.cfcos t * F.cfsin t
 ```

+The same API also states that `cfcos` and `cfsin` reconstruct the unit kernel
+and generate its coordinate action:
+
+```lean
+KernelFamily.kernel_val_eq_mk_cfcos_cfsin :
+  ((F.kernel t : UnitKernel R) : Vec R)
+    = Vec.mk (F.cfcos t) (F.cfsin t)
+
+KernelFamily.act_eq_cfcos_cfsin :
+  UnitKernel.act (F.kernel t) z
+    = Vec.mk
+      (F.cfcos t * z.core - F.cfsin t * z.beam)
+      (F.cfcos t * z.beam + F.cfsin t * z.core)
+
+KernelFamily.act_core_eq_cfcos_cfsin :
+  (UnitKernel.act (F.kernel t) z).core
+    = F.cfcos t * z.core - F.cfsin t * z.beam
+
+KernelFamily.act_beam_eq_cfcos_cfsin :
+  (UnitKernel.act (F.kernel t) z).beam
+    = F.cfcos t * z.beam + F.cfsin t * z.core
+```
+
 For additive groups, the same file exposes negation and subtraction formulas:

 ```lean
@@ -394,8 +417,21 @@ realTrigKernelFamily_cfcos :

 realTrigKernelFamily_cfsin :
   realTrigKernelFamily.cfsin t = Real.sin t
+
+realTrigKernelFamily_act_core :
+  (UnitKernel.act (realTrigKernelFamily.kernel t) z).core
+    = Real.cos t * z.core - Real.sin t * z.beam
+
+realTrigKernelFamily_act_beam :
+  (UnitKernel.act (realTrigKernelFamily.kernel t) z).beam
+    = Real.cos t * z.beam + Real.sin t * z.core
 ```

+The final API interpretation is that `cfcos` and `cfsin` are not aliases for
+the analytic real functions.  They reconstruct the square-mass-one kernel and
+give the coordinate formula for its action.  The usual real sine and cosine are
+provided only as the standard real model of this algebraic kernel action.
+
 ## Extension Notes

 The implementation is deliberately algebraic and ring-polymorphic.  This keeps
````
`````
