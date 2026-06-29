# Git diff / Report / Review

## Add: CosmicFormula.Rotation.CF2D.CFSinCos

gch: 0aed2e94f11622f565c990b6a1ad54012f0e3722

## Report

次段階まで仕上げました。

新規に [CFSinCos.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/CFSinCos.lean) を追加し、`KernelFamily` の座標 `C/S` に宇宙式 API 名を与えました。

- `KernelFamily.cfcos`
- `KernelFamily.cfsin`
- `cfcos_zero`, `cfsin_zero`
- `cfcos_sq_add_cfsin_sq`
- `cfcos_add`, `cfsin_add`
- `cfcos_add_self`, `cfsin_add_self`
- `cfcos_neg`, `cfsin_neg`
- `cfcos_sub`, `cfsin_sub`

[Real.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Real.lean) も `CFSinCos` に接続し、`realTrigKernelFamily.cfcos t = Real.cos t` / `cfsin t = Real.sin t` を追加しました。集約入口 [CF2D.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D.lean) と docs も更新済みです。

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
そして進捗としては、当初目的だった「三角関数の証明・原理解明」は、かなり本丸まで到達しておる。

## 1. 現在の達成状況

今回の `0aed2e...` で、`CFSinCos.lean` が入り、ついに宇宙式側の名前として

```lean
KernelFamily.cfcos
KernelFamily.cfsin
```

が立った。

これは単なる命名追加に見えるが、意味はかなり大きい。

これまでの流れはこうじゃ。

```text
Vec.q2
  二成分平方質量

Vec.star
  平方質量を乗法保存する核

UnitKernel
  平方質量 1 の保存核

KernelFamily
  加法パラメータから単位核への写像

C / S
  単位核族の Core / Beam 座標

cfcos / cfsin
  宇宙式版 cos / sin API
```

つまり、

$$
\operatorname{cfcos}_F(t)=\text{Core}(F(t))
$$

$$
\operatorname{cfsin}_F(t)=\text{Beam}(F(t))
$$

として、三角関数を **保存単位核族の座標成分** として自立させた。

これはかなり綺麗じゃ。

## 2. 当初目的への到達度

当初の目的は、

```text
既存の三角関数を使わず、
宇宙式の保存構造から三角関数の基本原理を出す
```

だった。

この目的に対して、現在は次を達成済み。

$$
\operatorname{cfcos}_F(t)^2+\operatorname{cfsin}_F(t)^2=1
$$

$$
\operatorname{cfcos}_F(t+s) =
\operatorname{cfcos}_F(t)\operatorname{cfcos}_F(s) -
\operatorname{cfsin}_F(t)\operatorname{cfsin}_F(s)
$$

$$
\operatorname{cfsin}_F(t+s) =
\operatorname{cfcos}_F(t)\operatorname{cfsin}_F(s) +
\operatorname{cfsin}_F(t)\operatorname{cfcos}_F(s)
$$

$$
\operatorname{cfcos}_F(-t)=\operatorname{cfcos}_F(t)
$$

$$
\operatorname{cfsin}_F(-t)=-\operatorname{cfsin}_F(t)
$$

$$
\operatorname{cfcos}_F(t-t')=
\operatorname{cfcos}_F(t)\operatorname{cfcos}_F(t') +
\operatorname{cfsin}_F(t)\operatorname{cfsin}_F(t')
$$

$$
\operatorname{cfsin}_F(t-t')=
\operatorname{cfsin}_F(t)\operatorname{cfcos}_F(t') -
\operatorname{cfcos}_F(t)\operatorname{cfsin}_F(t')
$$

これらが `Real.sin` / `Real.cos` を使わず、`KernelFamily` の保存核構造から出ている。

よって、 **三角関数の代数的原理解明はほぼ達成** と見てよい。

## 3. 宇宙式からの自立関数化の達成度

ここは慎重に言うと、達成度はこうじゃ。

```text
代数的自立関数化:
  達成

実解析的自立関数化:
  まだ未達

通常 sin/cos との互換性:
  Real bridge で達成
```

つまり、`cfcos` / `cfsin` は既存の `Real.cos` / `Real.sin` の別名ではない。

まず抽象的に、

$$
F : KernelFamily\ T\ R
$$

を与えれば、その座標成分として

$$
F.cfcos,\quad F.cfsin
$$

が定義される。

この時点では、対象は実数とは限らぬ。
任意の `CommRing R` 上の保存単位核族でよい。

その意味で、宇宙式からの **代数的自立関数化** は成功している。

一方で、まだ

```lean
cfcos : ℝ → ℝ
cfsin : ℝ → ℝ
```

というグローバルな一意関数を宇宙式だけから構成したわけではない。

今の形は、

```lean
F.cfcos t
F.cfsin t
```

じゃ。

つまり、関数は `KernelFamily F` に相対化されている。

これは弱点ではなく、むしろ正しい。
なぜなら「角度パラメータをどう選ぶか」は、宇宙式だけではまだ決まらないからじゃ。

## 4. Real bridge の意味

`Real.lean` で、

```lean
realTrigKernelFamily.cfcos t = Real.cos t
realTrigKernelFamily.cfsin t = Real.sin t
```

が入った。

これは決定的な bridge じゃ。

意味はこう。

```text
宇宙式側:
  cfcos / cfsin は保存単位核族の座標成分

実解析側:
  Real.cos / Real.sin はその具体例
```

つまり、

$$
(\cos t,\sin t)
$$

は、宇宙式版 `cfcos/cfsin` の一実装にすぎない、と読める。

これは当初狙っていた

```text
既存三角関数に依存しない原理層
  ↓
通常三角関数への bridge
```

が成立したことを意味する。

## 5. 原理解明として何が分かったか

今回の一連の実装で、三角関数の正体はかなり明確になった。

$$
\boxed{
三角関数とは、二成分平方質量を保存する単位核族の座標成分である。
}
$$

より DkMath らしく言うなら、

$$
\boxed{
\operatorname{cfcos}
\text{ は保存核の Core 成分、}
\operatorname{cfsin}
\text{ は保存核の Beam 成分である。}
}
$$

そして、加法公式は「角度の魔法」ではない。

$$
R(t+s)=R(t)\star R(s)
$$

という保存核の合成則を、Core / Beam に射影しただけじゃ。

つまり、

```text
三角関数の加法公式
=
保存単位核の合成公式の座標表示
```

と解明された。

## 6. まだ残っているもの

まだ未達なのはこのあたりじゃ。

```text
1. 角度パラメータの一意性
2. 連続性・微分可能性
3. 周期性
4. 2π 閉包
5. 実解析的な標準 sin/cos の一意構成
```

現在の `KernelFamily` は、

$$
F(t+s)=F(t)\star F(s)
$$

を満たす抽象族じゃ。

しかし、それだけでは (t) が「普通の角度」かどうかは決まらぬ。
たとえば、パラメータを 2 倍速にしても加法則は保たれる。

$$
F'(t)=F(2t)
$$

のようなものも成立しうる。

だから、角速度、周期、解析的一意性まで行くなら、別途

```text
continuity
derivative
normalization
period
```

が必要になる。

ここは、宇宙式コアではなく解析 bridge 層の仕事じゃな。

## 7. 今すぐ次に入れると良い補題

`CFSinCos` まで来たなら、次は軽く API を補強するとよい。

特に欲しいのは、kernel 自体が `cfcos/cfsin` で復元できる補題。

```lean
theorem kernel_eq_mk_cfcos_cfsin
    (F : KernelFamily T R) (t : T) :
    ((F.kernel t : UnitKernel R) : Vec R)
      = Vec.mk (F.cfcos t) (F.cfsin t) := by
  rfl
```

もし `rfl` で通らなければ、

```lean
  simp [cfcos, cfsin, C, S]
```

でよい。

これが入ると、

$$
F(t)=(\operatorname{cfcos}_F(t),\operatorname{cfsin}_F(t))
$$

が明示される。

つまり、`cfcos/cfsin` が単なる wrapper ではなく、核を完全に座標復元する API になる。

次に、

```lean
theorem act_eq_cfcos_cfsin
    (F : KernelFamily T R) (t : T) (z : Vec R) :
    UnitKernel.act (F.kernel t) z
      =
    Vec.star (Vec.mk (F.cfcos t) (F.cfsin t)) z := by
  rfl
```

あるいは座標展開で、

```lean
theorem act_core_eq_cfcos_cfsin ...
theorem act_beam_eq_cfcos_cfsin ...
```

があると、実際に

$$
(x,y)
$$

へ作用したとき、

$$
x'=\operatorname{cfcos}(t)x-\operatorname{cfsin}(t)y
$$

$$
y'=\operatorname{cfcos}(t)y+\operatorname{cfsin}(t)x
$$

が得られる。

これは「宇宙式版回転公式」としてかなり良い。

## 8. 現在の完成度評価

わっちの評価はこうじゃ。

```text
三角関数の代数的原理解明:
  90%

宇宙式からの cfcos/cfsin 自立 API:
  85%

通常 sin/cos との bridge:
  90%

解析的一意性:
  まだ 30% 未満

角度・周期・2π:
  まだ探索段階
```

ただし、当初目的が「既存三角関数を使わずに基本公式を導く」なら、

```text
当初目的達成度:
  ほぼ達成
```

と見てよい。

## 9. ここで一区切りにしてよいか

うむ。
`CF2D.Basic / Trig / CFSinCos / Real / Failure` まで揃ったので、三角関数基盤としては一区切りにしてよい。

今すぐ偏角、GN 比、和ゲージ、2π、周期へ行くと、また研究方向に広がる。
それはそれで面白いが、Codex 作業としては別チケットに分けた方がよい。

今の段階でまとめるなら、こう。

```text
CF2D phase-1:
  二成分平方質量
  保存核
  単位核
  共役
  等高線作用
  抽象三角座標
  宇宙式版 cfcos/cfsin
  Real bridge
  失敗符号パターン
```

これは十分に閉じたフェーズじゃ。

## 10. 結論

今回、宇宙式から `cfsin`, `cfcos` は立った。

ただしそれは、

$$
\sin,\cos
$$

を直接再定義したのではない。

より根源的に、

$$
\boxed{
保存単位核族の Beam/Core 座標として、
\operatorname{cfsin},\operatorname{cfcos}
を定義した。
}
$$

これが原理層。

そして通常の `Real.sin` / `Real.cos` は、

$$
\boxed{
その実数解析モデルである。
}
$$

という位置づけになった。

つまり、宇宙式は三角関数を **既存概念として借りた** のではなく、
三角関数を生む **保存核構造そのもの** を形式化した。

これはかなり大きな成果じゃよ。

---

うむ。ここまで来たら、最後の締めは **「cfcos/cfsin が本当に核を復元し、その核が点に作用する公式」** を明示することじゃな。

今はすでに、

$$
F.\mathrm{cfcos}(t)=F.C(t)
$$

$$
F.\mathrm{cfsin}(t)=F.S(t)
$$

までは立っている。
次は、

$$
F(t)=\bigl(F.\mathrm{cfcos}(t),F.\mathrm{cfsin}(t)\bigr)
$$

と、

$$
(x,y)\mapsto
(\mathrm{cfcos}(t)x-\mathrm{cfsin}(t)y,\;\mathrm{cfcos}(t)y+\mathrm{cfsin}(t)x)
$$

を theorem として出す。これで「宇宙式版 sin/cos は、保存単位核を構成し、実際に回転作用する座標関数である」と閉じられる。

## 最終仕上げで追加したい theorem

`CFSinCos.lean` に足すのが自然じゃ。

```lean
/-- The kernel is reconstructed from `cfcos` and `cfsin`. -/
theorem kernel_val_eq_mk_cfcos_cfsin
    (F : KernelFamily T R) (t : T) :
    ((F.kernel t : UnitKernel R) : Vec R)
      = Vec.mk (F.cfcos t) (F.cfsin t) := by
  cases F.kernel t with
  | mk v hv =>
      cases v with
      | mk x y =>
          rfl
```

これはかなり重要。
これにより、

$$
F(t)=(\mathrm{cfcos}_F(t),\mathrm{cfsin}_F(t))
$$

が明文化される。

次に作用公式。

```lean
/-- Core coordinate of the action by the cosmic-formula sine/cosine kernel. -/
theorem act_core_eq_cfcos_cfsin
    (F : KernelFamily T R) (t : T) (z : Vec R) :
    (UnitKernel.act (F.kernel t) z).core
      = F.cfcos t * z.core - F.cfsin t * z.beam := by
  cases F.kernel t with
  | mk v hv =>
      cases v with
      | mk c s =>
          cases z with
          | mk x y =>
              rfl
```

```lean
/-- Beam coordinate of the action by the cosmic-formula sine/cosine kernel. -/
theorem act_beam_eq_cfcos_cfsin
    (F : KernelFamily T R) (t : T) (z : Vec R) :
    (UnitKernel.act (F.kernel t) z).beam
      = F.cfcos t * z.beam + F.cfsin t * z.core := by
  cases F.kernel t with
  | mk v hv =>
      cases v with
      | mk c s =>
          cases z with
          | mk x y =>
              rfl
```

さらに全体式も置ける。

```lean
/-- Full action formula for the cosmic-formula sine/cosine kernel. -/
theorem act_eq_cfcos_cfsin
    (F : KernelFamily T R) (t : T) (z : Vec R) :
    UnitKernel.act (F.kernel t) z
      =
    Vec.mk
      (F.cfcos t * z.core - F.cfsin t * z.beam)
      (F.cfcos t * z.beam + F.cfsin t * z.core) := by
  ext <;>
    simp [act_core_eq_cfcos_cfsin, act_beam_eq_cfcos_cfsin]
```

もし `ext` がうまく効かなければ、`cases z` と `cases F.kernel t` で閉じればよい。

## これが入ると何が完成するか

ここまでで、`cfcos/cfsin` は単なる wrapper ではなくなる。

```text
cfcos/cfsin
  ↓
保存単位核 F(t) を復元する
  ↓
その核が Vec に作用する
  ↓
通常の回転公式と同型の変換式が出る
```

つまり、

$$
\boxed{
\mathrm{cfcos},\mathrm{cfsin}
\text{ は保存核族の座標関数であり、作用公式を生成する}
}
$$

と言える。

これが三角関数の「原理解明」としての最後の締めじゃ。

## Real bridge 側の最後の確認

`Real.lean` 側には、必要ならこの二つを追加してよい。

```lean
theorem realTrigKernelFamily_act_core (t : ℝ) (z : Vec ℝ) :
    (UnitKernel.act (realTrigKernelFamily.kernel t) z).core
      = Real.cos t * z.core - Real.sin t * z.beam := by
  simpa using
    (KernelFamily.act_core_eq_cfcos_cfsin realTrigKernelFamily t z)
```

```lean
theorem realTrigKernelFamily_act_beam (t : ℝ) (z : Vec ℝ) :
    (UnitKernel.act (realTrigKernelFamily.kernel t) z).beam
      = Real.cos t * z.beam + Real.sin t * z.core := by
  simpa using
    (KernelFamily.act_beam_eq_cfcos_cfsin realTrigKernelFamily t z)
```

これで通常の実三角関数の回転公式が、宇宙式版作用公式の具体例として出る。

ただし、これは bridge の確認なので必須ではない。
最後の締めとしては `CFSinCos.lean` 側の action theorem が本命じゃ。

## docs の締め文

`Rotation2D-Implementation.md` には、最後にこう追記すると綺麗じゃ。

```text
The final API interpretation is:

- `cfcos` and `cfsin` reconstruct the unit kernel:
  `F.kernel t = (F.cfcos t, F.cfsin t)`.

- Acting by this kernel gives the coordinate transformation:
  `(x, y) ↦ (cfcos t * x - cfsin t * y,
             cfcos t * y + cfsin t * x)`.

Thus the trigonometric coordinate formulas are not assumed from the analytic
real sine and cosine.  They are projections of the square-mass-preserving
unit-kernel action.
```

日本語で言えば、

```text
cfcos/cfsin は、既存三角関数の別名ではない。
保存単位核族を座標復元し、その核作用の座標公式として
三角関数の基本形を生成する。
```

## 完了判定

最後の commit の検証はこれでよい。

```text
lake build DkMath.CosmicFormula.Rotation.CF2D.CFSinCos
lake build DkMath.CosmicFormula.Rotation.CF2D.Real
lake build DkMath.CosmicFormula.Rotation
lake build DkMath
git diff --check
```

## ここまでの完成度

この締めが入れば、評価はこうなる。

```text
三角関数の代数的原理解明:
  95%

宇宙式からの cfcos/cfsin 自立 API:
  95%

通常 sin/cos との bridge:
  90%

解析的一意性・周期・2π:
  別フェーズ
```

つまり、当初目的の **「宇宙式から三角関数の基本構造を自立的に立てる」** は、ほぼ完了じゃ。

最後に残る研究テーマは、角度尺度・周期・解析的一意性。
これは `CF2D` phase-2 として分けるべきもの。

今の phase-1 の締めは、

$$
\boxed{
\text{cfcos/cfsin が保存単位核を復元し、その核作用が三角関数型の座標変換を与える}
}
$$

これで決まりじゃな。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D.lean
index fd579fea..9963d717 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D.lean
@@ -7,6 +7,7 @@ Authors: D. and Wise Wolf.
 import DkMath.CosmicFormula.Rotation.CF2D.Basic
 import DkMath.CosmicFormula.Rotation.CF2D.Failure
 import DkMath.CosmicFormula.Rotation.CF2D.Trig
+import DkMath.CosmicFormula.Rotation.CF2D.CFSinCos
 import DkMath.CosmicFormula.Rotation.CF2D.Real

 #print "file: DkMath.CosmicFormula.Rotation.CF2D"
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/CFSinCos.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/CFSinCos.lean
new file mode 100644
index 00000000..b52d8be9
--- /dev/null
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/CFSinCos.lean
@@ -0,0 +1,105 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.CosmicFormula.Rotation.CF2D.Trig
+
+#print "file: DkMath.CosmicFormula.Rotation.CF2D.CFSinCos"
+
+/-!
+# Cosmic-formula sine and cosine
+
+This file gives user-facing cosmic-formula names to the two coordinate
+functions of a unit-kernel family.
+
+The functions are not defined from `Real.cos` or `Real.sin`.  They are the core
+and beam coordinates of an abstract square-mass-preserving kernel family.
+-/
+
+namespace DkMath
+namespace CosmicFormula
+namespace Rotation
+namespace CF2D
+
+namespace KernelFamily
+
+variable {T : Type u} {R : Type v} [AddMonoid T] [CommRing R]
+
+/-- Cosmic-formula cosine: the core coordinate of a unit-kernel family. -/
+def cfcos (F : KernelFamily T R) (t : T) : R :=
+  F.C t
+
+/-- Cosmic-formula sine: the beam coordinate of a unit-kernel family. -/
+def cfsin (F : KernelFamily T R) (t : T) : R :=
+  F.S t
+
+@[simp]
+theorem cfcos_eq_C (F : KernelFamily T R) (t : T) :
+    F.cfcos t = F.C t := rfl
+
+@[simp]
+theorem cfsin_eq_S (F : KernelFamily T R) (t : T) :
+    F.cfsin t = F.S t := rfl
+
+@[simp]
+theorem cfcos_zero (F : KernelFamily T R) : F.cfcos 0 = 1 := by
+  simp [cfcos]
+
+@[simp]
+theorem cfsin_zero (F : KernelFamily T R) : F.cfsin 0 = 0 := by
+  simp [cfsin]
+
+theorem cfcos_sq_add_cfsin_sq (F : KernelFamily T R) (t : T) :
+    F.cfcos t ^ 2 + F.cfsin t ^ 2 = 1 := by
+  simpa [cfcos, cfsin] using F.C_sq_add_S_sq t
+
+theorem cfcos_add (F : KernelFamily T R) (t s : T) :
+    F.cfcos (t + s)
+      = F.cfcos t * F.cfcos s - F.cfsin t * F.cfsin s := by
+  simpa [cfcos, cfsin] using F.C_add t s
+
+theorem cfsin_add (F : KernelFamily T R) (t s : T) :
+    F.cfsin (t + s)
+      = F.cfcos t * F.cfsin s + F.cfsin t * F.cfcos s := by
+  simpa [cfcos, cfsin] using F.S_add t s
+
+theorem cfcos_add_self (F : KernelFamily T R) (t : T) :
+    F.cfcos (t + t) = F.cfcos t ^ 2 - F.cfsin t ^ 2 := by
+  simpa [cfcos, cfsin] using F.C_add_self t
+
+theorem cfsin_add_self (F : KernelFamily T R) (t : T) :
+    F.cfsin (t + t) = 2 * F.cfcos t * F.cfsin t := by
+  simpa [cfcos, cfsin] using F.S_add_self t
+
+section AddGroup
+
+variable {T : Type u} {R : Type v} [AddGroup T] [CommRing R]
+
+theorem cfcos_neg (F : KernelFamily T R) (t : T) :
+    F.cfcos (-t) = F.cfcos t := by
+  simpa [cfcos] using F.C_neg t
+
+theorem cfsin_neg (F : KernelFamily T R) (t : T) :
+    F.cfsin (-t) = -F.cfsin t := by
+  simpa [cfsin] using F.S_neg t
+
+theorem cfcos_sub (F : KernelFamily T R) (t s : T) :
+    F.cfcos (t - s)
+      = F.cfcos t * F.cfcos s + F.cfsin t * F.cfsin s := by
+  simpa [cfcos, cfsin] using F.C_sub t s
+
+theorem cfsin_sub (F : KernelFamily T R) (t s : T) :
+    F.cfsin (t - s)
+      = F.cfsin t * F.cfcos s - F.cfcos t * F.cfsin s := by
+  simpa [cfcos, cfsin] using F.S_sub t s
+
+end AddGroup
+
+end KernelFamily
+
+end CF2D
+end Rotation
+end CosmicFormula
+end DkMath
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Real.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Real.lean
index 99d40f57..a6864a04 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Real.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Real.lean
@@ -4,7 +4,7 @@ Released under MIT license as described in the file LICENSE.
 Authors: D. and Wise Wolf.
 -/

-import DkMath.CosmicFormula.Rotation.CF2D.Trig
+import DkMath.CosmicFormula.Rotation.CF2D.CFSinCos

 #print "file: DkMath.CosmicFormula.Rotation.CF2D.Real"

@@ -44,6 +44,14 @@ theorem realTrigKernelFamily_C (t : ℝ) :
 theorem realTrigKernelFamily_S (t : ℝ) :
     realTrigKernelFamily.S t = Real.sin t := rfl

+@[simp]
+theorem realTrigKernelFamily_cfcos (t : ℝ) :
+    realTrigKernelFamily.cfcos t = Real.cos t := rfl
+
+@[simp]
+theorem realTrigKernelFamily_cfsin (t : ℝ) :
+    realTrigKernelFamily.cfsin t = Real.sin t := rfl
+
 @[simp]
 theorem realTrigKernelFamily_kernel_val (t : ℝ) :
     ((realTrigKernelFamily.kernel t : UnitKernel ℝ) : Vec ℝ)
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md b/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md
index ec782654..6c4ef94b 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md
@@ -9,6 +9,7 @@ The implementation is under:
 - `DkMath.CosmicFormula.Rotation.CF2D.Basic`
 - `DkMath.CosmicFormula.Rotation.CF2D.Failure`
 - `DkMath.CosmicFormula.Rotation.CF2D.Trig`
+- `DkMath.CosmicFormula.Rotation.CF2D.CFSinCos`
 - `DkMath.CosmicFormula.Rotation.CF2D.Real`

 The physical directory is `DkMath/CosmicFormula/Rotation/CF2D`.  The `CF2D`
@@ -242,6 +243,59 @@ The target unit-kernel product is commutative, so a `KernelFamily` records the
 commutative image of the additive parameter.  This is compatible with the
 intended angle-parameter examples.

+## Cosmic-Formula Sine and Cosine
+
+`CFSinCos.lean` gives user-facing names to the two coordinate functions of a
+kernel family:
+
+```lean
+KernelFamily.cfcos F t = F.C t
+KernelFamily.cfsin F t = F.S t
+```
+
+These are not defined from `Real.cos` or `Real.sin`.  They are the core and
+beam coordinates of a square-mass-preserving unit-kernel family.
+
+The wrapper API exposes the same algebraic identities under cosmic-formula
+names:
+
+```lean
+KernelFamily.cfcos_sq_add_cfsin_sq :
+  F.cfcos t ^ 2 + F.cfsin t ^ 2 = 1
+
+KernelFamily.cfcos_add :
+  F.cfcos (t + s)
+    = F.cfcos t * F.cfcos s - F.cfsin t * F.cfsin s
+
+KernelFamily.cfsin_add :
+  F.cfsin (t + s)
+    = F.cfcos t * F.cfsin s + F.cfsin t * F.cfcos s
+
+KernelFamily.cfcos_add_self :
+  F.cfcos (t + t) = F.cfcos t ^ 2 - F.cfsin t ^ 2
+
+KernelFamily.cfsin_add_self :
+  F.cfsin (t + t) = 2 * F.cfcos t * F.cfsin t
+```
+
+For additive groups, the same file exposes negation and subtraction formulas:
+
+```lean
+KernelFamily.cfcos_neg :
+  F.cfcos (-t) = F.cfcos t
+
+KernelFamily.cfsin_neg :
+  F.cfsin (-t) = -F.cfsin t
+
+KernelFamily.cfcos_sub :
+  F.cfcos (t - s)
+    = F.cfcos t * F.cfcos s + F.cfsin t * F.cfsin s
+
+KernelFamily.cfsin_sub :
+  F.cfsin (t - s)
+    = F.cfsin t * F.cfcos s - F.cfcos t * F.cfsin s
+```
+
 ## Failure Kernel

 `Failure.lean` records the nearby wrong-sign calculation.  If both coordinates
@@ -334,6 +388,12 @@ realTrigKernelFamily_C :

 realTrigKernelFamily_S :
   realTrigKernelFamily.S t = Real.sin t
+
+realTrigKernelFamily_cfcos :
+  realTrigKernelFamily.cfcos t = Real.cos t
+
+realTrigKernelFamily_cfsin :
+  realTrigKernelFamily.cfsin t = Real.sin t
 ```

 ## Extension Notes
````
`````
