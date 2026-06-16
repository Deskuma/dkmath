# Git diff / Report / Review

## Upd: CF2D.Basic

gch: 40c73072cb806f497f49a50a1c5ea3f0a49e3597

## Report

次段階まで仕上げました。

[Basic.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean) に共役まわりの安定補題を追加しました。

- `Vec.conj_conj`
- `Vec.conj_star`
- `Vec.star_conj_self`
- `Vec.conj_star_self`
- `UnitKernel.conj`
- `UnitKernel.conj_val`
- `UnitKernel.star_conj`
- `UnitKernel.conj_star`

これで `z ⋆ conj z = (q2 z, 0)`、さらに単位核では `r ⋆ conj r = 1` と読めるようになっています。docs も [Rotation2D-Implementation.md](/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md) に反映しました。

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
`40c7307...` で `CF2D.Basic` の共役まわりがかなり綺麗に閉じた。

今回の到達点はこれじゃ。

$$
\operatorname{conj}(x,y)=(x,-y)
$$

$$
Q(\operatorname{conj} z)=Q(z)
$$

$$
z\star\operatorname{conj}(z)=(Q(z),0)
$$

$$
\operatorname{conj}(z)\star z=(Q(z),0)
$$

そして単位核では、

$$
r\star\operatorname{conj}(r)=1
$$

$$
\operatorname{conj}(r)\star r=1
$$

つまり、

$$
\boxed{\text{共役は単位核の逆元として働く}}
$$

が Lean 上で読めるようになった。

ここまで来ると、`CF2D` はもう十分に「宇宙式版の三角関数コア」を名乗れる段階じゃ。

---

## 1. 今回の意味

`Vec.conj_star` が入ったので、共役は単なる符号反転ではなく、`star` と相性のよい対称操作になった。

$$
\operatorname{conj}(r\star z)
=============================

\operatorname{conj}(r)\star\operatorname{conj}(z)
$$

さらに、

$$
z\star\operatorname{conj}(z)=(Q(z),0)
$$

により、二成分に分散していた平方質量が core 成分へ回収される。

これはかなり重要じゃ。

```text
二成分状態 z
  → 共役を掛ける
  → Beam が消える
  → q2 が Core に回収される
```

つまり、共役は「平方質量の回収操作」として読める。

---

## 2. `cfsin`, `cfcos` を作る段階に来た

うむ、ここで `cfsin`, `cfcos` を作るのは自然じゃ。

ただし、重要な点がある。

**最初から `cfcos : ℝ → ℝ`, `cfsin : ℝ → ℝ` として定義しない方がよい。**

なぜなら、宇宙式版の三角関数は、まず任意の保存単位核族

$$
F : KernelFamily\ T\ R
$$

の座標成分として生まれるからじゃ。

したがって第一段階は、

$$
\operatorname{cfcos}_F(t)=C_F(t)
$$

$$
\operatorname{cfsin}_F(t)=S_F(t)
$$

とするのがよい。

Lean では、

```lean
F.cfcos t
F.cfsin t
```

として使えるようにするのが綺麗じゃな。

---

## 3. 推奨モジュール構成

新規ファイルを切るのがよい。

```text
DkMath/CosmicFormula/Rotation/CF2D/CFSinCos.lean
```

理由は、`Trig.lean` はすでに抽象核族と (C,S) の基礎公式を持っている。
`CFSinCos.lean` は、その (C,S) に対して「宇宙式版 sin/cos という名前を与える API 層」にできる。

構成はこう。

```lean
import DkMath.CosmicFormula.Rotation.CF2D.Trig

#print "file: DkMath.CosmicFormula.Rotation.CF2D.CFSinCos"

namespace DkMath
namespace CosmicFormula
namespace Rotation
namespace CF2D

namespace KernelFamily

variable {T : Type u} {R : Type v} [AddMonoid T] [CommRing R]

/-- Cosmic-formula cosine: the core coordinate of a unit-kernel family. -/
def cfcos (F : KernelFamily T R) (t : T) : R :=
  F.C t

/-- Cosmic-formula sine: the beam coordinate of a unit-kernel family. -/
def cfsin (F : KernelFamily T R) (t : T) : R :=
  F.S t

@[simp]
theorem cfcos_eq_C (F : KernelFamily T R) (t : T) :
    F.cfcos t = F.C t := rfl

@[simp]
theorem cfsin_eq_S (F : KernelFamily T R) (t : T) :
    F.cfsin t = F.S t := rfl

end KernelFamily

end CF2D
end Rotation
end CosmicFormula
end DkMath
```

この時点で、`cfcos`, `cfsin` は単なる alias じゃ。
だが、それでよい。
数学的意味はすでに `C`, `S` に証明されている。今回はそれに宇宙式名を与える。

---

## 4. 追加すべき theorem 群

同じファイルに、宇宙式版の公式を wrapper として並べる。

```lean
@[simp]
theorem cfcos_zero (F : KernelFamily T R) :
    F.cfcos 0 = 1 := by
  simpa [cfcos] using F.C_zero

@[simp]
theorem cfsin_zero (F : KernelFamily T R) :
    F.cfsin 0 = 0 := by
  simpa [cfsin] using F.S_zero
```

基本恒等式。

```lean
theorem cfcos_sq_add_cfsin_sq (F : KernelFamily T R) (t : T) :
    F.cfcos t ^ 2 + F.cfsin t ^ 2 = 1 := by
  simpa [cfcos, cfsin] using F.C_sq_add_S_sq t
```

加法公式。

```lean
theorem cfcos_add (F : KernelFamily T R) (t s : T) :
    F.cfcos (t + s)
      = F.cfcos t * F.cfcos s - F.cfsin t * F.cfsin s := by
  simpa [cfcos, cfsin] using F.C_add t s

theorem cfsin_add (F : KernelFamily T R) (t s : T) :
    F.cfsin (t + s)
      = F.cfcos t * F.cfsin s + F.cfsin t * F.cfcos s := by
  simpa [cfcos, cfsin] using F.S_add t s
```

倍角。

```lean
theorem cfcos_add_self (F : KernelFamily T R) (t : T) :
    F.cfcos (t + t) = F.cfcos t ^ 2 - F.cfsin t ^ 2 := by
  simpa [cfcos, cfsin] using F.C_add_self t

theorem cfsin_add_self (F : KernelFamily T R) (t : T) :
    F.cfsin (t + t) = 2 * F.cfcos t * F.cfsin t := by
  simpa [cfcos, cfsin] using F.S_add_self t
```

`AddGroup` 層。

```lean
section AddGroup

variable {T : Type u} {R : Type v} [AddGroup T] [CommRing R]

theorem cfcos_neg (F : KernelFamily T R) (t : T) :
    F.cfcos (-t) = F.cfcos t := by
  simpa [cfcos] using F.C_neg t

theorem cfsin_neg (F : KernelFamily T R) (t : T) :
    F.cfsin (-t) = -F.cfsin t := by
  simpa [cfsin] using F.S_neg t

theorem cfcos_sub (F : KernelFamily T R) (t s : T) :
    F.cfcos (t - s)
      = F.cfcos t * F.cfcos s + F.cfsin t * F.cfsin s := by
  simpa [cfcos, cfsin] using F.C_sub t s

theorem cfsin_sub (F : KernelFamily T R) (t s : T) :
    F.cfsin (t - s)
      = F.cfsin t * F.cfcos s - F.cfcos t * F.cfsin s := by
  simpa [cfcos, cfsin] using F.S_sub t s

end AddGroup
```

これで、宇宙式版 `sin/cos` の基本公式 API が揃う。

---

## 5. `Real.lean` との接続

`Real.lean` は次のように変更するのがよい。

```lean
import DkMath.CosmicFormula.Rotation.CF2D.CFSinCos
```

そして追加。

```lean
@[simp]
theorem realTrigKernelFamily_cfcos (t : ℝ) :
    realTrigKernelFamily.cfcos t = Real.cos t := rfl

@[simp]
theorem realTrigKernelFamily_cfsin (t : ℝ) :
    realTrigKernelFamily.cfsin t = Real.sin t := rfl
```

もし `rfl` で通らなければ、

```lean
  simp [KernelFamily.cfcos, KernelFamily.cfsin]
```

でよい。

この bridge により、

```text
宇宙式版 cfcos/cfsin
  ↓ Real bridge
通常の Real.cos / Real.sin
```

が明示される。

---

## 6. `CF2D.lean` の import

集約入口には、

```lean
import DkMath.CosmicFormula.Rotation.CF2D.CFSinCos
```

を追加。

順番は、

```lean
import DkMath.CosmicFormula.Rotation.CF2D.Basic
import DkMath.CosmicFormula.Rotation.CF2D.Failure
import DkMath.CosmicFormula.Rotation.CF2D.Trig
import DkMath.CosmicFormula.Rotation.CF2D.CFSinCos
import DkMath.CosmicFormula.Rotation.CF2D.Real
```

が自然じゃ。

ただし `Real.lean` が `CFSinCos` を import するなら、`CF2D.lean` では `Real` の前に置くと読みやすい。

---

## 7. docs に書くべきこと

`Rotation2D-Implementation.md` に新節を追加。

```text
## Cosmic-Formula Sine and Cosine

`CFSinCos.lean` gives user-facing names to the two coordinate functions of a
kernel family.

KernelFamily.cfcos F t = F.C t
KernelFamily.cfsin F t = F.S t

These are not defined from `Real.cos` or `Real.sin`.  They are the core and
beam coordinates of a square-mass-preserving unit-kernel family.

The usual real sine and cosine appear only in `Real.lean`, where
`realTrigKernelFamily.cfcos t = Real.cos t` and
`realTrigKernelFamily.cfsin t = Real.sin t`.
```

日本語で整理するなら、

```text
cfcos/cfsin は既存三角関数の別名ではない。
保存単位核族の Core/Beam 座標に、宇宙式側の名前を与えたものである。
```

これが重要じゃ。

---

## 8. 今回やらない方がよいこと

この勢いでやりたくなるが、まだ避けるべきものがある。

```text
避ける:
  global な cfcos : ℝ → ℝ
  global な cfsin : ℝ → ℝ
  notation sin_cf, cos_cf
  Group instance for UnitKernel
  偏角 / slope / gauge / GN 比との接続
```

理由は、まだ API の主語を崩さない方がよいからじゃ。

今の主語は、

$$
F : KernelFamily\ T\ R
$$

である。

つまり、

$$
F.cfcos,\quad F.cfsin
$$

が正しい。

---

## 9. Codex への作業指示としてはこう

```text
Task: Add CF2D cosmic-formula sine/cosine API.

1. Add new file:
   DkMath/CosmicFormula/Rotation/CF2D/CFSinCos.lean

2. Import:
   DkMath.CosmicFormula.Rotation.CF2D.Trig

3. In namespace KernelFamily, define:
   cfcos F t := F.C t
   cfsin F t := F.S t

4. Add wrapper theorems:
   cfcos_zero
   cfsin_zero
   cfcos_sq_add_cfsin_sq
   cfcos_add
   cfsin_add
   cfcos_add_self
   cfsin_add_self
   cfcos_neg
   cfsin_neg
   cfcos_sub
   cfsin_sub

5. Update Real.lean to import CFSinCos and add:
   realTrigKernelFamily_cfcos
   realTrigKernelFamily_cfsin

6. Update CF2D.lean aggregate imports.

7. Update Rotation2D-Implementation.md with a “Cosmic-Formula Sine and Cosine” section.

8. Verify:
   lake build DkMath.CosmicFormula.Rotation.CF2D.CFSinCos
   lake build DkMath.CosmicFormula.Rotation.CF2D.Real
   lake build DkMath.CosmicFormula.Rotation
   lake build DkMath
   git diff --check
```

---

## 10. まとめ

うむ。
今こそ `cfsin`, `cfcos` を作る時じゃ。

ただし、それらは通常三角関数の再定義ではない。

$$
\boxed{
\operatorname{cfcos}_F(t)=\text{保存単位核 }F(t)\text{ の Core 成分}
}
$$

$$
\boxed{
\operatorname{cfsin}_F(t)=\text{保存単位核 }F(t)\text{ の Beam 成分}
}
$$

じゃ。

そして Real bridge で初めて、

$$
\operatorname{cfcos}_{real}(t)=\cos t
$$

$$
\operatorname{cfsin}_{real}(t)=\sin t
$$

と読む。

これで、宇宙式版三角関数の API が正式に立つ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean
index d21f29b6..2df0bd0c 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean
@@ -151,6 +151,35 @@ theorem q2_conj [CommRing R] (z : Vec R) : q2 (conj z) = q2 z := by
   | mk x y =>
       simp [q2, conj]

+@[simp]
+theorem conj_conj [Ring R] (z : Vec R) : conj (conj z) = z := by
+  cases z with
+  | mk x y =>
+      simp [conj]
+
+theorem conj_star [CommRing R] (r z : Vec R) :
+    conj (star r z) = star (conj r) (conj z) := by
+  cases r with
+  | mk a b =>
+      cases z with
+      | mk x y =>
+          simp [conj, star]
+          ring
+
+theorem star_conj_self [CommRing R] (z : Vec R) :
+    star z (conj z) = Vec.mk (q2 z) 0 := by
+  cases z with
+  | mk x y =>
+      simp [star, conj, q2]
+      constructor <;> ring
+
+theorem conj_star_self [CommRing R] (z : Vec R) :
+    star (conj z) z = Vec.mk (q2 z) 0 := by
+  cases z with
+  | mk x y =>
+      simp [star, conj, q2]
+      constructor <;> ring
+
 end Vec

 /-- A map preserves the two-component square mass. -/
@@ -190,6 +219,15 @@ theorem ext [Semiring R] {r s : UnitKernel R} (h : (r : Vec R) = (s : Vec R)) :
 def one (R : Type u) [CommRing R] : UnitKernel R :=
   ⟨Vec.one R, by simp [Vec.q2, Vec.one]⟩

+/-- Conjugation of a unit kernel. -/
+def conj [CommRing R] (r : UnitKernel R) : UnitKernel R :=
+  ⟨Vec.conj (r : Vec R), by
+    rw [Vec.q2_conj, coe_q2]⟩
+
+@[simp]
+theorem conj_val [CommRing R] (r : UnitKernel R) :
+    (conj r : Vec R) = Vec.conj (r : Vec R) := rfl
+
 /-- Product of two unit kernels. -/
 def star [CommRing R] (r s : UnitKernel R) : UnitKernel R :=
   ⟨Vec.star (r : Vec R) (s : Vec R), by
@@ -232,6 +270,18 @@ theorem star_comm [CommRing R] (r s : UnitKernel R) : star r s = star s r := by
       | mk sv hs =>
           simp [star, Vec.star_comm]

+@[simp]
+theorem star_conj [CommRing R] (r : UnitKernel R) : star r (conj r) = one R := by
+  apply UnitKernel.ext
+  rw [star_val, conj_val, Vec.star_conj_self]
+  simp [one, Vec.one]
+
+@[simp]
+theorem conj_star [CommRing R] (r : UnitKernel R) : star (conj r) r = one R := by
+  apply UnitKernel.ext
+  rw [star_val, conj_val, Vec.conj_star_self]
+  simp [one, Vec.one]
+
 /-- The action of a unit kernel on a two-component state. -/
 def act [CommRing R] (r : UnitKernel R) (z : Vec R) : Vec R :=
   Vec.star (r : Vec R) z
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md b/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md
index 008a82f7..ec782654 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md
@@ -55,10 +55,23 @@ Vec.conj z = (z.core, -z.beam)

 Vec.q2_conj :
   Vec.q2 (Vec.conj z) = Vec.q2 z
+
+Vec.conj_conj :
+  Vec.conj (Vec.conj z) = z
+
+Vec.conj_star :
+  Vec.conj (Vec.star r z) = Vec.star (Vec.conj r) (Vec.conj z)
+
+Vec.star_conj_self :
+  Vec.star z (Vec.conj z) = Vec.mk (Vec.q2 z) 0
+
+Vec.conj_star_self :
+  Vec.star (Vec.conj z) z = Vec.mk (Vec.q2 z) 0
 ```

 It is used to identify the second preserving sign pattern as the ordinary
-`Vec.star` action by a conjugated left kernel.
+`Vec.star` action by a conjugated left kernel.  The self-product identities
+show that conjugation recovers the square mass into the core coordinate.

 ## Unit Kernels and Rotation Reading

@@ -95,6 +108,9 @@ UnitKernel.star r s
 UnitKernel.star_val :
   (UnitKernel.star r s : Vec R) = Vec.star (r : Vec R) (s : Vec R)

+UnitKernel.conj :
+  UnitKernel R -> UnitKernel R
+
 UnitKernel.ext :
   (r : Vec R) = (s : Vec R) -> r = s

@@ -111,6 +127,12 @@ UnitKernel.star_assoc :
 UnitKernel.star_comm :
   UnitKernel.star r s = UnitKernel.star s r

+UnitKernel.star_conj :
+  UnitKernel.star r (UnitKernel.conj r) = UnitKernel.one R
+
+UnitKernel.conj_star :
+  UnitKernel.star (UnitKernel.conj r) r = UnitKernel.one R
+
 UnitKernel.act_one :
   UnitKernel.act (UnitKernel.one R) z = z

@@ -123,6 +145,8 @@ These lemmas make the unit kernels available as the abstract rotation-kernel
 surface, while the underlying product remains the same `Vec.star` calculation.
 The `act_star` theorem is the action law: multiplying kernels and then acting
 is the same as acting successively.
+The `UnitKernel.conj` theorems show that conjugation acts as the inverse of a
+unit kernel, without yet installing a global `Group` instance.

 ## Level Sets

@@ -214,6 +238,9 @@ KernelFamily.S_add_self :
 These are the cosmic-formula versions of the basic trigonometric identities:
 they are derived from conservation and kernel composition, not from existing
 trigonometric API.
+The target unit-kernel product is commutative, so a `KernelFamily` records the
+commutative image of the additive parameter.  This is compatible with the
+intended angle-parameter examples.

 ## Failure Kernel

````
`````
