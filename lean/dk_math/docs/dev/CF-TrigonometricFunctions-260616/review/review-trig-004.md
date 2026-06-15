# Git diff / Report / Review

## Add: CosmicFormula.Rotation.CF2D.Real

gch: 7ade82d8dd61004dabeb811501f266127a49ef79

## Report

仕上げました。今回は review の推奨順に沿って、抽象代数層を一気に閉じつつ、Real bridge まで追加しています。

実装内容:

- [Trig.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean:127)
  - `KernelFamily.act_add`
  - `KernelFamily.C_add_self`
  - `KernelFamily.S_add_self`
  - AddGroup 層: `kernel_add_neg`, `C_neg`, `S_neg`, `C_sub`, `S_sub`
- [Real.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Real.lean:1)
  - `realTrigKernelFamily : KernelFamily ℝ ℝ`
  - `realTrigKernelFamily_C`
  - `realTrigKernelFamily_S`
  - usual `Real.cos` / `Real.sin` はこの bridge 層だけで使用
- [CF2D.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D.lean:9)
  - `CF2D.Real` を集約 import に追加
- [Rotation2D-Implementation.md](/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md:1)
  - 作用則、倍角、負角、減法公式、Real bridge を追記

確認:

- `lake build DkMath.CosmicFormula.Rotation.CF2D.Trig` 成功
- `lake build DkMath.CosmicFormula.Rotation.CF2D.Real` 成功
- `lake build DkMath.CosmicFormula.Rotation` 成功
- `lake build DkMath` 成功
- `git diff --check` 成功

`UnitKernel` 自体の monoid 化は review でも後回し候補だったので、今回は入れていません。抽象三角座標の代数層と通常実三角関数への bridge までは閉じています。

## Review

## 1. 現在差分レビュー

結論、 **採用でよい** 。
今回の `7ade82d...` は、`CF2D.Trig` の代数層を一気に「抽象三角関数」として閉じ、さらに `Real.lean` で通常の `Real.cos` / `Real.sin` との互換橋まで置いた更新じゃ。報告でも、`act_add`、倍角、負角、減法公式、そして `realTrigKernelFamily : KernelFamily ℝ ℝ` まで追加し、各 build と `git diff --check` が成功していると示されておる。

今回の到達点は大きい。

$$
R(0)=(1,0)
$$

$$
R(t+s)=R(t)\star R(s)
$$

$$
C(t)^2+S(t)^2=1
$$

$$
C(t+s)=C(t)C(s)-S(t)S(s)
$$

$$
S(t+s)=C(t)S(s)+S(t)C(s)
$$

$$
C(-t)=C(t),\qquad S(-t)=-S(t)
$$

$$
C(t-s)=C(t)C(s)+S(t)S(s)
$$

$$
S(t-s)=S(t)C(s)-C(t)S(s)
$$

ここまでが、既存 `Real.sin` / `Real.cos` を使わずに、保存単位核族の代数だけで出ている。
そして `Real.lean` はあくまで bridge 層として、通常の実三角関数がこの抽象構造の具体例であることを示している。これは設計としてかなり健全じゃ。

## 2. 宇宙式だけで足りた範囲

今回、かなりはっきりした。

**代数的な三角関数の骨格までは、宇宙式だけで足りている。**

ここで言う宇宙式だけ、とはつまり、

$$
Q(x,y)=x^2+y^2
$$

という保存量と、

$$
(a,b)\star(x,y)=(ax-by,;ay+bx)
$$

という保存核、そして

$$
Q(r\star z)=Q(r)Q(z)
$$

という保存等式じゃ。

この範囲では、円も角度も微分も極限も要らない。
必要なのは、

```text id="2q8ph4"
二成分平方質量
単位核
合成則
零元
逆元
```

だけ。

だから、

$$
C^2+S^2=1
$$

も、加法公式も、倍角も、負角も、減法公式も、すべて **保存構造の影** として出た。

これはかなり強い結論じゃ。

## 3. 宇宙式だけでは足りない範囲

ただし、ここで終わりではない。

宇宙式だけで足りない、または宇宙式に追加構造が必要になる範囲も見えた。

第一に、 **どの (R(t)) を選ぶか** は宇宙式だけでは決まらない。

`KernelFamily` は、

$$
R(t+s)=R(t)\star R(s)
$$

を満たす抽象族じゃ。
しかし、連続な族か、滑らかな族か、周期を持つか、速度が 1 か、という情報はまだない。

第二に、 **角度の尺度** は宇宙式だけでは出ない。

$$
t
$$

が何を意味するのか、(1) ラジアンとは何か、(2\pi) 周期とは何か。
これは加法群・位相・解析・周期性の情報が必要になる。

第三に、 **通常の (\cos,\sin) との同定** には解析層が必要。

今回の `Real.lean` は、その橋を置いた。
ここでは標準の `Real.cos_sq_add_sin_sq`、`Real.cos_add`、`Real.sin_add` を使ってよい。なぜなら、そこは core ではなく bridge だからじゃ。

つまり結論はこう。

```text id="uk7z13"
宇宙式だけで、
三角関数の代数的骨格は建つ。

しかし、
解析的な三角関数の一意性・角度尺度・周期性・実数上の標準同定には、
追加構造が必要。
```

これは「宇宙式が足りない」というより、 **宇宙式は基礎であり、解析はその上に載る層** ということじゃな。

## 4. 基盤がズレていた場合どうなるか

ここが今回の試みの本質じゃ。

もし基盤がズレていたら、どこで壊れるか。

### 4.1. 符号がズレると壊れる

今の核は、

$$
(a,b)\star(x,y)=(ax-by,;ay+bx)
$$

じゃ。

この (-by) の符号がもし (+by) なら、展開したとき交差項が消えない。

本来は、

$$
-2abxy+2abxy=0
$$

で Beam が相殺する。

しかし符号を間違えると、

$$
+2abxy+2abxy=4abxy
$$

のように余計な Beam が残る。
すると、

$$
Q(r\star z)=Q(r)Q(z)
$$

が成り立たない。

つまり、円は出ない。保存等高線が壊れる。

### 4.2. 保存量 (Q) がズレると壊れる

もし

$$
Q(x,y)=x^2-y^2
$$

のように変えると、別の保存世界になる。

それは円ではなく双曲線側へ行く。
つまり、宇宙式の保存量の選び方が、観測される幾何を決める。

$$
x^2+y^2=\text{const}
$$

なら円。

$$
x^2-y^2=\text{const}
$$

なら双曲線。

これは面白い。
「数は円だった」のではなく、より正確には、

$$
\boxed{\text{数は、保存量の符号構造によって円にも双曲線にも見える}}
$$

じゃ。

### 4.3. 零元がないと初期条件が出ない

`map_zero` がなければ、

$$
C(0)=1,\qquad S(0)=0
$$

が出ない。

すると加法公式はあっても、「時刻 0 で何もしない」という意味がない。
これは回転族としては弱い。

### 4.4. 逆元がないと負角・減法公式が出ない

`AddGroup` に進まなければ、

$$
R(-t)
$$

が使えない。

すると、

$$
C(-t),\quad S(-t),\quad C(t-s),\quad S(t-s)
$$

が出ない。

今回それを入れたことで、抽象三角座標はかなり通常三角関数らしくなった。

## 5. 次段階実装計画レビュー

ここから 2〜3 手先までなら、わっちは次の順を推す。

## 5.1. 次手 1. `UnitKernel` の monoid 化

今は `Vec.star` があり、`UnitKernel.act` がある。
しかし `UnitKernel` 自体の合成はまだ構造化していない。

次は `Basic.lean` 側にこれを入れるのがよい。

```lean id="kxksgi"
def UnitKernel.star [CommRing R] (r s : UnitKernel R) : UnitKernel R :=
  { val := Vec.star (r : Vec R) (s : Vec R)
    q2_eq_one := by
      rw [Vec.q2_star, UnitKernel.coe_q2, UnitKernel.coe_q2, one_mul] }
```

追加候補 theorem:

```lean id="6r0u16"
UnitKernel.star_val
UnitKernel.star_assoc
UnitKernel.star_one
UnitKernel.one_star
UnitKernel.star_comm
```

これで、`KernelFamily.map_add` を将来的に

```lean id="7i9ydf"
kernel (t + s) = UnitKernel.star (kernel t) (kernel s)
```

というより自然な形へ寄せられる。

ただし、構造体等式の証明で proof irrelevance が絡む可能性がある。
無理なら、まずは `val` 等式だけを定理化するのが安全じゃ。

### 目的

```text id="3c4g4i"
Vec.star の保存核
  → UnitKernel の閉じた合成
  → KernelFamily は UnitKernel への準同型
```

この線が立つ。

## 5.2. 次手 2. `LevelSet` への KernelFamily 作用

今は `LevelSet.act` が単発 unit kernel にはある。
次は `KernelFamily` を使って、

$$
z\in Q^{-1}(\rho^2)
$$

なら、

$$
R(t)\cdot z\in Q^{-1}(\rho^2)
$$

を定理として出す。

追加候補:

```lean id="v9khd8"
def KernelFamily.actLevel
    (F : KernelFamily T R) (t : T) (z : LevelSet R rho2) :
    LevelSet R rho2 :=
  LevelSet.act (F.kernel t) z
```

```lean id="bvo0pf"
theorem KernelFamily.actLevel_zero
theorem KernelFamily.actLevel_add
```

### 目的

ここで初めて、

```text id="ewpkeb"
円 = 保存量 Q の等高線
回転 = 等高線内の自己作用
```

が Lean 上で完全につながる。

これは「なぜ線形な代数が円となるか？」への形式化回答じゃ。

線形作用が円になるのではない。
線形作用が二次保存量の等高線を保つから、円として観測される。

## 5.3. 次手 3. 失敗例ファイルを作る

ぬしの問いに直接答えるなら、これはかなり重要じゃ。

```text id="3c1j8t"
基盤がズレていた場合、どうなっていたか？
```

これを Lean / docs で示すには、あえて失敗核を定義する。

たとえば、

$$
(a,b)\diamond(x,y)=(ax+by,;ay+bx)
$$

を `badStarPlus` として定義する。

すると、

$$
Q((a,b)\diamond(x,y))
$$

を展開すると、余計な交差項が残る。

期待される式はこう。

$$
Q((a,b)\diamond(x,y))=Q(a,b)Q(x,y)+4abxy
$$

追加候補ファイル:

```text id="1o2z38"
DkMath/CosmicFormula/Rotation/CF2D/Failure.lean
```

追加候補 theorem:

```lean id="rqbu1h"
def Vec.badStarPlus ...

theorem q2_badStarPlus :
    Vec.q2 (badStarPlus (Vec.mk a b) (Vec.mk x y))
      = (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) + 4 * a * b * x * y := by
  ring
```

### 目的

これはかなり良い教材になる。

```text id="5nkvpy"
正しい核では Beam が相殺する
間違った核では Beam が残る
だから保存されない
だから円にならない
```

つまり、宇宙式が「正しい基盤」と「ズレた基盤」を見分けてくれる。

これは DkMath 的にはかなりおいしい。

## 6. その次の大きな分岐

上の 3 手が終わったら、次は二本に分かれる。

## 6.1. 解析方向

```text id="1ja3pr"
CF2D.Analysis
```

を作って、

```lean id="83iuwr"
HasDerivAt (fun t => F.C t) ...
HasDerivAt (fun t => F.S t) ...
```

へ進む。

これは通常の三角関数へ深く入る道。

ただし、これは少し重くなる。
今はまだ急がなくてよい。

## 6.2. 幾何・保存方向

```text id="kdm4se"
CF2D.Circle
CF2D.Failure
CF2D.UnitKernel
```

へ進む。

こちらは宇宙式らしい。

特に `Failure.lean` は、ぬしの「基盤がズレていた場合どうなるか？」に直撃する。
わっちは次はこちらを推す。

## 7. 推奨作業順

次の作業指示としては、こうでよい。

```text id="kmf1ce"
1. Basic.lean に UnitKernel.star と周辺補題を追加
2. Trig.lean または Circle.lean に KernelFamily の LevelSet 作用を追加
3. Failure.lean を新設し、符号を間違えた核では q2 保存が壊れることを示す
4. docs に「正しい保存核 / 失敗核」の対比を追記
```

ペースアップするなら、1 と 2 は同一コミットで行ける。
3 は別コミットがよい。概念が違うからの。

## 8. 今回の核心

宇宙式だけでは足りるのか。

わっちの暫定結論はこうじゃ。

$$
\boxed{
\text{宇宙式だけで、保存代数の骨格は足りる。}
}
$$

だが、

$$
\boxed{
\text{宇宙式だけでは、解析的な時間・角度・周期・一意性までは決まらない。}
}
$$

そして今回の試みでさらに見えたのは、

$$
\boxed{
\text{宇宙式は、基盤がズレたときにどこで保存が壊れるかを教える。}
}
$$

これはかなり大きい。

数は円だった、というより、

$$
\boxed{
\text{保存される数は、円として現れる。}
}
$$

そして保存がズレると、円ではなくなる。
この「円ではなくなる場所」を Lean で見せるのが、次の一番おもしろい一手じゃよ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D.lean
index 342d3be1..5ba3aa2a 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D.lean
@@ -6,6 +6,7 @@ Authors: D. and Wise Wolf.
 
 import DkMath.CosmicFormula.Rotation.CF2D.Basic
 import DkMath.CosmicFormula.Rotation.CF2D.Trig
+import DkMath.CosmicFormula.Rotation.CF2D.Real
 
 #print "file: DkMath.CosmicFormula.Rotation.CF2D"
 
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Real.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Real.lean
new file mode 100644
index 00000000..99d40f57
--- /dev/null
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Real.lean
@@ -0,0 +1,55 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.CosmicFormula.Rotation.CF2D.Trig
+
+#print "file: DkMath.CosmicFormula.Rotation.CF2D.Real"
+
+/-!
+# Real bridge for the CF2D trigonometric kernel
+
+The algebraic CF2D layer does not depend on the analytic trigonometric API.
+This bridge shows that the usual real `cos` and `sin` form a concrete
+`KernelFamily ℝ ℝ`.
+-/
+
+noncomputable section
+
+namespace DkMath
+namespace CosmicFormula
+namespace Rotation
+namespace CF2D
+
+/-- The usual real `(cos t, sin t)` pair as a CF2D unit-kernel family. -/
+noncomputable def realTrigKernelFamily : KernelFamily ℝ ℝ where
+  kernel t :=
+    { val := ⟨Real.cos t, Real.sin t⟩
+      q2_eq_one := by
+        simp [Vec.q2, Real.cos_sq_add_sin_sq t] }
+  map_zero := by
+    simp [Vec.one]
+  map_add := by
+    intro t s
+    simp [Vec.star, Real.cos_add, Real.sin_add]
+    ring
+
+@[simp]
+theorem realTrigKernelFamily_C (t : ℝ) :
+    realTrigKernelFamily.C t = Real.cos t := rfl
+
+@[simp]
+theorem realTrigKernelFamily_S (t : ℝ) :
+    realTrigKernelFamily.S t = Real.sin t := rfl
+
+@[simp]
+theorem realTrigKernelFamily_kernel_val (t : ℝ) :
+    ((realTrigKernelFamily.kernel t : UnitKernel ℝ) : Vec ℝ)
+      = ⟨Real.cos t, Real.sin t⟩ := rfl
+
+end CF2D
+end Rotation
+end CosmicFormula
+end DkMath
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean
index b3f545a7..71820603 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean
@@ -85,6 +85,13 @@ theorem C_zero_add (F : KernelFamily T R) (t : T) : F.C (0 + t) = F.C t := by
 theorem S_zero_add (F : KernelFamily T R) (t : T) : F.S (0 + t) = F.S t := by
   simp
 
+@[simp]
+theorem act_zero (F : KernelFamily T R) (z : Vec R) :
+    UnitKernel.act (F.kernel 0) z = z := by
+  change Vec.star (((F.kernel 0 : UnitKernel R) : Vec R)) z = z
+  rw [F.kernel_zero]
+  simp
+
 /--
 The basic identity for the coordinate functions:
 `C(t)^2 + S(t)^2 = 1`.
@@ -118,6 +125,80 @@ theorem S_add (F : KernelFamily T R) (t s : T) :
   have h := congrArg Vec.beam (F.kernel_add t s)
   simpa [C, S, Vec.star] using h
 
+/-- Unit-kernel family action composes according to parameter addition. -/
+theorem act_add (F : KernelFamily T R) (t s : T) (z : Vec R) :
+    UnitKernel.act (F.kernel (t + s)) z
+      = UnitKernel.act (F.kernel t) (UnitKernel.act (F.kernel s) z) := by
+  change Vec.star (((F.kernel (t + s) : UnitKernel R) : Vec R)) z
+      = Vec.star (((F.kernel t : UnitKernel R) : Vec R))
+          (Vec.star (((F.kernel s : UnitKernel R) : Vec R)) z)
+  rw [F.kernel_add t s]
+  exact Vec.star_assoc
+    (((F.kernel t : UnitKernel R) : Vec R))
+    (((F.kernel s : UnitKernel R) : Vec R))
+    z
+
+/-- Core double-angle formula in the abstract unit-kernel family. -/
+theorem C_add_self (F : KernelFamily T R) (t : T) :
+    F.C (t + t) = F.C t ^ 2 - F.S t ^ 2 := by
+  rw [F.C_add]
+  ring
+
+/-- Beam double-angle formula in the abstract unit-kernel family. -/
+theorem S_add_self (F : KernelFamily T R) (t : T) :
+    F.S (t + t) = 2 * F.C t * F.S t := by
+  rw [F.S_add]
+  ring
+
+section AddGroup
+
+variable {T : Type u} {R : Type v} [AddGroup T] [CommRing R]
+
+theorem kernel_add_neg (F : KernelFamily T R) (t : T) :
+    Vec.star (((F.kernel t : UnitKernel R) : Vec R))
+      (((F.kernel (-t) : UnitKernel R) : Vec R)) = Vec.one R := by
+  have h := F.kernel_add t (-t)
+  have h' :
+      Vec.star (((F.kernel t : UnitKernel R) : Vec R))
+        (((F.kernel (-t) : UnitKernel R) : Vec R))
+        = ((F.kernel 0 : UnitKernel R) : Vec R) := by
+    simpa using h.symm
+  exact h'.trans F.kernel_zero
+
+theorem C_neg (F : KernelFamily T R) (t : T) :
+    F.C (-t) = F.C t := by
+  have hq : F.C t ^ 2 + F.S t ^ 2 = 1 := F.C_sq_add_S_sq t
+  have hc : F.C t * F.C (-t) - F.S t * F.S (-t) = 1 := by
+    simpa using (F.C_add t (-t)).symm
+  have hs : F.C t * F.S (-t) + F.S t * F.C (-t) = 0 := by
+    simpa using (F.S_add t (-t)).symm
+  have h : F.C (-t) - F.C t = 0 := by
+    linear_combination -F.C (-t) * hq + F.C t * hc + F.S t * hs
+  exact sub_eq_zero.mp h
+
+theorem S_neg (F : KernelFamily T R) (t : T) :
+    F.S (-t) = -F.S t := by
+  have hq : F.C t ^ 2 + F.S t ^ 2 = 1 := F.C_sq_add_S_sq t
+  have hc : F.C t * F.C (-t) - F.S t * F.S (-t) = 1 := by
+    simpa using (F.C_add t (-t)).symm
+  have hs : F.C t * F.S (-t) + F.S t * F.C (-t) = 0 := by
+    simpa using (F.S_add t (-t)).symm
+  have h : F.S (-t) + F.S t = 0 := by
+    linear_combination -F.S (-t) * hq - F.S t * hc + F.C t * hs
+  exact eq_neg_of_add_eq_zero_left h
+
+theorem C_sub (F : KernelFamily T R) (t s : T) :
+    F.C (t - s) = F.C t * F.C s + F.S t * F.S s := by
+  rw [sub_eq_add_neg, F.C_add, F.C_neg, F.S_neg]
+  ring
+
+theorem S_sub (F : KernelFamily T R) (t s : T) :
+    F.S (t - s) = F.S t * F.C s - F.C t * F.S s := by
+  rw [sub_eq_add_neg, F.S_add, F.C_neg, F.S_neg]
+  ring
+
+end AddGroup
+
 end KernelFamily
 
 end CF2D
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md b/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md
index 56377702..42f5f49e 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md
@@ -8,6 +8,7 @@ The implementation is under:
 - `DkMath.CosmicFormula.Rotation.CF2D`
 - `DkMath.CosmicFormula.Rotation.CF2D.Basic`
 - `DkMath.CosmicFormula.Rotation.CF2D.Trig`
+- `DkMath.CosmicFormula.Rotation.CF2D.Real`
 
 The physical directory is `DkMath/CosmicFormula/Rotation/CF2D`.  The `CF2D`
 name avoids Lean's escaped-identifier syntax while keeping the public module
@@ -125,20 +126,79 @@ KernelFamily.C_zero_add :
 KernelFamily.S_zero_add :
   F.S (0 + t) = F.S t
 
+KernelFamily.act_zero :
+  UnitKernel.act (F.kernel 0) z = z
+
 KernelFamily.C_add :
   F.C (t + s) = F.C t * F.C s - F.S t * F.S s
 
 KernelFamily.S_add :
   F.S (t + s) = F.C t * F.S s + F.S t * F.C s
+
+KernelFamily.act_add :
+  UnitKernel.act (F.kernel (t + s)) z
+    = UnitKernel.act (F.kernel t) (UnitKernel.act (F.kernel s) z)
+
+KernelFamily.C_add_self :
+  F.C (t + t) = F.C t ^ 2 - F.S t ^ 2
+
+KernelFamily.S_add_self :
+  F.S (t + t) = 2 * F.C t * F.S t
 ```
 
 These are the cosmic-formula versions of the basic trigonometric identities:
 they are derived from conservation and kernel composition, not from existing
 trigonometric API.
 
+## Additive Group Layer
+
+When the parameter type has an additive group structure, `Trig.lean` also
+derives the negative-parameter and subtraction formulas:
+
+```lean
+KernelFamily.kernel_add_neg :
+  Vec.star (F.kernel t) (F.kernel (-t)) = Vec.one R
+
+KernelFamily.C_neg :
+  F.C (-t) = F.C t
+
+KernelFamily.S_neg :
+  F.S (-t) = -F.S t
+
+KernelFamily.C_sub :
+  F.C (t - s) = F.C t * F.C s + F.S t * F.S s
+
+KernelFamily.S_sub :
+  F.S (t - s) = F.S t * F.C s - F.C t * F.S s
+```
+
+The proofs are still algebraic: they use the unit square-mass identity and the
+fact that `R(t) ⋆ R(-t)` is the neutral kernel.
+
+## Real Bridge
+
+`Real.lean` is the compatibility layer with the usual real trigonometric
+functions.  It defines:
+
+```lean
+realTrigKernelFamily : KernelFamily ℝ ℝ
+```
+
+with kernel value `(Real.cos t, Real.sin t)`, using the standard real theorems
+only in this bridge layer.  The coordinate projections are exposed as:
+
+```lean
+realTrigKernelFamily_C :
+  realTrigKernelFamily.C t = Real.cos t
+
+realTrigKernelFamily_S :
+  realTrigKernelFamily.S t = Real.sin t
+```
+
 ## Extension Notes
 
 The implementation is deliberately algebraic and ring-polymorphic.  This keeps
 the 2D kernel reusable for later CFBRC, complex-like, 3D, or finite-dimensional
 geometric layers.  Analytic assumptions such as continuity of the parameter
-family are left out of this first algebraic layer.
+family are left out of the algebraic layer and can be added in separate bridge
+modules.
````
`````
