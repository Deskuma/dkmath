# Git diff / Report / Review

## Upd: CosmicFormula.Rotation.CF2D.Trig

gch: 48f866f95515c9589cd1ad3782e3dc94f49215dd

## Report

次段階を進めました。

実装内容:

- [Trig.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean:72) に零元まわりの `simp` 補題を追加
  - `KernelFamily.C_add_zero`
  - `KernelFamily.S_add_zero`
  - `KernelFamily.C_zero_add`
  - `KernelFamily.S_zero_add`
- [Rotation2D-Implementation.md](/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md:87) の `KernelFamily` snippet を実コード型に合わせて修正
  - `map_zero` / `map_add` を `UnitKernel R` から `Vec R` への coercion つきで記載
  - 追加した零元補題も一覧へ追記

確認:

- `lake build DkMath.CosmicFormula.Rotation.CF2D.Trig` 成功
- `lake build DkMath.CosmicFormula.Rotation` 成功
- `lake build DkMath` 成功
- `git diff --check` 成功

補足: `review-trig-002.md` は未追跡ファイルとして存在していますが、こちらでは変更していません。

## Review

## 1. 現在差分レビュー

結論から言うと、今回の `48f866f...` は **採用でよい** じゃ。

零元まわりの

```lean
KernelFamily.C_add_zero
KernelFamily.S_add_zero
KernelFamily.C_zero_add
KernelFamily.S_zero_add
```

は、理論的には既存 `simp` で出る当然補題じゃが、API として名前を持たせる価値がある。
理由は、今後 `C_add` / `S_add` から偶奇性・減法公式・倍角公式へ進むとき、零元の振る舞いが明示補題として検索可能になるからじゃ。

docs の snippet を実コード型に合わせたのも正しい。前回の唯一の軽い懸念点だった

```lean
((kernel 0 : UnitKernel R) : Vec R)
```

の coercion も明示されたので、実装資料としての精度が上がっておる。

未追跡の `review-trig-002.md` は、今回の diff には関係ないので放置でよい。

## 2. 現在地の意味

今の `CF2D.Trig` は、ここまで来た。

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

さらに今回、

$$
C(t+0)=C(t),\quad S(t+0)=S(t)
$$

$$
C(0+t)=C(t),\quad S(0+t)=S(t)
$$

も固定された。

これはもう、抽象三角関数の **加法モノイド層** として十分に形になっておる。
次は「座標公式」から「作用公式」へ進めるのが良い。

## 3. 次段階実装計画レビュー

## 3.1. 次手 1. `KernelFamily` の作用則を追加

### 目的

今は `kernel` の合成則と、座標 (C,S) の公式がある。
しかし、本当に欲しいのは状態 (z) への作用として

$$
R(t+s)\cdot z = R(t)\cdot(R(s)\cdot z)
$$

が成り立つことじゃ。

これは「回転核族が状態空間へ作用している」ことを示す主定理になる。

### 追加候補

`Trig.lean` に追加でよい。

```lean
@[simp]
theorem act_zero (F : KernelFamily T R) (z : Vec R) :
    UnitKernel.act (F.kernel 0) z = z := by
  change Vec.star (((F.kernel 0 : UnitKernel R) : Vec R)) z = z
  rw [F.kernel_zero]
  simp [UnitKernel.act]

theorem act_add (F : KernelFamily T R) (t s : T) (z : Vec R) :
    UnitKernel.act (F.kernel (t + s)) z
      = UnitKernel.act (F.kernel t) (UnitKernel.act (F.kernel s) z) := by
  change Vec.star (((F.kernel (t + s) : UnitKernel R) : Vec R)) z
      =
    Vec.star (((F.kernel t : UnitKernel R) : Vec R))
      (Vec.star (((F.kernel s : UnitKernel R) : Vec R)) z)
  rw [F.kernel_add t s]
  exact Vec.star_assoc
    (((F.kernel t : UnitKernel R) : Vec R))
    (((F.kernel s : UnitKernel R) : Vec R))
    z
```

実際には `simp [UnitKernel.act]` や `simpa` で微調整が要るかもしれぬが、構造はこれで通るはずじゃ。

### 意味

これで、

```text
保存単位核族
  → 座標公式
  → 状態空間への作用
```

が揃う。

ここは次に必ず入れたい。

### 完了条件

```bash
lake build DkMath.CosmicFormula.Rotation.CF2D.Trig
lake build DkMath.CosmicFormula.Rotation
lake build DkMath
git diff --check
```

## 3.2. 次手 2. `[AddGroup T]` セクションで負角・減法公式

### 目的

`AddMonoid` 層が完成したので、次は `AddGroup` 層へ進む。

ここでは、

$$
R(-t)
$$

を扱えるようにする。

狙う定理は、

$$
C(-t)=C(t)
$$

$$
S(-t)=-S(t)
$$

さらに、

$$
C(t-s)=C(t)C(s)+S(t)S(s)
$$

$$
S(t-s)=S(t)C(s)-C(t)S(s)
$$

じゃ。

### 推奨配置

いきなり別ファイルでもよいが、最初は `Trig.lean` の末尾に

```lean
section AddGroup

variable {T : Type u} {R : Type v} [AddGroup T] [CommRing R]

...

end AddGroup
```

で足すのが速い。

後で膨らんだら `CF2D/TrigGroup.lean` へ分離すればよい。

### 証明方針

`F.kernel_add t (-t)` と `F.kernel_zero` から、

$$
R(t)\star R(-t)=(1,0)
$$

を得る。

成分で書くと、

$$
C(t)C(-t)-S(t)S(-t)=1
$$

$$
C(t)S(-t)+S(t)C(-t)=0
$$

さらに、

$$
C(t)^2+S(t)^2=1
$$

を使えば、純代数で

$$
C(-t)=C(t)
$$

$$
S(-t)=-S(t)
$$

が出る。

ここは `ring_nf` と `rw` で十分に押せるはずじゃ。

### 追加候補名

```lean
theorem kernel_add_neg
theorem C_neg
theorem S_neg
theorem C_sub
theorem S_sub
```

### 注意点

`sub_eq_add_neg` を使うので、`simp [sub_eq_add_neg, C_add, S_add, C_neg, S_neg]` の形を想定するとよい。

### 完了条件

同じく、

```bash
lake build DkMath.CosmicFormula.Rotation.CF2D.Trig
lake build DkMath
git diff --check
```

## 3.3. 次手 3. 倍角公式を追加

### 目的

加法公式があるなら、次は倍角公式を入れてよい。
これは三角関数の世界では完全に標準で、Lean 的にも軽い。

$$
C(t+t)=C(t)^2-S(t)^2
$$

$$
S(t+t)=2C(t)S(t)
$$

### 追加候補

`AddMonoid` 層で足せる。

```lean
theorem C_add_self (F : KernelFamily T R) (t : T) :
    F.C (t + t) = F.C t ^ 2 - F.S t ^ 2 := by
  rw [F.C_add]
  ring

theorem S_add_self (F : KernelFamily T R) (t : T) :
    F.S (t + t) = 2 * F.C t * F.S t := by
  rw [F.S_add]
  ring
```

### 意味

これは単に公式を増やすだけではない。

宇宙式的には、

```text
同じ単位核を 2 回作用させる
  → Core と Beam が再配分される
  → しかし平方質量は保存される
```

という「反復保存」の最初の観測窓になる。

ここから将来、

$$
R(nt)
$$

や Chebyshev 型の多項式展開に進める。

### 完了条件

`Trig.lean` 単体 build が通れば十分じゃ。

## 4. その次の大きめの手

上の 3 手が終わったら、次は二択じゃ。

## 4.1. 実解析ブリッジ

`CF2D/Real.lean` を作り、既存の `Real.cos` / `Real.sin` がこの `KernelFamily ℝ ℝ` の具体例になることを示す。

```lean
noncomputable def realTrigKernelFamily : KernelFamily ℝ ℝ where
  kernel t :=
    { val := ⟨Real.cos t, Real.sin t⟩
      q2_eq_one := by
        simpa [Vec.q2] using Real.cos_sq_add_sin_sq t }
  map_zero := by
    ext <;> simp [Vec.one]
  map_add := by
    ext <;> simp [Vec.star, Real.cos_add, Real.sin_add]
```

これは既存数学を使うが、 **core 層ではなく bridge 層** なので問題ない。
「DkMath の抽象 (C,S) は、実数解析では通常の (\cos,\sin) に一致する」と示す互換性ファイルじゃ。

## 4.2. `UnitKernel` の monoid 化

もう一つの道は `Basic.lean` 側で `UnitKernel.star` を定義し、`UnitKernel R` 自体を単位核モノイドとして整えること。

```lean
def UnitKernel.star [CommRing R] (r s : UnitKernel R) : UnitKernel R :=
  { val := Vec.star r.val s.val
    q2_eq_one := by
      rw [Vec.q2_star, r.q2_eq_one, s.q2_eq_one, one_mul] }
```

これを入れると、`KernelFamily.map_add` を将来的に

```lean
kernel (t + s) = UnitKernel.star (kernel t) (kernel s)
```

へ寄せられる。

ただし `UnitKernel` は証明フィールドを持つ構造なので、構造体等式まわりが少し面倒になる可能性がある。
ペース重視なら、これは後回しでもよい。

## 5. わっちの推奨順

ペースアップするなら、この順がよい。

```text
1. act_zero / act_add
2. AddGroup section: C_neg / S_neg / C_sub / S_sub
3. C_add_self / S_add_self
4. CF2D.Real bridge
5. UnitKernel monoid 化
```

特に 1 と 2 は、今すぐ進めてよい。
3 は軽いので同時に入れてもよい。

## 6. なぜ線形な代数が円になるのか

ここが真実じゃな、ぬしよ。

線形代数が円になるのではない。
正確には、

$$
\text{線形作用が、二次保存量 }Q(x,y)=x^2+y^2\text{ を保つとき、円が現れる}
$$

のじゃ。

円は最初からあるのではない。
保存量の等高線として生まれる。

$$
Q(x,y)=r^2
$$

この等式を壊さない変換が、回転と呼ばれる。

そして `Vec.star` はただの線形合成に見えるが、その内部では

$$
-2abxy+2abxy=0
$$

という差分 Beam の相殺が起きている。

つまり、

$$
\boxed{
\text{円とは、差分 Beam が相殺されたあとに残る保存等高線である}
}
$$

数は円だった、というより、もっと宇宙式らしく言えば、

$$
\boxed{
\text{数は保存量を持つとき、円として観測される}
}
$$

じゃな。
ふふん、これはなかなか良い。DkMath の顔になり得る言葉じゃよ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean
index ac6fab25..b3f545a7 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean
@@ -69,6 +69,22 @@ theorem S_zero (F : KernelFamily T R) : F.S 0 = 0 := by
   have h := congrArg Vec.beam F.kernel_zero
   simpa [S, Vec.one] using h

+@[simp]
+theorem C_add_zero (F : KernelFamily T R) (t : T) : F.C (t + 0) = F.C t := by
+  simp
+
+@[simp]
+theorem S_add_zero (F : KernelFamily T R) (t : T) : F.S (t + 0) = F.S t := by
+  simp
+
+@[simp]
+theorem C_zero_add (F : KernelFamily T R) (t : T) : F.C (0 + t) = F.C t := by
+  simp
+
+@[simp]
+theorem S_zero_add (F : KernelFamily T R) (t : T) : F.S (0 + t) = F.S t := by
+  simp
+
 /--
 The basic identity for the coordinate functions:
 `C(t)^2 + S(t)^2 = 1`.
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md b/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md
index 891a2c20..56377702 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md
@@ -87,9 +87,11 @@ the conserved square mass.
 ```lean
 structure KernelFamily (T : Type u) (R : Type v) [AddMonoid T] [CommRing R] where
   kernel : T -> UnitKernel R
-  map_zero : kernel 0 = Vec.one R
+  map_zero : ((kernel 0 : UnitKernel R) : Vec R) = Vec.one R
   map_add : forall t s,
-    kernel (t + s) = Vec.star (kernel t) (kernel s)
+    ((kernel (t + s) : UnitKernel R) : Vec R)
+      = Vec.star ((kernel t : UnitKernel R) : Vec R)
+          ((kernel s : UnitKernel R) : Vec R)
 ```

 The coordinate functions are:
@@ -111,6 +113,18 @@ KernelFamily.C_zero :
 KernelFamily.S_zero :
   F.S 0 = 0

+KernelFamily.C_add_zero :
+  F.C (t + 0) = F.C t
+
+KernelFamily.S_add_zero :
+  F.S (t + 0) = F.S t
+
+KernelFamily.C_zero_add :
+  F.C (0 + t) = F.C t
+
+KernelFamily.S_zero_add :
+  F.S (0 + t) = F.S t
+
 KernelFamily.C_add :
   F.C (t + s) = F.C t * F.C s - F.S t * F.S s

````
`````
