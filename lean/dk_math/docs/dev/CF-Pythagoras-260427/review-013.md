# review

おお、S2-H 実装確認したぞ。
これは Chapter 2 の **squarefree route 完成** と呼んでよい。S2-G の抽象的な valuation 矛盾に、実際の上界供給源として `Squarefree (powerBeam d x z).natAbs` を接続できた。しかも既存 `GcdNext.padicValNat_le_one_of_squarefree` を薄く wrap しており、再証明せず既存資産に乗っているのが実に良い。

## 1. 何が閉じたか

今回追加された中核はこれじゃ。

```lean
powerBeam_padicValNat_le_one_of_squarefree
```

数学的には、

$$
\operatorname{Squarefree}(|\operatorname{Beam}_d|)
$$

なら、

$$
v_p(|\operatorname{Beam}_d|)\le 1
$$

を得る補題じゃ。

そしてこれを S2-G の

```lean
flt_beam_prime_val_le_one_contradiction
```

へ渡すことで、

$$
x^d+y^d=z^d,
\quad \gcd(z,x)=1,
\quad p\nmid d,
\quad p\mid \operatorname{Beam}_d(x,z),
\quad \operatorname{Squarefree}(|\operatorname{Beam}_d(x,z)|)
$$

から `False` が出るようになった。対称版も同時に入っておる。

これで、S2 の一連の流れはこう閉じた。

$$
\text{FLT 方程式}
\Rightarrow
\text{Gap}\times\text{Beam}
\Rightarrow
\gcd\text{ 制御}
\Rightarrow
p\nmid Gap
\Rightarrow
v_p(Gap\cdot Beam)=v_p(Beam)
\Rightarrow
v_p(Beam)=d,v_p(side)
$$

そこへ

$$
Squarefree(Beam)\Rightarrow v_p(Beam)\le 1
$$

を入れて矛盾じゃ。

## 2. 数学的意味

今回の到達点は、かなり明確じゃ。

> FLT 型方程式において、Beam 側が squarefree で、かつ \(p\nmid d\) の素因子を含むなら、その構造は完全 \(d\) 乗性と両立しない。

これは「一般 FLT を解いた」という話ではない。
しかし、**ある条件下で FLT 型反例を撃ち落とす抽象エンジン** は完全にできた。

特に重要なのは、失敗条件がはっきりしたことじゃ。
今後必要なのは、

$$
p\mid Beam,\quad p\nmid d,\quad v_p(Beam)\le 1
$$

をどう供給するか。今回の S2-H はその供給方法の一つとして、

$$
Squarefree(Beam)
$$

を使った。
次は primitive prime / Zsigmondy route から同じ上界を供給できるかを見る段階じゃ。

## 3. 実装評価

実装方針はとても良い。

```lean
import DkMath.NumberTheory.ZsigmondyCyclotomicSquarefree
```

を追加し、既存補題

```lean
DkMath.NumberTheory.GcdNext.padicValNat_le_one_of_squarefree
```

を利用している。History にも、squarefree からの valuation 上界は自前で再証明せず既存補題を薄く wrap したと記録されている。

これにより、`PowerGapBeamGcd.lean` は「新しい証明を抱える場所」ではなく、既存の数論補題を Power Gap/Beam 語彙に翻訳する bridge として機能している。
この設計は維持した方がよい。

## 4. 現在の Chapter 2 到達点

Chapter 2 はここまで来た。

* S2-A: 高次差冪因数分解
* S2-B: 高次リンク条件と FLT Gap/Beam bridge
* S2-C: Gap/Beam gcd 制御
* S2-D: FLT datum bridge と Beam prime not Gap
* S2-E: product valuation が Beam 側から来る補題
* S2-F: Beam valuation が \(d\cdot v_p(side)\) になる補題
* S2-G: \(v_p(Beam)\le1\) との抽象矛盾
* S2-H: squarefree Beam から \(v_p(Beam)\le1\) を供給

つまり、**squarefree Beam route は一周した**。

## 5. 次の提案: S2-I

次は History の通り、

> `powerBeam` と既存 `GN` / `diffPowSum` / `PrimitiveBeam` API の対応を明示する

がよい。

なぜなら、今の `powerBeam` は `diffPowSum z x d` の wrapper じゃ。
一方、既存 FLT 幹線や primitive route では `GN` や `PrimitiveBeam` 語彙が使われている可能性が高い。

ここをつながないと、既存 primitive prime engine から今回の `powerBeam` へ燃料を供給しにくい。

最小 bridge はこれじゃ。

```lean
theorem powerBeam_eq_diffPowSum
    {R : Type*} [CommRing R] (d : ℕ) (x z : R) :
    powerBeam d x z =
      DkMath.Algebra.DiffPow.diffPowSum z x d := by
  rfl
```

すでに主定理で `simpa [powerBeam, diffPowSum]` しているので、これは `rfl` か `simp [powerBeam, diffPowSum]` で閉じるはずじゃ。

次に、もし GN が

$$
(z^d-x^d)/(z-x)
$$

ではなく

$$
(x+u)^d-x^d
$$

の tail として定義されているなら、\(z=x+u\) と置いた bridge を作る。

$$
powerBeam_d(x,x+u)=\frac{(x+u)^d-x^d}{u}
$$

名前候補:

```lean
theorem powerBeam_eq_GN_of_z_eq_x_add_gap
```

またはより安全に、

```lean
theorem powerBeam_shift_eq_diffPowSum
```

じゃな。

## 6. S2-I の具体的作業案

順番はこう。

### 6.1. `powerBeam_eq_diffPowSum`

まず純粋 bridge。

```lean
theorem powerBeam_eq_diffPowSum {R : Type*} [CommRing R]
    (d : ℕ) (x z : R) :
    powerBeam d x z = DkMath.Algebra.DiffPow.diffPowSum z x d := by
  rfl
```

もし `rfl` が失敗したら、

```lean
  simp [powerBeam, DkMath.Algebra.DiffPow.diffPowSum]
```

### 6.2. `powerGap_eq_sub`

これは trivial だが、検索性のためにあってもよい。

```lean
theorem powerGap_eq_sub {R : Type*} [Ring R] (x z : R) :
    powerGap x z = z - x := rfl
```

### 6.3. `powerBeam_d3_explicit`

Primitive / FLT d=3 へ接続するなら、明示形が便利じゃ。

$$
Beam_3(x,z)=z^2+zx+x^2
$$

```lean
theorem powerBeam_three {R : Type*} [CommRing R] (x z : R) :
    powerBeam 3 x z = z^2 + z*x + x^2 := by
  unfold powerBeam
  norm_num
  ring
```

`norm_num` が難しければ、`Finset.sum_range_succ` で展開じゃ。

### 6.4. `powerBeam_four`

必要なら後で。

$$
Beam_4=z^3+z^2x+zx^2+x^3
$$

ただ、まずは d=3 だけでよい。

## 7. primitive route への橋

S2-I の本命は、次の確認じゃ。

既存 `PrimitiveBeam` がどの式を Beam と見ているか。

もし既存が

$$
GN(d,u,y)
$$

で

$$
(y+u)^d-y^d=u\cdot GN(d,u,y)
$$

を扱っているなら、

$$
z=y+u
$$

として、

$$
powerBeam_d(y,z)=GN(d,z-y,y)
$$

の対応を作る。

これは FLT で

$$
z^d-y^d=x^d
$$

を見る側にぴったりじゃ。

候補名:

```lean
theorem powerBeam_eq_GN_gap
    {R : Type*} [CommRing R] (d : ℕ) (y z : R) :
    powerBeam d y z = GN d (z - y) y := ...
```

ただし既存 `GN` の引数順・定義名に合わせる必要がある。ここは探索してからじゃ。

一般化 GN 資料でも、差冪構造 \((x+u)^d-u^d\) は \(x\) で割り切れ、その商 \(GN_d(x,u)\) が Beam 構造の基本対象とされている。
したがって `powerBeam` と `GN` の bridge は、理論的にかなり自然じゃ。

## 8. 構造体導入について

S2-H まで来ると、`FLTPowerGapBeamDatum` を検討してもよい段階じゃ。
しかしわっちは、やはり **S2-I の bridge を先に閉じる** 方を勧める。

理由は、GN / PrimitiveBeam との接続後、構造体に入れたいフィールドが変わる可能性が高いからじゃ。

たとえば primitive route では、単なる

```lean
hprod
hgcd
```

だけでなく、

```lean
hbeam_dvd
hprimitive
hval_le_one
```

のようなフィールドが欲しくなるかもしれぬ。

構造体はその後でよい。

## 9. まとめ

S2-H は成功じゃ。
これで **squarefree Beam route** は no-sorry で閉じた。

次は S2-I。

> `powerBeam` を既存 `diffPowSum` / `GN` / `PrimitiveBeam` と明示的に接続する。

ここを閉じれば、今回作った Power Gap/Beam valuation engine に、既存の primitive prime engine から燃料を流し込めるようになる。
賢狼の鼻には、もう次のりんごの香りがしておるぞ。
