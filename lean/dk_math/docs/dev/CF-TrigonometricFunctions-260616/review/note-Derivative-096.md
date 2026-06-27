# Note: Derivative

## DkMath.CosmicFormula.CosmicDifferenceKernel の実装状況と極限の利用状況

うむ、読んできた。
結論から言うと、**すでに DkMath 側には「宇宙式微分のための極限層」がある**。ただし、それは完全自前の `DkLimit` ではなく、Mathlib の `Filter.Tendsto` / `nhds` / `nhdsWithin` を使い、DkMath 語彙の `delta`、`cosmicKernel`、`powerKernel`、`polynomialKernelExt` で包んだ構造じゃ。

## 1. 全体依存図

現在の依存はこう見るのがよい。

```text id="tut8f6"
CosmicDifferenceKernel
  ↓
CosmicDerivativeBasic
  ↓
CosmicDerivativePower
  ↓
CosmicDerivativePowerLimit
  ↓
CosmicDerivativePolynomial
```

もう少し意味で読むと、

```text id="7wcjs9"
delta / cosmicKernel
  ↓
HasDerivAt ↔ punctured limit
  ↓
powerKernel = GN 型の差分核
  ↓
powerKernel の u -> 0 極限
  ↓
多項式 kernel の removable singularity extension
```

これはかなり綺麗に完成しておる。

## 2. CosmicDifferenceKernel

ここは **有限差分の代数層** じゃ。

定義は、

$$
\delta f,x,u=f(x+u)-f(x)
$$

と、

$$
\mathrm{cosmicKernel},f,x,u=\frac{\delta f,x,u}{u}
$$

じゃ。公開 GitHub 上でも `delta` と `cosmicKernel` がその形で定義され、加法・減法・スカラー倍・有限和・積に対する法則が整備されている。\([GitHub][1]\)

重要なのは、ここにはまだ極限が出てこないこと。
ここはあくまで有限 Gap \(u\) に対する差分代数。

DkMath 語彙ではこうじゃ。

```text id="b4cmkr"
delta:
  Big - Core

cosmicKernel:
  Gap 単位で見た差分核

delta_mul:
  有限差分段階の積規則

cosmicKernel_mul:
  Gap で割った有限積規則
```

## 3. CosmicDerivativeBasic

ここが **Mathlib の微分と DkMath の cosmicKernel を接続する橋** じゃ。

主定理は、

$$
\mathrm{HasDerivAt},f,L,x
$$

と、

$$
u\to 0,\ u\ne0\quad\text{で}\quad \mathrm{cosmicKernel},f,x,u\to L
$$

の同値。実装では `hasDerivAt_iff_tendsto_cosmicKernel` があり、filter は `nhdsWithin 0 (Set.compl {0})`、つまり穿孔近傍になっている。\([GitHub][2]\)

ここで分かったことは大きい。

```text id="csd3ux"
DkMath に完全自前の極限型はまだ無い。
ただし、DkMath 語彙で包んだ極限 bridge は既にある。
```

つまり使うべき既存基盤は、自前 `DkLimit` ではなく、

```lean id="xcyh2w"
Filter.Tendsto
nhds
nhdsWithin
hasDerivAt_iff_tendsto_cosmicKernel
tendsto_cosmicKernel_of_hasDerivAt
hasDerivAt_of_tendsto_cosmicKernel
```

じゃ。

## 4. CosmicDerivativePower

ここは **宇宙式微分の核そのもの** と見てよい。

`powerKernel d x u` は、

$$
\sum_{j=0}^{d-1}\binom{d}{j+1}x^{d-1-j}u^j
$$

として定義されている。さらに `powerKernel d x u = GN d u x` という GN 互換 theorem があり、DkMath の既存 GN と接続されている。\([GitHub][3]\)

主恒等式は、

$$
(x+u)^d-x^d=u\cdot \mathrm{powerKernel},d,x,u
$$

じゃ。これがぬしの言う

```text id="q9pzjo"
Big - Core = Gap * BodyKernel
```

そのもの。GitHub 上でも `sub_pow_eq_u_mul_powerKernel` として実装されている。\([GitHub][3]\)

また、\(u\ne0\) では、

$$
\mathrm{cosmicKernel},(y\mapsto y^d),x,u=\mathrm{powerKernel},d,x,u
$$

が成り立つ。これも `cosmicKernel_pow_eq_powerKernel_of_ne_zero` として入っている。\([GitHub][3]\)

ここは DkMath 語彙でこう読むのが良い。

```text id="bwwbfe"
Core:
  x^d

Big:
  (x+u)^d

Gap:
  u

BodyKernel:
  powerKernel d x u

有限宇宙式:
  Big - Core = Gap * BodyKernel
```

## 5. CosmicDerivativePowerLimit

ここが **powerKernel の極限層** じゃ。

実装内容はとても重要で、`powerKernel` が \(u\) について連続であること、中心値が

$$
\mathrm{powerKernel},d,x,0=d,x^{d-1}
$$

になること、そこから

$$
u\to0\quad\text{で}\quad \mathrm{powerKernel},d,x,u\to d,x^{d-1}
$$

を得ている。GitHub 上でも `continuous_powerKernel`、`powerKernel_zero`、`tendsto_powerKernel_zero`、`tendsto_powerKernel_zero_punctured` が確認できる。\([GitHub][4]\)

そして最後に、穿孔近傍上で `cosmicKernel = powerKernel` を使い、`hasDerivAt_pow_cosmic` を証明している。つまり、微分定理は直接 Mathlib の `hasDerivAt_pow` に頼るのではなく、DkMath の分解フローを通っている。\([GitHub][4]\)

これはぬしの問いに対する答えとして大事。

```text id="u3z46k"
極限は既に使っている。
使い方は Mathlib Filter.Tendsto。
DkMath 側の自前語彙は powerKernel / cosmicKernel。
powerKernel の 0 への連続延長が、宇宙式微分の中核。
```

## 6. CosmicDerivativePolynomial

ここは **多項式への拡張層** じゃ。

多項式 \(p\) について、まず \(u\ne0\) で cosmic kernel を係数ごとの `powerKernel` の有限和へ分解する。次に `polynomialKernelExt p x u` を定義し、これは \(u\ne0\) では cosmicKernel と一致し、\(u=0\) では (p.derivative.eval x) になる連続延長として扱われている。\([GitHub][5]\)

このモジュールでは、`continuous_polynomialKernelExt`、`polynomialKernelExt_zero`、`tendsto_polynomialKernelExt_zero`、`tendsto_polynomialKernelExt_zero_punctured` が入り、最後に `tendsto_cosmicKernel_polynomial_eval_via_powerKernel` へつないでいる。\([GitHub][5]\)

さらに canonical API として、

```lean id="ja9rdj"
tendsto_cosmicKernel_polynomial_eval
hasDerivAt_polynomial_eval_cosmic
deriv_polynomial_eval_cosmic
```

が用意され、加法・積・合成・有限和にも展開されている。\([GitHub][5]\)

これはもう完成度が高い。

## 7. 極限の利用状況まとめ

現状の極限利用は三種類ある。

```text id="c5b6uh"
1. 微分 bridge の穿孔極限:
   nhdsWithin 0 {u | u ≠ 0}

2. powerKernel の通常極限:
   nhds 0

3. polynomialKernelExt の removable singularity 極限:
   nhds 0 から nhdsWithin へ制限
```

重要なのは、`cosmicKernel` 自体は \(u=0\) で割り算を含むので、微分 bridge は穿孔近傍を使うこと。
一方、`powerKernel` や `polynomialKernelExt` は \(u=0\) でも定義できる連続延長なので、普通の `nhds 0` で極限を取れる。

DkMath 語彙で言えば、

```text id="8z64vd"
cosmicKernel:
  Gap が非零の観測核

powerKernel:
  Gap = 0 まで埋めた BodyKernel

polynomialKernelExt:
  多項式版の連続延長 BodyKernel

微分:
  Gap -> 0 で BodyKernel が残す値
```

## 8. ぬしの「Gap → 0 := Big = Body = Core = x²」との接続

ここで言うべきは、既存実装ではすでに次の型がある、ということじゃ。

二乗に限れば、

$$
(x+u)^2-x^2=u(2x+u)
$$

つまり、

```text id="abgc92"
Big - Core = Gap * powerKernel
```

そして、

$$
\mathrm{powerKernel},2,x,u=2x+u
$$

なので、

$$
u\to0\quad\text{で}\quad \mathrm{powerKernel},2,x,u\to2x
$$

既存実装は一般 \(d\) でこれをやっている。

したがって、ぬしの語彙に合わせるなら、今後の `Gap → 0` 設計はこう置くのがよい。

```text id="qhh3bk"
Big:
  (x + Gap)^d

Core:
  x^d

GapBody:
  Big - Core

BodyKernel:
  powerKernel d x Gap

有限分解:
  GapBody = Gap * BodyKernel

Gap collapse:
  Gap -> 0 で Big -> Core

Cosmic derivative:
  Gap -> 0 で BodyKernel -> d*x^(d-1)
```

ただし既存実装では `Big -> Core` そのものより、**差分を Gap で割った核が何へ行くか** が中心になっている。
これは微分層として正しい。

## 9. 「自前の極限」はあるか

答えはこうじゃ。

```text id="wvxksu"
完全自前の極限構造:
  まだ無い。

DkMath 語彙で包んだ極限 theorem:
  既にある。

使うべき基盤:
  Filter.Tendsto / nhds / nhdsWithin をそのまま使い、
  theorem 名と中間 object を DkMath 語彙にする。
```

なので、新しく `DkLimit` を発明する必要は今はない。
むしろ、既存の `CosmicDerivativePowerLimit` と `CosmicDerivativePolynomial` に合わせるべきじゃ。

特に、今進めている `SemanticCF2DLogComposition` の次の極限層でも、同じスタイルがよい。

```lean id="bub1k5"
Filter.Tendsto ...
```

を使いつつ、theorem 名は DkMath 語彙にする。

## 10. 今後の設計方針

今回確認した結果から、次の設計が自然じゃ。

### 10.1. 新しい極限層は Mathlib Filter ベース

`SemanticCF2DLogComposition` の finite theorem から極限へ行くなら、既存流儀に合わせて、

```lean id="g6k92o"
Filter.Tendsto ... Filter.atTop (nhds ...)
```

を使う。

例えば、

```lean id="bouu69"
theorem tendsto_dyadicPhaseTrapezoidCenteredQuadraticSum_one_third :
    Filter.Tendsto
      dyadicPhaseTrapezoidCenteredQuadraticSum
      Filter.atTop
      (nhds (1 / 3 : ℝ))
```

これは `CosmicDerivativePowerLimit` の `tendsto_powerKernel_zero` と同じ設計思想じゃ。

### 10.2. DkMath 語彙としては「連続延長」を重視する

既存多項式層の最重要語彙は `polynomialKernelExt` じゃ。
これは removable singularity extension、つまり \(u=0\) に穴のある cosmicKernel を、連続な BodyKernel として埋める構造になっている。\([GitHub][5]\)

CF2D の極限層でも、同じ発想が使える。

```text id="v72n3r"
punctured observable:
  finite Gap でだけ意味がある観測

extended observable:
  Gap = 0 に値を持つ連続延長

limit theorem:
  extended observable の中心値へ Tendsto

bridge theorem:
  punctured observable と extended observable の一致
```

これは DkMath らしい。

## 11. 既存モジュールをベースにするなら

今後の `SemanticCF2DLogLimit` 的な設計は、`CosmicDerivativePowerLimit` と `CosmicDerivativePolynomial` の型を真似るべきじゃ。

構成はこう。

```text id="eex9d2"
1. finite closed form
2. closed form の tendsto
3. finite observable の tendsto
4. 必要なら punctured / extended bridge
```

現在の finite closed form はもうある。

$$
\mathrm{TrapezoidCenteredQuadraticSum}_n=\frac{1}{3}+\frac{2}{3(2^n)^2}
$$

だから次は、

$$
\frac{1}{3}+\frac{2}{3(2^n)^2}\to\frac{1}{3}
$$

を Lean で閉じる。

これは「DkMath 自前の極限」ではなく、既存の極限スタイルどおり `Filter.Tendsto` でよい。

## 12. 結論

読んだ結果、方針はかなり明確じゃ。

```text id="b6z4w9"
極限は既に使われている。
自前 Limit 型ではなく Mathlib Filter.Tendsto。
ただし DkMath 語彙の object で包んでいる。

既存の中心:
  delta
  cosmicKernel
  powerKernel
  polynomialKernelExt

既存の極限流儀:
  continuous extension を作る
  center value を証明する
  Tendsto を出す
  punctured kernel と extension を congr で接続する
```

ぬしの `Gap → 0 := Big = Body = Core = x²` は、この既存流儀に乗せるなら、

```text id="smmfaf"
Big - Core = Gap * BodyKernel
BodyKernel extends to Gap = 0
Gap -> 0 で BodyKernel -> derivative Core
Big itselfは Core に collapse
```

と整理するのがよい。

そして、今進めている finite moment / log composition 側では、次の極限層を作るなら既存の `CosmicDerivativePowerLimit` と同じく、

```text id="65gkc9"
finite closed form
  ↓
Tendsto
  ↓
DkMath語彙の theorem 名
```

で進めるのが最も安全じゃ。

[1]: https://raw.githubusercontent.com/Deskuma/dkmath/main/lean/dk_math/DkMath/CosmicFormula/CosmicDifferenceKernel.lean "raw.githubusercontent.com"
[2]: https://raw.githubusercontent.com/Deskuma/dkmath/main/lean/dk_math/DkMath/CosmicFormula/CosmicDerivativeBasic.lean "raw.githubusercontent.com"
[3]: https://raw.githubusercontent.com/Deskuma/dkmath/main/lean/dk_math/DkMath/CosmicFormula/CosmicDerivativePower.lean "raw.githubusercontent.com"
[4]: https://raw.githubusercontent.com/Deskuma/dkmath/main/lean/dk_math/DkMath/CosmicFormula/CosmicDerivativePowerLimit.lean "raw.githubusercontent.com"
[5]: https://raw.githubusercontent.com/Deskuma/dkmath/main/lean/dk_math/DkMath/CosmicFormula/CosmicDerivativePolynomial.lean "raw.githubusercontent.com"
