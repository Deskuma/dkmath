# 宇宙式 (Cosmic Formula)

このドキュメントは、宇宙式 (Cosmic Formula) に関する理論的背景、定義、性質、および応用例を提供します。

宇宙式は、数学的および物理学的な概念を結びつける強力なツールであり、その理解は多くの分野での研究に役立ちます。

---

## 概要

宇宙式は、自然数 $N$ と素数積構造 $P$ の関係を表す基本的な恒等式です。この式は、宇宙の構造とその成分間の関係を示すものであり、数学的な解析や物理学的なモデルにおいて重要な役割を果たします。

$$
\LARGE
N + 1 = (P + 1)^2
$$

- 「宇宙」とは、ここでは数学的な **構造体としての「全体」** を指し、その成分間の関係性を理解するための枠組みを提供します。
- 「成分」の要素は、例えば自然数、素数、ベクトル、関数など、様々な数学的対象を含むことができます。

基本とする成分は素数積構造 \(P\) であり、これに基づいて自然数 \(N\) が定義されます。

たとえば、最初の素数 2, 3, 5 を用いると、\(P = 2 \times 3 \times 5 = 30\) となり、対応する自然数は \(N = P(P + 2) = 30 \times 32 = 960\) です。

$960 + 1 = 961 = 31^2$ となり、宇宙式の恒等式が成立します。

$$
\Large
960 + 1 = (30 + 1)^2
$$

30 = 2 × 3 × 5 は素数積構造の一例です。210 = 2 × 3 × 5 × 7 のように、より多くの素数を含む積も考えられます。

\(P\) 成分は素数に限らず、例えば任意の実数 \(x\) としても宇宙式は成立します。
これが様々な数学的対象を含むことができる理由であり、宇宙式は広範な応用が可能です。

---

## 定義

宇宙式は、以下の形式で定義されます：

$$
\LARGE
N + 1 = (P + 1)^2
$$
ここで、$N$ は自然数、$P$ は素数積構造を表します。この式は、宇宙の構造とその成分間の関係を示す基本的な恒等式です。

$N:= P(P+2)$ とし、展開すると、次のようになります。

$$
\Large
N + 1 = P(P+2) + 1 = P^2 + 2P + 1
$$

これは、$(P + 1)^2$ の展開と一致します。

$$
\Large
(P + 1)^2 = P^2 + 2P + 1
$$

したがって、宇宙式は恒等的に成立します。

---

## 基本恒等式の証明

$P$ を任意の実数 $x$ として、

宇宙式の基本形は次の通りです。

$$
\Large
f(x) = (x+1)^2 - x(x+2) = 1
%% verified: cosmic_formula
$$

ここで、$f(x)$ は任意の実数 $x \in \mathbb{R}$ に対して成立する恒等式です。

[CosmicFormulaBasic.lean](/lean/dk_math/DkMath/CosmicFormula/CosmicFormulaBasic.lean#L16)#cosmic_formula_one

```lean
/-- A: 宇宙式 Basic Cosmic Formula -/
def cosmic_formula_one (x : ℝ) : ℝ :=
  (x + 1)^2 - x * (x + 2)
  -- 宇宙式の基本形（恒等式）
```

---

## 展開

宇宙式を変形します：

$x(x+2)$を展開し、

$$
f(x) = (x+1)^2 - x^2 - 2x = 1
$$

両辺に$-1$を加えます。

$$
f(x) = (x+1)^2 - x^2 - 2x - 1 = 0
$$

$-1$ を括り出しておきます。

$$
f(x) = (x+1)^2 - (x^2 + 2x + 1) = 0
%% verified: cosmic_formula_expanded
$$

さらに展開を進めます：

$$
\Large
f(x) = (x^2 + 2x + 1) - (x^2 + 2x + 1) = 0
%% verified: cosmic_formula_expanded_steps
$$

この展開により、各項が互いに打ち消し合い、恒等的にゼロとなることが確認できます。

$(x+1)^2$ の展開を差し引けば、ゼロになるのは当然の結果です。

---

### 一般化: 単位宇宙式（平方完成 版）

#### 定数項

$$
\Large
+1 \to +u
%% verified: cosmic_formula_unit_shift
$$

と、単位差 $\pm u$ 記号にすると宇宙式は、**単位** 宇宙式として次の恒等式を得ます。

$$
f_u(x) = (x+u)^2 - x^2 - 2xu - u^2 = 0
%% verified: cosmic_formula_unit_identity
$$

これは、任意の $x$ に依存せず $u \to u^2$ の恒等式を与えます。
（両辺に $+u^2$ する）

$$
f(x;u) = (x+u)^2 - x^2 - 2xu = u^2
%% verified: cosmic_formula_unit_identity_rearranged
$$

$u$ を自乗（べき乗）へと昇華させます。

$$
\Large
f(x;u) = u^2
%% verified: cosmic_formula_unit_identity_final
$$

この形は、宇宙式の一段階、一般化された形式であり $u$ の値に応じて異なる恒等式を提供します。

---

### 一般化: 無次元宇宙式（d 次元完成 版）

べき乗の差の因数分解の公式より、以下の恒等式が導けます。

$$
f_d(x;u) = (x+u)^d - \binom{d}{1} x^{d-1} u = \binom{d}{2} x^{d-2} u^2 + \binom{d}{3} x^{d-3} u^3 + \cdots + u^d.
%% verified: cosmic_formula_dim_identity
$$

- $\binom{d}{1} x^{d-1} u = (x^d + d x^{d-1} u)$ と書き換えられます。
- ここで、$d\in\mathbb{N}$ は任意の正整数です。$x$ および $u$ は実数です。

この無次元宇宙式は、より高次の多項式に対しても同様の恒等式を提供します。

和の二項展開式表示では、

$$
f_d(x;u) = \sum_{k=2}^{d} \binom{d}{k}\ x^{d-k}\ u^k
%% verified: cosmic_formula_dim_identity_sum
$$

となります。

> $u^d = (x^d + d x^{d-1} u)$ を引いた形で、べき乗の差の因数分解を表現しています。
>
> **二項定理の公式**
>
> $$
> (x+u)^d = \sum_{k=0}^{d} \binom{d}{k}\ x^{d-k}\ u^k
> $$
>
> その中で、$k=0,1$ の項を除いた残りの和が得られます。
>
> $$
> (x+u)^d = x^d + d x^{d-1} u + \sum_{k=2}^{d} \binom{d}{k}\ x^{d-k}\ u^k
> $$
>
> ここから $x^d + d x^{d-1} u$ を引くと、上記の恒等式が得られます。
> $$
> f_d(x;u) = (x+u)^d - \left( x^d + d x^{d-1} u \right) = \sum_{k=2}^{d} \binom{d}{k}\ x^{d-k}\ u^k
> $$
> これは、べき乗の差の因数分解の一般形を示しています。
> $$
> (x+u)^d - u^d = x \sum_{k=0}^{d-1} \binom{d}{k+1} x^k u^{d-1-k}
> $$

---

### 無次元単位宇宙式 $U_d$

$f_d(x;u) \to U_d(x;u)$ と関数名を変えます。

$$
f_d(x;u) = U_d(x;u) := (x+u)^d -\left( x \sum_{k=0}^{d-1} \binom{d}{k+1} x^k u^{d-1-k} \right) = u^d
%% verified: cosmic_formula_dim_identity_binom
$$

これは [CosmicFormulaBinom](/lean/dk_math/DkMath/CosmicFormula/CosmicFormulaBinom.lean#L104)#cosmic_id モジュールで形式化された恒等式です。

```lean
theorem cosmic_id {R : Type _} [CommRing R] (d : ℕ) (x u : R) :
        (x + u) ^ d - x * G d x u = u ^ d := by ...
```

二項定理項を$G$と定義すると、

$$
\Large
G_{d-1}(x,u) := \sum_{k=0}^{d-1} \binom{d}{k+1}\,x^k\,u^{(d-1-k)}
%% verified: cosmic_formula_dim_identity_G_definition
$$

```lean
/-- d 次元の「無次元実体項」G の定義（係数は Nat.choose を射影したもの） -/
def G {R : Type _} [CommRing R] (d : ℕ) (x u : R) : R :=
    ∑ k ∈ Finset.range d, (Nat.choose d (k + 1) : R) * x ^ k * u ^ (d - 1 - k)
```

同様に [CosmicFormulaDim.lean](/lean/dk_math/DkMath/CosmicFormula/CosmicFormulaDim.lean#L19)

```lean
/-- d 次元の「実体項」G の定義 -/
noncomputable def G (d : ℕ) (x u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range d,
    (Nat.choose d (k+1) : ℝ) * x^k * u^(d-1-k)
```

に対応します。

---

### Zero-sum Game: $Z_d$ 恒等式

$G$ にかかる $x$ 係数 $\Rightarrow x\ G_{d-1}(x,u)$ は、以下の恒等式を満たします。

$$
\large
Z_d(x;u) = \bigl[\ (x+u)^d - u^d \ \bigr] - \bigl[\ x\ G_{d-1}(x,u) \ \bigr] = 0
%% verified: cosmic_formula_dim_identity_Z_definition
$$

で、ゼロサムゲームです。

[CosmicFormulaBinom](/lean/dk_math/DkMath/CosmicFormula/CosmicFormulaBinom.lean#L180)#Z_eq_zero モジュールで形式化された恒等式です。

```lean
/-- Z_d は恒等的に 0 である -/
theorem Z_eq_zero {R : Type _} [CommRing R] (d : ℕ) (x u : R) : Z d x u = 0 := by ...
```

上記より、べき乗の差の因数分解と二項定理の恒等式が得られます。

$$
(x+u)^d - u^d = x\,G_{d-1}(x,u) \iff \frac{(x+u)^d - u^d}{x} = G_{d-1}(x,u)
%% verified: cosmic_formula_dim_identity_power_difference
$$
これは、べき乗の差の因数分解の一般形に対応します。[^1]

[^1]:

    - 注意：可換環 $\mathbb{R}$ の元として両辺を割る場合は $x$ が可逆（unit）である必要がある。
      - 「$x$ が可逆（unit）である」は、$\mathbb{R}$ に逆元 $x⁻¹$ が存在して $x·x⁻¹ = 1$ とできることを意味する。
      可逆でない元についてはリング内で「$÷x$」を定義できない（$x⁻¹$ を掛けられない）。
      - だが今回の等式は多項式環 $R[x,u]$ 内の話であって、$(x+u)^d - u^d$ は定数項が $0$ なので多項式として $x$ で割り切れる。
      つまりある多項式 $G(x,u) ∈ R[x,u]$ が存在して $(x+u)^d - u^d = x · G(x,u)$ となる。
      ここでの「$/x$」は多項式除法（商多項式を取ること）であり、$x$ の逆元を要しない。
    - 留意点：ある $r∈\R$ を代入してから両辺を $\mathbb{R}$ 内で割りたい（数として $/r$ をとる）なら、その代入値 $r$ が $\mathbb{R}$ の単元である必要がある。また、等式 $x·A = x·B$ から $A = B$ を結論づけるには一般に $x$ が零因子でないこと（あるいは可逆であること）が必要となる。

---

### $x$ 係数による表現

べき乗の差の因数分解を$T$と定義すると、

$$
T_d(x;u) := \frac{(x+u)^d - u^d}{x} = G_{d-1}(x,u)
%% verified: cosmic_formula_dim_identity_T_definition
$$

$x$ を掛け直すと、

$$
x\,T_d(x;u) = (x+u)^d - u^d = x\,G_{d-1}(x,u)
%% verified: cosmic_formula_dim_identity_T_multiplication
$$

よって、

$$
T_d(x;u) = G_{d-1}(x,u)
%% verified: cosmic_formula_dim_identity_T_equals_G
$$

となる。[^1]

---

### $x,u$ の交換と対称性

$x,u$ の役割を変えると、

$$
(x+u)^d - x^d = \sum_{k=1}^{d} \binom{d}{k}\ u^k\ x^{d-k}
%% verified: cosmic_formula_dim_identity_power_difference_expanded
$$

が、成り立ちます。

$$
(x+u)^d - u^d = \sum_{k=1}^{d} \binom{d}{k}\ x^k\ u^{d-k}
%% verified: cosmic_formula_dim_identity_power_difference_expanded_reversed
$$

ともに、二項定理の展開式が得られます。
異なるのは、引かれるべき項が $x^d$ か $u^d$ かの違いだけです。

---

### 全体: 総体の定義と差の定義

この２つの間にあたる $W$ を定義すると、

- $W$ の定義

    $$
    W = (x+u)^d
    $$

つまり、引かれる前の全体そのもの。

全体からの差は、

1. $x^d$ を差し引いた形

    $$
    Y = W - x^d = \sum_{k=1}^{d} \binom{d}{k}\ u^k\ x^{d-k}
    $$

2. $u^d$ を差し引いた形

    $$
    Y = W - u^d = \sum_{k=1}^{d} \binom{d}{k}\ x^k\ u^{d-k}
    $$

3. 二項係数の対称性（パスカルの三角形の根拠）

    $$
    \binom{d}{k} = \binom{d}{d-k}
    $$

を用いると、上記２つの差は互いに入れ替え可能であることが分かります。

つまり、総体は、

$$
\begin{align*}
W = (x+u)^d &= x^d + Y = u^d + Y \\[8pt]
&= x^d + \sum_{k=1}^{d} \binom{d}{k}\ u^k\ x^{d-k} \\[4pt]
&= u^d + \sum_{k=1}^{d} \binom{d}{k}\ x^k\ u^{d-k} \\[16pt]
&= \sum_{k=0}^{d} \binom{d}{k}\ x^k\ u^{d-k}
\end{align*}
%% verified: cosmic_formula_dim_identity_total_definition
$$

となり、二項定理の基本形が得られます。

---

### 宇宙式の特殊ケース $(d=2)$

$$
\hat{f}(\hat{x};\hat{u}) = \frac{f(x;u)}{u^2} = \left(1 + \frac{x}{u}\right)^2 - \left(\frac{x}{u}\right)^2 - 2\left(\frac{x}{u}\right) = 1
$$

ここで、$\hat{x} = \frac{x}{u}$および$\hat{u} = 1$と定義されます。無次元宇宙式は、変数のスケーリングに依存せず、恒等的に1となる形式を提供します。
この無次元形式は、宇宙式のさらなる一般化であり、数学的および物理学的な応用において重要な役割を果たします。

### 証明

$$
\hat{f}(\hat{x};\hat{u}) = \frac{(x+u)^2 - x^2 - 2xu}{u^2} = \frac{u^2}{u^2} = 1
%% verified: cosmic_formula_dimensionless_identity
$$

---

## 応用例

### セル増加数の計算

$$
(x+u)^d = u^d + x\sum_{k=0}^{d-1}\binom{d}{k+1}\ x^k\ u^{d-1-k}
$$

$$
V_d^+(x;u) = (x+u)^d + u^d
  = 2u^d + x\sum_{k=0}^{d-1}\binom{d}{k+1}\ x^k\ u^{d-1-k}
$$

$$
\Delta_d(x;u) := (x+2u)^d - \bigl((x+u)^d+u^d\bigr)
$$

$$
\Delta_d(x;u)
  = \sum_{j=1}^{d-1}\binom{d}{j}(2^j-1)\ x^{d-j}\ u^j + (2^d-2)u^d
$$

$$
\text{追加セル数} = \frac{\Delta_d(x;u)}{u^d}
$$

$$
\Delta_d(x;1) = (x+2)^d - (x+1)^d -1
$$

---

VSCode and GitHub Markdown $\LaTeX$ Style Documentation

This document uses GitHub-flavored Markdown and $\LaTeX$ for mathematical expressions. To render the $\LaTeX$ expressions correctly, ensure that your Markdown viewer supports MathJax or a similar library.
