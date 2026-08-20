# CFBRC の中心座標と臨界線外零点排除の基礎

## 1. この文書の位置づけ

この文書は、`DkMath.RH.CFBRC` によるリーマン予想形式化を依存順に説明する最初の数学的事実層である。

ここでは、リーマンゼータ関数の零点、関数等式、eta 級数、素数、Pascal 構造などはまだ用いない。

最初に固定するのは、CFBRC 側だけで成立する次の事実である。

> 標準 CFBRC を臨界線 $\Re(s)=1/2$ を中心とする実座標で評価すると、その CFBRC 零点は中心座標 $0$ にしか存在しない。

この層は後続のゼータ関数との bridge に依存しない **Core** である。

対象 module:

```text
DkMath.RH.CFBRC.OffCriticalExclusion
DkMath.RH.CFBRC.OffCriticalExclusionGeneral
```

namespace:

```lean
DkMath.RH.CFBRCProjection
```

## 2. 臨界線を原点へ移す

Lean では、実部 $\sigma$ をそのまま扱うのではなく、臨界線 $1/2$ からの差を取り出す。

```lean
noncomputable def centeredSigma (σ : ℝ) : ℝ :=
  σ - (1 : ℝ) / 2
```

数学的には、

$$
\operatorname{centeredSigma}(\sigma)=\sigma-\frac12.
$$

したがって、中心座標が零になることと臨界線上にいることは同値である。

```lean
@[simp] theorem centeredSigma_eq_zero_iff (σ : ℝ) :
    centeredSigma σ = 0 ↔ σ = (1 : ℝ) / 2
```

すなわち、

$$
\operatorname{centeredSigma}(\sigma)=0
\iff
\sigma=\frac12.
$$

ここで重要なのは、$1/2$ を CFBRC の零点性から後付けしているのではないことである。まずリーマン予想の臨界線を中心とする座標変換を明示的に定義し、その座標上で CFBRC の零点幾何を調べる。

## 3. off-critical CFBRC の定義

中心化した実座標を標準 CFBRC に入力する。

```lean
noncomputable def offCriticalCFBRC (d : ℕ) (σ Θ : ℝ) : ℂ :=
  cfbrcR d (centeredSigma σ) Θ
```

数学的には、

$$
\operatorname{offCriticalCFBRC}(d,\sigma,\Theta)
:=
\operatorname{cfbrcR}\!\left(d,\sigma-\frac12,\Theta\right).
$$

$\Theta$ は CFBRC の第二実パラメータであり、この段階ではゼータ関数から導かれる位相量とは仮定しない。

定義のコメントにも明記されている通り、この対象にはゼータ零点 predicate は含まれていない。

したがって、

```text
offCriticalCFBRC = 0
```

という命題だけからリーマン予想を主張することはできない。後に標準ゼータ零点をこの CFBRC 零点へ写す bridge が別途必要になる。

## 4. degree 2 の CFBRC 零点

最初に形式化された排除定理は次数 $2$ である。

既存 CFBRC の二次展開は、実入力 $X,\Theta$ に対して概念的に、

$$
\operatorname{cfbrcR}(2,X,\Theta)
=
X^2+2iX\Theta
$$

という形を持つ。

Lean theorem:

```lean
theorem cfbrcR_two_eq_zero_iff_x_eq_zero (X Θ : ℝ) :
    cfbrcR 2 X Θ = 0 ↔ X = 0
```

したがって、

$$
\operatorname{cfbrcR}(2,X,\Theta)=0
\iff
X=0.
$$

### 4.1 証明の流れ

零点を仮定すると複素数全体が $0$ なので、その実部も $0$ である。

Lean では、

```lean
have hre : Complex.re (cfbrcR 2 X Θ) = 0 := by
  rw [h]
  simp
```

とし、既存 theorem `cfbrc_two_re` によって実部を $X^2$ へ落とす。

```lean
rw [cfbrc_two_re] at hre
nlinarith
```

これにより $X=0$ が得られる。

逆方向は $X=0$ を代入すれば CFBRC 定義から直接閉じる。

この証明にはゼータ関数も RH も使われていない。

## 5. degree 2 での臨界線固定

中心座標と degree 2 の零点定理を合成すると、

```lean
theorem offCriticalCFBRC_two_eq_zero_iff_re_eq_half (σ Θ : ℝ) :
    offCriticalCFBRC 2 σ Θ = 0 ↔ σ = (1 : ℝ) / 2
```

を得る。

数学的には、

$$
\operatorname{offCriticalCFBRC}(2,\sigma,\Theta)=0
\iff
\sigma=\frac12.
$$

証明は三つの既存事実の rewrite だけである。

```lean
rw [offCriticalCFBRC,
    cfbrcR_two_eq_zero_iff_x_eq_zero,
    centeredSigma_eq_zero_iff]
```

したがって、この時点で degree 2 の CFBRC 零点集合は、$\Theta$ の値によらず、実座標では一本の線

$$
\sigma=\frac12
$$

に固定される。

## 6. 任意の正次数への一般化

次に degree 2 固有の実部展開に依存せず、任意の正次数 $d>0$ へ一般化された。

Lean theorem:

```lean
theorem cfbrcR_eq_zero_iff_x_eq_zero
    {d : ℕ} (hd : 0 < d) (X Θ : ℝ) :
    cfbrcR d X Θ = 0 ↔ X = 0
```

数学的には、

$$
d>0
\Longrightarrow
\left(
\operatorname{cfbrcR}(d,X,\Theta)=0
\iff
X=0
\right).
$$

### 6.1 零点条件を冪の等式へ戻す

`cfbrcR d X Θ = 0` から、CFBRC 定義を展開して、

$$
(X+i\Theta)^d=(i\Theta)^d
$$

を得る。

Lean では `sub_eq_zero.mp` を用いて差が零であることを等式へ戻している。

### 6.2 複素ノルムを比較する

両辺へ複素ノルムを適用すると、

$$
\left\|X+i\Theta\right\|^d
=
\left\|i\Theta\right\|^d
$$

となる。

次数 $d$ は正なので、非負実数上で冪をキャンセルし、

$$
\left\|X+i\Theta\right\|
=
\left\|i\Theta\right\|
$$

を得る。

Lean では `pow_left_inj₀` がこの段階を担う。

### 6.3 norm square へ落とす

さらに `Complex.normSq` を用いると、

$$
X^2+\Theta^2=\Theta^2
$$

となる。

よって、

$$
X^2=0
$$

であり、実数上では、

$$
X=0
$$

が従う。

Lean の最後は `nlinarith` で閉じられる。

この一般証明の重要点は、次数ごとの二項展開を必要としないことである。

## 7. 任意の正次数での臨界線固定

一般定理を中心座標へ移すと、

```lean
theorem offCriticalCFBRC_eq_zero_iff_re_eq_half
    {d : ℕ} (hd : 0 < d) (σ Θ : ℝ) :
    offCriticalCFBRC d σ Θ = 0 ↔ σ = (1 : ℝ) / 2
```

を得る。

すなわち、任意の正次数について、

$$
\boxed{
\operatorname{offCriticalCFBRC}(d,\sigma,\Theta)=0
\iff
\sigma=\frac12
}
$$

である。

この theorem の特徴は $\Theta$ に制約を置かないことである。

したがって CFBRC 側だけを見れば、第二パラメータがどのような値であっても、零点の実座標は中心 $1/2$ 以外へ移動しない。

## 8. この段階で証明されていること

ここまでで Lean に固定されているのは次である。

```text
centeredSigma σ = 0
  ↔ σ = 1/2

cfbrcR 2 X Θ = 0
  ↔ X = 0

0 < d
  → (cfbrcR d X Θ = 0 ↔ X = 0)

0 < d
  → (offCriticalCFBRC d σ Θ = 0 ↔ σ = 1/2)
```

集合として書けば、正次数 $d$ と任意の $\Theta$ に対して CFBRC 零点の実座標集合は、

$$
Z_{\mathrm{CFBRC}}=\left\{\frac12\right\}
$$

となる。

複素平面上の縦線として読めば、CFBRC が許す中心実部は、

$$
\Re(s)=\frac12
$$

だけである。

## 9. この段階では証明されていないこと

この distinction は重要である。

ここまでの theorem は、

$$
\zeta(s)=0
\Longrightarrow
\operatorname{offCriticalCFBRC}(d,s.re,\Theta(s))=0
$$

を証明していない。

したがって、まだ

$$
\zeta(s)=0
\Longrightarrow
\Re(s)=\frac12
$$

は得られていない。

この段階で確定したのは、

> **もし対象となる零点を CFBRC 零点として zero-preserving に写せるなら、その実部は自動的に $1/2$ に固定される。**

という CFBRC 側の幾何である。

ゼータ関数との接続は後続文書で別の事実層として扱う。

## 10. 最初の bridge interface

この分離を型として明示するため、degree 2 では、

```lean
structure ZeroToCFBRCTwoBridge (Zero : ℂ → Prop) where
  phase : ℂ → ℝ
  map_zero : ∀ {s : ℂ}, Zero s → offCriticalCFBRC 2 s.re (phase s) = 0
```

一般正次数では、

```lean
structure ZeroToCFBRCBridge (Zero : ℂ → Prop) where
  d : ℕ
  hd : 0 < d
  phase : ℂ → ℝ
  map_zero : ∀ {s : ℂ}, Zero s → offCriticalCFBRC d s.re (phase s) = 0
```

が定義されている。

ここで load-bearing field は `map_zero` である。

CFBRC 零点から $1/2$ を取り出す処理は既に完成している。

```lean
theorem re_eq_half_of_zeroToCFBRCBridge
```

がその合成を行う。

したがって今後の形式化では、`map_zero` をどの数学から供給しているかを必ず監査しなければならない。

## 11. DkMath 的な分類

この文書の内容を DkMath 用語で分類すると次のようになる。

```text
Core:
  centeredSigma
  centeredSigma_eq_zero_iff
  cfbrcR_two_eq_zero_iff_x_eq_zero
  offCriticalCFBRC_two_eq_zero_iff_re_eq_half
  cfbrcR_eq_zero_iff_x_eq_zero
  offCriticalCFBRC_eq_zero_iff_re_eq_half

Beam / interface:
  ZeroToCFBRCTwoBridge
  ZeroToCFBRCBridge

Gap:
  実際の標準ゼータ非自明零点から map_zero を供給する数学
```

`ZeroToCFBRCBridge` 自体を埋めただけでは数学的 Gap は解決しない。`map_zero` が独立な証明から供給される必要がある。

## 12. 次の文書へ

次の事実層では、Mathlib の `RiemannHypothesis` と DkMath の `NontrivialRiemannZetaZero` を正確に対応させ、標準ゼータ零点を CFBRC へ写すことがどの論理的位置にあるかを記録する。

この順序を守ることで、

```text
CFBRC の零点幾何
↓
標準ゼータ零点 predicate
↓
zero-preserving bridge
↓
RH
```

を混同せず追跡できる。