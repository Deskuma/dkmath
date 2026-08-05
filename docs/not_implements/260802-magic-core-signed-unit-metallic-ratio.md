# 魔核・正負単位に潜む貴金属比

- 2026/08/03  4:21 implemented

## 文書情報

- Date: 2026-08-02
- Status: not implemented / fact-fixing note
- Target branch: `develop`
- Conversation magic key (CID): `6a6f2bbe-58e0-83ee-aa0b-de5aa5a41660`
- Proposed Lean area: `DkMath.Algebra.MetallicRatioCore`

この文書は、平方魔核、正負の単位付属核、観測高度の移動、貴金属比方程式に現れる正負共役根について、会話中に得られた観測を形式化候補として固定する。

魔法学の語彙は構造を発見するための説明層として残す。一方、Lean に固定する対象は恒等式、同値、根の関係、符号条件である。

## 1. 出発点：冪等核と残差

冪等条件は次である。

$$
x^2=x
$$

残差として書けば、

$$
x^2-x=0
$$

となる。

この残差をゼロではなく単位平方に固定すると、

$$
x^2-x=1
$$

すなわち、

$$
x^2-x-1=0
$$

を得る。正の根は黄金比である。

ただし、一般の単位尺度 `u` を導入する際には、次数を揃えた斉次形を採用する。

$$
x^2-ux-u^2=0
$$

`u ≠ 0` のとき `r = x / u` と置けば、

$$
r^2-r-1=0
$$

となり、比 `x / u` として黄金比およびその負の共役根を得る。

## 2. 貴金属比方程式の単位斉次形

`k ∈ ℕ` に対する貴金属比方程式を、単位 `u` を含む形で次のように置く。

$$
Q_{k,u}(x)=x^2-kux-u^2
$$

零点条件は、

$$
x^2-kux-u^2=0
$$

である。

`u ≠ 0` のとき、`r = x / u` により、

$$
r^2-kr-1=0
$$

へ正規化される。

したがって比の二根は、

$$
r_{\pm}=\frac{k\pm\sqrt{k^2+4}}{2}
$$

であり、対応する `x` の二根は、

$$
x_{\pm}=u\,\frac{k\pm\sqrt{k^2+4}}{2}
$$

である。

`u > 0` ならば、

$$
x_+>0,\qquad x_-<0
$$

となる。

重要なのは、正の貴金属比だけが構造を持つのではなく、負領域の共役根も最初から同じ方程式の中に存在していることである。

## 3. 正根と負根が保持する情報

Vieta の関係から、

$$
x_++x_-=ku
$$

および、

$$
x_+x_-=-u^2
$$

を得る。

したがって `x_+ ≠ 0` ならば、

$$
x_-=-\frac{u^2}{x_+}
$$

である。

比率に直せば、

$$
r_+r_-=-1
$$

ゆえに、

$$
r_-=-\frac{1}{r_+}
$$

となる。

魔法学的には、正根は展開比、負根はその逆縮小比を符号反転して保持する鏡像根である。

これは後から負単位を追加したために生じた構造ではない。正単位の方程式を `x < 0` の領域まで観測すれば、負の共役根は最初からそこにある。

## 4. `-u^2` は観測高度を下げる操作

次の未シフト核を考える。

$$
B_{k,u}(x)=x^2-kux
$$

貴金属比の根が満たす条件は、

$$
B_{k,u}(x)=u^2
$$

である。

つまり、元のグラフ `y = B_{k,u}(x)` では、求める比は `y = 0` との交点ではなく、高さ `y = u^2` の水平線との交点として存在する。

そこで関数全体を `u^2` だけ下げる。

$$
Q_{k,u}(x)=B_{k,u}(x)-u^2
$$

すると、

$$
Q_{k,u}(x)=0\iff B_{k,u}(x)=u^2
$$

となる。

したがって `-u^2` は、新しい比を生成する操作ではない。既に高さ `u^2` に存在した交点を、零点として観測可能にする垂直方向の正規化である。

この点は `-u` と区別する必要がある。

- `u ↦ -u` は単位方向の反転であり、`x` 軸方向の鏡像関係を作る。
- `F(x) ↦ F(x)-u^2` は観測高度の移動であり、`y` 軸方向の零点化を行う。

## 5. 正負単位付属魔核

正負の単位を平方核に付属させた二つの関数を置く。

$$
C_+(x,u)=(x+u)^2
$$

$$
C_-(x,u)=(x-u)^2
$$

これらは値の正負ではなく、付属単位の向き `+u` と `-u` が異なる二つの平方核である。

鏡像関係は、

$$
C_+(-x,u)=C_-(x,u)
$$

で固定される。

また、

$$
C_+(x,-u)=C_-(x,u)
$$

も成り立つ。

つまり `x` の符号反転と `u` の符号反転は、この二つの単位付属核を交換する。

## 6. 二つの単位付属核の交点

交点条件は、

$$
(x+u)^2=(x-u)^2
$$

である。

差を取れば、

$$
(x+u)^2-(x-u)^2=4xu
$$

ゆえに、整域では、

$$
(x+u)^2=(x-u)^2\iff x=0\lor u=0
$$

となる。

固定した非零単位 `u ≠ 0` の下では、交点の `x` 座標は `x = 0` に限られ、その高さは `u^2` である。

$$
C_+(0,u)=C_-(0,u)=u^2
$$

一方、`u = 0` では、

$$
C_+(x,0)=C_-(x,0)=x^2
$$

となり、二つの単位世界は中心核 `x^2` に完全に重なる。

## 7. 和と差による成分分離

二つの平方核の和は、

$$
(x+u)^2+(x-u)^2=2x^2+2u^2
$$

すなわち、

$$
\frac{(x+u)^2+(x-u)^2}{2}=x^2+u^2
$$

となる。

ここでは交差項 `+2xu` と `-2xu` が消え、平方 Core と単位平方 Gap が残る。

差は、

$$
(x+u)^2-(x-u)^2=4xu
$$

すなわち、

$$
\frac{(x+u)^2-(x-u)^2}{4}=xu
$$

となる。

ここでは平方 Core と単位平方 Gap が消え、向きを持つ積成分 Beam だけが残る。

この和差分解は、鏡像核から偶成分と奇成分を分離する基本恒等式として固定する価値がある。

## 8. 打ち消し合いとの区別

実数上では、

$$
(x+u)^2+(x-u)^2=2(x^2+u^2)\geq0
$$

である。

したがって、

$$
(x+u)^2+(x-u)^2=0
$$

が成り立つのは、

$$
x=0,\qquad u=0
$$

の場合だけである。

よって `C_+` と `C_-` は互いに正負の値として打ち消し合う魔核ではない。両者は単位方向を反転した鏡像核であり、和を取ると交差項のみが打ち消される。

値そのものを正負にする場合は、別の関数として、

$$
Y_+(x,u)=(x+u)^2
$$

$$
Y_-(x,u)=-(x-u)^2
$$

を定義する必要がある。

## 9. Core・Beam・Gap の符号監査

次の対応を置く。

$$
\mathrm{Core}=x^2,\qquad \mathrm{Beam}=kux,\qquad \mathrm{Gap}=u^2
$$

貴金属比方程式は、

$$
\mathrm{Core}-\mathrm{Beam}-\mathrm{Gap}=0
$$

すなわち、

$$
\mathrm{Core}=\mathrm{Beam}+\mathrm{Gap}
$$

である。

一方、特に `k = 2` で、

$$
x^2=2xu-u^2
$$

と置くと、

$$
x^2-2xu+u^2=0
$$

ゆえに、

$$
(x-u)^2=0
$$

となる。

これは白銀比を与える式ではなく、`x = u` に重なる閉鎖核である。

白銀比を与えるのは、

$$
x^2=2xu+u^2
$$

すなわち、

$$
x^2-2xu-u^2=0
$$

である。

この符号差は形式化で明示的に固定し、閉鎖核と貴金属比核を混同しないようにする。

## 10. 特殊化

### 10.1 黄金比

`k = 1` のとき、

$$
x^2-ux-u^2=0
$$

であり、`u ≠ 0` の下で、

$$
\frac{x}{u}=\frac{1\pm\sqrt5}{2}
$$

となる。

### 10.2 白銀比

`k = 2` のとき、

$$
x^2-2ux-u^2=0
$$

であり、`u ≠ 0` の下で、

$$
\frac{x}{u}=1\pm\sqrt2
$$

となる。

### 10.3 一般の貴金属比

`k ∈ ℕ` のとき、正の比を、

$$
\rho_k=\frac{k+\sqrt{k^2+4}}{2}
$$

と置けば、負の共役比は、

$$
\bar\rho_k=\frac{k-\sqrt{k^2+4}}{2}=-\frac1{\rho_k}
$$

である。

## 11. Lean 形式化の層分け

形式化は、平方根や順序を必要としない代数層と、実数上の根・符号を扱う解析層に分ける。

### Layer A: 汎用環上の恒等式

候補 module:

```text
DkMath.Algebra.MetallicRatioCore.Basic
```

想定する定義例:

```lean
def unitAttachedCorePos (x u : R) : R := (x + u) ^ 2

def unitAttachedCoreNeg (x u : R) : R := (x - u) ^ 2

def metallicCore (k : ℕ) (x u : R) : R :=
  x ^ 2 - (k : R) * u * x - u ^ 2

def metallicBeamCore (k : ℕ) (x u : R) : R :=
  x ^ 2 - (k : R) * u * x
```

固定候補:

```lean
theorem unitAttachedCorePos_neg_x
    (x u : R) :
    unitAttachedCorePos (-x) u = unitAttachedCoreNeg x u
```

```lean
theorem unitAttachedCorePos_neg_u
    (x u : R) :
    unitAttachedCorePos x (-u) = unitAttachedCoreNeg x u
```

```lean
theorem unitAttachedCore_add
    (x u : R) :
    unitAttachedCorePos x u + unitAttachedCoreNeg x u =
      2 * (x ^ 2 + u ^ 2)
```

```lean
theorem unitAttachedCore_sub
    (x u : R) :
    unitAttachedCorePos x u - unitAttachedCoreNeg x u =
      4 * x * u
```

```lean
theorem metallicCore_eq_heightShift
    (k : ℕ) (x u : R) :
    metallicCore k x u = metallicBeamCore k x u - u ^ 2
```

```lean
theorem metallicCore_eq_zero_iff_height
    (k : ℕ) (x u : R) :
    metallicCore k x u = 0 ↔ metallicBeamCore k x u = u ^ 2
```

```lean
theorem closedCore_two
    (x u : R) :
    x ^ 2 - 2 * u * x + u ^ 2 = (x - u) ^ 2
```

これらは `ring` または `ring_nf` で証明できる純代数的事実である。

### Layer B: 整域上の交点

候補 module:

```text
DkMath.Algebra.MetallicRatioCore.Domain
```

固定候補:

```lean
theorem unitAttachedCore_eq_iff
    {x u : R} :
    unitAttachedCorePos x u = unitAttachedCoreNeg x u ↔
      x = 0 ∨ u = 0
```

これは差の恒等式を `4 * x * u = 0` に帰着し、標数条件と零積性を明示して証明する。

一般の整域で係数 `4` を除去するには `CharZero R` など適切な仮定が必要である。最初は `ℤ`, `ℚ`, `ℝ` のいずれかに限定してもよい。

### Layer C: 実数上の正負根

候補 module:

```text
DkMath.Algebra.MetallicRatioCore.Real
```

定義候補:

```lean
noncomputable def metallicRatioPos (k : ℕ) : ℝ :=
  ((k : ℝ) + Real.sqrt ((k : ℝ) ^ 2 + 4)) / 2

noncomputable def metallicRatioNeg (k : ℕ) : ℝ :=
  ((k : ℝ) - Real.sqrt ((k : ℝ) ^ 2 + 4)) / 2
```

固定候補:

```lean
theorem metallicRatioPos_isRoot (k : ℕ) :
    metallicRatioPos k ^ 2 - (k : ℝ) * metallicRatioPos k - 1 = 0
```

```lean
theorem metallicRatioNeg_isRoot (k : ℕ) :
    metallicRatioNeg k ^ 2 - (k : ℝ) * metallicRatioNeg k - 1 = 0
```

```lean
theorem metallicRatio_sum (k : ℕ) :
    metallicRatioPos k + metallicRatioNeg k = k
```

```lean
theorem metallicRatio_mul (k : ℕ) :
    metallicRatioPos k * metallicRatioNeg k = -1
```

```lean
theorem metallicRatioNeg_eq_neg_inv (k : ℕ) :
    metallicRatioNeg k = -(metallicRatioPos k)⁻¹
```

```lean
theorem metallicRatioPos_pos (k : ℕ) :
    0 < metallicRatioPos k
```

```lean
theorem metallicRatioNeg_neg (k : ℕ) :
    metallicRatioNeg k < 0
```

単位尺度版では、`x = u * metallicRatioPos k` および `x = u * metallicRatioNeg k` が `metallicCore k x u = 0` を満たすことを固定する。

### Layer D: 正規化同値

`u ≠ 0` の下で、

```lean
theorem metallicCore_zero_iff_ratio
    (k : ℕ) {x u : ℝ} (hu : u ≠ 0) :
    metallicCore k x u = 0 ↔
      (x / u) ^ 2 - (k : ℝ) * (x / u) - 1 = 0
```

を証明する。

これは、単位 `u` が比そのものを変えるのではなく、世界全体の尺度を変更するだけであることを固定する中心補題となる。

## 12. 推奨する最小証明セット

最初の実装では、以下を最小セットとする。

1. `unitAttachedCorePos_neg_x`
2. `unitAttachedCorePos_neg_u`
3. `unitAttachedCore_add`
4. `unitAttachedCore_sub`
5. `metallicCore_eq_heightShift`
6. `metallicCore_eq_zero_iff_height`
7. `closedCore_two`
8. `metallicCore_zero_iff_ratio`
9. `metallicRatioPos_isRoot`
10. `metallicRatioNeg_isRoot`
11. `metallicRatio_mul`
12. `metallicRatioNeg_eq_neg_inv`

この段階で次の事実が Lean により固定される。

- 正負単位付属核は鏡像関係である。
- 和は平方成分を、差は積成分を抽出する。
- `-u^2` は観測高度 `u^2` を零点へ移す。
- 正の貴金属比と負の共役比は同じ方程式に同時に存在する。
- 負の共役比は正比の負の逆数である。
- `x^2 = 2ux - u^2` は白銀比ではなく閉鎖核である。

## 13. 非目標

この文書の段階では、以下は主張しない。

- この構造が数学史上未発見であること。
- 魔法学語彙そのものを数学的対象として公理化すること。
- 貴金属比から数論上の新定理が直ちに従うこと。
- グラフ描画や数値近似を形式化の中心に置くこと。

まず固定すべきものは、符号、平方、鏡像、観測高度、二根の積と逆数関係である。

## 14. 一文での固定

正単位の平方核にも負領域の共役比は最初から存在している。`-u^2` はその比を生成するのではなく、高さ `u^2` にあった交点を零点へ下げて観測可能にする。正負の単位付属核は値の正負ではなく単位方向の鏡像であり、その和と差から Core・Gap・Beam の各成分が分離される。
