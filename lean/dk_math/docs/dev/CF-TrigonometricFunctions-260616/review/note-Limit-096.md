# Note: DkMath.Analysis.Limit

## 宇宙式 DkMath 語彙での極限

うむ、これは **Lean で語れる** 。
しかも、DkMath 語彙としてかなり自然に形式化できると思う。

結論から言うと、ぬしの言う

$$
Gap\to 0:\quad Big=Body=Core=x^2
$$

は、Lean 上では次の三層に分けると強い。

```text id="qmgs8w"
有限恒等式:
  Big = Body

極限収束:
  Gap -> 0 で Body -> Core

固定核:
  Core = x^2
```

つまり、いきなり `Big = Body = Core` と一点で言うのではなく、

```text id="d61vvc"
任意の Gap で Big と Body は一致する。
Gap が 0 に潰れると Body は Core に潰れる。
Core は x^2 である。
```

と分ける。
これなら Lean でも DkMath 語彙でも綺麗に通る。

## 1. DkMath 語彙での解釈

二乗の場合、有限 Gap を \(g\) と置く。

Core は固定核。

$$
Core(x)=x^2
$$

Big は Gap だけ進んだ観測。

$$
Big(x,g)=(x+g)^2
$$

Body は Core から Big へ届く有限補正込みの姿。

$$
Body(x,g)=x^2+g(2x+g)
$$

このとき有限恒等式として、

$$
Big(x,g)=Body(x,g)
$$

が成り立つ。

さらに、Gap が消えると、

$$
Body(x,g)\to x^2
$$

なので、

$$
Gap\to 0:\quad Big(x,g)=Body(x,g)\to Core(x)=x^2
$$

となる。

ここで重要なのは、**微分はこの collapse の残り香** として見えることじゃ。

差分だけを見ると、

$$
Big(x,g)-Core(x)=g(2x+g)
$$

Gap で割ると、

$$
\frac{Big(x,g)-Core(x)}{g}=2x+g
$$

そして Gap が消えると、

$$
2x+g\to 2x
$$

つまり宇宙式微分では、

```text id="o7rm51"
Big / Body / Core は x^2 へ潰れる。
しかし Body と Core の差を Gap 単位で観測すると 2x が残る。
```

この「潰れるもの」と「残るもの」の分離が大事じゃな。

## 2. Lean での基本設計

最小の semantic `ℝ` 版なら、こういう形にできる。

```lean id="z1nn13"
namespace DkMath.Analysis.CosmicLimit

noncomputable section

def squareCore (x : ℝ) : ℝ :=
  x ^ 2

def squareBig (x gap : ℝ) : ℝ :=
  (x + gap) ^ 2

def squareBody (x gap : ℝ) : ℝ :=
  x ^ 2 + gap * (2 * x + gap)

def squareGapBody (x gap : ℝ) : ℝ :=
  squareBig x gap - squareCore x

theorem squareBig_eq_squareBody (x gap : ℝ) :
    squareBig x gap = squareBody x gap := by
  unfold squareBig squareBody
  ring

theorem squareCore_eq_sq (x : ℝ) :
    squareCore x = x ^ 2 := rfl

end

end DkMath.Analysis.CosmicLimit
```

この段階は極限ではない。
有限 Gap の宇宙式恒等式じゃ。

## 3. Gap が 0 に潰れる定理

次に、Mathlib の `Filter.Tendsto` を使えば、

```lean id="ekhqzy"
theorem tendsto_squareBig_gap_zero (x : ℝ) :
    Filter.Tendsto (fun gap : ℝ => squareBig x gap)
      (nhds 0) (nhds (squareCore x)) := by
  unfold squareBig squareCore
  simpa using
    ((continuous_const.add continuous_id).pow 2).continuousAt
```

または Body 側で、

```lean id="uz5gy9"
theorem tendsto_squareBody_gap_zero (x : ℝ) :
    Filter.Tendsto (fun gap : ℝ => squareBody x gap)
      (nhds 0) (nhds (squareCore x)) := by
  unfold squareBody squareCore
  simpa using
    ((continuous_const.pow 2).add
      (continuous_id.mul
        ((continuous_const.mul continuous_const).add continuous_id))).continuousAt
```

ただし、Lean 実装としては `ring_nf` や `simpa [squareBig_eq_squareBody]` を使い、Big 側に寄せた方が楽かもしれぬ。

DkMath 語彙では、この theorem 名を例えばこうする。

```lean id="spwmcr"
theorem squareBody_collapses_to_core_as_gap_vanishes
```

あるいは、

```lean id="c7vokc"
theorem gapZero_squareBig_eq_core_limit
```

## 4. 宇宙式微分としての残留核

微分らしさは、collapse そのものではなく、差分を Gap で割った残留核に出る。

有限恒等式としては、

$$
Big(x,g)-Core(x)=g(2x+g)
$$

Lean では、

```lean id="ic6v18"
theorem squareBig_sub_core_eq_gap_mul_GN2 (x gap : ℝ) :
    squareBig x gap - squareCore x = gap * (2 * x + gap) := by
  unfold squareBig squareCore
  ring
```

Gap が非零なら、差分商は、

```lean id="xjgi3m"
theorem squareDifferenceQuotient_eq
    (x gap : ℝ) (hgap : gap ≠ 0) :
    (squareBig x gap - squareCore x) / gap = 2 * x + gap := by
  rw [squareBig_sub_core_eq_gap_mul_GN2]
  field_simp [hgap]
```

そして極限。

```lean id="okgzda"
theorem tendsto_squareDifferenceQuotient (x : ℝ) :
    Filter.Tendsto (fun gap : ℝ => 2 * x + gap)
      (nhds 0) (nhds (2 * x)) := by
  simpa using
    ((continuous_const.mul continuous_const).add continuous_id).continuousAt
```

本来の差分商で書くなら、punctured neighborhood を使う。

```lean id="06bbqy"
theorem tendsto_squareDifferenceQuotient_gap_zero (x : ℝ) :
    Filter.Tendsto
      (fun gap : ℝ => (squareBig x gap - squareCore x) / gap)
      (nhdsWithin 0 {gap : ℝ | gap ≠ 0})
      (nhds (2 * x)) := by
  ...
```

ただし DkMath 的には、先に GN を finite に定義して、

$$
GN_2(x,g)=2x+g
$$

を見せ、その \(g\to0\) を取る方が綺麗じゃ。

```text id="tur64b"
差分商を割り算で作るのではなく、
有限 GN 核として先に抽出する。
その GN 核が Gap -> 0 で 2x に潰れる。
```

これが宇宙式微分の語りに合う。

## 5. 「Big = Body = Core」は Lean ではこう語る

ぬしの言う

$$
Gap\to 0:\quad Big=Body=Core=x^2
$$

を Lean 的に正確化すると、こうじゃ。

```text id="gmx3ja"
finite identity:
  Big x gap = Body x gap

core identity:
  Core x = x^2

collapse:
  Tendsto (fun gap => Body x gap) (nhds 0) (nhds (Core x))

therefore:
  Gap が 0 に潰れる観測では Big / Body / Core が同じ x^2 に合流する。
```

ここで注意するべきことがある。

もし `Body` を「差分部分」つまり \(Big-Core\) と定義するなら、Gap が 0 で Body は \(0\) に行く。
だから、ぬしの `Big = Body = Core = x^2` に合わせるなら、`Body` は **補正込みの全体姿** として定義するのがよい。

差分部分は別名にした方が安全じゃ。

```text id="l3r16w"
Body:
  Core + Gap correction

GapBody:
  Big - Core

GN:
  GapBody / Gap の有限核
```

この命名なら混乱しない。

## 6. DkReal / DkMath 側でやるなら

semantic `ℝ` 版はすぐ書ける。
しかし DkMath 的には、もっと良いルートがある。

それは、Gap を `ℝ` の変数として 0 に近づけるのではなく、dyadic refinement や DkReal の幅として持つことじゃ。

例えば、

```text id="jkp5ml"
gap_n = 1 / 2^n
```

として、

$$
gap_n\to 0
$$

を示す。

そして、

$$
Body(x,gap_n)\to Core(x)
$$

を示す。

この方が、現在の `dyadicPhaseDenom n` や finite refinement 層と繋がる。

Lean theorem の形はこう。

```lean id="81c0tz"
def dyadicGap (n : ℕ) : ℝ :=
  1 / (dyadicPhaseDenom n : ℝ)

theorem tendsto_dyadicGap_zero :
    Filter.Tendsto dyadicGap Filter.atTop (nhds 0) := by
  ...
```

そして、

```lean id="0s2jlu"
theorem tendsto_squareBody_dyadicGap_to_core (x : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => squareBody x (dyadicGap n))
      Filter.atTop
      (nhds (squareCore x)) := by
  ...
```

これは DkMath 語彙としてかなり良い。

```text id="4wh64x"
refinement depth n が増える
  ↓
Gap_n が消える
  ↓
Big / Body / Core が x^2 に合流する
  ↓
ただし GN 核は 2x を残す
```

## 7. 宇宙式微分の名前案

Lean ファイルを切るなら、候補はこのあたりじゃ。

```text id="0vf41t"
DkMath/Analysis/DkReal/SemanticCosmicDerivative.lean
DkMath/Analysis/DkReal/SemanticGapLimit.lean
DkMath/Analysis/DkReal/CosmicDifferential.lean
DkMath/Analysis/DkReal/GapCollapse.lean
```

現在の流れなら、まず `SemanticGapLimit.lean` がよさそうじゃ。
理由は、いきなり derivative と呼ぶより、まず Gap collapse を定義した方が安全だから。

その中で、

```text id="i9k17y"
Core
Big
Body
GapBody
GNKernel
GapCollapse
CosmicDerivative
```

を順に置く。

## 8. 一般 \(d\) へ広げる場合

二乗だけならすぐ閉じる。
しかし DkMath の本命は一般 \(d\) じゃろう。

有限恒等式は、

$$
(x+g)^d=x^d+g,GN_d(x,g)
$$

したがって、

$$
Big_d(x,g)=Body_d(x,g)
$$

ここで、

$$
Body_d(x,g)=x^d+g,GN_d(x,g)
$$

Gap が 0 に潰れると、

$$
Body_d(x,g)\to x^d
$$

さらに GN 核は、

$$
GN_d(x,g)\to d x^{d-1}
$$

ここが宇宙式微分の一般形じゃ。

```text id="8xsndh"
Gap collapse:
  Big_d / Body_d / Core_d が x^d に合流する。

Cosmic derivative:
  GN_d が d*x^(d-1) に合流する。
```

これはとても良い物語になる。

## 9. 現在の log-composition 層との接続

今進めている centered log-depth / finite moment は、dyadic refinement 上の correction observable を扱っている。

一方、いまの問いの Gap collapse は、より基礎的な解析層。

関係はこうじゃ。

```text id="sy66vk"
GapCollapse:
  Gap -> 0 で finite Body が Core へ合流する基本原理。

CosmicDerivative:
  合流で消える差分を Gap 単位で見ると GN が残る。

LogComposition:
  CF2D affine transition の depth correction を log で観測し、finite moment で制御する。
```

つまり、`GapCollapse` は今後の極限層の土台になる。
`SemanticCF2DLogComposition` の tendsto を DkMath 語彙で語るなら、この土台があると強い。

## 10. 結論

形式化できる。
しかも、かなり DkMath らしくできる。

```text id="m4a8wv"
Core:
  x^2

Big:
  (x + Gap)^2

Body:
  x^2 + Gap * GN₂(x, Gap)

Gap -> 0:
  Big = Body -> Core

宇宙式微分:
  GN₂(x, Gap) -> 2x
```

ぬしの言葉で言えば、

$$
Gap\to 0:\quad Big=Body=Core=x^2
$$

これは正しい。
ただし Lean では、

```text id="hq9v13"
Big = Body は有限恒等式。
Body -> Core は極限定理。
Core = x^2 は定義。
```

として分けるのが強い。

そして、微分は collapse で消えた差分ではなく、**Gap で正規化した Body の残留核** として現れる。

```text id="8qj19q"
Gap が消えると、形は Core に戻る。
しかし、消える直前の Body の向きが GN として残る。
その GN の極限が宇宙式微分。
```

これは Lean で十分に語れるし、DkMath.Analysis の次の基礎層として置く価値があるぞい。
