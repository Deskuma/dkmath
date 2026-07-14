# Implementation Design: DkMath.Analysis.DkLimit

## 実装設計

そうじゃ、その理解で合っている。

今回は **素直に `Filter.Tendsto` ベースで進める** のが一番よい。
ただし、裸の `Tendsto` theorem を直接ばら撒くのではなく、DkMath 語彙の theorem 名で包んでおく。

つまり設計方針はこうじゃ。

```text id="mviv80"
実装の中身:
  Mathlib の Filter.Tendsto / nhds / atTop を使う。

公開 API 名:
  DkMath 語彙で命名する。

将来:
  DkReal 自前極限や GapLimit 型を作ったら、
  theorem の中身を置き換え、外側の API 名は維持する。
```

## 1. 今回の極限層の置き方

例えば、今の finite closed form から進むなら、まずはこういう theorem を置く。

```lean id="frmb8z"
theorem tendsto_dyadicPhaseClosedQuadraticBound_one_third :
    Filter.Tendsto
      (fun n : ℕ =>
        1 / 3 + 2 / (3 * (dyadicPhaseDenom n : ℝ) ^ 2))
      Filter.atTop
      (nhds (1 / 3 : ℝ))
```

これは中身としては普通の `Tendsto` じゃ。
でも theorem 名で、

```text id="qjz9ei"
dyadicPhase
ClosedQuadraticBound
one_third
```

という DkMath 文脈を保つ。

次に、

```lean id="nkshlr"
theorem tendsto_dyadicPhaseTrapezoidCenteredQuadraticSum_one_third :
    Filter.Tendsto
      dyadicPhaseTrapezoidCenteredQuadraticSum
      Filter.atTop
      (nhds (1 / 3 : ℝ))
```

これは閉形式 theorem を `rw` して、上の bound の tendsto に帰着できる。

## 2. エイリアスとして包む発想

ぬしの言う「後々で置き換えるためのエイリアスとして包む」はかなり重要じゃ。

たとえば将来、自前の極限語彙として、

```lean id="owxw6r"
DkTendstoAtTop f L
```

や、

```lean id="0yh84o"
GapRefinesToZero gap
```

のようなものを作るかもしれない。

しかし今はまだ要らない。
だから、今の段階では theorem 名だけ DkMath 語彙にして、中身は `Filter.Tendsto` で進める。

後で置換するなら、

```lean id="x75t5e"
theorem tendsto_dyadicPhaseTrapezoidCenteredQuadraticSum_one_third :
    Filter.Tendsto ...
```

を残したまま、

```lean id="v20u66"
theorem dkTendsto_dyadicPhaseTrapezoidCenteredQuadraticSum_one_third :
    DkTendstoAtTop ... := ...
```

を追加してもよいし、逆に `DkTendstoAtTop` を単なる abbrev にしてもよい。

```lean id="es0mv2"
abbrev DkTendstoAtTop (f : ℕ → ℝ) (a : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds a)
```

この程度の alias なら、今すぐ置いてもよい。
ただし、まだ DkReal 自前極限に本気で行く前なら、無理に alias を増やさず theorem 名だけで包む方が安全じゃ。

## 3. 既存 CosmicDerivative 系との整合

既存の `CosmicDerivativePowerLimit` も、極限そのものは `Filter.Tendsto` でやっている。
しかし theorem 名と対象 object は DkMath 語彙になっている。

```text id="yq5fom"
tendsto_powerKernel_zero
tendsto_powerKernel_zero_punctured
hasDerivAt_pow_cosmic
```

これと同じやり方でよい。

今回なら、

```text id="eymlqw"
tendsto_dyadicPhaseClosedQuadraticBound_one_third
tendsto_dyadicPhaseTrapezoidCenteredQuadraticSum_one_third
```

のように置く。

中身は Mathlib。
外側は DkMath。
これが一番壊れにくい。

## 4. 注意点

`centered log-depth sum` 本体については、まだ

$$
\mathrm{TrapezoidCenteredLogDepthSum}_n\to\frac{1}{3}
$$

とは言えない。

今あるのは上界だけ。

$$
\mathrm{TrapezoidCenteredLogDepthSum}_n\le\frac{1}{3}+\frac{2}{3(2^n)^2}
$$

だから、極限で言えるのはまず支配側。

```text id="ioq4iv"
quadratic bound -> 1/3
quadratic moment -> 1/3
log-depth sum はまだ上界のみ
```

なので次に置くべき極限定理は、log-depth ではなく quadratic 側じゃ。

## 5. 実装順序案

安全な順序はこれ。

```text id="9w3q3v"
1. dyadicPhaseDenom が atTop へ発散する補題
2. 1 / (dyadicPhaseDenom n : ℝ) -> 0
3. 2 / (3 * denom^2) -> 0
4. closedQuadraticBound -> 1/3
5. trapezoid centered quadratic sum -> 1/3
```

その後に、

```text id="jqtncd"
trapezoid centered log-depth sum は limsup 的に 1/3 以下
```

と言いたくなるかもしれぬ。
ただし `limsup` を使うかどうかは、まだ急がなくてよい。

## 6. DkMath 語彙ではこう説明できる

```text id="xzdk2t"
finite correction:
  2 / (3 * denom_n^2)

refinement:
  denom_n grows

gap collapse:
  finite correction vanishes

limit core:
  quadratic moment collapses to 1/3
```

つまりここでも、

$$
Gap\to0
$$

は、

$$
\frac{1}{(\mathrm{denom}_n)^2}\to0
$$

として見える。

dyadic mesh の幅を

$$
h_n=\frac{1}{2^n}
$$

と読むなら、

$$
\frac{2}{3(2^n)^2}=\frac{2}{3}h_n^2
$$

なので、

```text id="2b91dk"
finite correction is quadratic in Gap.
Gap -> 0 で二次補正が消える。
```

これは DkMath 語彙にかなり合う。

## 7. 結論

そう。
今回は素直に `Tendsto` でよい。

ただし、こうする。

```text id="s7vuhs"
Mathlib の極限を使う。
DkMath の theorem 名で包む。
将来の DkLimit / DkReal 極限へ置換できるように、外側 API を安定させる。
```

ぬしの言う通り、これは「後で置き換えるためのエイリアス設計」じゃ。

今は無理に自前極限を作らない。
既存の `CosmicDerivativePowerLimit` と同じ道を通る。
そして theorem 名だけ、DkMath の言葉で石を置いていけばよい。
