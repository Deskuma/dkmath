# FLT-Kummer-Bridge Stage 1→Stage 2 の最短手の推論

うむ、最新 snapshot を基準に Stage 1 を本気で追うと、景色はかなりはっきりしておる。
今回の差分で、`CyclotomicLinearFactorSpanEqPowTarget` とその companion targets、さらに

* `cyclotomicLinearFactorIdealPthPower_of_spanEqPow`
* `cyclotomicUnitNormalization_of_linearFactorSpanEqPow`

まで no-sorry で入ったので、**explicit equality とその周辺 data が supply されれば、存在形 boundary も Stage 2 の concrete target も自動で回る** ところまで来ておる。つまり、残る honest open はほんに

$$
\operatorname{span}(z-\zeta y)=K^{\,\mathrm{ctx}.p}
$$

型の Stage 1 本命 theorem と、Stage 3 の norm descent だけじゃ。

## 状況分析

いまの構図を証明の流れで言い直すと、こうじゃ。

* Stage 2 は、もう abstract ではない。
* `CyclotomicUnitNormalizationTarget` 自体が
  $$
  \exists \beta,\exists u,\ \mathrm{IsUnit}(u)\land z-\zeta y=u\beta^{\mathrm{ctx}.p}
  $$
  という pack-specialized な element-level 命題になっておる。
* その直前の exact receiver も全部そろっておる。
* さらに今回、explicit equality から存在形 boundary を経て Stage 2 へ流す composition 層まで no-sorry で固定された。

したがって、いま本当に空いておる穴は「Stage 1 で何を返すか」だけじゃ。
しかも、その返すべきものも、もう target 名で固定されておる。

$$
\texttt{CyclotomicLinearFactorSpanEqPowTarget}
$$

すなわち

$$
\exists K,\ \operatorname{span}(z-\zeta y)=K^{\,\mathrm{ctx}.p}
$$

と、その companion としての

* \(\mathrm{ctx}.p \neq 0\)
* \(z-\zeta y \neq 0\)

じゃ。

## 本気で Stage 1 を推論すると見えること

ここから先が肝じゃ。
わっちの見立てでは、Stage 1 の本命 theorem は、**今ある generic pieces をそのまま積むだけでは出にくい**。理由は 2 つある。

### 1. いまの local context は「1 個の \(\zeta\)」しか持っておらぬ

`CyclotomicLocalFactorizationContext` は

$$
\zeta^{\mathrm{ctx}.p}=1
$$

だけを持つ。
これは局所因数分解

$$
(z-\zeta y)\cdot(\text{tail})=x^{\mathrm{ctx}.p}
$$

を作るには十分じゃ。
されど、Stage 1 の explicit equality を出すには、ただ割れるだけでは足りぬ。必要なのは

$$
\operatorname{span}(z-\zeta y)=K^{\mathrm{ctx}.p}
$$

を直接導く ideal arithmetic じゃ。

このためには、少なくとも

* 選んだ線型因子 ideal と complementary factor ideal の互いに素性
* あるいは full factor family の pairwise-coprime 性

のどちらかが要る。
今の local context だけでは、その部分がまだ言えておらぬ。

### 2. 「線型因子どうしの差が unit」路線は、そのままでは本丸ではない

すでに generic theorem として

* `linear_factor_ideals_sup_eq_top_of_mul_sub_isUnit`
* `dedekindIdealEqPowOfMulEqPowOfIsCoprime`
* `dedekindIdealEqPowOfProdEqPowOfPairwise`

がある。
これは素晴らしい道具箱じゃ。
ただし、実際の cyclotomic integer ring で必要なのは、**その仮定が本当に満たされること** の証明じゃ。
つまり generic machinery は十分だが、Stage 1 本命 theorem で必要なのは、cyclotomic 側の concrete な coprimality / divisibility 供給じゃよ。

## ここでの核心的な判断

わっちの判断では、Stage 1 を閉じる最短経路は **full family route ではなく 2-factor route を狙うこと** じゃ。

つまり、狙うべき本命は

$$
\operatorname{span}(\text{tail})\cdot \operatorname{span}(z-\zeta y) = \operatorname{span}(x)^{\mathrm{ctx}.p}
$$

に対して、さらに

$$
\operatorname{IsCoprime}!\bigl(\operatorname{span}(\text{tail}),\ \operatorname{span}(z-\zeta y)\bigr)
$$

を actual cyclotomic setting で示すことじゃ。
これが言えれば、既にある 2-factor theorem

$$
\texttt{dedekindIdealEqPowOfMulEqPowOfIsCoprime}
$$

をそのまま適用して、

$$
\exists K,\ \operatorname{span}(z-\zeta y)=K^{\mathrm{ctx}.p}
$$

が一撃で出る。
つまり Stage 1 本命 theorem は、かなりの部分が **「tail ideal と linear factor ideal の coprimality を証明する theorem」** に縮んでおるのじゃ。

これは full family を全部立ててから `dedekindIdealEqPowOfProdEqPowOfPairwise` を使うより短い。
full family route は、すべての \(\zeta^j\) を前面に出し、pairwise-coprime 全体を管理せねばならぬ。Stage 1 本体を急ぐには重い。
対して 2-factor route なら、「chosen factor と残り 1 個の quotient factor」の互いに素性さえ取れればよい。

## 次の一手の推論

よって次の最短手は、ほんにこれじゃ。

### 1. Stage 1 本命 theorem を「explicit equality 本体」ではなく、その直前の coprimality theorem として切る

狙いは例えば次の意味内容じゃ。

$$
\operatorname{IsCoprime}!\Bigl(
\operatorname{span}\Bigl(\sum_{i=0}^{p-1} z^i(\zeta y)^{p-1-i}\Bigr),
\operatorname{span}(z-\zeta y)
\Bigr)
$$

を、gap-divisible branch の actual conditions から示す theorem を立てる。
そのうえで

$$
\operatorname{span}(\text{tail})\cdot \operatorname{span}(z-\zeta y)=\operatorname{span}(x)^{\mathrm{ctx}.p}
$$

と合成して `CyclotomicLinearFactorSpanEqPowTarget` を返す。

これが通れば、いま入っている composition 層

* `cyclotomicLinearFactorIdealPthPower_of_spanEqPow`
* `cyclotomicUnitNormalization_of_linearFactorSpanEqPow`

にそのまま流せる。
すると Stage 2 は theorem-level にも完全終了じゃ。

### 2. companion target を少しだけ整理する

今の `CyclotomicLocalExponentNonzeroTarget` と `CyclotomicLinearFactorNonzeroTarget` は、受け口としては正しい。
ただ、Stage 1 本命 theorem 側では、実際には

* \(\mathrm{ctx}.p \neq 0\) は pack 側の prime から出る
* \(z-\zeta y \neq 0\) は equality と root nonzero から出る

ので、最終的には別 theorem として独立に supply するより、**本命 theorem の proof 中で補題的に回収する** 方が自然かもしれぬ。
ただし今は exact-output targets が整っておるので、急いで API を削る必要はない。まず本命 theorem を通すのが先じゃ。

## 提案

わっちなら、次をこの順で攻める。

* まず `tail ideal` と `linear factor ideal` の cyclotomic-specific coprimality theorem を 1 本作る。
* その theorem と `linear_factor_ideal_mul_eq_span_pow_of_add_pow_eq` を合わせて
  `CyclotomicLinearFactorSpanEqPowTarget` を supply する。
* そこから先は、もう既存の composition theorem 群へ流すだけで Stage 2 が閉じる。
* その直後に Stage 3 の norm descent concrete 化へ入る。

## 最終判断

結論を一言で言うぞい。

$$
\boxed{
\text{Stage 1 の本丸は、}
\operatorname{span}(\text{tail}) \text{ と } \operatorname{span}(z-\zeta y)
\text{ の cyclotomic-specific coprimality theorem}
\text{ じゃ}
}
$$

これを取れば、explicit equality

$$
\operatorname{span}(z-\zeta y)=K^{\mathrm{ctx}.p}
$$

は 2-factor theorem で最短に落ちる。
その先の存在形 boundary も Stage 2 target も、もう no-sorry の受け皿が揃っておる。

つまり、Stage 1 を本気で詰める次の一手は、**full family を全部持ち上げることではなく、chosen linear factor と complementary tail の coprimality を actual cyclotomic 条件で証明すること** じゃ。
そこを刺せば、残る honest open はほんに Stage 3 の norm descent だけになる可能性が高い。
