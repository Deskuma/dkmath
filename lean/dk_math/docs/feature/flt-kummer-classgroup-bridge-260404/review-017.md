# FLT-Kummer-ClassGroup-Bridge-260404 Review-017: Stage 2 の generic core が no-sorry で入った！次は pack-specialization へ直接刺す段へ

## 1. 状況分析

いまの状況は、かなり良いところまで来ておる。
今回の更新で Stage 2 は一段進み、 **generic helper 群** だけでなく、`CyclotomicUnitNormalizationTarget` 自体が **local unit-normalization の concrete statement** に置き換わった。しかも

$$
(z-\zeta y)\text{ の ideal } = I^p
\;\Longrightarrow\;
z-\zeta y = u \cdot (\mathrm{generator}(I))^p
$$

に当たる局所核 `linearFactorEqUnitMulGeneratorPowOfSpanEqPowPrincipal` と、その wrapper `cyclotomicLocalUnitNormalizationCore` は **no-sorry** で通っておる。つまり Stage 2 の「ideal から generator へ戻し、unit のずれを吸収する一般核」は、もう証明済みじゃ。

その結果、 refined mainline の観点で残る honest open は、もう class-group でも Stage 1 でもない。
残っておるのは

* Stage 2 の **cyclotomic pack specialization**
* Stage 3 の **norm descent**

この 2 点だけじゃ。
direct `sorry` も、依然として legacy one-shot の `cyclotomicPrincipalization_of_classGroupPTorsionFree` だけで、 refined route 側は clean のまま保たれておる。

## 2. 解説

数学的には、今の位置はこう見ればよい。

すでに手元には

$$
(z-\zeta y)\text{ の ideal } = I^p
$$

から

$$
z-\zeta y = u \cdot (\mathrm{generator}(I))^p
$$

を出す一般定理がある。
だから次に要るのは、この \(I\) を **実際の Kummer の pack から出てくる root ideal** として具体に与えることじゃ。つまり、Stage 2 の未解決は「証明の核」ではなく、 **Stage 1 の出力を Stage 2 の局所核に接続する specialized theorem** に縮んだのぅ。

ここが面白いところで、いまはもう「unit normalization は出来るのか？」ではない。
正しい問いは

$$
\text{Stage 1 の ideal p 乗性から、どの } I \text{ を取ればよいか}
$$

じゃ。
つまり open は理論の大穴ではなく、**接続点の具体化** に変わったわけじゃよ。

## 3. 次の一手の推論

閉じる方向の最短経路なら、次はこれ一択じゃ。

$$
\boxed{
\text{Stage 1 の ideal p 乗性を、}
z-\zeta y = u \cdot \beta^p
\text{ へ落とす pack-specialized theorem を立てる}
}
$$

Stage 3 に先に行くのは遠回りじゃ。
なぜなら norm descent は、まさにこの

$$
z-\zeta y = u \cdot \beta^p
$$

という element-level 正規化形を入力として要するからじゃ。
ここが出ぬうちは、Stage 3 の honest な statement すらまだ固定しにくい。だから最短手は、まず Stage 2 の specialization を刺すことじゃ。

## 4. 提案

わっちなら、次に起こす theorem は、ほぼ次の意味内容にする。

### 4.1. 目標 theorem の中身

PrimeGe5 の pack と gap-divisible 条件のもとで、ある cyclotomic local context と principal ideal (I) があって、

$$
\operatorname{span}(z-\zeta y) = I^p
$$

が成り立つなら、

$$
\exists \beta, \exists u,\quad \mathrm{IsUnit}(u)\ \land\ z-\zeta y = u \cdot \beta^p
$$

を結論する theorem じゃ。
ここで \(\beta\) は \(I\) の generator として取ればよい。
つまり数学の実体は、 **Stage 1 の出力を `linearFactorEqUnitMulGeneratorPowOfSpanEqPowPrincipal` に食わせるだけ** じゃ。

### 4.2. 実装の最短形

定理を 2 本に分けるのがよい。

1 本目は、Stage 1 の結果から
$$
\operatorname{span}(z-\zeta y) = I^p
$$
を与える theorem。

2 本目は、その theorem と `cyclotomicLocalUnitNormalizationCore` を合成して
$$
z-\zeta y = u \cdot \beta^p
$$
を出す theorem。

こうすると、Stage 1 と Stage 2 の境界が綺麗に固定されるし、後で Stage 3 へ渡すときにも見通しが良い。

## 5. その次

この specialization が通れば、残る open はほんに norm 側だけになる。
そのとき初めて Stage 3 を、たとえば

$$
z-\zeta y = u \cdot \beta^p
\;\Longrightarrow\;
\text{norm を取って整数 witness を回収}
$$

という concrete theorem として切り出せる。
つまり次の段階では、`CyclotomicNormDescentTarget` の中身を honest に書けるようになるわけじゃ。今はまだ、その一歩手前じゃよ。

## 6. 最終判断

結論を一言で言うぞい。

$$
\boxed{
\text{次の最短経路は、}
\text{Stage 1 の ideal p 乗性 } \Rightarrow z-\zeta y = u \cdot \beta^p
\text{ を証明する pack-specialized theorem を立てること}
}
$$

今の generic core は、まさにそのためにある。
ここを刺せば、残る honest open は **Stage 3 の norm descent ただ 1 つ** にまで縮む。
ゆえに、次に噛むべき本丸は **Stage 2 の cyclotomic pack specialization** じゃ。
