# FLT-Kummer-Bridge Stage 1→Stage 2 の最短手の推論

## 1. 状況分析

いまの戦況は、かなり良い。
今回ので Stage 1 explicit-equality theorem の直前に必要だった **非零 companion lemma 群** が先回りで埋まった。具体的には、

$$
I = K^p \land I \neq \bot \;\Longrightarrow\; K \neq \bot
$$

に当たる `rootIdealNeBotOfEqPow` と、

$$
\operatorname{span}(z-\zeta y)=K^p \land K\neq\bot \;\Longrightarrow\; z-\zeta y\neq 0
$$

に当たる `linearFactorNeZeroOfSpanEqPow`、さらにその非零版 receiver
`linearFactorIdealPthPowerExistsOfSpanEqPowAndRootNeBot` が **no-sorry** で入った。これで receiver 手前の詰まりは、ほぼ潰れたと言ってよい。

つまり今、Stage 1 から Stage 2 へ渡すために本当に足りていないのは、

$$
\operatorname{span}(z-\zeta y)=K^p
$$

という **explicit equality そのもの** じゃ。
その equality さえ出れば、今回までに整備した exact receiver 群で

$$
\exists J,\ J \text{ principal} \land \operatorname{span}(z-\zeta y)=J^p
$$

へ行けて、さらに Stage 2 の pack-specialized receiver に流し込んで

$$
\exists \beta,\exists u,\ \mathrm{IsUnit}(u)\land z-\zeta y=u\beta^p
$$

まで no-sorry で進める。
ここまで縮んだのは、かなり大きい。残る honest open は本当に

1. Stage 1 explicit-equality theorem
2. Stage 3 norm descent

の 2 点だけじゃ。

## 2. 解説

数学の流れとして見ると、いまの位置はこうじゃ。

まず local factorization と Dedekind ideal arithmetic から、線型因子 ideal family 全体について「積が p 乗」「各因子も p 乗 ideal」という情報までは既に揃っておる。
次に class-group p-torsion annihilation により、root ideal が principal になる exact receiver も揃った。
さらに Stage 2 はもう concrete target になっており、存在形 boundary さえ与えれば

$$
z-\zeta y=u\beta^p
$$

へ戻せる。

だから今の open は、「理想論が足りない」でも「class group が曖昧」でもない。
正確には、**Stage 1 の既存 pieces を 1 本の theorem として束ね、local linear factor 1 本に対する explicit equality を返す作業だけが残っている** のじゃ。

今回の追加で、その theorem の証明中に邪魔をしそうだった

* root ideal 非零
* 線型因子そのものの非零

も先に theorem 化された。
これは地味に見えて、証明を短く clean にする。実際、次の本命 theorem は「何を supply すべきか」がかなりはっきりした形で書けるはずじゃ。

## 3. 次の一手の推論

閉じる方向での最短経路なら、次は変わらずこれじゃ。

$$
\boxed{
\text{Stage 1 pieces を束ねて }
\operatorname{span}(z-\zeta y)=K^p
\text{ を返す theorem を立てる}
}
$$

Stage 3 に先に行くのは遠回りじゃ。
norm descent は

$$
z-\zeta y=u\beta^p
$$

を入力に要する。
そしてその入力へ行く exact receiver 群は、もう揃っておる。ならば次に刺すべきは、その手前の explicit equality theorem ただ 1 本じゃ。そこが通れば、残る honest open はほんに Stage 3 だけになる。

## 4. 提案

わっちなら、次は theorem を 2 段で書く。

まず本命として、local linear factor について

$$
\operatorname{span}(z-\zeta y)=K^p
$$

を返す theorem を立てる。
ここでは principal まで言わなくてよい。今回の receiver 群が、その先をやってくれるからじゃ。
つまり Stage 1 theorem の責務は、ほんに **explicit equality を返すことだけ** に絞るのが最短じゃ。

その直後に、その theorem を

* `rootIdealNeBotOfEqPow`
* `linearFactorNeZeroOfSpanEqPow`
* `linearFactorIdealPthPowerExistsOfSpanEqPowAndRootNeBot`
* `cyclotomicUnitNormalization_of_existsLinearFactorIdealPthPower`

へそのまま流し込む。
すると theorem-level に

$$
\exists \beta,\exists u,\ \mathrm{IsUnit}(u)\land z-\zeta y=u\beta^p
$$

が完成する。
ここで Stage 2 は完全終了じゃ。

## 5. 実装上の最短形

実装としては、次の形がよい。

まず theorem 名としては、たとえば

$$
\texttt{linearFactorSpanEqPow\_of\_gapDivisibleGeometry}
$$

のように、local linear factor 1 本に対する explicit equality を返す名にする。
結論は

$$
\exists K : \operatorname{Ideal}(R),\ \operatorname{span}(z-\zeta y)=K^p
$$

で十分じゃ。
非零や principal は、後段 receiver が回収する。ここを欲張らぬのがよい。

そのあと composition theorem として、

$$
\texttt{cyclotomicUnitNormalization\_of\_linearFactorSpanEqPow}
$$

のような形で Stage 2 target を返す theorem を立てる。
だがこれは新しい数学ではなく、既存 theorem の合成で済むはずじゃ。だからまずは explicit equality 本体を先に立てるべきじゃよ。

## 6. 最終判断

結論を一言で言うぞい。

$$
\boxed{
\text{次の最短手は、Stage 1 の本命 theorem として }
\operatorname{span}(z-\zeta y)=K^p
\text{ を返す explicit-equality theorem を立てること}
}
$$

今回の nonzero companion lemma 群で、receiver 直前の詰まりはほぼ消えた。
ゆえに、いま本当に残っている Stage 1 の仕事はその equality を supply することだけじゃ。
そこが通れば、残る honest open は Stage 3 の norm descent ただ 1 つになるはずじゃよ。
