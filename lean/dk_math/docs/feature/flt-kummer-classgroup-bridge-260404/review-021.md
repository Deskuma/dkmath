## 1. 状況分析

いまの戦況は、かなり良い。
今回の追加で、Stage 1 と Stage 2 のあいだに必要だった **exact receiver** 群がさらに concrete になった。特に

$$
I = K^p \;\Longrightarrow\; \exists J,\ J \text{ principal} \land I = J^p
$$

を返す `principalRootIdealExistsOfEqPowAndTorsionKill` と、その線型因子版 `linearFactorIdealPthPowerExistsOfSpanEqPowAndTorsionKill` が no-sorry で入ったことで、Stage 1 が **explicit equality** さえ supply できれば、存在形 boundary まではもう generic に回収できるようになった。つまり、残る open は「class-group 側」でも「Stage 2 の核」でもなく、**Stage 1 の explicit equality をどう出すか** と **Stage 3 の norm descent** の 2 点へ縮んだ、と見てよい。

言い換えると、いまは

$$
\operatorname{span}(z-\zeta y)=K^p
$$

が出れば、

$$
\exists J,\ J \text{ principal} \land \operatorname{span}(z-\zeta y)=J^p
$$

を取り直せて、さらに

$$
z-\zeta y=u\beta^p
$$

へも no-sorry で進める段じゃ。
ここまで来ると、Stage 2 は実質もう終わっておる。残る仕事は、Stage 1 の出力をその exact 形にすることだけじゃ。

## 2. 解説

数学の流れとしては、いまこうなっておる。

まず local factorization から線型因子 ideals の積が \((x)^p\) になる。
次に pairwise-coprime ideal arithmetic から、各線型因子 ideal が \(K^p\) と書ける。
そのあと class-group p-torsion annihilation で root ideal \(K\) が principal だと分かる。
最後に unit normalization で

$$
z-\zeta y=u\beta^p
$$

まで戻す。

今回の追加は、このうち

$$
K^p \Rightarrow J^p \text{ with } J \text{ principal}
$$

の回収を theorem として独立させたことじゃ。
ゆえに、Stage 1 側が supply すべきものは、もう本当に

$$
\operatorname{span}(z-\zeta y)=K^p
$$

という **explicit equality** にまで細くなった。
この sharpen はかなり大きい。証明の焦点が、もう曖昧ではないからの。

## 3. 次の一手の推論

閉じる方向での最短経路なら、次はほぼ一択じゃ。

$$
\boxed{
\text{Stage 1 pieces を束ねて }
\operatorname{span}(z-\zeta y)=K^p
\text{ を返す theorem を立てる}
}
$$

これじゃ。
Stage 3 に先に行くのは遠回りじゃよ。norm descent は

$$
z-\zeta y=u\beta^p
$$

という element-level 正規化形を入力に要する。
そしてその正規化形へ進む exact receiver 群は、もう揃っておる。ならば次にやるべきは、その手前の explicit equality を Stage 1 から出すことだけじゃ。そこが通れば、残る honest open はほんに norm 側だけになる。

## 4. 具体的提案

わっちなら、次は theorem を 2 段で切る。

* まず、Stage 1 の generic pieces をまとめて、ある線型因子 ideal について
  $$
  \exists K,\ \operatorname{span}(z-\zeta y)=K^p
  $$
  を返す theorem を立てる。
* ついで、それを今回の `linearFactorIdealPthPowerExistsOfSpanEqPowAndTorsionKill` と
  `cyclotomicUnitNormalization_of_existsLinearFactorIdealPthPower` に流し込んで、
  $$
  \exists \beta, \exists u,\ \mathrm{IsUnit}(u)\land z-\zeta y=u\beta^p
  $$
  を theorem-level で完成させる。

ここで大事なのは、最初の theorem では **principal まで言わなくてよい** ことじゃ。
principal 性の回収は、今回追加した exact receiver がやってくれる。
だから Stage 1 theorem の仕事は、ほんに

$$
\operatorname{span}(z-\zeta y)=K^p
$$

を返すところまででよい。そこを欲張らぬ方が最短じゃ。

## 5. ひとつだけ注意点

細いが大事な点として、receiver 側では

* \(p \neq 0\)
* \(z-\zeta y \neq 0\)

も使っておる。
\(p \neq 0\) は PrimeGe5 pack からすぐ出る。
\(z-\zeta y \neq 0\) も、後で困らぬように Stage 1 theorem の近くで companion lemma として切っておくとよい。
これを後回しにすると、explicit equality は出たのに receiver へ渡す直前で止まる、という妙な詰まり方をするからの。

## 6. 最終判断

結論を一言で言うぞい。

$$
\boxed{
\text{次の最短手は、Stage 1 から }
\operatorname{span}(z-\zeta y)=K^p
\text{ を返す theorem を立てること}
}
$$

これが通れば、Stage 2 は theorem-level にも実質完了する。
その時点で残る honest open は、ほんに **Stage 3 の norm descent** だけじゃ。
いま噛むべき本丸は、もうそこへ至る最後の Stage 1 explicit-equality theorem じゃよ。
