# FLT-Kummer-Bridge の Stage 2 への接続点の precise 化

## 1. 状況分析

これはかなり良い前進じゃ。
今回で Stage 1 → Stage 2 の境界が、ようやく **数学的に自然な形** へ整った。

要点は 2 つある。

ひとつめは、`CyclotomicLinearFactorIdealPthPowerTarget` を「任意の principal ideal (I)」ではなく、

$$
\exists I,\ I \text{ principal} \;\land\; \operatorname{span}(z-\zeta y)=I^p
$$

という **存在形** に直したことじゃ。これは Stage 1 の出力として正しい。Stage 1 が自然に返すのは「ある root ideal がある」であって、「どの principal ideal に対しても成り立つ」ではないからの。

ふたつめは、その存在形 boundary から

$$
\exists \beta, \exists u,\ \mathrm{IsUnit}(u)\ \land\ z-\zeta y=u\beta^p
$$

という Stage 2 の element-level 正規化形まで、`cyclotomicUnitNormalization_of_existsLinearFactorIdealPthPower` で **no-sorry** に到達できたことじゃ。つまり、Stage 2 側はもはや open ではなく、**Stage 1 が正しい境界条件を供給しさえすれば閉じる** 段まで来た。

## 2. 解説

数学的には、いまの構図はこうじゃ。

Stage 1 の仕事は、線型因子 ideal について

$$
\operatorname{span}(z-\zeta y)=I^p
$$

となる principal ideal (I) の存在を出すこと。
Stage 2 の仕事は、その (I) の generator を (\beta) として

$$
z-\zeta y=u\beta^p
$$

へ戻すこと。
今回の更新で、Stage 2 は完全にこの後者の役へ縮退した。つまり、**unit normalization そのものは解決済みで、残るのは Stage 1 出力の explicit 化だけ** と言ってよい。

これはかなり大きい。
以前は「Stage 2 がまだ abstract target の器」という色が残っておったが、いまは違う。Stage 2 の theorem-level receiver は、もはや generic core でも local core でもなく、**pack-specialized existence boundary から直接動く exact receiver** にまで降りてきた。

## 3. 次の一手の推論

閉じる方向での最短経路なら、次はもうほぼ一択じゃ。

$$
\boxed{
\text{Stage 1 側から } \texttt{CyclotomicLinearFactorIdealPthPowerTarget}
\text{ を供給する theorem を立てる}
}
$$

これじゃ。
Stage 3 に先に行くのは遠回りじゃ。理由は単純で、norm descent は

$$
z-\zeta y=u\beta^p
$$

という Stage 2 の正規化形を入力として要するからじゃ。
いまその入力を返す theorem はもうある。ならば次に要るのは、その入力の前段、すなわち

$$
\exists I,\ I \text{ principal} \land \operatorname{span}(z-\zeta y)=I^p
$$

を Stage 1 の theorem として出すことだけじゃ。そこが通れば、残る honest open はほんに Stage 3 だけになる。

## 4. 提案

わっちなら、次は次の形の theorem を 1 本立てる。

### 4.1. 目標 theorem の意味

pack と gap-divisible 条件のもとで、

$$
\exists I : \operatorname{Ideal}(R),\ I \text{ principal} \land
\operatorname{span}(z-\zeta y)=I^p
$$

を返す theorem じゃ。
名前はたとえば

$$
\texttt{cyclotomicLinearFactorIdealPthPower_of_gapDivisibleGeometry}
$$

あるいは refined route 由来ならそれを示す名でよい。

### 4.2. どこから出すか

これは、いままで積んできた Stage 1 の generic theorem 群を組み合わせれば、かなり近いはずじゃ。

流れはこうじゃ。

まず local factorization から線型因子 ideals の積が ((x)^p) になる。
次に pairwise-coprime から、各因子 ideal が p 乗 ideal になる。
さらに class-group p-torsion annihilation と principal extraction から、その root ideal が principal であることを得る。
すると欲しい

$$
\operatorname{span}(z-\zeta y)=I^p
$$

が、ある principal ideal (I) について成立する。
つまり、新しい数学を発明する段ではなく、**既存の Stage 1 pieces を explicit existence theorem に束ねる段** じゃ。

## 5. その直後にやること

その theorem が通ったら、すぐに

$$
\texttt{cyclotomicUnitNormalization_of_existsLinearFactorIdealPthPower}
$$

へ食わせればよい。
すると、

$$
\exists \beta, \exists u,\ \mathrm{IsUnit}(u)\ \land\ z-\zeta y=u\beta^p
$$

が theorem-level で確立する。
ここまで行けば、Stage 2 は完全に終わりじゃ。残る honest open は norm descent の concrete 化だけになる。

## 6. 最終判断

結論を一言で言うぞい。

$$
\boxed{
\text{次の最短手は、Stage 1 の出力を }
\exists I,\ I \text{ principal} \land \operatorname{span}(z-\zeta y)=I^p
\text{ として concrete 化すること}
}
$$

今回の更新で Stage 2 は「未解決の理論」ではなく「受け皿が完成した receiver」になった。
ゆえに、次に噛むべき本丸は **Stage 1 の存在形 boundary theorem** ただひとつじゃ。そこを通せば、残りはほんに Stage 3 の norm descent だけになるはずじゃよ。
