# Stage 1 の残る本丸は actual cyclotomic setting での coprimality 供給

うむ、Stage 1 を本気で眺めると、いまの戦況はかなり明瞭じゃ。
今回の差分で 2-factor route の exact receiver 層が入り、

* tail ideal と chosen linear factor ideal の積が \((x)^p\) になる
* その 2 つが互いに素
* \((x)\neq \bot\)

の 3 つが supply されれば、`span(z - ζy) = K^p` も、そこから Stage 2 の concrete target も no-sorry で落ちる形が固定された。つまり、Stage 1 本体が今ほんとうに supply すべきものは、この 3 点にまで絞れた、ということじゃ。

しかも、local factorization 側にはすでに

$$
\operatorname{span}(\text{tail}) \cdot \operatorname{span}(z-\zeta y) = \operatorname{span}(x)^p
$$

へつながる局所 ideal identity の核が用意されておる。差分でも `linear_factor_ideal_mul_eq_span_pow_of_add_pow_eq` が既に入っており、chosen factor と tail の 2-factor 分解へ持ち込む土台はある。ゆえに、Stage 1 の残る本丸は **product equality そのもの** より、**actual cyclotomic setting での coprimality 供給** の方に寄っていると見るのが自然じゃ。

さらに、receiver 直前で邪魔になりそうだった

* root ideal の非零
* 線型因子そのものの非零

も `rootIdealNeBotOfEqPow`、`linearFactorNeZeroOfSpanEqPow`、`linearFactorIdealPthPowerExistsOfSpanEqPowAndRootNeBot` で先回りして潰してある。よって、Stage 1 本命 theorem は「explicit equality を出したのに receiver 接続で詰まる」類の事故をかなり避けられる状態になっておる。

## 解説

いまの論理は、ほぼこう読める。

まず Stage 1 で local linear factor 1 本について

$$
\operatorname{span}(z-\zeta y)=K^{\mathrm{ctx}.p}
$$

を出す。
すると既にある composition 層で

$$
\exists I,\ I\ \text{principal} \land \operatorname{span}(z-\zeta y)=I^{\mathrm{ctx}.p}
$$

へ行ける。
さらに Stage 2 は target のレベルでも concrete 化されており、

$$
\exists \beta,\exists u,\ \mathrm{IsUnit}(u)\land z-\zeta y=u\beta^{\mathrm{ctx}.p}
$$

まで no-sorry で到達できる。つまり、Stage 2 はもう未解決ではなく、Stage 1 の explicit output を待っている receiver になったわけじゃ。

その意味で、わっちの見立てでは、Stage 1 本体の芯は次の 2 段に分かれる。

$$
\text{(A)}\quad
\operatorname{span}(\text{tail}) \cdot \operatorname{span}(z-\zeta y)=\operatorname{span}(x)^{\mathrm{ctx}.p}
$$

$$
\text{(B)}\quad
\operatorname{IsCoprime}\bigl(\operatorname{span}(\text{tail}),\operatorname{span}(z-\zeta y)\bigr)
$$

\(A\) と \(B\) から、既にある generic theorem
`linearFactorSpanEqPowOfTailMulEqSpanPowAndIsCoprime` が explicit equality を返す。差分でもその exact receiver と、そこから Stage 2 まで流す wrapper が追加されておるので、Stage 1 本体の責務はこの 2 つを actual cyclotomic 条件から供給することに尽きる。

## 次の一手の推論

閉じる方向での最短経路なら、次の優先順位はこうじゃ。

### 1. 最優先は `CyclotomicTailLinearFactorCoprimeTarget` の供給

これが本丸じゃ。
理由は、product equality 側は local factorization theorem の延長としてかなり近いが、coprimality 側だけは actual cyclotomic arithmetic の中身が必要だからじゃ。差分でも 2-factor route の exact receiver 群はそろったが、なお残る課題として真っ先に `CyclotomicTailLinearFactorCoprimeTarget` の actual theorem 化が挙げられておる。

### 2. `CyclotomicTailLinearFactorMulEqSpanPowTarget` はできれば同時に押さえる

こちらは同じ 2-factor route でも、既存の local factorization identity と自然に接続しやすい。
実務上は、coprimality を詰める過程で tail の具体式を固定するはずなので、そのとき product equality も同じ theorem 群の中で片付く公算が大きい。わざわざ別の大仕事として構える必要は薄い。

### 3. `CyclotomicXSpanNonzeroTarget` は軽い

`PrimeGe5CounterexamplePack` には \(x \neq 0\) が含まれておるので、actual ring が domain なら \((x)\neq\bot\) は比較的容易に supply できるはずじゃ。これは本丸ではなく companion lemma の部類じゃな。ユーザー貼り付けの pack 読み取りメモでも `hx0` が確認されておる。

## 具体的提案

わっちなら、次は theorem を 2 本に分ける。

ひとつは、tail を **明示的に定義した** product-equality theorem じゃ。
形としては、chosen linear factor の complementary tail を

$$
\mathrm{tail}(z,y,\zeta):=
\sum_{i=0}^{p-1} z^i(\zeta y)^{p-1-i}
$$

と置いて、

$$
\operatorname{span}(\mathrm{tail})\cdot \operatorname{span}(z-\zeta y) = \operatorname{span}(x)^{\mathrm{ctx}.p}
$$

を返すものじゃ。これは local factorization theorem の直 specialization としてかなり近い。

もうひとつは、その **同じ tail** に対する coprimality theorem じゃ。
つまり

$$
\operatorname{IsCoprime}\bigl(\operatorname{span}(\mathrm{tail}),\operatorname{span}(z-\zeta y)\bigr)
$$

を、actual cyclotomic 条件から示す。ここで鍵になるのは、おそらく

* gap-divisible 条件
* pack の互いに素性
* \(\zeta\) の root-of-unity 条件
* 差の unit 性へ落とす局所計算

のどれをどう使うかじゃ。 generic 側では「差が unit なら線型因子 ideals は互いに素」が既にあるので、actual proof の狙いは **tail と chosen factor の差あるいは合同から unit を捻り出すこと** にある、と見るのがよい。

## 最終判断

結論を一言で言うぞい。

$$
\boxed{
\text{次の最短手は、actual cyclotomic setting で }
\texttt{CyclotomicTailLinearFactorCoprimeTarget}
\text{ を supply する theorem を立てること}
}
$$

その際、tail を明示的に固定した product-equality theorem も同時に入れるのがよい。
これが通れば、2-factor route により Stage 1 explicit equality は no-sorry で落ち、そこから Stage 2 も自動で閉じる。
そうなれば、残る honest open はほんに Stage 3 の norm descent だけになるはずじゃ。
