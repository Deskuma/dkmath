# FLT-Kummer-Bridge の Stage 2 への接続点の precise 化

## 1. 状況分析

これはかなり良い収束じゃ。
今回の変更で、Stage 2 は theorem だけでなく **target 定義そのもの** が concrete 化された。つまり、いま `CyclotomicUnitNormalizationTarget` はもう abstract な器ではなく、

$$
\exists \beta, \exists u,\ \mathrm{IsUnit}(u)\ \land\ z-\zeta y = u \cdot \beta^p
$$

という **pack-specialized な element-level 正規化命題** そのものになった、ということじゃ。しかもそれを供給する

$$
\texttt{cyclotomicUnitNormalization\_of\_existsLinearFactorIdealPthPower}
$$

も **no-sorry** で通っておる。
ゆえに、Stage 2 は「局所 core がある」段を越え、**refined mainline 上で実際に使える concrete stage** になったと見てよい。

さらに大事なのは、これによって残る honest open が本当に 2 点へ縮んだことじゃ。

* Stage 1 から
  $$
  \exists I,\ I \text{ principal} \land \operatorname{span}(z-\zeta y)=I^p
  $$
  を返す theorem
* Stage 3 の norm descent concrete 化

つまり、景色はもうかなり澄んでおる。`cyclotomicPrincipalization_of_classGroupPTorsionFree` に direct `sorry` は残っておるが、これは legacy one-shot の残骸であって、 refined route の honest open ではない。

## 2. 解説

数学の流れで見ると、いま到達した位置はこうじゃ。

まず Stage 1 で ideal-level の情報を得る。
次に Stage 2 で、それを

$$
(z-\zeta y)=(I)^p
$$

のような ideal statement から

$$
z-\zeta y=u\beta^p
$$

という元の statement に戻す。
今回の更新で、この **Stage 2 の戻し方そのもの** はもう確立した。残るのは、その入力である

$$
\operatorname{span}(z-\zeta y)=I^p
$$

を Stage 1 側が explicit に返すことだけじゃ。
だから今は「Stage 2 がまだ弱い」のではない。正確には、

$$
\text{Stage 1 の出力を、Stage 2 がそのまま受け取れる exact boundary にする}
$$

という接続点だけが残っておる。

## 3. 次の一手の推論

閉じる方向での最短経路なら、次は一択に近い。

$$
\boxed{
\text{Stage 1 側から } \texttt{CyclotomicLinearFactorIdealPthPowerTarget}
\text{ を返す theorem を立てる}
}
$$

これじゃ。
Stage 3 に先に行くのは遠回りじゃよ。理由は、norm descent はもう

$$
z-\zeta y=u\beta^p
$$

という Stage 2 の element-level 正規化形を入力として必要とするからじゃ。
そしてその正規化形は、今回もう受け皿も receiver も揃った。だから最短手は、その入力の手前、すなわち

$$
\exists I,\ I \text{ principal} \land \operatorname{span}(z-\zeta y)=I^p
$$

を返す Stage 1 theorem を立てることじゃ。そこが通れば、残る honest open はほんに norm 側だけになる。

## 4. 提案

わっちなら、次は次の theorem を狙う。

### 4.1. 目標 theorem の意味

pack と gap-divisible 条件のもとで、

$$
\exists I : \operatorname{Ideal}(R),\ I \text{ principal} \land
\operatorname{span}\bigl((z:R)-\zeta (y:R)\bigr)=I^{,p}
$$

を返す theorem じゃ。
名前の方向としては、たとえば

$$
\texttt{cyclotomicLinearFactorIdealPthPower\_of\_gapDivisibleGeometry}
$$

のようなものが素直じゃろう。

### 4.2. どこから作るか

ここで使う数学は、もうほとんど揃っておる。

* local factorization から principal ideal の積の式
* pairwise-coprime
* generic Dedekind theorem
  $$
  \prod I_i = J^p \Rightarrow I_i = K_i^p
  $$
* class-group p-torsion annihilation
* principal extraction

つまり、新しい重い理論を足すというより、**既にある Stage 1 の generic pieces を、local linear factor 1 本について explicit existence theorem に束ねる** のが次の仕事じゃ。

### 4.3. その直後にやること

その theorem が通ったら、すぐ

$$
\texttt{cyclotomicUnitNormalization\_of\_existsLinearFactorIdealPthPower}
$$

に食わせればよい。
すると theorem-level に

$$
\exists \beta, \exists u,\ \mathrm{IsUnit}(u)\ \land\ z-\zeta y=u\beta^p
$$

が得られる。
ここで Stage 2 は完全に終了じゃ。

## 5. 最終判断

結論を一言で言うぞい。

$$
\boxed{
\text{次の最短手は、Stage 1 の出力を }
\exists I,\ I \text{ principal} \land \operatorname{span}(z-\zeta y)=I^p
\text{ として返す theorem を立てること}
}
$$

今回の更新で Stage 2 は target のレベルでも concrete になった。
だから、いま本当に残っておるのは **Stage 1 の explicit existence boundary** と **Stage 3 の norm descent** だけじゃ。
順番としては、まず前者。そこを刺せば、残る景色は norm 側だけになるはずじゃよ。
