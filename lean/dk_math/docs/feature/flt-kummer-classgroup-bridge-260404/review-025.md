# FLT-Kummer-Bridge Stage 1 がまだ閉じぬ理由

## 1. 結論

まだ Stage 1 が閉じぬ理由は、もうかなり限定されておる。
**理由は「積の等式」が足りぬからではなく、chosen linear factor ideal と complementary tail ideal の** actual cyclotomic な互いに素性 **が、まだ theorem として供給されておらぬからじゃ。**

今回ので actual supply 側はかなり進み、

* `ctx.p = p` を仮定すれば tail-product equality は出せる
* 同じく `ctx.p ≠ 0` も出せる
* `(x)` 非零は generic ではなく `CharZero` 付きなら honest に出せる

ところまで concrete 化できた。
だが **`CyclotomicTailLinearFactorCoprimeTarget` の actual theorem** は、まだ無い。差分の報告でも、残る本丸はそこだとはっきり整理されておる。

## 2. 何がもう閉じていて、何が閉じていないか

いま no-sorry で閉じておるのは、2-factor route の receiver 層じゃ。

* tail ideal と chosen factor ideal の積が \((x)^p\)
* 両者が互いに素
* `(x)` が nonzero ideal

この 3 つが supply されれば、

$$
\operatorname{span}(z-\zeta y)=K^p
$$

という explicit equality が出て、さらに Stage 2 の

$$
\exists \beta,\exists u,\ \mathrm{IsUnit}(u)\land z-\zeta y=u\beta^p
$$

まで no-sorry で流れる形は、もう theorem-level に固定された。つまり Stage 1 の「出口」は出来ておる。

それでも Stage 1 が閉じぬのは、その出口に入れる **actual input** のうち、product equality 側と exponent nonzero 側は進んだが、**coprimality 側だけがまだ本体のまま残っている** からじゃ。

## 3. なぜ coprimality が難しいのか

ここが本質じゃ。

局所因数分解そのものは

$$
\text{tail}\cdot(z-\zeta y)=x^p
$$

という **乗法恒等式** を与える。
これは「掛けると \(p\) 乗になる」を言うだけで、**共通因子が無い** ことまでは言わぬ。

Stage 1 を閉じるには、

$$
\operatorname{IsCoprime}\bigl((\text{tail}),\ (z-\zeta y)\bigr)
$$

を、actual cyclotomic 条件から示さねばならぬ。
ここでは generic ideal arithmetic ではなく、**cyclotomic 特有の局所計算** が要る。差分の整理でも、次の最短手はここに尽きると明言されておる。

## 4. もう少し数学的に言うと

なぜそこが hard かと言えば、共通素因子 \(P\) を仮定したとき、

* \(P\) が \(z-\zeta y\) を割る
* かつ \(P\) が tail も割る

から、**\(z^p-y^p\) における repeated-root 的な状況** を引き出して矛盾へ持ち込む必要があるからじゃ。

自然な見取り図はこうじゃ。

$$
z-\zeta y \equiv 0 \pmod P
$$

なら \(z \equiv \zeta y \pmod P\) じゃ。
さらに tail も \(P\) で割れるなら、商

$$
\frac{z^p-y^p}{z-\zeta y}
$$

も \(P\) で割れる。
これは「その root が単純根でない」ことを示唆する。すると普通は

* \(P\) が \(p\) を割る
* あるいは \(\zeta\) の差や derivative 的量を割る

のどちらかへ落ちる。
つまり、最後に必要なのは generic machinery ではなく、**common divisor を “(p) 側へ押し込む” または “unit 差へ押し込む” 局所計算** なのじゃ。

ここがまだ theorem 化されておらぬから、Stage 1 は閉じきらぬ。

## 5. もう一つの理由

副次的だが大事なのが、**context の情報量が最小すぎる** ことじゃ。

`CyclotomicLocalFactorizationContext` は、基本的に

$$
\zeta^{\mathrm{ctx}.p}=1
$$

しか持たぬ。
これで product equality は作れる。
だが coprimality を出すには、しばしば

* \(\mathrm{ctx}.p = p\)
* \(\zeta \neq 1\)
* 異なる root 同士の差の unit 性
* あるいは primitive root 的条件

が要る。
今回、\(\mathrm{ctx}.p = p\) については target と theorem が追加され、product equality 供給には足りるようになった。だが coprimality に必要な **“\(\zeta\) の arithmetic 側の強い情報”** は、まだ context や theorem に露出しておらぬ。

## 6. さらに小さな理由

`hx0 : x \neq 0` から generic domain 上で \((x)\neq\bot\) は出ない、という caveat も露出した。
そこで `(x)` 非零は `CharZero` 付きの honest variant に切り分けられた。これは正しい整理じゃが、逆に言うと **Stage 1 は generic に押し切れない** ことも確定した。
つまり Stage 1 が閉じぬのは、「generic target を全部 actual にできる」という期待がもう破れておるからでもある。
actual cyclotomic ring の条件を正面から使う必要があるわけじゃ。

## 7. 次の一手

最短手は、やはりこれじゃ。

$$
\boxed{
\text{actual cyclotomic setting で }
\texttt{CyclotomicTailLinearFactorCoprimeTarget}
\text{ を supply する theorem を立てる}
}
$$

しかも、その証明方針はかなり絞れておる。

* tail を明示する
* common prime ideal \(P\) が tail と \(z-\zeta y\) の両方を割ると仮定する
* そこから repeated-root / derivative 型の議論で
  $$
  P \mid p
  $$
  あるいは
  $$
  P \mid (\zeta_i-\zeta_j)
  $$
  型へ落とす
* それを first-case 的条件、gap-divisible 条件、unit 差の補題で潰す

この route がいちばん筋がよい。
差分の進展から見ても、product equality 側と exponent nonzero 側は既に concrete 化できておるので、**残る本丸は coprimality の一点** じゃ。

## 8. 提案

わっちなら、次は theorem を 2 本で切る。

ひとつめは、tail を明示した local lemma じゃ。
内容は「共通 prime ideal が tail と chosen factor の両方を割るなら、その prime ideal は \(p\) を割るか、\(\zeta\) の差を割る」といった形にする。

ふたつめは、その局所 lemma から `CyclotomicTailLinearFactorCoprimeTarget` を返す actual theorem じゃ。
これが通れば、今ある

* `cyclotomicLinearFactorSpanEqPow_of_tailFactorCoprime`
* `cyclotomicUnitNormalization_of_tailFactorCoprimeRoute`

へ即座に流せる。Stage 1 はほぼ閉じ、残る honest open は Stage 3 の norm descent だけになる。

## 9. まとめ

Stage 1 がまだ閉じぬ理由は、ひとことで言えばこれじゃ。

$$
\boxed{
\text{積の等式は出たが、tail と chosen factor の “actual cyclotomic coprimality” がまだ出ていないから}
}
$$

generic machinery は揃っておる。
receiver も揃っておる。
nonzero companion も揃っておる。
だから残るのは、ほんに **cyclotomic arithmetic の局所計算 1 箇所** なのじゃよ。
