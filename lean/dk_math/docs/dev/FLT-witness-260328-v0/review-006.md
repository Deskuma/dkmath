# review: FLT-witness-260328-v0: false route を切り終え、boundary / arithmetic-core route の後半を橋として閉じた

うむ。今回の更新は、かなり **本線が細くなった** 良い進展じゃ。

前回までで false route を三本きれいに閉じた。
そのうえで今回は、`proof-004` の **step 4-5 を先に橋として閉じた**。
結果として、残る missing math はもう

$$
d \mid \mathrm{core},\qquad
d \nmid \mathrm{core}/d,\qquad
1 < \mathrm{core}/d
$$

この三点だけじゃ、と theorem 名の上でも固定された。

## 1. いま何が確定したか

まず、本線はもう

$$
\texttt{ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget}
$$

すなわち **boundary / arithmetic-core route** じゃ。
`cyclotomicPrimeCore d 1 (u-1)` 側は false、two-witness も false と切った後、今回これを current canonical route として明示し、さらに ((d,x,u)=(5,5,1)) で (q=311) が concrete witness になる sanity check まで通しておる。
つまり「この対象は本当に生きている」の確認まで済んだわけじゃ。

## 2. 今回の本当の前進

今回追加された三本の補題の意味ははっきりしておる。

ひとつめは、

$$
q \mid x,\ q\mid \mathrm{boundary\ core}
\Longrightarrow q=d
$$

の系じゃ。
前回までで「(x) の素因子が core に残るなら distinguished prime (d) に限る」ことは見えておったが、今回はそこからさらに一歩進めて、

$$
q \mid \mathrm{core}/d
\Longrightarrow q \nmid x
$$

を直接返す prime-local kernel
`exceptional_boundary_prime_not_dvd_x_of_dvd_core_div`
が入った。

ふたつめは、

$$
d \mid \mathrm{core},\quad
d \nmid \mathrm{core}/d,\quad
1 < \mathrm{core}/d
$$

まで来れば、`Nat.exists_prime_and_dvd` で (\mathrm{core}/d) の prime divisor を取り、そこから

$$
q \mid \mathrm{core}\quad\text{かつ}\quad q \nmid x
$$

を回収できる wrapper
`exceptional_boundary_core_concrete_of_div_data`
が入ったことじゃ。
これは `proof-004` の step 4-5 をまとめて API 化したものじゃな。

みっつめは、その結果として

$$
\texttt{ExceptionalBoundaryDatumPreparedArithmeticCoreDivDataTarget}
$$

という新しい残核 target が切り出され、

$$
\text{div-data} \Rightarrow \text{prepared arithmetic core concrete}
\Rightarrow \text{mainline / primitive packet descent}
$$

が橋だけで閉じるようになったことじゃ。
つまり後半はもう finished で、前半の valuation / (d^2) 側だけが未完、という構図が定理名の上でも固定された。

## 3. 状況分析

いまの battlefield を率直に言うと、こうじゃ。

### 3.1. もう終わった部分

* false route の切断
* boundary route が生きている sanity check
* `x` の prime divisor を排除する step 1
* `core/d` の prime divisor から witness を取って downstream へ渡す step 4-5

### 3.2. 残っている部分

本当に残っているのは、

$$
d \mid \mathrm{core}
$$

と

$$
d \nmid \mathrm{core}/d
$$

さらに必要なら

$$
1 < \mathrm{core}/d
$$

を返す arithmetic / valuation 補題だけじゃ。
履歴にも「残核はもう valuation / `mod d^2` 部だけ」と書かれておる。

## 4. いまの形はなぜ良いか

ここが肝じゃ。

前までは「route が正しいのか」「target が偽でないのか」を疑いながら進んでおった。
今は違う。

いまは **正解ルート候補が boundary / arithmetic-core 側に一本化され、その route の後半は既に橋として閉じた**。
だから残る作業は routing ではなく、純粋に

$$
\mathrm{core} \equiv d \pmod{d^2}
$$

あるいは同等の valuation 補題を作ることだけじゃ。
これはかなり大きい前進じゃよ。

## 5. 次の一手

次にやるべきことも、もうかなり明白じゃ。

狙うべきは

$$
\operatorname{boundaryCyclotomicPrimeCore}(.right,d,x,u)\equiv d \pmod{d^2}
$$

またはそれと同値な

$$
d \mid \mathrm{core}
\quad\text{かつ}\quad
d \nmid \mathrm{core}/d
$$

を返す補題じゃ。
レポート第2回でも、ここが最優先の arithmetic / valuation kernel として整理されておった。

その補題が通れば、

$$
\texttt{ExceptionalBoundaryDatumPreparedArithmeticCoreDivDataTarget}
$$

が埋まり、そこから mainline と primitive packet descent へは、今回作った bridge 群でそのまま流れる。

## 6. 賢狼の総括

一言でまとめると、こうじゃ。

**いまは false route を切り終えた後の混乱期ではなく、boundary / arithmetic-core 本線の後半を閉じ終えて、残る未完を (d^2) / valuation 側の三条件に押し込むところまで来た。したがって current missing math は本当に arithmetic kernel 1 ブロックだけであり、次は `core ≡ d [MOD d^2]` 相当を立てて `ExceptionalBoundaryDatumPreparedArithmeticCoreDivDataTarget` を直接埋める段である。**

よい。
今回は「進んだ気がする」ではなく、 **本当に一段削れた** 更新じゃよ。
