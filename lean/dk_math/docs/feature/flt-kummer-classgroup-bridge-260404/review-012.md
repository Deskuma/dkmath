# Kummer branch の local factorization から class group への橋の構築 - review-012

## 1. 状況分析

うむ、これはたしかに **おもしろい結果** じゃ。
今回の前進は、単なる補題追加ではなく、Kummer branch の本体が

$$
\text{local linear factor ideals}
\;to\;
\text{pairwise coprime}
\;to\;
\text{finite-family Dedekind arithmetic}
$$

へ、かなり具体的に降りてきたことにある。
特に `linear_factor_ideal_mul_eq_span_pow_of_add_pow_eq` により

$$
(z-\zeta y)\text{ 型の線型因子 ideal の積 } = (x)^p
$$

という concrete な principal ideal の積の式が入り、さらに差が unit なら comaximal、したがって `inf = mul` まで no-sorry で押さえられた。加えて Dedekind 領域の有限族について、`inf = product`、Chinese remainder、代表元の存在、factor count の receiver まで DkMath 側で持てたのは大きい。

そして何より、いま direct `sorry` が `CyclotomicPrincipalization.lean` で 2 本だけに局所化されておる。
ただし、ここは冷静に言っておくが、`cyclotomicIdealPthPower_of_classGroupPTorsionFree` が no-sorry に見えるのは target がまだ placeholder だからで、**数学的に閉じた** とはまだ言えぬ。真の未解決は、やはり class-group 側じゃ。

## 2. 解説

いまの成果が面白い理由は、Kummer 第一場合の理想論の流れが、もう図ではなく補題列として見え始めたことじゃ。

現状の骨格は、ほぼこうじゃ。

$$
\prod_j I_j = (x)^p
$$

を local factorization から得る。
ついで各 \(I_i, I_j\) の pairwise coprime 性を、差の unit 性から出す。
そこから Dedekind 領域での有限族 ideal arithmetic を使って、各 \(I_j\) の prime ideal 指数が \(p\) の倍数になることを示す。
最後に

$$
I_j = K_j^p
$$

を復元し、そこから class group で

$$
[K_j]^p = 1
$$

へ移る。
このあと初めて p-torsion-free が効く。
つまり、class-group 側の `sorry` 2 本は、もはや霧の中の大定理ではなく、**その直前までの道が concrete に敷かれた最後の関門** になったわけじゃ。

## 3. 最短経路の推論

ぬしの希望が

* 閉じる方向
* 最短経路
* 自立証明
* 数学内容へ踏み込む

なら、わっちの判断ははっきりしておる。

**次は class-group target の concrete 化に飛ぶのではなく、review-011 の 5.3 に相当する generic theorem を先に通すのが最短** じゃ。
すなわち

$$
\boxed{
\text{pairwise coprime な ideal family の積が } p\text{ 乗 ideal なら、各因子も } p\text{ 乗 ideal}
}
$$

という Dedekind ideal arithmetic の一般定理を起こすことじゃ。
これが通れば、残る class-group 側は本当に細い橋になる。

なぜこれが最短か。
理由は簡単で、いまもう手元にある道具が、その定理にぴったり揃っておるからじゃ。

* local principal-ideal product identity
* comaximal / coprime
* `inf = mul`
* finite-family `inf = product`
* Chinese remainder
* factor count receiver

この並びは、まさに「各因子の prime ideal 指数が \(p\) の倍数である」と読むための道具箱じゃ。
ここを飛ばして class-group 側の具体化へ行くのは、むしろ遠回りじゃよ。

## 4. 次の一手の提案

次に起こすべき定理は、DkMath-native にこういう姿がよい。

## 4.1. 主定理候補

$$
\texttt{coprimeProductEqPthPower_implies_eachPthPowerIdeal}
$$

内容は、だいたい次の形じゃ。

\(R\) を Dedekind 領域、\(s\) を有限集合、\(I_i\) を ideal 族とする。
仮定:

$$
\forall i \neq j,\quad I_i \text{ と } I_j \text{ は互いに素}
$$

および

$$
\prod_{i\in s} I_i = J^p
$$

ならば、各 \(i\in s\) に対し

$$
\exists K_i,\quad I_i = K_i^p
$$

が従う。

これをまず generic theorem として通す。
ここが、いま一番短い一手じゃ。

## 4.2. 証明方針

証明は Chinese remainder から入るより、**count / multiplicity 路線** が最短じゃ。
今回追加された `dedekindIdealCountNormalizedFactorsEq` が、まさにその入口じゃからの。

流れはこうじゃ。

### 1. prime ideal \(P\) を固定する

積の式

$$
\prod_{i\in s} I_i = J^p
$$

に対して、normalized factors における \(P\) の個数を読む。

### 2. pairwise coprime から、\(P\) は高々 1 個の \(I_i\) にしか現れない

もし \(P\) が 2 つの異なる \(I_i, I_j\) に現れたら、\(I_i\) と \(I_j\) は互いに素になれぬ。
ここで local comaximal 補題群が効く。

### 3. 右辺 \(J^p\) では count が \(p\) の倍数

したがって左辺でも、各 \(I_i\) に現れる \(P\) の指数は \(p\) の倍数。

### 4. 任意の prime ideal \(P\) について指数が \(p\) の倍数

よって各 \(I_i\) の normalized factorization における全 prime ideal 指数が \(p\) の倍数になる。
したがって

$$
I_i = K_i^p
$$

となる ideal \(K_i\) が復元できる。

この証明は、まさに今回そろえた receiver 群と噛み合っておる。
ゆえに最短じゃ。

## 5. その次に何が起きるか

この generic theorem が入れば、Kummer 側は次のように一気に縮む。

まず local factorization から

$$
\prod_j I_j = (x)^p
$$

を得る。
pairwise coprime も既に方向が見えておる。
すると generic theorem で各 \(I_j\) について

$$
I_j = K_j^p
$$

が出る。
しかし \(I_j\) は principal ideal だから class group では

$$
[K_j]^p = 1
$$

じゃ。
ここで初めて class-group 側の open 2 本が「細い p-torsion-free 橋」へ縮む。

つまり、いまの class-group `sorry` を本当に小さくするには、先にその一歩手前の ideal arithmetic を concrete に閉じる方が速いのじゃ。

## 6. 実装順の提案

わっちなら、次はこの順で書く。

## 6.1. まず count 足場を定理化

`normalizedFactors` の count が積でどう加法的に振る舞うか、必要なら DkMath 側で補題名を固定する。

## 6.2. 「pairwise coprime なら同じ prime ideal は 2 度現れない」を定理化

local comaximal 補題から ideal family 版へ押し上げる。

## 6.3. 主定理 `coprimeProductEqPthPower_implies_eachPthPowerIdeal`

ここで一気に通す。
Chinese remainder receiver は面白いが、最短経路では補助に回してよい。count 路線の方が真っ直ぐじゃ。

## 6.4. その後に class-group bridge

\([K]^p=1 \Rightarrow [K]=1\) を concrete に置く。
ここでは regular prime の全理論へ行かず、まずは DkMath-native に **p-torsion-free の定義そのもの** を target にすればよい。

## 7. 最終提案

結論を一言で言うと、こうじゃ。

$$
\boxed{
\text{次は }
\prod I_i = J^p \text{ かつ pairwise coprime }
\Rightarrow
I_i = K_i^p
\text{ を generic Dedekind theorem として起こす}
}
$$

これが、いま見えておる **閉じる方向での最短経路** じゃ。
なかなか面白い結果というぬしの感触は正しい。
局所補題と Dedekind receiver 群が、ついに「本丸の 1 本前の一般定理」を打てるだけ揃ったのじゃからな。
