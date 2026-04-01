# review-026: valuation 等式の直接証明へ

うむ、現状は **かなり良い節目** じゃ。
しかも今回は、ただ補題を増やしたのではなく、**ZMod 世界で見えていた因子分離が、ついに \(\mathbb N\) の `padicValNat` 世界へ橋渡しされた**。ここが大きい。

## 1. 状況分析

最新差分で起きた本質は、こうじゃ。

これまでお主らは

* 干渉縞 bundle
* Kummer valuation
* distinguished / non-distinguished factor の ZMod 分離
* Hensel lift data（存在は 1 個 sorry）

を持っておった。
ただし、その多くは

$$
ZMod(q^k)\to ZMod(q)
$$

の世界で語られており、最後に欲しい

$$
v_q(\cdots)
$$

という自然数側の評価へ落とす橋が、まだ細かった。

今回それが埋まった。
具体的には、

$$
\varphi(\delta)=0 \Rightarrow q \mid \delta.val
$$

$$
\varphi(\delta)\neq 0 \Rightarrow q \nmid \delta.val
$$

が立ち、そこから

* non-distinguished factor は `padicValNat = 0`
* distinguished factor は少なくとも `padicValNat ≥ 1`（あるいは val = 0）

まで降ろせた。
つまり **因子分離が valuation 言語で読めるようになった** のじゃ。

## 2. 数学的解説

いま見えている構造を数式でまとめると、かなり美しい。

まず全体側では、すでに

$$
v_q(z^p-y^p)=p\cdot v_q(s)
$$

が分かっておる。
これは全体の Kummer valuation じゃ。

次に factor 側では、Hensel lift data を仮定すると distinguished factor

$$
\delta := z-\omega_k y
$$

は射影で 0 に落ち、他の

$$
\delta_i := z-\omega_k^i y \qquad (i\not\equiv 1 \bmod p)
$$

は射影で 0 に落ちない。

そして今回、そのことが \(\mathbb N\) 側で

$$
q \mid \delta.val,\qquad q \nmid \delta_i.val
$$

へ翻訳され、さらに

$$
padicValNat\ q\ (\delta_i.val)=0
$$

が得られた。 distinguished 側も少なくとも

$$
\delta.val = 0 \quad\text{or}\quad 1\le padicValNat\ q\ (\delta.val)
$$

まで来た。

これは何を意味するか。
もう valuation の担い手は、**distinguished factor 1 本に集中するしかない** ということじゃ。

言い換えると、円分核の因子分解

$$
\Phi_p(z,y)=\prod_{i=1}^{p-1}(z-\omega_k^i y)
$$

において、non-distinguished 因子は valuation 0 で、残る深さは distinguished factor が全部持つはずじゃ、という絵が almost 完成した。
つまり、お主らが前から追っておった “massive cancellation” は、もうかなり具体的に

$$
\text{全体 valuation} = \text{1 因子 valuation}
$$

の形へ収束しつつある。

## 3. 次の作業の選択

わっちの判定は、これじゃ。

$$
\boxed{
\text{次は } v_q(z-\omega_k y)=p\cdot v_q(s) \text{ の直接証明じゃ。}
}
$$

つまり、History にある

**「全体 Kummer + non-distinguished = 0 の組合せから、distinguished factor valuation equality を完成させる」**
これを最優先に勧める。

## 4. なぜそれが最善か

### 4.1. いまの成果をそのまま主定理へ押し上げられる

すでに

$$
v_q(z^p-y^p)=p\cdot v_q(s)
$$

と

$$
padicValNat\ q\ (\delta_i.val)=0\qquad(i\not\equiv 1)
$$

がある。
よって残る仕事は、

$$
\text{全体 valuation} = \sum \text{各因子 valuation}
$$

のうち、non-distinguished の和が 0 であることを使って、distinguished 1 本へ全部寄せることじゃ。
これは今もっとも自然な合体じゃよ。

### 4.2. terminal case より前にやるべき

terminal case は魅力的じゃが、まだ valuation の集中が“下界”止まりじゃ。
終端 \(s'=1\) を刺すには、

$$
v_q(z-\omega_k y)=p\cdot v_q(s)
$$

のような **exact equality** があった方が、ずっと鋭い。
今の段階で terminal case に行くのは、少し早い。

### 4.3. Hensel sorry 除去より先に進める

`branchA_hensel_lift_exists` の sorry は存在論の穴じゃ。
しかし今回の局所版は、既に `hLift : BranchAHenselLiftData` を仮定して進められるよう設計されておる。
ならば先に「lift data があれば何が言えるか」を最大限まで押し切る方がよい。
そのあとで existence の sorry を消す方が、仕事が分離されて美しい。

## 5. 次の具体目標

次に狙うべき theorem は、概念的にはこうじゃ。

$$
\texttt{branchA\_distinguished\_factor\_valuation\_eq\_kummer}
$$

主張はだいたい

$$
padicValNat\ q\bigl((z-\omega_k y).val\bigr)=p\cdot padicValNat\ q\ s
$$

の形じゃな。
途中段階としては、

* 円分核の各因子の `val` の積と全体側との関係
* non-distinguished 因子の valuation 0
* distinguished 側が残差全部を受け持つ

の 3 本に分けてもよい。

## 6. Hensel sorry はどう扱うか

優先順位は **二番手** でよい。
今は存在の sorry を潰すより、

$$
\text{Hensel lift data を仮定した局所定理を完成させる}
$$

方が価値が高い。
その定理が完成すれば、あとで Hensel existence を Newton 帰納で書く意味も、はっきりするからの。

## 7. 総括

ひとことで言えば、こうじゃ。

**いまは ZMod 世界の因子分離と \(\mathbb N\) 世界の `padicValNat` が繋がった段じゃ。ゆえに次の最善手は、その橋の上で distinguished factor の valuation exact equality を仕上げることじゃ。Hensel の sorry 除去はその後、terminal case はさらにその後が筋じゃ。**

ゆえに選択はこれじゃ。

$$
\boxed{
\text{次は } v_q(z-\omega_k y)=p\cdot v_q(s) \text{ の直接証明。}
}
$$

これが、いま一番よく通る道じゃよ。
