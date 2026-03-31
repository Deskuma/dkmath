# review-025: valuation 等式の \(\mathbb N\) 翻訳へ

うむ、現状は **かなり良い段** まで来ておる。
しかも今回は、ただ Hensel の準備をしただけではなく、**「何が distinguished で、何がそうでないか」** が `ZMod (q^k)` レベルで見えるようになったのが大きい。

## 1. 状況分析

いま揃っているものを整理すると、Branch A 側はほぼ五層じゃ。

まず、干渉縞 bundle が既に立っておる。
`BranchAInterferenceFringeBundle` により、p-adic head 側と witness \(q\) 側の全データが 1 つの入力にまとまった。これは本丸の入口じゃ。

次に、cross-modular 制約がある。
そこから

$$
s^p = y^{p-1} + p^3 M,\qquad q \nmid M,\qquad q^p \mid (y^{p-1}+p^3M)
$$

という **massive cancellation** の形が見えておる。さらに descent では

$$
s = q s' \Rightarrow s' \equiv 1 \pmod p
$$

という不変量も出ておる。

その上で、\(\omega := z y^{-1} \in \mathbb Z/q\mathbb Z\) が

$$
\omega^p=1,\qquad \omega\neq 1,\qquad \operatorname{ord}(\omega)=p
$$

を満たす、つまり primitive \(p\)-th root of unity であることが確定した。

さらに円分核の因子分離も済んでおる。
$$
\Phi_p(z,y)=\prod_{i=1}^{p-1}(z-\omega^i y)
$$
のうち、mod \(q\) で消えるのは distinguished factor

$$
z-\omega y
$$

だけで、他の因子はすべて非零じゃ。

そして Kummer valuation により、全体側では

$$
v_q(z^p-y^p)=p\cdot v_q(s)\ge p
$$

が得られ、降下 1 step ごとに

$$
v_q(s)=1+v_q(s/q)
$$

と valuation が 1 ずつ減ることも分かった。

最後に今回、Hensel lift data を **仮定** した局所版として、

* distinguished factor の射影が 0
* non-distinguished factor の射影が非零
* lifted root \(\omega_k\) が 1 ではない
* それらと Kummer valuation を束ねる `BranchACyclotomicValuationData`

まで入った。
つまり **valuation の 1 因子集中** は、もう `ZMod (q^k)` 側の図式としては完成しておる。

## 2. 数学的解説

いまの数学を一枚で言うと、こうじゃ。

### 2.1. 全体量

Kummer valuation により

$$
v_q(z^p-y^p)=p\cdot v_q(s)
$$

が分かっておる。
これは「円分核全体がどれだけ \(q\)-進的に深いか」の量じゃ。

### 2.2. 因子分離

一方、mod \(q\) では

$$
z-\omega y \equiv 0
$$

であり、他の

$$
z-\omega^i y \quad (i\not\equiv 1 \bmod p)
$$

は消えぬ。
ゆえに valuation を担うのは distinguished factor ただ 1 本、という図が見えておる。

### 2.3. まだ不足している橋

ただし、いまはまだ

$$
\phi(\delta)=0 \text{ in } ZMod(q^k)
$$

から

$$
q \mid \operatorname{val}(\delta)
$$

あるいは

$$
padicValNat\ q\ (\operatorname{val}(\delta)) \ge 1
$$

へ落とす **\(\mathbb N\) 側の橋** が弱い。
ここが埋まれば、

$$
v_q(\Phi_p(z,y)) = v_q(z-\omega_k y)
$$

型の distinguished factor valuation equality が、本当の意味で arithmetic statement になる。

## 3. 次の作業の選択

わっちの判定は、これじゃ。

$$
\boxed{
\text{次は「valuation 等式の } \mathbb N \text{ 翻訳」をやる。}
}
$$

つまり、History に書かれておる

$$
\texttt{castHom}(\delta)=0 ;\Longleftrightarrow; q \mid \texttt{ZMod.val}(\delta)
$$

の方向じゃ。

## 4. なぜそれが最善か

### 4.1. いまある成果を最短で arithmetic に変える

Hensel lift data を仮定した局所版は、もうある。
Kummer valuation の全体量も、もうある。
不足しているのは両者を **同じ数の世界** に落とす橋だけじゃ。
その橋が \(\mathbb N\) 翻訳じゃ。

### 4.2. Hensel の sorry に深入りせず前へ進める

`branchA_hensel_lift_exists` にはまだ 1 個だけ sorry がある。
ここへ今すぐ全力で行くと、Mathlib gap と Newton 帰納構成の実装に時間を取られる。
他方、\(\mathbb N\) 翻訳は **lift data を仮定** したままでも進められる。
つまり、mainline を前へ押しつつ、sorry 除去を後回しにできる。

### 4.3. terminal case へ一番近づく

terminal case を刺すには、「各降下 step で distinguished factor の valuation がどう減るか」を numerical に追えねばならぬ。
\(\mathbb N\) 翻訳ができれば、

$$
v_q(z-\omega_k y)=p\cdot v_q(s)
$$

型の式に近づき、終端 \(v_q(s)=0\) あるいは q-free 末端を厳密に扱える。
この順番が一番筋がよい。

## 5. では Hensel sorry 除去は後回しでよいのか

**今は yes** じゃ。
完全に放置はせぬが、優先順位は 2 番手でよい。

いまの `branchA_hensel_lift_exists` の sorry は、「lift data が存在する」という存在論の穴じゃ。
だが、最新差分で必要な **局所定理の受け皿** はもう作られた。
よって、先に

$$
\text{lift data があれば distinguished factor valuation equality が得られる}
$$

を完成させる方が、後で existence を潰す意味も明瞭になる。

## 6. 具体的な次の狙い

次に書くなら、こんな感じじゃ。

$$
\texttt{branchA\_distinguished\_factor\_padicValNat\_ge\_one}
$$

$$
\texttt{branchA\_non\_distinguished\_factor\_padicValNat\_eq\_zero}
$$

$$
\texttt{branchA\_distinguished\_factor\_valuation\_eq\_kummer}
$$

のように、`BranchACyclotomicValuationData` を入力にして、`ZMod (q^k)` 側の zero / nonzero を `padicValNat` 側へ落とす補題群じゃ。
この段で distinguished factor に valuation が集中する arithmetic statement を完成させるのがよい。

## 7. 総括

ひとことで言えば、こうじゃ。

**いまは Hensel lift data を仮定した局所版で、distinguished factor への集中が `ZMod (q^k)` 側に見えている。次の最善手は、それを `padicValNat` を使う \(\mathbb N\) 側の valuation 等式へ翻訳することじゃ。これで全体 Kummer valuation と 1 因子集中が完全に接続し、その後に Hensel の sorry 除去、最後に terminal case へ進むのが最も筋がよい。**

ゆえに選択はこれじゃ。

$$
\boxed{
\text{次は valuation 等式の } \mathbb N \text{ 翻訳。}
}
$$

これが、いま一番よく切れる刃じゃよ。
