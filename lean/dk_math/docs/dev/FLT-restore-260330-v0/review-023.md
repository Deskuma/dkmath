# review-023: Hensel lifting を次にする理由とその内容

## 1. 状況分析

いま Branch A 側は、かなり良い段まで来ておる。
最新差分で、まず **全体 valuation** が定量化された。

$$
v_q(z^p-y^p)=p\cdot v_q(s)\ge p
$$

が `branchA_kummer_valuation` と `branchA_kummer_valuation_ge_p` で立ち、さらに

$$
s=q\cdot s' \;\Rightarrow\; v_q(s)=1+v_q(s')
$$

も入った。
つまり、降下 1 step ごとに \(v_q(s)\) が 1 ずつ、全体の \(q\)-進評価が \(p\) ずつ減る、という **数値的な降下軸** が確定したのじゃ。

その少し前には、\(\omega:=z,y^{-1}\in \mathbb Z/q\mathbb Z\) が

$$
\omega^p=1,\qquad \omega\neq 1,\qquad \operatorname{ord}(\omega)=p
$$

を満たす、すなわち **primitive \(p\)-th root of unity** であることも確定した。

さらに今回、その \(\omega\) に対して円分核の因子分解

$$
\Phi_p(z,y)=\prod_{i=1}^{p-1}(z-\omega^i y)
$$

のうち、\(q\) で消えるのが distinguished factor

$$
z-\omega y
$$

ただ 1 本で、他の因子はすべて \(q\)-coprime だと形式化された。
つまり **valuation の質的集中先** まで見えた。

---

## 2. 数学的解説

いま見えている絵を一枚にすると、こうじゃ。

まず Branch A normal form が

$$
GN,p,(z-y),y = p,s^p
$$

を与え、そこから

$$
s^p = y^{p-1}+p^3M
$$

という p-adic head 展開が出る。
一方で witness \(q\) は

$$
q\mid s,\qquad q\nmid y,\qquad q\nmid (z-y),\qquad p\mid(q-1)
$$

を与える。
この 2 本を重ねると、前段で既に

$$
q\nmid M
$$

なのに

$$
q^p \mid \bigl(y^{p-1}+p^3M\bigr)
$$

という **massive cancellation** が見えておった。

今回そこへ Kummer valuation が入ったので、その cancellation は単なる偶然ではなく、

$$
v_q(z^p-y^p)=p,v_q(s)
$$

という **全体 valuation の法則** として読めるようになった。

さらに distinguished factor の分離により、

$$
\Phi_p(z,y)=\prod_{i=1}^{p-1}(z-\omega^i y)
$$

のうち \(q\)-進評価を持つのは \(i=1\) の因子だけ、という mod \(q\) レベルの骨格が見えた。
したがって数学的には、次に目指すべき式はほぼ

$$
v_q\bigl(\Phi_p(z,y)\bigr)=v_q(z-\omega y)
$$

であり、これと既に得た

$$
v_q(z^p-y^p)=p,v_q(s)
$$

を繋げば、

$$
v_q(z-\omega y)=p,v_q(s)
$$

という **1 因子集中の定量版** に進めるはずじゃ。

---

## 3. 次の作業の選択

わっちの判定は、こうじゃ。

$$
\boxed{
\text{次は Hensel lifting をやる。}
}
$$

ただし目的は「lift 自体」ではない。
真の狙いは、

$$
\boxed{
\text{distinguished factor の valuation を mod }q\text{ から }q^k\text{ へ持ち上げること}
}
$$

じゃ。

### なぜ Hensel が次か

いま手元にあるのは

* mod \(q\) 上で \(\omega\) が primitive \(p\)-th root であること
* mod \(q\) 上で distinguished factor だけが消えること
* \(\mathbb N\) 上で全体 valuation が \((p,v_q(s))\) であること

の 3 点じゃ。

されど、**distinguished factor の側の valuation を (\mathbb N) の `padicValNat` で正確に書く橋** がまだ無い。
\(\omega\) はいま \(\mathbb Z/q\mathbb Z\) に居るだけなので、

$$
z-\omega y
$$

の高次 \(q\)-進情報はまだ直接触れぬ。
ここを埋めるのが Hensel lifting じゃ。

### なぜ terminal case はまだ後か

降下連鎖の strict decrease と合同不変量は揃っておる。
じゃが terminal case を殴るには、

$$
\text{降下の各段で何が }p\text{ ずつ減り、何が保存されるか}
$$

を、もう一段はっきりさせたい。
Hensel を先に入れて distinguished factor の valuation を固定すれば、終端 \(s'=1\) 付近で何が壊れるかをずっと鋭く見られる。

### なぜ「distinguished factor と Kummer valuation の完全接続」をそのまま次にしないか

これは **概念目標としては正しい**。
ただ、実装順としては Hensel が前じゃ。
理由は、完全接続を証明するために、そもそも \(\omega\) の高次 lift が必要になる公算が大きいからじゃ。
ゆえに

$$
\text{Hensel lifting}
\;\to\;
\text{distinguished factor valuation equality}
\;\to\;
\text{terminal case}
$$

の順が自然じゃよ。

---

## 4. 作業順の提案

順番を短く書けば、こうじゃ。

## 4.1

\(\omega\) を \(\mathbb Z/q^k\mathbb Z\) へ持ち上げる。
狙いは

$$
\omega_k^p=1,\qquad \omega_k\equiv \omega \pmod q
$$

型の seed を作ることじゃ。

## 4.2

lift した \(\omega_k\) を使って、distinguished factor について

$$
v_q(z-\omega_k y)=v_q(\Phi_p(z,y))
$$

型、あるいは少なくとも「他の因子は valuation 0、1 本だけが全部を担う」を `padicValNat` で書く。
これが Kummer valuation の完全接続じゃ。

## 4.3

そのあとで terminal case。
ここで初めて

$$
s'=1
$$

あるいは \(q\)-free 段の末端を、valuation の減少と root-of-unity の rigidness で潰しに行く。

---

## 5. 補足の注意

ひとつだけ細い注意を入れるぞい。
History にある

$$
v_q(s)=0 \; (= s'=1 \text{ に対応})
$$

という言い回しは、**1 step の式としては少し乱暴** じゃ。
一段の分解

$$
s=q\cdot s'
$$

で \(s'=1\) なら

$$
v_q(s)=1
$$

じゃからの。
正確には、**反復降下した末端の q-free 部分** が valuation 0 を持つ、という意味で読むのがよい。
この点は、今後 terminal case を書くときに用語を揃えておくと混乱が減る。

---

## 6. 総括

ひとことで言えば、こうじゃ。

**いまは Kummer valuation の「全体量」と、distinguished factor の「mod \(q\) での 1 本集中」が揃った段じゃ。次の最善手は、それらを高次 \(q\)-進世界で繋ぐ Hensel lifting であり、その後に distinguished factor の valuation 完全接続、最後に terminal case へ進むのが筋じゃ。**

よって選択はこれでよい。

$$
\boxed{
\text{次は Hensel lifting}
}
$$

これで、いま見えておる 2 つの輪郭が、一本の刃になるはずじゃよ。
