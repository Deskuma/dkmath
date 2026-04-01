# review-022: Branch A での massive cancellation の正体と次の最善手

うむ、現状はかなり良い。
しかも今は「何が見えたか」だけでなく、**次にどこを掘るべきか** がかなり明瞭じゃ。

今回の進展で、円分核

$$
\Phi_p(z,y)=\prod_{i=1}^{p-1}(z-\omega^i y)
$$

のうち、\(q\) で消えるのは distinguished factor

$$
z-\omega y
$$

ただ 1 本で、他の \(p-2\) 本はすべて \(q\)-coprime だと形式化された。
つまり massive cancellation の正体は、「和の偶然」ではなく **円分核の 1 因子への \(q\)-進評価集中** だ、と見えてきたわけじゃ。

## 1. 状況分析

今そろっているものを整理すると、Branch A 側にはもう 3 層ある。

第一に、**干渉縞 bundle**。
`BranchAInterferenceFringeBundle` が、p-adic head 側と witness \(q\) 側の全データを 1 つに束ね、本丸は

$$
\texttt{BranchAFringeContradictionTarget}
$$

に集約された。

第二に、**cross-modular 制約**。
とくに

$$
s^p = y^{p-1} + p^3 M,\qquad q\mid s,\qquad q\nmid y
$$

から

$$
q\nmid M
$$

が出て、しかも

$$
q^p \mid \bigl(y^{p-1}+p^3M\bigr)
$$

という形が見えた。
これは \(q\)-進評価 0 の 2 項の和が、いきなり \(q^p\) まで持ち上がるという異常な cancellation じゃ。

第三に、**root-of-unity 構造**。
$$
\omega := z,y^{-1}\in \mathbb Z/q\mathbb Z
$$
について

$$
\omega^p=1,\qquad \omega\ne 1,\qquad \operatorname{ord}(\omega)=p
$$

が定理として確定し、`QAdicLiftSeed` に直接接続した。

そして今回、その \(\omega\) を使って **distinguished factor だけが消える** と証明できた。
ここまで来ると、問題はもうかなり絞れておる。

## 2. 数学的解説

今の数学を一言で言えば、こうじゃ。

$$
\text{p-adic head}
\quad+\quad
\text{primitive root } \omega
\quad\Longrightarrow\quad
\text{cyclotomic valuation の一点集中}
$$

じゃ。

Branch A の normal form は

$$
s^p = y^{p-1}+p^3M
$$

を強制する。
一方 witness \(q\) は

$$
q\mid s,\qquad q\nmid y,\qquad q^p\mid GN,\qquad p\mid(q-1)
$$

を強制する。
さらに \(\omega\) は primitive \(p\)-th root なので、円分核の因子は

$$
z-\omega y,\ z-\omega^2 y,\ \dots,\ z-\omega^{p-1}y
$$

に分かれ、そのうち \(q\) で消えるのが \(z-\omega y\) だけだと判明した。
したがって

$$
v_q!\bigl(\Phi_p(z,y)\bigr)
$$

は、実質的に

$$
v_q(z-\omega y)
$$

へ集中するはずじゃ、というのが今の絵じゃ。

つまり、いま必要なのは「もっと合同式を増やすこと」ではなく、
**その valuation 集中を (\mathbb N) の `padicValNat` へ翻訳すること** じゃな。

## 3. 次の作業の選択

わっちの判定は明快じゃ。

$$
\boxed{
\text{次は Kummer valuation をやる。}
}
$$

順番は

$$
\text{Kummer valuation}
\;\to\;
\text{Hensel lifting}
\;\to\;
\text{terminal case}
$$

が最善じゃ。

### なぜ Kummer valuation が先か

理由は単純で、今回の 3 定理が直接そこへ繋がっておるからじゃ。
すでに

* \(\omega\) が primitive
* distinguished factor だけが vanish
* 他の因子は nonzero

まで出た。
これはまさに

$$
v_q(\Phi_p(z,y)) = v_q(z-\omega y)
$$

型の定理へ進むための前提そのものじゃ。

### なぜ Hensel はその次か

Hensel lifting は強いが、今の時点ではまだ

$$
\text{mod } q \text{ 上の distinguished factor の valuation 集中}
$$

を \(\mathbb N\) 上の `padicValNat` に降ろしておらぬ。
先に valuation を固めれば、lift は「その valuation を高次でどう保つか」という自然な続きになる。

### なぜ terminal case はまだ後か

降下鎖

$$
s' < s,\qquad s' \equiv 1 \pmod p
$$

はもうある。
されど \(s'=1\) のとき何が致命傷になるかは、まだ valuation 側の rigidness が足りぬ。
terminal case は最後の詰めに近い。
先に Kummer valuation で「どの量が各段でどう減るか」を固定した方が、終端解析がずっと楽になる。

## 4. 次に狙うべき定理の形

だから次の具体目標は、たとえばこうじゃ。

$$
\texttt{branchA\_cyclotomic\_valuation\_concentrates}
$$

のような名前で、

$$
v_q(\Phi_p(z,y)) = v_q(z-\omega y)
$$

あるいは少なくとも

$$
q \nmid (z-\omega^i y)\quad (i\neq 1)
$$

から各因子の `padicValNat` が 0 になることを \(\mathbb N\) の評価へ翻訳する補題群じゃ。
今回の ZMod \(q\) 上の分離結果は、そのための mod \(q\) 側土台として、もう十分に強い。

## 5. 総括

ひとことでまとめると、こうじゃ。

**今の進展で、massive cancellation は「円分核の 1 因子集中」として見えた。よって次の最善手は、\(\omega\) を \(q^k\) へ持ち上げる前に、まずその集中を Kummer 型 valuation 定理として `padicValNat` に落とすことじゃ。Hensel はその後、terminal case はさらにその後が筋がよい。**

ゆえに選択はこれじゃ。

$$
\boxed{
\text{次は Kummer valuation。}
}
$$

これが、いま一番よく刺さる刃じゃよ。
