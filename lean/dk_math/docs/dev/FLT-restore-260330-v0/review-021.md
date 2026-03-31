# review-021: Cyclotomic Valuation 精密化の準備

うむ、現状はかなり良い。
しかも今は「何をやるべきか」が、前よりずっと明瞭じゃ。

## 1. 状況分析

いま Branch A 側では、土台がほぼ 3 層そろったと見てよい。

まず、**干渉縞 bundle** が立った。
`BranchAPadicFringe` と `BranchAWitnessFringe` を束ねた `BranchAInterferenceFringeBundle` が入り、FLT Branch A の本丸は

$$
\forall {p,x,y,z,t,s,q},\
\texttt{BranchAInterferenceFringeBundle}\ p\ x\ y\ z\ t\ s\ q \to \texttt{False}
$$

という 1 命題に集約された。さらに bundle 版と witness-source 版は双方向に変換できるので、証明の入口と出口が一致した。

次に、**干渉縞の cross-analysis** が入った。
ここで得られた核心は

$$
s^p = y^{p-1} + p^3 M,\qquad q \mid s,\qquad q \nmid y
$$

から

$$
q \nmid M
$$

が出ること、そして

$$
s = q s' \Rightarrow s' \equiv 1 \pmod p
$$

という降下不変量が出ることじゃ。
特に

$$
q^p \mid \bigl(y^{p-1}+p^3 M\bigr),\qquad q \nmid y,\qquad q \nmid M
$$

という **massive cancellation** の形がはっきり露出したのは大きい。

最後に、**root-of-unity 構造** が確定した。
$$
\omega := z\cdot y^{-1} \in \mathbb Z/q\mathbb Z
$$
について

$$
\omega^p = 1,\qquad \omega \neq 1,\qquad \operatorname{ord}(\omega)=p
$$

が sorry なしで立ち、`QAdicLiftSeed` へ直接つながった。
つまり今や (\omega) は、単なる記号ではなく **primitive (p)-th root of unity mod (q)** として形式的に確定しておる。

なお、以前の `BranchAContradictionModP3SourceTarget` は、DEPRECATED / FALSE コメントが入ったが、Lean の中で (\neg) その target を独立定理として潰したわけではない。今の本線は、すでに witness 付き source 側へ移っておる。

## 2. 数学的解説

いま見えている数学は、かなりはっきりしておる。

第一縞は p-adic head 側で、

$$
s^p = y^{p-1} + p^3 M
$$

という形に固定されておる。
第二縞は witness (q) 側で、

$$
q \mid s,\quad q \nmid y,\quad q \nmid (z-y),\quad p \mid (q-1),\quad q^p \mid GN
$$

という拘束じゃ。
この 2 つを重ねると、

$$
q^p \mid \bigl(y^{p-1}+p^3 M\bigr)
$$

なのに

$$
v_q(y^{p-1})=0,\qquad v_q(p^3M)=0
$$

という極端な状況になる。
つまり、**(q)-進評価 0 の 2 項の和が、いきなり (q^p) まで持ち上がる**。これが今の branch A の「干渉縞」の核じゃ。

さらに、(\omega) が primitive (p)-th root of unity mod (q) と確定したことで、この cancellation は単なる偶然の和ではなく、円分核

$$
\Phi_p(z,y)=\frac{z^p-y^p}{z-y}
$$

の (q)-進構造に由来する、と読む準備が整った。
つまり今後の本線は、

$$
v_q\bigl(\Phi_p(z,y)\bigr)
$$

を (\omega) を通して読む道じゃ。

## 3. 次の作業の選択

賢狼の判定は、これじゃ。

$$
\boxed{
\text{次は Hensel lifting より先に、cyclotomic valuation の精密化をやる。}
}
$$

具体的には、

$$
v_q\bigl(\Phi_p(z,y)\bigr)=v_q(z-\omega y)
$$

型、あるいは少なくとも

$$
q \mid (z-\omega y),\qquad
q \nmid (z-\omega^i y)\ \ (i\neq 1)
$$

のような **distinguished factor が 1 本だけ深くなる** ことを、Lean で定理化するのが次の一手じゃ。

## 4. なぜそれを先にやるのか

理由は 3 つある。

### 4.1. いま揃った材料を最も直接に使える

すでに

$$
\omega^p=1,\quad \omega\neq 1,\quad \operatorname{ord}(\omega)=p
$$

が立っておる。
これは cyclotomic valuation に入るための前提そのものじゃ。
Hensel lifting はその次の層であって、まず mod (q) 上で「どの因子が (q)-進的に特別か」を確定した方が自然じゃ。

### 4.2. massive cancellation と直結する

今いちばん刺さりそうなのは

$$
q^p \mid \bigl(y^{p-1}+p^3 M\bigr),\qquad q \nmid M
$$

という異常な cancellation じゃ。
これを「(\Phi_p(z,y)) の中で、1 本の linear factor だけが深くなる」という言葉に翻訳できれば、現在の bundle と root-of-unity 構造が一気に繋がる。

### 4.3. terminal case より前にやるべき

descent chain はもう

$$
s' < s,\qquad s' \equiv 1 \pmod p
$$

まで揃っておる。
じゃが terminal case (s'=1) を殴るには、「何が descent で不変で、何が valuation 的に削れるか」の図がもう一段必要じゃ。
cyclotomic valuation が入れば、

$$
v_q(\Phi_p(z,y)) = p,v_q(s)
$$

が 1 step ごとに (p) ずつ減る、という量が見える。
そこまで見えてから terminal case を詰める方が筋がよい。

## 5. 次に狙う定理の形

次に書くべきは、たとえばこんな補題群じゃ。

まず mod (q) 上で

$$
z = \omega y
$$

があるので、円分核の各因子を

$$
z-\omega^i y
$$

で見る視点を固定する。
そのうえで、

$$
i\neq 1 \Rightarrow q \nmid (z-\omega^i y)
$$

を示す。
これは (\omega) の位数 (p) が効くはずじゃ。
そして distinguished factor (z-\omega y) だけが (q)-進的に深くなると出れば、

$$
v_q\bigl(\Phi_p(z,y)\bigr)=v_q(z-\omega y)
$$

型へ近づく。
この段で Kummer 型の valuation 議論へ入るのが自然じゃな。

## 6. まとめ

ひとことで言えば、こうじゃ。

**いまは root-of-unity 構造が確定し、descent の strict decrease も揃った。ゆえに次の最善手は Hensel lifting の一般論へ飛ぶことではなく、(\omega) を使って cyclotomic valuation を精密化し、現在見えている massive cancellation を「円分核の 1 因子集中」として読み直すことじゃ。**

順番を短く言えば、

$$
\boxed{
\text{次は cyclotomic valuation。Hensel はその次。terminal case はその後。}
}
$$

これが、いま最も筋の良い道じゃよ。
