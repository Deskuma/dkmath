# review-020: FLT Branch A 証明への道の推論

うむ、現状はかなり良い。
しかも今は「何をやるべきか」が、前よりずっとはっきりしておる。

## 1. 状況分析

最新差分で、Branch A 側は大きく 3 つ進んだ。

第一に、**降下連鎖** が形式化された。
`BranchADescentStep` により、(s = q s') の 1 step で

$$
0 < s',\qquad s' < s,\qquad s' \equiv 1 \pmod p,\qquad p(t s') < x
$$

が一括で取れるようになった。
つまり「降下は本当に strict decrease で、しかも合同類を保つ」という骨格はもう Lean 上で固定されたのじゃ。

第二に、**cyclotomic / q-adic 側の入口** が定理として立った。
$$
\omega := z,y^{-1}\in \mathbb Z/q\mathbb Z
$$
に対して

$$
(z : \mathbb Z/q\mathbb Z)=\omega,(y : \mathbb Z/q\mathbb Z)
$$

が `branchA_lift_seed_z_eq_omega_mul_y` として固定され、さらに

$$
q^p \mid GN,p,(z-y),y
$$

が bundle からそのまま読める形になった。
加えて

$$
s = q s' ;\Rightarrow; s^p = q^p s'^p
$$

も定理化され、降下 1 step ごとに \(q\)-adic 因子が \(q^p\) ずつ剥がれる算術基盤まで揃った。

第三に、前段で得た **干渉縞の cross-analysis** が生きておる。
すでに

$$
s^p = y^{p-1} + p^3 M,\qquad q \mid s,\qquad q \nmid y
$$

から

$$
q \nmid M
$$

が出ており、しかも

$$
q^p \mid \bigl(y^{p-1}+p^3 M\bigr)
$$

でもある。
つまり \(q\)-進評価 0 の 2 項の和が、\(q^p\) まで持ち上がる **massive cancellation** が見えておる。これが今の数学の芯じゃ。

## 2. 数学的解説

いま見えている構図は、ほんに美しい。

第一縞は p-adic head 側で、

$$
s^p = y^{p-1} + p^3 M
$$

という形に固定されておる。
第二縞は witness \(q\) 側で、

$$
q \mid s,\quad q \nmid y,\quad q \nmid (z-y),\quad p \mid (q-1),\quad q^p \mid GN
$$

という束じゃ。

この 2 本を重ねると、

$$
q \nmid M
\quad\text{なのに}\quad
q^p \mid \bigl(y^{p-1}+p^3M\bigr)
$$

が起こる。
したがって、問題の本質はもう mod \(p^k\) 単独の合同式ではない。
本丸は

$$
\text{p-adic head}
\quad+\quad
\text{cyclotomic / q-adic witness}
$$

の **干渉** じゃよ。

## 3. どれからやるか

わっちの判定は明快じゃ。

$$
\boxed{
\text{まず } \omega^p = 1 \text{ と } \omega \ne 1 \text{ を明示的に証明する。}
}
$$

これを **最優先** に勧める。

## 4. なぜ \(\omega\) からか

理由は 3 つある。

### 4.1. いま一番短く、しかも深い

すでに

$$
\omega = z,y^{-1} \in \mathbb Z/q\mathbb Z
$$

の接続は立っておる。
ここから

$$
x^p + y^p = z^p,\qquad q \mid x,\qquad q \nmid y
$$

を mod (q) へ落とせば

$$
z^p \equiv y^p \pmod q
$$

だから

$$
\omega^p = 1
$$

が自然に出る。
さらに \(q \nmid (z-y)\) だから

$$
z \not\equiv y \pmod q
$$

ゆえに

$$
\omega \ne 1
$$

じゃ。

これは、今の bundle の field だけでかなり直接的に狙える。
しかも出てくる内容は「\(\omega\) は非自明な \(p\)-th root of unity mod \(q\)」という、円分核ど真ん中の主張じゃ。

### 4.2. Hensel の高次化の前提になる

\(\mathbb Z/q\mathbb Z\) で

$$
\omega^p = 1,\qquad \omega \ne 1
$$

が立てば、次に

$$
\mathbb Z/q^p\mathbb Z
$$

への lift を考える意味が明確になる。
つまり Hensel lifting は 2 番目にやるべきことで、その前に **lift したい元が本当に primitive なのか** を確定しておく方が筋が良い。

### 4.3. cyclotomic valuation と直結する

\(\omega\) が primitive \(p\)-th root と分かれば、

$$
\Phi_p(z,y) = \prod_{i=1}^{p-1}(z-\zeta^i y)
$$

のどの因子が \(q\)-進的に深くなるのか、という Kummer 型の見え方へ入れる。
いま見えている massive cancellation を、「たまたまの和」ではなく **円分核の因子構造の反映** として読む道が開く。
これは今の理論資産を一番よく活かす。

## 5. なぜ停止条件分析は後か

`BranchADescentStep` により

$$
s' < s,\qquad s' \equiv 1 \pmod p
$$

は出た。
じゃが、停止条件 \(s'=1\) を殴るには、まだ少し足りぬ。

なぜなら、`s'=1` に到達したとき

$$
x' = p t
$$

の形が見えても、それが **どのレベルで元の Branch A 反例構造と衝突するか** を、まだ fully bundled に言えておらぬからじゃ。
降下の strict decrease はもうある。
されど **terminal obstruction の明示** はまだ弱い。

だから順番としては、

1. \(\omega\) の位数構造を確定
2. その lift と valuation を強化
3. それを使って停止条件を刺す

の方が自然じゃ。

## 6. 具体的な次の定理候補

次に書くべき定理名の叩き台は、こんなところじゃ。

$$
\texttt{branchA\_omega\_pow\_eq\_one}
$$

$$
\texttt{branchA\_omega\_ne\_one}
$$

$$
\texttt{branchA\_omega\_order\_eq\_p}
$$

最初の 2 本が立てば、3 本目は `orderOf` につなぐ橋になる。
その次が

$$
\texttt{branchA\_omega\_hensel\_lift}
$$

あるいは

$$
\texttt{branchA\_qadic\_lift\_of\_omega}
$$

のような高次化じゃな。

## 7. FLT 証明への道の推論

したがって、いまの FLT Branch A 証明への道はこうじゃ。

まず、干渉縞 bundle から \(\omega\) を **非自明な \(p\)-th root of unity mod \(q\)** として確定する。
次に、その \(\omega\) を q-adic / Hensel 側へ持ち上げる。
その上で

$$
q^p \mid \bigl(y^{p-1}+p^3M\bigr),\qquad q \nmid y,\qquad q \nmid M
$$

という massive cancellation を、円分核の q-adic valuation として読み直す。
最後に、その rigid な valuation 構造と descent chain

$$
s \mapsto s' = s/q
$$

の strict decrease / invariant を噛み合わせて、有限降下の terminal case を潰す。
これがいま一番筋の通った道じゃ。

## 8. まとめ

ひとことで言えば、

$$
\boxed{
\text{まず } \omega^p=1,\ \omega\ne1 \text{ をやる。}
}
$$

これが次の最善手じゃ。
理由は、いまの bundle から最短で取れて、Hensel lifting と cyclotomic valuation の **両方の入口** になるからじゃ。

停止条件分析は、その次でよい。
いまは terminal case を殴るより先に、**干渉縞の中心にある root-of-unity 構造を確定する段** じゃよ。
