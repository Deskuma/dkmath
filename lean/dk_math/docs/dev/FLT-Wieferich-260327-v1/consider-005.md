# consider: PrimeGe5BranchA の攻め筋について

うむ。わっちなら、 **いきなり packet を作りに行かず** 、まず

$$
\text{seed が packet へ昇格するために何が足りぬか}
$$

を、型で炙り出す攻め方をするのぅ。

いま確定しておるのは、`smaller packet` 全体が

$$
\texttt{valuation peel route} ;+; \texttt{primitive packet descent route}
$$

の二分岐で閉じること、そして valuation peel 側では既に

$$
p \mid t
;\Longrightarrow;
\exists t_1,B,;
t = p t_1,\quad
s^p = y^{p-1} + p^{2p-1}(t_1^p B)
$$

という **seed contract** まで concrete 化できておることじゃ。

## 1. . わっちの第一手

まずは valuation peel 側を主戦場にする。
理由は単純で、ここだけはもう「抽象論」ではなく、手で触れる seed があるからじゃ。

ただし、ここで大事なのは、

$$
(t_1,B)\ \text{から} \ (t',s',y',z')
$$

を **直接ひねり出そうとしない** ことじゃ。

なぜなら、いまの seed は

$$
s^p = y^{p-1} + p^{2p-1}(t_1^p B)
$$

という「head + tail」の形までは与えるが、
まだそれが

$$
GN\bigl(p,p^{p-1}t_1^p,y'\bigr)=p,{s'}^p
$$

という **宇宙式の canonical tail** と一致するとは言っておらぬ。
ここを飛ばして packet を書こうとすると、だいたい途中で嘘になる。

## 2. . だから、次に置くべき補題

わっちなら、まずこの中間補題を新設する。

### 2.1. . Canonical tail への整形補題

目標は、

$$
s^p = y^{p-1} + p^{2p-1}(t_1^p B)
$$

を、単なる seed ではなく

$$
s^p
===

\frac{1}{p},GN\bigl(p,p^{p-1}t_1^p,y\bigr)
;+;
\text{余剰項}
$$

の形に **正規分解** することじゃ。

つまり、(B) をそのまま眺めるのでなく、

$$
B = B_{\rm cosmic} + B_{\rm excess}
$$

と分けられるかを調べる。
もし (B_{\rm excess}=0) まで落ちれば、その時点で

$$
y' := y,\qquad
t' := t_1,\qquad
s' := s,\qquad
z' := y + p^{p-1} t_1^p
$$

がそのまま smaller packet 候補になる。

この見立てのよいところは、 **成功条件が明確** なことじゃ。
「packet が作れるか」ではなく、

$$
B \stackrel{?}{=} B_{\rm cosmic}
$$

を調べればよい。

## 3. . 第二手. 失敗したら不足情報を定理化する

もし上の整形で余剰項

$$
B_{\rm excess} \neq 0
$$

が残るなら、その時点で valuation peel seed だけでは足りぬことが分かる。
その場合は、そこで初めて contract を 1 本追加する。

わっちなら次はこう切る。

$$
\texttt{PrimeGe5BranchAValuationPeelCanonicalSeedTarget}
$$

として、

$$
p \mid t
\Longrightarrow
\exists t_1,;
t = p t_1
;\land;
GN\bigl(p,p^{p-1}t_1^p,y\bigr)=p,s^p
$$

あるいはそれに準ずる **canonical equality** を直接返す target を置く。
要するに、いまの seed は「因子がある」ことしか言わぬ。
packet 再構成に必要なのは「その tail が **まさに GN tail である** 」という情報じゃ。

ここを切り分ければ、valuation peel route の失敗理由も綺麗に見える。

## 4. . 第三手. valuation peel が無理なら、すぐ primitive 側へ寄る

そして、もし上の canonical 化が難航するなら、わっちは執着せぬ。
その場合は valuation peel は

$$
\text{余分な } p\text{-深さの検出器}
$$

として扱い、真の降下は primitive 側へ渡す。

workspace では既に

$$
\texttt{PrimeGe5BranchAPrimitivePacketDescentTarget}
$$

が分離されておるから、構造上は美しい。

つまり戦略はこうなる。

$$
p \mid t
\Rightarrow
\text{peel で canonical packet を狙う}
$$

これが無理なら

$$
p \nmid t
\ \text{または peel 不足}
\Rightarrow
\text{primitive packet descent へ送る}
$$

じゃ。

## 5. . もっと具体的に言うと、わっちは何を Lean に書くか

この順で書くのぅ。

### 5.1. . `GN/p` の tail 展開補題

$$
\frac{1}{p}GN\bigl(p,p^{p-1}u,y\bigr)
=====================================

y^{p-1} + p^{p-1}u\cdot C_p(u,y)
$$

型の補題を、まず **完全に explicit** にする。

### 5.2. . `u = t_1^p` 代入版

$$
\frac{1}{p}GN\bigl(p,p^{p-1}t_1^p,y\bigr)
=========================================

y^{p-1} + p^{p-1}t_1^p\cdot C_p(t_1,y)
$$

へ落とす。

### 5.3. . seed の (B) と (C_p) の比較補題

$$
s^p = y^{p-1}+p^{2p-1}t_1^p B
$$

と

$$
\frac{1}{p}GN\bigl(p,p^{p-1}t_1^p,y\bigr)
=========================================

y^{p-1}+p^{p-1}t_1^p C_p
$$

を比べて、

$$
C_p \stackrel{?}{=} p^p B
$$

が出るか、あるいは差が何かを明示する。

ここまで行けば、packet 再構成が可能か不可能かが **証明図式として** 見える。

## 6. . 率直な見立て

率直に言えば、わっちの勘では valuation peel だけでそのまま smaller packet が出る確率は、そこまで高くない。
なぜなら seed は「深さ」を返しておるが、packet に必要なのは「深さ」だけでなく **正しい宇宙式 tail の形** だからじゃ。

じゃが、だからこそ攻める価値がある。
ここを叩けば、

* そのまま packet が出る
* 出ないなら、何が足りないかが exact に見える

このどちらかになる。
研究では、こういう補題は大当たりか、良い失敗かのどちらかで、どちらでも得じゃ。

## 7. . まとめ

わっちなら、こう攻める。

$$
\boxed{
\text{valuation peel seed を、まず canonical cosmic tail に整形できるか調べる}
}
$$

できれば、そのまま smaller packet へ昇格。
できなければ、不足情報を新 contract に切り出し、primitive packet descent を本命へ押し上げる。

つまり、

$$
\text{seed} \to \text{canonical tail} \to \text{packet}
$$

をまず試し、無理なら

$$
\text{seed} \to \text{obstruction extraction} \to \text{primitive descent}
$$

へ切る。
これが、いまの workspace と宇宙式の骨格にいちばん噛み合う攻め筋じゃよ。
