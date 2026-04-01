# review-018: `PthRootTarget` を `GNReducedGapTarget` に置き換えることの意味と今後の攻略

キタの。
これは **かなり美しい前進** じゃ。しかも、ただ橋が増えただけではなく、**open kernel の座標系そのものが project-native に置き換わった**。そこが大きい。

## 1. . 戦況分析

いまの戦況を一行で書けば、こうじゃ。

$$
\boxed{
\text{最後の門が } \texttt{PthRootTarget} \text{ から } \texttt{GNReducedGapTarget} \text{ へ移った}
}
$$

前段では open kernel は

$$
\exists z',\quad p^p (t s')^p + y^p = z'^p
$$

という **p 乗根の存在問題** として見えておった。
今回の差分で、それを

$$
\exists g',\quad g' \cdot GN_p(g',y) = p^p (t s')^p
$$

という **GN の一致問題** に翻訳した。しかもその翻訳が、Cosmic Formula の核恒等式

$$
(g'+y)^p = g' \cdot GN_p(g',y) + y^p
$$

そのもので支えられている。これは DkMath の家主が finally 本丸の門に出てきた、という意味じゃ。

## 2. . 何が勝ったのか

今回の勝ちは 3 つある。

### 2.1. open kernel の表現が project の言葉になった

`PthRootReducedTarget` は数学的には自然でも、まだ「根の存在」を問う顔をしておった。
それに対し `GNReducedGapTarget` は、

$$
\text{新しい gap } g'
\quad\text{と}\quad
\text{その Body } g' \cdot GN_p(g',y)
$$

を直接問う。
これは Cosmic Formula / GN / Beam / Tail の語彙そのものじゃ。よって今後の補題も project の既存資産をそのまま使いやすい。

### 2.2. 等価性が no-sorry で往復した

今回の実装で

* GNReducedGap \(\to\) PthRootReduced
* PthRootReduced \(\to\) GNReducedGap
* GNReducedGap \(\to\) PthRoot
* GNReducedGap \(\to\) RestoreFromArithmeticStrong 全 chain
* contradiction \(\to\) GNReducedGap

まで全部 no-sorry で通った。
つまり GN 形式は「別表現」ではなく、**mainline を背負える canonical form** になったということじゃ。

### 2.3. mainline と fallback の役割分担がさらに明瞭になった

いまは

$$
\texttt{GNReducedGapTarget}
\to
\texttt{PthRootReducedTarget}
\to
\texttt{PthRootTarget}\\
\to
\cdots
\to
\texttt{FringeDescentToRefuter}
$$

が **canonical GN mainline**、
一方で contradiction route は fallback/oracle として GN 側へも落とせる。
この分離は設計としてとても健全じゃ。

## 3. . 解説

なぜ GN が理想か。
それは今回の差分自身が示しておる。

`PthRootReducedTarget` は

$$
\exists z',\quad p^p (t s')^p + y^p = z'^p
$$

だった。
ここでは未知は (z') で、論理の顔つきは「ある冪和が完全 p 乗か」という classical descent / Kummer 的な顔になりやすい。

しかし `GNReducedGapTarget` にすると未知は (g' = z' - y) になり、

$$
g' \cdot GN_p(g',y)
$$

が reduced RHS と一致するか、という **差の冪の因数分解問題** になる。
これは

* cosmic_id_csr'
* GN の tail 構造
* q-adic valuation が GN 側へ集中する観測
* Beam / Gap / Body 分解

と自然につながる。
つまり、**p 乗根を直接取るのではなく、差の冪の構造を再構成する** 路線へ変わったのじゃ。
これが project-native という意味じゃよ。

## 4. . 現在の真の open kernel

いま genuine open kernel は、もうこれでよい。

$$
\boxed{
\exists g',\quad g' \cdot GN_p(g',y) = p^p (t s')^p
}
$$

ただし、ここで重要な留意点がある。
この kernel は「一般の GN 方程式を解け」という話ではない。
欲しいのは **today の Branch A descent data から生じる特殊形** に対する存在だけじゃ。
この限定があるから、full Kummer より GN/q-adic 特化 route がまだ現実的なんじゃ。

## 5. . 次の攻め

わっちなら、ここからは **GNReducedGapTarget をさらに 2 層に割る**。

### 5.1. 第一段. q-adic 剥離層

いま手元には

* (GN = p \cdot s^p)
* (s = q \cdot s')
* (q \nmid (z-y))

がある。
ゆえに (q^p) は GN 側から剥がれる。
ここでまず狙うべきは、

$$
GN_p(z-y,y) = p \cdot q^p \cdot s'^p
$$

から、**q^p を一段剥いだ新しい GN equation の候補** を書き出すことじゃ。
まだ (g') を existential にせず、

$$
\text{“もし新 gap } g' \text{ があるなら満たすべき q-adic 条件”}
$$

を補題として固定する。

### 5.2. 第二段. GN の局所存在層

次に、上の q-adic 条件を満たす (g') の存在を **一般 Hensel ではなく特殊形専用** に狙う。
つまり、

$$
F(g) := g \cdot GN_p(g,y) - p^p (t s')^p
$$

という関数を置き、

* (F(g_0) \equiv 0 \pmod{q})
* (F'(g_0) \not\equiv 0 \pmod{q})

型の局所存在を調べる。
ここで初めて Hensel 風の議論が出るが、対象は (F(g)) という **GN-native function** じゃ。
この順なら、Hensel は家主ではなく補助になる。

### 5.3. 第三段. GN mainline の正式固定

この段階で theorem 名や docstring でも、

$$
\texttt{GNReducedGapTarget}
$$

を「open kernel」「mainline entry」と明示しておくとよい。
今後の議論が 다시 p-th root 側へ戻りにくくなる。

## 6. . いまはやらなくてよいこと

* full (\mathbb{Z}[\zeta_p]) Kummer route へ飛ぶこと
* 一般 Hensel theorem のフル実装に突っ込むこと
* `PthRootTarget` を直接 mainline の家主に戻すこと

いまは GN が家主じゃ。
そこからはみ出すと、せっかく得た座標系がまた霞む。

## 7. . 総評

今回の差分は、わっちに言わせれば

$$
\boxed{
\text{“最後の門” を project の母語へ翻訳した勝利}
}
$$

じゃ。

前は「p 乗根があるか」という、少し借り物の顔をしておった。
今は違う。

$$
\boxed{
\text{新しい gap } g' \text{ があり、その Body が reduced RHS に一致するか}
}
$$

という、まさに DkMath らしい門になった。
この翻訳は強い。
次はこの GN-native kernel に対して、q-adic を **補助兵** として食わせる局面じゃよ。🍎
