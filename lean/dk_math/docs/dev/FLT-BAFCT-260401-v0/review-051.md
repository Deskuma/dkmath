# review-051: `2m-global` の仮定を監査して、最後の open kernel が `2m-pure` だと特定できたことの意味

うむ。今回はかなり **重要な転換点** じゃ。
そして、ぬしの「ルートが変わって、ロードマップも変わってそう」という感覚は正しい。前回まで primitive 側の最終 open kernel は `2m-global` だと整理されておったが、今回の差分で **`2m-global` の結論は witness (R) に依存しておらぬ** と明示され、より鋭い R-free 版 `2m-pure` が切り出された。しかも `2m-pure → 2m-global → 無限降下法 → FLT` までの supply chain は Lean 上で通る形に固定された。つまり、primitive 側の open kernel 候補がさらに一段 sharpen された、ということじゃ。

## 1. いま何が変わったのか

前回までの整理では、primitive 側は

$$
\text{2m-global} \Rightarrow \text{PthRootCore} \Rightarrow \text{GNReducedGap} \Rightarrow \text{無限降下法}
$$

というルートが Lean 上で接続され、primitive 側に限れば open kernel は `2m-global` ただ 1 本、と読めるようになっておった。今回の差分は、その `2m-global` の仮定を監査して、「結論 (\exists g') は witness (R) を書き下していない」という事実を抽出し、さらに強い statement として `2m-pure` を導入したものじゃ。だから今回の前進は「別の橋が増えた」ではなく、 **open kernel の statement 自体を sharpen した** ところにある。

## 2. `2m-pure` の数学的意味

`2m-pure` の主張は、要するに

$$
\forall,\text{pack},\ \forall q,\ \bigl(q \mid x\bigr)
\Rightarrow
\exists g' \in \mathbb{N},\quad g' , GN(p,g',y) = (x/q)^p
$$

じゃ。
ここで大事なのは、**結論の側に (R) が全く出てこない** ことじゃな。実際、報告にもある通り、右辺 ((x/q)^p) は pack と (q \mid x) で決まり、左辺も (g') と (y) だけで決まる。だから「witness (R) があるとき存在する」より、「witness に触れずに存在する」の方が概念的には鋭い。今回の `2m-pure` は、その鋭さを formal に切り出したものじゃ。

さらに、宇宙式的に見れば

$$
g' , GN(p,g',y) = (x/q)^p
\quad\Longleftrightarrow\quad
(g'+y)^p = (x/q)^p + y^p
$$

じゃから、これはまさに **descent existence そのもの** じゃ。
つまり `2m-pure` は、q-adic witness の存在ではなく、「((x/q, y)) から smaller Fermat tuple が本当に存在するか」という、真に global な跳躍点をそのまま表しておる。ここはかなり本質的じゃよ。

## 3. ただし、ここは注意が要る

今回の報告の中で、一箇所だけ論理上の注意点がある。
表と履歴ではきちんと

* `2m-pure → 2m-global` は成立
* `2m-global → 2m-pure` は一般には不成立

と整理されておる。これは正しい。なぜなら `2m-global` は「witness (R) が与えられたとき (\exists g')」であり、`2m-pure` は「witness なしで (\exists g')」だから、後者の方が強いからじゃ。ところが、差分中の §20.1 コメントには一時的に「`2m-global ↔ 2m-pure` が自明」と読める記述が混ざっておる。これは theorem 群の実装内容とは食い違うので、 **コメント側の修正が必要** じゃ。コード上は `qAdicGapReductionGlobal_of_pure` の一方向しか入っておらず、その点は健全じゃ。

## 4. では、いまの本当の open kernel は何か

ここは二段に分けて言うのが正確じゃ。

第一に、**証明アーキテクチャとして FLT へ十分なのは `2m-global`** じゃ。
前回までに `2m-global → 無限降下法 → FLT` は concrete に接続済みで、primitive 側は `2m-global` が通れば落ちることが Lean で保証されておる。だから「最小十分条件」という意味では、まだ `2m-global` が主戦場じゃ。

第二に、**概念的により鋭い statement は `2m-pure`** じゃ。
`2m-global` は proof のための witness を仮定しておるが、`2m-pure` は existence 命題そのものをむき出しにする。だから「最後の真理形」に近いのは `2m-pure` と言える。今回の差分は、まさにこの distinction を見えるようにしたのじゃ。

言い換えると、

* **証明しやすい open kernel** は `2m-global`
* **意味的に鋭い open kernel** は `2m-pure`

じゃ。
この 2 つを混同せぬことが、今後かなり大事になる。

## 5. ロードマップはどう変わるか

ここが、ぬしの一番聞きたいところじゃろう。

前のロードマップは、

$$
\text{Level 1s} \to \text{2m-local} \to \text{2m-global}
$$

という、局所 witness を育てて global gap へ持ち込む流れが主軸じゃった。
それは今でも **証明ルート** としては有効じゃ。実際 `2m-global` さえ concrete 化されれば、無限降下法が回るところまで道はできておる。

しかし今回の差分で、**意味論ルート** が別に見えた。
すなわち、

$$
\text{2m-pure} \Rightarrow \text{2m-global} \Rightarrow \text{無限降下法} \Rightarrow \text{FLT}
$$

じゃ。
この意味で、新しいロードマップは 2 本立てになったと見るべきじゃ。

### A. 証明フレンドリー路線

`2m-global` を直接 concrete 化する。
witness (R) を proof data として持ち込み、その上で (g') を構成する。これは **constructive / q-adic 寄り** の道じゃ。

### B. 意味論フレンドリー路線

`2m-pure` を狙う。
witness を statement から消し、((x/q, y)) から smaller tuple が存在することを直接言う。これは **descent existence の本質をそのまま殴る** 道じゃ。

いまの段階では、わっちは **A を主ルート、B を副ルート** と見る。
理由は単純で、Lean 上で既に `2m-global` から先は concrete に閉じており、そこへ接続する具体物 (R) も `2m-local` から供給できるからじゃ。 `2m-pure` は美しいが、強すぎる主張ゆえに証明はむしろ難しくなる可能性がある。

## 6. ここから先、具体的に何をすべきか

ぬしが前に指摘した通り、「主戦場はここ」と言うだけでは足りぬ。
なので、次の 3 手を具体に書くぞい。

### 1. コメント修正

§20.1 の「`2m-global ↔ 2m-pure` が自明」と読める文は修正すべきじゃ。
定理として成立しているのは `2m-pure → 2m-global` だけで、逆向きは一般には false と整理するのが正しい。ここを放置すると、後の設計メモが混乱する。

### 2. `2m-global` の witness 依存性をさらに点検

今の `2m-global` の仮定のうち、

* 本当に (R) の詳細が必要なのか
* 実は (\sum R^i = 0) だけで足りるのか
* あるいは (z = Ry) だけでよいのか

を切り分ける。
ここで witness 仮定がさらに削れれば、`2m-global` は `2m-pure` に一歩近づく。

### 3. `2m-pure` の宇宙式同値を theorem 化

報告では comment レベルで

$$
g' , GN(p,g',y) = (x/q)^p
\quad\Longleftrightarrow\quad
(g'+y)^p = (x/q)^p + y^p
$$

と読んでおるが、これを formal に theorem 化すると、`2m-pure` が「smaller Fermat tuple existence」そのものだと明示できる。
これは今後、整数語彙と幾何語彙の橋として非常に強い。

## 7. 賢狼の率直な判断

だから、ぬしの問いに率直に答えるとこうじゃ。

**まだ閉じておらぬ。**
じゃが今は、「最後の敵が見えていない」のではない。
**最後の敵を、証明ルートでは `2m-global`、意味論ルートでは `2m-pure` と、二重に見分けられるようになった** のじゃ。これはかなり大きい前進じゃよ。

一言でまとめるなら、

**前のロードマップは `2m-global` が終点に見えていたが、今回の差分で `2m-pure` というより鋭い終点候補が現れた。ただし、実際に FLT を落とす主ルートとしては、まだ `2m-global` を concrete 化する方が筋が良い。**
