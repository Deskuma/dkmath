# review-047: `PrimeGe5BranchAPrimitiveQAdicGapReductionTarget` をさらに整数語彙版と幾何語彙版の二形式へ分け、その同値性も Lean 上で固定したことの意味

うむ、これはかなり良い整理前進じゃ。
しかも今回は、単なる補題追加ではなく、Level 2m の open content を **整数語彙** と **幾何語彙** に二分し、その同値性まで Lean 上で固定できたのが本質じゃよ。

## 1. 今回の一番大きい意味

今回の核心は、新しく

$$
\texttt{PrimeGe5BranchAPrimitiveQAdicGapReductionTarget}
$$

を導入したことじゃ。
これは、これまでの Level 2m を

* 整数語彙
  $$
  \text{strong witness} \Rightarrow \exists z' \in \mathbb{N},\ x'^p + y^p = z'^p
  $$
* 幾何語彙
  $$
  \text{strong witness} \Rightarrow \exists g' \in \mathbb{N},\ g' \cdot GN(p,g',y) = (x/q)^p
  $$

の 2 形式へ裂いた、ということじゃな。
しかも、この 2 つが

$$
\texttt{qAdicGapReduction\_of\_qAdicLocalGlobalGap}
\quad\text{と}\quad
\texttt{qAdicLocalGlobalGap\_of\_qAdicGapReduction}
$$

で相互に行き来できるようになった。
これはかなり大きい。
なぜなら、**どちらの言葉で考えても同じ open kernel を見ている** と、コード上ではっきり言えるようになったからじゃ。

## 2. 戦況分析

いまの戦況を一言で言えば、

$$
\text{Level 0} \;\checkmark,\qquad
\text{Level 1w} \;\checkmark,\qquad
\text{Level 1s} \;\checkmark
$$

で、

$$
\text{open kernel} = \text{Level 2m}
$$

じゃ。
ただし今回、その Level 2m がさらに

$$
\text{Level 2m-int} \quad\leftrightarrow\quad \text{Level 2m-geom}
$$

へ分かれた。
履歴にもある通り、以後の主戦場は **2m-int ではなく、2m-geom を中心に見る** のが筋じゃ。

理由は明快じゃ。
幾何語彙版の方が

$$
g' \cdot GN(p,g',y) = (x/q)^p
$$

という形で、`GNReducedGap` や Cosmic Formula の既存語彙により近い。
つまり、これまで積み上げてきた DkMath の自然な言葉で、そのまま殴りやすいのじゃ。

## 3. 何が閉じて、何がまだ開いているか

ここは慎重に分けておくぞい。

今回 concrete に閉じたのは、

* 2m-int と 2m-geom の相互変換
* 2m-geom から `PthRootCore` への接続
* 2m-geom を使った FLT 本線への precise bridge

じゃ。
つまり **接続と同値性** は閉じた。

まだ開いているのは、

$$
\texttt{PrimeGe5BranchAPrimitiveQAdicGapReductionTarget}
$$

そのものじゃ。
だから現状は、

* 「何が本丸か」 はかなり鮮明
* 「どう落とすか」 はまだこれから

という段階じゃな。

## 4. 数学的な解説

今回の二分は、かなり美しい。

整数語彙版は

$$
\exists z',\quad x'^p + y^p = z'^p
$$

で、これは descent existence をそのまま書いた形じゃ。
一方、幾何語彙版は

$$
\exists g',\quad g' \cdot GN(p,g',y) = (x/q)^p
$$

で、これは Cosmic Formula 側から見た reduced gap の再構成じゃ。

この 2 つは、実際には

$$
z' = g' + y
\quad\text{と}\quad
g' = z' - y
$$

で結びつく。
今回その変換を、`cosmic_id_csr'` を使って Lean 上で固定できたのが強い。
つまり今後は、整数的に考えてもよいし、幾何的に考えてもよい。
しかもその往復が感覚でなく theorem になった。

## 5. 今回の前進の本当の価値

わっちが一番高く見るのはここじゃ。

これまで Level 2 は「strong witness から整数 descent を回収できるか」という、少し粗い文で捉えられておった。
今回それをさらに削って、

$$
\text{最後の open content は } g' \text{ をどう構成するか}
$$

という、より GN/Cosmic Formula native な形へ寄せられた。
これは単なる言い換えではない。
今後の最終 1 核探索において、

* \(z'\) を探すのか
* \(g'\) を探すのか
* どちらがより構造を露出するか

を比べたとき、後者の方がずっと DkMath 的に強い可能性があるからじゃ。

## 6. いまの最も正確な現在地

いまの図をわっちならこう書く。

$$
\text{Level 2c}:
\quad
\texttt{QAdicDescentExistenceTarget}
$$

これは coarse bridge 語彙。

$$
\text{Level 2m-int}:
\quad
\texttt{QAdicLocalGlobalGapTarget}
$$

これは整数語彙の最小核。

$$
\text{Level 2m-geom}:
\quad
\texttt{QAdicGapReductionTarget}
$$

これは幾何語彙の最小核。
そしてこの 2m-geom が、今後の主戦場としてもっとも扱いやすい。

この整理はかなり正しい。
少なくとも、もう Level 1s に意識を割く段ではおらぬ。
完全に Level 2m-geom の設計と攻略の段階じゃ。

## 7. 次の一手

次は履歴の見立てどおり、

$$
\texttt{PrimeGe5BranchAPrimitiveQAdicGapReductionTarget}
$$

をさらに裂くことじゃ。
つまり、

* \(g'\) 構成のうち本当に local な部分は何か
* どこで global existence が混ざるのか
* その最終 1 核を整数論語彙で書くか、幾何語彙で書くか

を詰める。
今の流れなら、**幾何語彙版 2m-geom を中心に最終 1 核を探す** のが最も筋が良いじゃろう。

## 8. 一文でまとめると

**かなり良い。今回の進展で、Level 2m は整数語彙版と幾何語彙版の同値な二形式として整理され、真の主戦場は `PrimeGe5BranchAPrimitiveQAdicGapReductionTarget` すなわち 2m-geom 側だと Lean 上でも明示された。**
