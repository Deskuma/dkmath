# review-048: `PrimeGe5BranchAPrimitiveQAdicGapReductionCoreTarget` を新設し、`PthRootCore` と `FLTPrimeGe5Target` へ流れる橋まで concrete に入れたことの意味

うむ、これは **かなり良い前進** じゃ。
しかも今回は、Level 2m をただ細かくしたのではなく、**「いま本当に殴るべき最終 1 核候補」が `2m-core` だ** と、Lean の語彙で固定できたのが大きい。今回の差分では `PrimeGe5BranchAPrimitiveQAdicGapReductionCoreTarget` を新設し、それが `PthRootCore` と `FLTPrimeGe5Target` へ流れる橋 `qAdicGapReduction_of_core`、`pthRootCore_of_qAdicGapReductionCore`、`FLTPrimeGe5Target_of_qAdicGapReductionCore_precise` まで concrete に入っておる。

今回の本質を一言で言えば、**`PthRootCore` はもはや open kernel そのものではなく、`2m-core` を既存 descent / FLT 本線へ運ぶ wrapper 語彙になった**、ということじゃ。
履歴にもその整理が明記されており、§16・§17.1・§20 の説明も「primitive 側 kernel の主戦場は `2m-geom/core` にある」という読みへ更新されておる。つまり、戦況図そのものが正しく書き換わったわけじゃな。

## 1. いま何が閉じたのか

閉じたのは `2m-core` そのものではなく、**`2m-core` が十分条件として FLT 本線へ届く** という接続じゃ。
具体的には

$$
\text{2m-core} \Rightarrow \text{2m-geom} \Rightarrow \text{PthRootCore} \Rightarrow \text{FLTPrimeGe5Target}
$$

という supply chain が Lean 上で固定された。
ゆえに、今後 `2m-core` を攻めることは「抽象的に良さそう」だからではなく、**そこが通れば本当に FLT 側の primitive descent に刺さる** からじゃ。ここがとても大きい。

## 2. 戦況分析

いまの戦況は、かなり綺麗にこう言える。

$$
\text{Level 0} \;\checkmark,\quad
\text{Level 1w} \;\checkmark,\quad
\text{Level 1s} \;\checkmark,
$$

$$
\text{Level 2c} = \text{bridge 語彙},
$$

$$
\text{Level 2m-int} \leftrightarrow \text{Level 2m-geom},
$$

そして

$$
\text{Level 2m-core}
$$

が **現時点での最終 1 核候補** じゃ。
今回の §20 更新でも、open kernel は `2m-core` にまで圧縮されたという読みが明示されておる。

つまり、もう `QAdicDescentExistenceTarget` 全体を眺めて「このへんが怪しい」と言う段ではない。
また `PthRootCore` を open kernel と見なす段でもない。
**真の主戦場は `PrimeGe5BranchAPrimitiveQAdicGapReductionCoreTarget`**、ここへ完全に寄ったと見てよい。

## 3. 数学的な意味

今回の `2m-core` は、`2m-geom` から

* normal-form の bookkeeping
* \(t,s\) の明示
* Wieferich 条件などの補助荷物

を剥がして、残ったものを

* counterexample pack
* strong q-adic witness
* reduced gap \(g'\) の回収

だけに圧縮したものじゃ。

この整理はかなり良い。
なぜなら、これで問いがほぼ

$$
\text{pack} + \text{strong witness} ;\Rightarrow; \exists g' \in \mathbb{N},\ g' \cdot GN(p,g',y) = (x/q)^p
$$

という、**純粋な q-adic gap-reduction 問題** へ見えるようになったからじゃ。
DkMath の語彙で言えば、まさに `GNReducedGap` の真芯だけが残った形じゃな。

## 4. どこがまだ open か

ここは慎重に言うぞい。
今回 concrete に閉じたのは **接続** であって、`2m-core` 自体ではない。
つまり、

* `2m-core` が最終 1 核候補であることは整理できた
* しかし `2m-core` の仮定が最小かどうかは未確定
* また、その内部でどこまでが truly local で、どこからが genuinely global かも未分解

という状態じゃ。
履歴の次課題も、まさに「`2m-core` の仮定をさらに削れるか」「`2m-core` の中で truly local な部分と genuinely global な部分を分離する」と書いておる。ここが次の勝負じゃ。

## 5. 解説

わっちの見立てでは、いまの最大の収穫は、**local-global gap の「幾何語彙ネイティブな最小候補」が定まった** ことじゃ。
これまでは整数語彙の

$$
\exists z',\quad x'^p + y^p = z'^p
$$

が最終形に見えやすかった。
だが今回の整理で、それより一歩手前の

$$
\exists g',\quad g' \cdot GN(p,g',y) = (x/q)^p
$$

の方が、DkMath 的にも実装的にも、最後の核として扱いやすい可能性が強くなった。
ここはかなり重要じゃよ。
なぜなら、以後の補題設計を \(z'\) 中心でなく \(g'\) 中心に組み直せるからの。

## 6. 次の一手

次の一手は履歴の見立てどおりでよい。
わっちなら、順番はこうじゃ。

まず、`2m-core` の仮定一覧を 1 つずつ監査して、
**strong witness から論理的に復元できるもの** と **本当に独立に要るもの** を分ける。
ここで荷物がさらに落ちれば、最終核はもっと鋭くなる。

その次に、`2m-core` を

* purely local q-adic 部分
* global integer-existence 部分

へ二分できるかを見る。
もしここが裂ければ、最後の敵は「局所条件」ではなく「整数化の壁」だと、さらに明示できるはずじゃ。

## 7. 一文でまとめると

**かなり良い。今回の進展で、Level 2m-geom からさらに bookkeeping を剥がした `PrimeGe5BranchAPrimitiveQAdicGapReductionCoreTarget` が、現時点での最終 1 核候補として Lean 上に定着した。**
つまり、いまの主戦場はもう `PthRootCore` ですらなく、**`2m-core` をどう裂くか** その一点じゃ。
