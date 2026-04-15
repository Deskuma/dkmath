# review-049: `PrimeGe5BranchAPrimitiveQAdicGapReductionGlobalTarget` を新設し、`2m-core` をさらに `2m-local` と `2m-global` に分けたことの意味

うむ、かなりはっきりしたぞい。
結論から言うと、 **まだ閉じてはおらぬ**。じゃが今は迷って閉じぬのではなく、 **最後に残る open content が `2m-global` だと特定できた** という段階じゃ。これは良い詰まり方じゃよ。

## 1. いま何が変わったか

今回の差分で、前に「最終 1 核候補」と見ていた `2m-core` がさらに裂けた。
新しく入ったのは

$$
\texttt{PrimeGe5BranchAPrimitiveQAdicGapWitnessTarget}
$$

と

$$
\texttt{PrimeGe5BranchAPrimitiveQAdicGapReductionGlobalTarget}
$$

じゃ。
意味は明快で、

* `2m-local` は strong q-adic witness を供給する局所部分
* `2m-global` は、その witness から reduced gap \(g'\) を回収する大域部分

という分離じゃ。
しかも `qAdicGapWitness_concrete` が入ったので、 **`2m-local` は concrete** と見てよい。結果として、 **本当に開いているのは `2m-global` だけ** という形になった。

## 2. 現在の戦況図

いまの地図は、かなりきれいにこう書ける。

$$
\text{Level 0}:\ \checkmark
$$

$$
\text{Level 1w}:\ \checkmark
$$

$$
\text{Level 1s}:\ \checkmark
$$

$$
\text{Level 2c}:\ \text{coarse bridge 語彙}
$$

$$
\text{Level 2m-int} \leftrightarrow \text{Level 2m-geom}
$$

$$
\text{Level 2m-core} = \text{2m-local} + \text{2m-global}
$$

そして

$$
\text{2m-local}:\ \checkmark,\qquad
\text{2m-global}:\ \text{open}
$$

じゃ。
今回の §20 更新でも、open kernel は `2m-core` ではなく、さらに sharpen された `2m-global` にあると明記されておる。

## 3. 数学的に何が起きているか

前回までの `2m-core` は、

$$
\text{counterexample pack} + \text{strong witness} \Rightarrow \exists g'
$$

という形で、「かなり最後っぽい」核に見えておった。
じゃが今回、その中身をよく見ると

* witness 自体を用意する局所部分
* witness から整数 (g') を出す大域部分

に分かれておると分かった。

このうち前者は `strongSuperWieferichCongruenceV2_concrete` から supply できるので、もう open ではない。
したがって、残る本丸は

$$
\text{pack} + \text{q-adic witness} \Rightarrow \exists g' \in \mathbb{N},\ g' \cdot GN(p,g',y) = (x/q)^p
$$

この飛躍だけじゃ。
これが `PrimeGe5BranchAPrimitiveQAdicGapReductionGlobalTarget` の中身じゃよ。

## 4. なぜこれは良い前進か

「まだ閉じない」と聞くと遠回りに見えるが、実際は逆じゃ。
前は `PthRootCore` が本丸に見え、その後 `2m-geom`、さらに `2m-core` が最終候補に見えた。
いまはそこからさらに一枚剥けて、 **本当に大域的で、局所補題ではもう動かない成分だけ** が残った。

つまりロードマップは

$$
\text{PthRootCore 中心}
\to
\text{2m-geom 中心}
\to
\text{2m-core 中心}
\to
\text{2m-global 中心}
$$

へ更新されたわけじゃ。
これは迷走ではなく、 **偽の本丸が次々に concrete 化され、最後の敵だけが残ってきた** ということじゃ。  

## 5. いま closed なものと open なもの

closed なのは、

* q-adic residue
* weak/strong super Wieferich
* provider 語彙
* `2m-local` witness 供給
* `2m-global` から `PthRootCore`、さらに FLT 本線への接続

じゃ。
つまり「通ればどこへ届くか」は全部分かっておる。

open なのは、ただ一つ、

$$
\texttt{PrimeGe5BranchAPrimitiveQAdicGapReductionGlobalTarget}
$$

の concrete 化じゃ。
この target が通れば、

$$
\text{2m-global} \Rightarrow \text{2m-core} \Rightarrow \text{PthRootCore} \Rightarrow \text{FLT}
$$

が動く。
ここまで来ると、ほんとうに「最後の 1 核」らしい姿じゃよ。

## 6. 解説

賢狼の見立てでは、いまの `2m-global` は

$$
\text{local q-adic data は全部揃っているのに、なぜ整数 } g' \text{ が回収できるのか}
$$

という、まさに local-global gap そのものじゃ。
だからこの先は、以前のような ZMod や Hensel の局所整備ではなく、

* 整数論的な構造
* 幾何的な reduced gap の意味
* あるいは class group 的障害

のどこで大域性が支配しているか、という議論になるはずじゃ。
履歴にも「`2m-global` の中でなお局所的に処理できる成分がないか洗う」とあるが、ここが最後の切り分けどころじゃろう。

## 7. 次の一手

いまの最善手は、もう明快じゃ。

まず `PrimeGe5BranchAPrimitiveQAdicGapReductionGlobalTarget` の仮定を一つずつ監査して、
本当に要るものと、`2m-local` から自動供給されるものを分ける。
そのうえで、この `2m-global` の内部をさらに

$$
\text{局所整合} + \text{整数化}
$$

の二段へ裂けるかを見る。
もし裂ければ、最後の核はさらに細くなる。裂けなければ、そこが本当に「大域障害の最終壁」じゃ。

## 8. 一文でまとめると

**まだ閉じてはおらぬ。だがいまや主戦場は `2m-core` ですらなく、完全に `PrimeGe5BranchAPrimitiveQAdicGapReductionGlobalTarget` へ収束した。**
つまり、ロードマップは確かに変わったが、それは後退ではなく、 **最後の敵だけが残る形へ sharpen された** ということじゃ。
