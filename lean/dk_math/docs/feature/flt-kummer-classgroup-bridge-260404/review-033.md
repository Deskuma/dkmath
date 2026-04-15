# review-033

うむ、これはかなり大きい前進じゃ。
**target 2 が埋まったことで、戦況は一段どころか二段くらい前へ進んだ** と見てよい。

いまの整理を率直に言えば、Stage 1 のうち「構造」と「分岐処理」の大半はもう終わっておる。前の段階で、`noPrimeOrY_of_firstCase_of_coprime` と `chosenLinearFactor_isCoprime_with_other_of_firstCase_of_pack` により、coprimality へ至る論理鎖そのものは、2 本の deep target を仮定すれば no-sorry で完成しておった。今回さらに `integerInZetaMinusOneIdealDivisibleByP_fill` が入り、target 2 である
$$
(n : \mathcal O_K)\in (\zeta-1)\ \Longrightarrow\ p \mid n
$$
が、norm を使う自力証明として実際に埋まった。つまり残る deep target は、もう
$$
\texttt{PrimeOverPEqualsZetaMinusOneTarget}
$$
ただ 1 本じゃ。

今回の意味は大きい。というのも、target 2 は「深い cyclotomic theory だから target のまま残るかもしれぬ」と見えていた場所じゃった。それが実際には、Mathlib の norm API を橋にして
$$
N(\zeta-1)=p,\qquad N(n)=n^{[K:\mathbf Q]}
$$
の線で押し切れた。これは単に 1 本 theorem が増えたというだけではない。**残る敵が “ramification の一点” にまで縮んだ** という意味を持つ。

戦況を軍略風に言えば、外堀と内堀はもう落ちておる。
共通 prime ideal \(P\) を仮定したときの分岐
$$
P \mid (p)\ \lor\ y \in P
$$
のうち、\(y\in P\) は以前に閉じ、今回で \(P\mid(p)\) 分岐に必要だった 2 本のうち 1 本も落ちた。だから今の本丸は、ほんに
$$
P \mid (p),\ P\ \text{prime},\ P\neq\bot
\ \Longrightarrow
P = (\zeta-1)
$$
という「\(p\) の上の prime ideal は \((\zeta-1)\) ただ一つ」という完全分岐の定式化だけじゃ。

ここでの注意点も、以前よりずっとはっきりした。
もう疑うべきは target 2 ではない。あれは埋まった。したがって、今後の論点は「target 1 が真か偽か」より、**今の形の target 1 が強すぎるか、あるいはそのまま狙ってよいか** じゃ。とはいえ、今回の差分で `PrimeOverPEqualsZetaMinusOneTarget` の向きを修正し、`zeta_sub_one_ideal_isPrime` まで mainline に入っておるので、完全に見当外れな target を追っている感じではない。むしろ「唯一の prime divisor」を ideal factorization / ramification で拾いに行く、かなり自然な最終局面に入ったと見るのが妥当じゃ。

わっちの見立てでは、次の戦略はこうじゃ。
まず、Stage 1 はもう「全体をまた組み直す」段ではない。**target 1 専用の攻城戦** に切り替えるべきじゃ。具体的には、\((p)\) の prime ideal factorization か、少なくとも「\((p)\) を割る prime ideal は \((\zeta-1)\) を含む」から等号へ落ちる短い補題列を探す。もし Mathlib 表面 API にそのまま無ければ、今回の target 2 と同じく、既存の部品をつないで自力で短い adapter を書くのが筋じゃ。いまはもう、それで十分届く位置におる。

ひとことで総括すると、

$$
\boxed{
\text{戦況は優勢。Stage 1 の残敵は deep target 2 本から 1 本へ減り、
いま本当に残っているのは ramification の一点だけ}
}
$$

じゃよ。
これはかなり良い戦果じゃ。
