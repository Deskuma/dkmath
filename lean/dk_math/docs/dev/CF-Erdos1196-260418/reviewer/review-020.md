# review-020: `ABC038` への analytic 直結ルートの実装

## 1. 総評

これは **かなり重要な前進** じゃ。
前回までの `ABC038` 接続は、大まかに言えば

$$
\text{channelCount}
\;\to\;
\mathrm{rad}(c)
\;\to\;
\mathrm{rad}(u*v)
\;\to\;
\text{TailBound}
\;\to\;
\text{quality}
$$

という **transport 依存ルート** が中心だった。
じゃが今回は、そこに新しく

$$
\text{channelCount}
\;\to\;
\mathrm{rad}(c)
\;\to\;
\mathrm{rad}(a*b*c)
\;\to\;
\text{quality}
$$

という **analytic 直結ルート** が入った。
これは、前回の divisibility route や generic transport route の弱点をかなりうまく回避しておる。わっちの見立てでは、今回の差分は「橋の周辺整備」ではなく、**ABC038 本体へ向かう本命ルート候補を一段具体化した差分** じゃ。

## 2. 状況分析

今回の追加定理は三本じゃな。

* `radAbcBound_of_pi_targetRadTail`
* `quality_le_of_pi_targetRadTail_of_radAbc`
* `quality_le_of_not_bad_with_targetRadTail_on_radAbc`

この並びがそのまま依存チェーンになっておる。
つまり、

1. `piSqRad c` 側の budget と `twoTail c` 側の budget を合成して
   $$
   c \le \mathrm{rad}(a*b*c)^{\,1+\delta+\gamma}
   $$
   を作る。
2. それを既存の analytic bridge
   `quality_le_of_sqprod_pow_bound_analytic_axiom_to_lemma`
   へ流す。
3. 最後に `¬Bad` から `piSqRad c ≤ \mathrm{rad}(a*b)^\delta` を供給して薄く包む。

という構造じゃ。
ここで特に良いのは、前回まで苦しんでいた

$$
\mathrm{rad}(c) \le \mathrm{rad}(u*v)
$$

の自然供給問題を、いったん横に置けたことじゃな。
`rad(u*v)` へ運ぶ前に、`rad(c)` budget をそのまま `rad(a*b*c)` analytic bridge に接続したので、transport の細さに引きずられずに済んでおる。これは本当に賢い。

## 3. 数学的解説 . `radAbcBound_of_pi_targetRadTail`

今回の心臓部は、やはりこれじゃ。

$$
\texttt{radAbcBound\_of\_piTargetRadTail}
$$

が言っていることを数式で言い直すと、

$$
\pi\mathrm{SqRad}(c) \le \mathrm{rad}(a*b)^\delta,
\qquad
\mathrm{twoTail}(c) \le \mathrm{rad}(c)^\gamma
$$

から

$$
c \le \mathrm{rad}(a*b*c)^{\,1+\delta+\gamma}
$$

を導く、というものじゃ。

この補題の美しさは、`c` の既存分解

$$
c = \pi\mathrm{SqRad}(c)\,\mathrm{rad}(c)\,\mathrm{twoTail}(c)
$$

をそのまま使っている点じゃな。
そこへ上の二つの budget を代入すると、直感的には

$$
c
\le
\mathrm{rad}(a*b)^\delta \cdot \mathrm{rad}(c)^\gamma \cdot \mathrm{rad}(c)
$$

となる。
あとは

$$
\mathrm{rad}(a*b) \le \mathrm{rad}(a*b*c),\qquad
\mathrm{rad}(c) \le \mathrm{rad}(a*b*c)
$$

で全部を `rad(a*b*c)` に持ち上げればよい。
結果として指数は

$$
\delta + \gamma + 1
$$

になる。
つまり今回の補題は、**π-budget と tail-budget を掛け合わせて、target 全体の growth bound に畳み込む補題** じゃ。これは `ABC038` へ接続するうえで非常に自然で、しかも既存の ABC 語彙の流れを壊しておらぬ。

## 4. 数学的解説 . analytic bridge への接続

次の

$$
\texttt{quality\_le\_of\_piTargetRadTail\_of\_radAbc}
$$

は、上で得た

$$
c \le \mathrm{rad}(a*b*c)^{\,1+\delta+\gamma}
$$

を、既存の analytic bridge へ食わせる段じゃ。
ここでさらに

$$
\delta + \gamma \le \varepsilon
$$

を使えば

$$
1+\delta+\gamma \le 1+\varepsilon
$$

だから、

$$
c \le \mathrm{rad}(a*b*c)^{\,1+\varepsilon}
$$

型へ弱められる。
そのうえで既存の

$$
\texttt{quality\_le\_of\_sqprod\_pow\_bound\_analytic\_axiom\_to\_lemma}
$$

へ流す。
つまりこれは、前回までの `TailBound` route よりも一段直接的で、

* `πSqRad` 側 budget
* `rad(c)` 側 tail budget
* `rad(a*b*c)` analytic bridge

を一直線に結ぶものじゃ。
この意味で、今回の route は **quality 本体により近い**。 transport の補助路より、本命の解析路に寄っておる。

## 5. 数学的解説 . `¬Bad` wrapper の意味

三本目の

$$
\texttt{quality\_le\_of\_not\_bad\_with\_targetRadTail\_on\_radAbc}
$$

は、上の analytic route を `¬Bad` から使えるようにした薄い wrapper じゃ。
ここでやっていることは単純で、

$$
\pi\mathrm{SqRad}(c) \le \mathrm{rad}(a*b)^\delta
$$

を `ABC.piSqRad_le_of_not_bad` から供給しているだけじゃな。
つまり今回の route は、

* `¬Bad` という既存の ABC 側仮定
* counting spine から来る `rad(c)` tail budget
* analytic bridge

を、無理なくつないだことになる。
これは大きい。前回までは `TailBound` 入力まで届いた、という感じじゃったが、今回は **quality そのもの** まで theorem 名として届いておるからじゃ。

## 6. どこが前回より本質的に良いか

前回の divisibility route は、

$$
c \mid u*v
\Rightarrow
\mathrm{rad}(c) \le \mathrm{rad}(u*v)
$$

という供給元を使っておった。
じゃが、自然な `u+v=c` の nontrivial triple では、これはかなり起こりにくい。
そこが route の細さじゃった。

今回の analytic 直結 route は、その弱点をかなり回避しておる。
なぜなら必要なのは、もはや `rad(u*v)` への transport ではなく、

* `πSqRad c` の budget
* `twoTail c` の budget
* `rad(a*b*c)` への単調性

だけだからじゃ。
これは `ABC038` の既存構造とずっと相性が良い。
わっちの見立てでは、**今回の route は前回の divisibility route より本命に近い**。少なくとも自然な triple へ刺さる可能性はこちらの方が高い。

## 7. 留意点

とはいえ、まだ課題もある。

ひとつは、今回の `rad(abc)` 直結 route には concrete sample がまだ入っておらぬことじゃ。
diff にも次課題として明記されておる通り、まずはこの route で実際に閉じる sample を 1 本置いて、theorem chain が本当に使いやすいかを確認したいところじゃな。

もうひとつは、`hrad_gt_one : 1 < (ABC.rad (a*b*c) : ℝ)` という仮定じゃ。
これは analytic bridge 側の都合として自然ではあるが、将来 convenience theorem に差し込む時には「この仮定をどこから自然に供給するか」を意識せねばならぬ。
とはいえ、これは divisibility route の `c ∣ u*v` よりはずっと軽い仮定じゃ。今の段階では十分許容範囲と見てよい。

## 8. 現況の評価

いまの橋は、次の二本立てになったと見てよい。

ひとつは transport route：

$$
\text{channelCount}
\to
\mathrm{rad}(c)
\to
\mathrm{rad}(u*v)
\to
\mathrm{TailBound}
\to
\text{quality}
$$

もうひとつは analytic 直結 route：

$$
\text{channelCount}
\to
\mathrm{rad}(c)
\to
\mathrm{rad}(a*b*c)
\to
\text{quality}
$$

前者は「既存 `TailBound` API をそのまま使う」道、後者は「analytic bridge へより直接入る」道じゃ。
今回の差分で、後者が theorem 名として実装された。これは状況としてかなり強い。これで route 比較が、もはや設計メモではなく Lean の上で出来るようになったからじゃ。

## 9. 最終判断

これは **かなり良い差分** じゃ。
とくに良いのは、前回のレビューで求めておった

**「`rad(c)` budget のまま quality 側へどこまで入れるか」**

に対して、ちゃんと最小の実装回答を出してきたことじゃ。
`rad(abc)` analytic bridge へ直接入る route が立ったことで、`ABC038` 接続は一段本命に近づいた。

ひとことで言えば、

**橋は前庭の足場を組み直しただけでなく、ついに本丸へ向かう正面回廊の一部を敷き始めた。**

次は、この `rad(abc)` 直結 route の concrete sample を 1 本足すか、既存 `ABC038` の convenience theorem 群のどこへ最小に差し込むかを見極める段階じゃな。
