# review-022: `rad(abc)` 直結 route の concrete sample を、`native_decide` 依存から一般補題へ置き換えて追加

うむ、これは **とても良い修正** じゃ。
前回わっちが述べた「sample 層の closed computation としての `native_decide` は許容できるが、再利用可能な部品に寄せられるならそのほうが美しい」という論点に対して、きれいに応えておる。今回の差分は、単に `native_decide` を消しただけではなく、`piSqRad 7 = 1` という局所事実を、一般補題 `piSqRad_eq_one_of_squarefree` の特殊例へ昇格させた。これは設計として一段上じゃ。

## 状況分析

今回の変化を大局で見ると、`ABC038BridgeExamples.lean` の concrete quality sample が、もう sample ファイル内の計算トリックに頼らず、`ABC016.lean` に置かれた **一般理論の補題** を参照して閉じるようになった、ということじゃ。
つまり、

* 前段の理論ファイルに一般補題を置く
* sample はその special case を読む

という、健全な依存方向に戻った。これは小さな差分に見えるが、プロジェクト全体の重心としてはかなり大事じゃ。sample が理論を支えるのでなく、理論が sample を支える形になったからの。

前回までの route はすでに

$$
\text{channelCount}
\to
\mathrm{rad}(c)\text{ budget}
\to
\mathrm{rad}(abc)\text{ analytic bridge}
\to
\text{quality}
$$

として動いておった。じゃが sample 中の `piSqRad_7_eq_one` だけが少し“閉じた計算”寄りだった。今回そこが一般補題に置き換わったことで、analytic 直結 route の concrete sample は、より素直に **ABC 側の理論補題の積み重ね** で読めるようになった。これは気持ちよく先へ進める、というお主の感覚で合っておる。

## 数学的解説

今回新設された補題

$$
\texttt{piSqRad\_eq\_one\_of\_squarefree}
$$

の中身は、とても自然じゃ。
squarefree な (n) に対して、まず既存補題から

$$
\mathrm{sqTail}(n)=1
$$

を得る。さらに別の既存補題で

$$
\mathrm{sqTail}(n)=\mathrm{piSqRad}(n)\cdot \mathrm{twoTail}(n)
$$

がある。これらを合わせると

$$
1=\mathrm{piSqRad}(n)\cdot \mathrm{twoTail}(n)
$$

となるから、(\mathrm{piSqRad}(n)) は 1 を割る。したがって

$$
\mathrm{piSqRad}(n)=1
$$

じゃ。
証明の流れとして実にまっすぐで、`piSqRad` の意味にも合っておる。squarefree なら「平方的な余剰部分」が無いのだから、(\pi)-側の寄与が 1 に潰れるのは自然じゃな。今回の証明は、その直感をきれいに Lean に写したものと見てよい。

しかも、この補題は sample 専用で終わらぬ。
今後もし squarefree な target (c) に対して `piSqRad c = 1` を読みたい場面が出れば、そのたびに局所計算を繰り返さずに済む。つまり今回の差分は、sample の掃除であると同時に、ABC 側語彙の小さな再利用部品を一つ増やした差分でもある。ここが良い。

## `native_decide` の件

ここもはっきり言うぞい。

前回の `native_decide` 使用は、**その局所用途に限れば十分正当化できた**。
なぜなら、

* 閉じた具体値 `7` に対する等式
* private lemma
* sample file 内限定
* build 成功済み

という条件だったからじゃ。論理的に危ない使い方ではなかった。

じゃが今回の修正後は、さらに一段良い状態になった。
もう `piSqRad 7 = 1` は「7 に対する計算結果」ではなく、

$$
\text{squarefree} \Rightarrow \pi\mathrm{SqRad}=1
$$

という一般命題の特殊例として読める。
これは数学的にも気分がよいし、将来の保守でも強い。ゆえに、**前回の `native_decide` は許容範囲、今回の置換は理想形に近い改善**、という評価になる。

## 何が前進したのか

今回の差分の価値は、「新しい route を増やした」ことではなく、**既に得た route の基礎を締め直した** ことじゃ。
特に concrete quality sample

$$
\mathrm{quality}(6,1,7)\le 2
$$

を読む流れが、これでより“本線の数学”だけで立つようになった。
今後 `ABC038` の convenience theorem 群へ差し込む段階では、こういう局所計算の残り香が少ないほどよい。だから今回の修正は、派手ではないが本当に価値がある。

## 最終判断

わっちの最終評価はこうじゃ。

* 前回の `native_decide` は、その場しのぎではなく局所用途としては妥当だった
* 今回の修正は、それを **一般補題へ昇格** させたので、明確に一段上の形になった
* 結果として `rad(abc)` 直結 route の concrete sample は、より理論的で再利用可能な部品群に支えられるようになった

ひとことで言えば、
**橋の石組みを、仮の足場からちゃんとした石材に置き換えた修正** じゃ。
これなら、本当に気持ちよく先へ進めるぞい。
