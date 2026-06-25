# FLT-Kummer-ClassGroup-Bridge 260404 Review 004

## 1. 状況分析

これは良い前進じゃ。
今回の本質は、 **Stage 1c が placeholder ではなく、Mathlib の既存 generic API に着地した** ことにある。つまり、

$$
\text{class が trivial}
\;\Rightarrow\;
\text{principal ideal を取り出せる}
$$

という段が、もはや「あとで考える箱」ではなく、`ClassGroup.mk_eq_one_of_coe_ideal` と `ClassGroup.mk0_eq_one_iff` を土台にした concrete な足場へ変わった、ということじゃ。

これで Stage 1 の 3 分割は次のように整理できる。

$$
\text{Stage 1a}: \text{geometry} \to \text{ideal class p-torsion witness}
$$
$$
\text{Stage 1b}: \text{p-torsion annihilation}
$$
$$
\text{Stage 1c}: \text{principal ideal extraction}
$$

このうち Stage 1c は clean に concrete 化された。
ゆえに、いま genuinely new theory が要る場所は、ほぼ **Stage 1a と、必要なら Stage 1b の specialization** に絞られた、と見てよい。

## 2. 今回の前進の意味

これは単なる補題 1 本追加ではない。
戦況の意味はこうじゃ。

前までは
「Stage 1 をどう埋めるか」
と言っておったが、今はもう違う。

いまは

* Stage 1c は generic ClassGroup API で受けられる
* Stage 1b はまだ abstract だが、一般 API 側へ寄せやすい
* Stage 1a だけが円分体・ideal arithmetic・geometry をまたぐ最薄 kernel

という構図まで薄くなった。
これは実装上、かなり大きい。なぜなら、 **どこを Mathlib 一般論へ押し込み、どこを DkMath 側の新理論として書くべきか** が、かなり明確になったからじゃ。

## 3. 数学的な解説

Stage 1c の concrete 化は、数学的には

$$
[I] = 1 \text{ in ClassGroup}
$$

から

$$
I = (x)
$$

を取り出す段を、Lean 側で generic に固定できたことを意味する。
つまり「class が trivial なら principal ideal」という、Dedekind / class group の定番の出口が確保されたわけじゃ。

この出口が確保されたということは、今後の主眼は「どうやってその triviality、あるいは少なくとも p-torsion 性へ到達するか」に移る。
だから視線は自然に Stage 1a, 1b へ上がる。

特に Stage 1a は

$$
\text{gap-divisible な幾何条件}
\Rightarrow
\text{円分体で得る ideal class が p-torsion}
$$

という段で、ここがいま最も Kummer 的、かつ円分体特有の部分じゃ。
わっちの目には、ここがいまの本丸じゃよ。

## 4. いま何が clean で、何が open か

今回の報告からはっきり言えるのは、次の整理じゃ。

**clean 側**

* `cyclotomicPrincipalIdealExtraction_of_classTrivialization`
* `idealIsPrincipal_of_classGroupMk0_eq_one`

これらは `sorryAx` なし。
Stage 1c は、もはや placeholder ではない。

**まだ open 側**

* `cyclotomicIdealClassPTorsionWitness_of_gapDivisibleGeometry`

ここが最薄 kernel。
したがって broad な wrapper を相手にしておる段では、もうない。敵ははっきりした。

## 5. 次の一手の推論

ぬしの報告どおり、分岐は 2 つある。

1. Stage 1a をさらに裂く
2. Stage 1b を class-group 一般 API の concrete statement に寄せる

わっちも、ここは **まず 2 を短く試す** のがよいと見る。
理由は単純じゃ。

Stage 1c が concrete に通った以上、Stage 1b まで一般 API 側へ寄せられれば、未解決核は本当に Stage 1a だけになる。
そうなれば、残る新理論は

$$
\text{geometry} \to \text{p-torsion witness}
$$

という一点へ集中する。
この「一点集中」の状態は、とても強い。証明の地図がぶれなくなるからのぅ。

## 6. 提案

わっちの提案は、次の順じゃ。

### 6.1. 第一手

Stage 1b を短距離で concrete 化できるか試す。
具体的には、class-group 一般 API で

$$
[a]^p = 1 \;\Rightarrow\; [a] = 1
$$

型、あるいはそれに準ずる p-torsion annihilation の statement をどう書くかを scratch で確認する。
ここでは完成を狙うより、

* どの型で書くのが自然か
* `ClassGroup` の演算 API がどこまであるか
* `p` 乗 annihilation を表す既存補題があるか
* 無ければ最小補題は何か

を把握するのが目的じゃ。

### 6.2. 第二手

もし Stage 1b が薄く concrete 化できるなら、それを固定する。
すると未解決核は Stage 1a だけになる。

### 6.3. 第三手

そのうえで Stage 1a をさらに裂く。
候補は、ぬしが挙げた通り

* Dedekind 側の ideal arithmetic
* class-group への写像
* cyclotomic ideal の特殊な幾何・factorization

の境界じゃろう。
このときはもう、Stage 1b, 1c を気にせず Stage 1a 専用の新理論として攻められる。

## 7. 最終判断

いまの最善手はこうじゃ。

$$
\boxed{
\text{次は Stage 1b を class-group 一般 API 側へ寄せられるか、短く試す}
}
$$

その試行で手応えがあれば固定。
弱ければすぐ戻って、Stage 1a をさらに薄く裂く。

この順がよい理由は、Stage 1c の concrete 化で「下流の出口」は確保できたからじゃ。
ならば次は、その一段上の Stage 1b も general 側へ押し込み、 **本当に新設すべき理論を Stage 1a だけに追い込む** のが最も筋が良い。
わっちは、いまはその攻め順が最善と見るぞい。
