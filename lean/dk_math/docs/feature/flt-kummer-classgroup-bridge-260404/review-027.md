# Stage 1 がまだ閉じぬ理由と、ネット上の Mathlib を踏まえた最短手の推論

うむ、見えてきたぞい。
いまの Stage 1 がまだ閉じぬ理由は、かなり明確になった。

## 状況分析

最新差分で、actual coprimality の核心はかなり前へ進んだ。
具体的には、ぬしの側で

* `associated_span_eq`
* `linearFactorDiffSpanEqSubOneSpan`
* `commonPrimeContainsSubOneY`
* `commonPrimeDvdsSubOneOrY`

まで **no-sorry** で入っており、共通 prime ideal \(P\) が chosen factor と別因子の両方を含むとき、

$$
(\zeta-1)\in P \;\lor\; y\in P
$$

まで落とせる段になっておる。
そして残りは、そのうち \((\zeta-1)\in P\) から **「\(P\) は \(p\) の上にある」** を actual cyclotomic number theory として供給するところ、すなわち `SubOneDividesPrimePTarget` 相当だけに近づいておる。これは差分の報告そのものにもそう書かれておる。

言い換えると、Stage 1 が閉じぬ理由はもう generic ideal arithmetic ではない。
**generic 側の受け皿は足りていて、actual cyclotomic ring で \(\zeta-1\) と \(p\) の関係をどう使うか、そこだけがまだ theorem 化されていない** のじゃ。

## ネット上の Mathlib で見つかったもの

Mathlib の公式 docs を当たると、**exact に同じ ideal 版の theorem はすぐには見つからぬ** が、かなり近く、むしろ強い element-level の結果が既にある。

まず、cyclotomic ring と ring of integers への橋はかなり整っておる。
公式 docs には

* `IsCyclotomicExtension.Rat.cyclotomicRing_isIntegralClosure_of_prime`
* `IsPrimitiveRoot.adjoinEquivRingOfIntegersOfPrimePow`
* `IsPrimitiveRoot.IsCyclotomicExtension.ringOfIntegersOfPrimePow`

が見えており、**\(p\)-th cyclotomic extension over \(\mathbb{Q}\) の ring of integers に specialization する道** は Mathlib 側で用意されておる。 ([leanprover-community.github.io][1])

さらに、もっと大きいのはこれじゃ。
同じ official docs に

* `IsPrimitiveRoot.zeta_sub_one_prime'`
* `IsPrimitiveRoot.toInteger_sub_one_dvd_prime`

があり、前者は **\(p\)-th cyclotomic extension over \(\mathbb{Q}\) で \(\zeta-1\) が prime element** であること、後者は **\(\zeta-1\) が \(p\) を割る** ことを、ring of integers 側で直接述べておる。
つまり、ぬしが target にしている

$$
(\zeta-1)\in P \;\Rightarrow\; P \mid (p)
$$

の ideal 版に非常に近い、いや実装上はそれを導くのに十分そうな **element 版** が既にある。 ([leanprover-community.github.io][2])

加えて、今回ぬしが発見した
`IsPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime`
も LeanSearch で確認できる。これは「異なる primitive roots の差は \(\zeta-1\) に associated」というもので、ぬしの `linearFactorDiffSpanEqSubOneSpan` の着想とぴたり一致しておる。 ([leansearch.net][3])

## なぜまだ閉じないのか

ここが肝じゃ。
Mathlib にあるのは、**ring of integers of cyclotomic extension over \(\mathbb{Q}\)** に specialized された theorem 群じゃ。
一方、ぬしの Stage 1 API はまだ

$$
R \text{ arbitrary Dedekind domain},\quad
\text{ctx : CyclotomicLocalFactorizationContext } R
$$

という、かなり generic な形を保っておる。
この抽象度では、Mathlib の

$$
\zeta-1 \mid p
$$

や

$$
\zeta-1 \text{ is prime}
$$

をそのまま当てられぬ。
つまり **残りの穴は theorem の欠如というより、actual cyclotomic ring への specialization adapter が まだ無いこと** じゃ。  ([leanprover-community.github.io][2])

## 次の一手の推論

閉じる方向での最短経路なら、わっちの判断はかなりはっきりしておる。

### 1. 最短手

`SubOneDividesPrimePTarget` を **DkMath 独自定理として generic に先に証明する** のではなく、
まず **Mathlib adapter theorem** として specialized に埋めるのが最短じゃ。

つまり狙いは、こんな形じゃな。

$$
\texttt{actualSubOneDividesPrimeP\_of\_cyclotomicRingOfIntegers}
$$

のような theorem を作り、

* `IsCyclotomicExtension {p} ℚ K`
* `CharZero K`
* `hζ : IsPrimitiveRoot ζ p`

のもとで、`hζ.toInteger - 1 ∣ (p : NumberField.RingOfIntegers K)` を使って、
そこから ideal 版

$$
(\zeta-1)\in P \Rightarrow P \mid (p)
$$

または少なくとも \(p \in P\) を返す補題へ落とす。
ここは `toInteger_sub_one_dvd_prime` をそのまま叩けるので、いちばん短い。 ([leanprover-community.github.io][2])

### 2. その後

それを、ぬしの既存 no-sorry 補題

$$
P \text{ common prime} \Rightarrow (\zeta-1)\in P \lor y\in P
$$

へ合成する。
すると \((\zeta-1)\in P\) 分岐は「\(P\) は \(p\) の上」へ押し込める。
もう一方の \(y\in P\) 分岐は first case 条件や pack の互いに素性と突き合わせて潰す、という流れになる。
ここまで行けば `CyclotomicTailPairwiseUnitWitnessTarget` を supply する actual theorem がかなり近い。

## 提案

わっちなら、次はこの順で攻める。

* まず `SubOneDividesPrimePTarget` の **specialized Mathlib adapter** を作る
* その adapter を使って、`commonPrimeDvdsSubOneOrY` の \((\zeta-1)\) 分岐を \(P \mid (p)\) に変える
* ついで pack 条件から common prime ideal が存在できぬことを示し、`CyclotomicTailPairwiseUnitWitnessTarget` を actual に供給する
* そこで Stage 1 を閉じて、残りを Stage 3 の norm descent だけにする

## ひとことで言うと

$$
\boxed{
\text{Stage 1 がまだ閉じぬ理由は、}
(\zeta-1)\in P \Rightarrow P \mid (p)
\text{ の actual cyclotomic 供給が、まだ adapter 化されていないから}
}
$$

そして、**ネット上の Mathlib を踏まえた最短手** は、

$$
\boxed{
\texttt{IsPrimitiveRoot.toInteger\_sub\_one\_dvd\_prime}
\text{ を起点に、ring of integers specialization で }
\texttt{SubOneDividesPrimePTarget}
\text{ を埋めること}
}
$$

じゃ。
exact に同名の ideal theorem は見つからなんだが、**もっと直接的な element divisibility theorem は既にある **。
ゆえに、いまは新理論を掘るより、** adapter を 1 本書くのが最短** と見るぞい。 ([leanprover-community.github.io][2])

[1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/Cyclotomic/Basic.html?utm_source=chatgpt.com "Mathlib.NumberTheory.NumberField.Cyclotomic.Basic"
[2]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/Cyclotomic/Basic.html "Mathlib.NumberTheory.NumberField.Cyclotomic.Basic"
[3]: https://leansearch.net/?q=For+any+nonzero+natural+number+%24n%24+and+primitive+%24n%24-th+root+of+unity+%24%5Czeta%24+in+a+commutative+ring+%24A%24%2C+the+images+%24%5Csigma%28%5Czeta+-+1%29%24+and+%24%5Ctau%28%5Czeta+-+1%29%24+are+associated+elements+in+%24A%24+for+any+%24R%24-algebra+automorphisms+%24%5Csigma%2C+%5Ctau%3A+A+%5Cto+A%24.&utm_source=chatgpt.com "Find theorems in Mathlib4 using natural language query"
