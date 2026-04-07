# FLT-Kummer-ClassGroup-Bridge: 2024-06-04 Review (戦況分析と次の戦略)

うむ、戦況はかなり良い。
しかも今回の更新で、**Stage 1 がまだ閉じぬ理由** は、ほぼ一点にまで縮んだぞい。

## 戦況分析

いま既に no-sorry で固まっておるものは、次の 3 層じゃ。

まず、2-factor route の受け皿そのものはもうある。
つまり

$$
\text{tail-product equality}
\;+\;
\text{coprimality}
\;+\;
(x)\neq \bot
$$

が入れば

$$
\operatorname{span}(z-\zeta y)=K^{\mathrm{ctx}.p}
$$

が出て、その先の Stage 2 の concrete target

$$
\exists \beta,\exists u,\ \mathrm{IsUnit}(u)\land z-\zeta y=u\beta^{\mathrm{ctx}.p}
$$

まで自動で流れる形は、既に theorem-level に固定されておる。

次に、actual supply 側でもかなり前進しておる。
今回の差分で、

* exponent agreement から tail-product equality
* exponent agreement から `ctx.p ≠ 0`
* `CharZero` のもとで `(x)` 非零
* ring of integers specialization で
  $$
  (\zeta-1)\in P \Rightarrow P\mid (p)
  $$

まで、全部 no-sorry で繋がった。つまり **structural な橋はもうだいぶ架かっておる** わけじゃ。

さらに、common prime ideal の分析もかなり sharpen された。
ぬしの側ではすでに

$$
P \text{ が chosen factor と別因子の両方を含む}
\Rightarrow
(\zeta-1)\in P \;\lor\; y\in P
$$

を no-sorry で出せており、その \((\zeta-1)\) 分岐は今や specialized adapter により

$$
P\mid (p)
$$

へ直ちに変換できる。
ゆえに、残る actual arithmetic gap はもう

$$
P\mid (p)\ \lor\ y\in P
$$

が **実際には起きえない** ことを、pack 条件からどう supply するかだけじゃ。

## なぜ Stage 1 はまだ閉じないのか

ひとことで言えばこうじゃ。

$$
\boxed{
\text{Stage 1 が閉じぬのは、理想論の機械が足りぬからではなく、}
P\mid (p)\lor y\in P
\text{ の contradiction がまだ theorem 化されておらぬから}
}
$$

つまり、いま残っておるのは **構造問題ではなく actual arithmetic contradiction 問題** じゃ。
generic API も receiver ももう十分細い。足りぬのは「その disjunction はこの branch では起きない」と言い切る最終局所補題だけなんじゃ。

## Mathlib を踏まえた解説

ここで戦略上の大事な判断がある。
今回の specialized adapter 路線は正しかった。

Mathlib の公式 docs には、cyclotomic ring of integers 側で

* `IsCyclotomicExtension.ringOfIntegers`
* `IsPrimitiveRoot.zeta_sub_one_prime'`
* `IsPrimitiveRoot.toInteger_sub_one_dvd_prime'`

が既にあり、\(\zeta-1\) が ring of integers に降りること、そして \(\zeta-1\) が \(p\) を割ることは一次情報として揃っておる。だから generic `SubOneDividesPrimePTarget` を最初から自前で掘るより、**ring-of-integers specialization で押す** 方が最短じゃったわけじゃ。 ([Leanプロヴァーコミュニティ][1])

つまり、戦略判断としては

* generic に戻る
  より
* specialized な first-case contradiction を 먼저閉じる

の方が、いまは明らかに筋が良い。

## 次の戦略

わっちの提案は、かなりはっきりしておる。

### 1. 次に切る theorem は「coprimality theorem」ではなく「contradiction target」

いま欲しいのは、たとえば意味として

$$
\forall P,\ P\ \text{prime ideal} \to \bigl(P\mid (p)\ \lor\ y\in P\bigr)\to \bot
$$

を返す theorem じゃ。
これをまず target として explicit に切るのがよい。

理由は単純で、`chosenLinearFactor_isCoprime_with_other_of_primeOrYContradiction_of_ringOfIntegersCyclotomic`
が既にあるので、この contradiction theorem が 1 本通れば、**pairwise coprimality は自動で回収できる** からじゃ。

### 2. その contradiction theorem は 2 本に割る

ここを一気にやるより、次の 2 片へ裂くのがよい。

ひとつは

$$
P\mid (p)\ \Rightarrow\ \bot
$$

の分岐。
これは first case 側の `p ∤ xyz`、あるいは regular-prime route が既に持っている \(p\)-adic / gap-divisible 条件と、prime ideal over \(p\) の情報をどう衝突させるかを詰める段じゃ。

もうひとつは

$$
y\in P\ \Rightarrow\ \bot
$$

の分岐。
こちらは pack の互いに素性、または chosen factor / other factor の同時包含と合わせて、mod \(P\) で \(z\equiv 0\) 型へ落とす route が濃厚じゃ。
少なくとも、今の構図ではこの 2 分岐は役割が違うので、別 theorem に切った方が詰めやすい。

### 3. その後に full family witness へ戻す

この contradiction theorem が入れば、

* chosen factor と別の 1 因子の pairwise coprimality
* それを full family 側へ押し上げる witness
* tail との coprimality
* explicit equality
* Stage 2

が、既存 receiver 群でほぼ雪崩のように閉じるはずじゃ。
すると Stage 1 は事実上閉じ、残る honest open は Stage 3 の norm descent だけになる見込みが高い。

## 提案

いまの最短手を一行で言うぞい。

$$
\boxed{
\text{次は }
P\mid (p)\ \lor\ y\in P
\text{ が起きないことを、first-case pack 条件から supply する theorem を立てる}
}
$$

そして実務上は、これを

* `NoPrimeOverPInCommonTarget`
* `NoYInCommonPrimeTarget`

のように 2 分岐へ割って証明するのがよい。
これが通れば、Stage 1 は「ほぼ閉じた」と言ってよいところまで行くはずじゃ。

いまの戦況は悪くない。
むしろ、**残敵が finally arithmetic contradiction の 1 点に見えてきた** のが今回の収穫じゃよ。

[1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/Cyclotomic/Basic.html?utm_source=chatgpt.com "Mathlib.NumberTheory.NumberField.Cyclotomic.Basic"
