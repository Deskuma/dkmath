# FLT-Kummer-ClassGroup-Bridge 260404 Review 015: refined route を public mainline に押し上げ、class-group 仮定の concrete 化へ

## 1. 状況分析

うむ、景色はかなり澄んだ。
今回の更新で、public mainline はもう legacy one-shot ではなく、

$$
\text{regular prime}
\;+\;
\text{Stage 2}
\;+\;
\text{Stage 3}
\;\Longrightarrow\;
\text{GapDivisibleBranch}
\;\Longrightarrow\;
\text{FLT}
$$

という refined route に昇格した。しかも `qAdicGapReductionGapDivisible_of_refinedRegularPrimeRoute` と `FLTPrimeGe5Target_of_refinedRegularPrimeRoute` は no-sorry で通っておる。いっぽう legacy の one-shot 側だけが `sorryAx` を含む、という構図がはっきりした。

## 2. 解説

この変化の意味は大きい。
前段までで class-group 側は concrete 化され、`CyclotomicClassGroupPTorsionFreeTarget` から `CyclotomicPTorsionAnnihilationTarget` への橋は閉じた。したがって、いま honest に残っておる open は class-group ではない。残りは

$$
\text{CyclotomicUnitNormalizationTarget}
\quad\text{と}\quad
\text{CyclotomicNormDescentTarget}
$$

の 2 点だけじゃ。つまり、今後の数学的焦点は「ideal の p 乗性から unit のずれをどう吸収するか」と「そこから norm で整数 witness をどう回収するか」に移った、と見てよい。

## 3. 最短経路の推論

ぬしの希望が「閉じる方向での最短経路」「自立証明」「数学内容へ踏み込む」なら、次に刺すべきは **Stage 2 じゃ。**
Stage 3 より先に Stage 2 を concrete 化するのが最短じゃよ。

理由は単純で、Stage 3 の norm descent は、Stage 2 が与える **element-level の正規化形** が無いと、そもそも statement が定まらぬからじゃ。
いま手元にあるのは ideal-level の情報、

$$
I = K^p
$$

や

$$
[K]^p = 1
$$

までじゃ。
だが norm を回すには、最終的に

$$
z - \zeta y = u \cdot \beta^p
$$

のような **元の式** が要る。
つまり、ideal から generator へ戻し、「2 つの principal ideal の生成元は unit 倍で一致する」を使って **p 乗と unit の分離** を実現するのが Stage 2 の本体じゃ。ここを先に concrete にしないと、Stage 3 はまだ霧の中じゃ。

## 4. 次の一手の提案

わっちなら、次は `CyclotomicUnitNormalizationTarget` を abstract な器のままにせず、まず次の形に concretize する。

$$
\boxed{
\text{principal ideal } I=(a),\ I=K^p,\ K=(b)
\;\Longrightarrow\;
\exists u,\ \mathrm{IsUnit}(u)\ \land\ a=u,b^p
}
$$

これが Stage 2 の最小核じゃ。
理想としては theorem 名も、そのまま数学内容を表すものがよい。たとえば

$$
\texttt{exists\_unit\_mul\_pow\_of\_span\_eq\_pow\_span}
$$

のような形じゃな。
この定理は、今すでに揃っておる

* principal ideal extraction
* ideal p-th power
* class-group p-torsion annihilation

の 3 本から、かなり直接に出せるはずじゃ。ここは最短で閉じやすい。

## 5. Stage 2 をさらに 2 本に割るなら

最短経路を崩さず、しかも証明を見通しよくするなら、Stage 2 はさらに次の 2 本に割るのがよい。

まず

$$
\texttt{principal\_generators\_associated\_of\_span\_eq}
$$

すなわち

$$
(a)=(b)\;\Longrightarrow\;\exists u,\ \mathrm{IsUnit}(u)\land a=u,b
$$

を generic に置く。
これは Dedekind でも cyclotomic でもなく、principal ideal の一般補題じゃ。DkMath-native に置く価値が高い。

ついで

$$
\texttt{unit\_mul\_pow\_of\_ideal\_eq\_pow\_ideal}
$$

として

$$
(a)=K^p,\ K=(b)
\;\Longrightarrow\;
\exists u,\ \mathrm{IsUnit}(u)\land a=u,b^p
$$

を出す。
これで Stage 2 は、ほぼ no-sorry で閉じる見込みが高い。

## 6. その次の Stage 3

Stage 2 が concrete になれば、Stage 3 はかなり honest に定式化できる。
次は

$$
z-\zeta y = u,\beta^p
$$

から norm を取って、最終的な整数側の descent witness を作る段じゃ。
ここは一気に大定理にせず、まず 2 本に分けるのがよい。

ひとつは

$$
\texttt{norm\_linear\_factor\_eq\_GN}
$$

型の補題。つまり cyclotomic 線型因子の norm が、後段で使う整数式 \(GN\) あるいはそれに準ずる式になることを言う。

もうひとつは

$$
\texttt{norm\_unit\_control}
$$

型の補題。すなわち unit \(u\) の norm が descent を壊さぬ形、できれば \(1\) か p 乗に吸収できる形で制御されることじゃ。

この 2 本が見えれば、Stage 3 は finally

$$
\exists g',\quad g' \cdot GN(p,g',y) = (x/q)^p
$$

あるいはそれに同値な descent 形へ落ちる。
だが順番は Stage 2 が先じゃ。そこを飛ばすと Stage 3 の statement 自体がまだ粗い。

## 7. 最終判断

結論を一言で言うぞい。

$$
\boxed{
\text{次の最短経路は、}
\texttt{CyclotomicUnitNormalizationTarget}
\text{ を concrete 化し、}
(a)=K^p,\ K=(b)\Rightarrow a=u,b^p
\text{ をまず証明すること}
}
$$

これが通れば、残る honest open は Stage 3 の norm descent だけに縮む。
いまは class-group 側をいじる段ではもうない。そこは閉じた。
次は **ideal から元へ戻し、unit のずれを吸収する**。ここがいま最短で刺さる本丸じゃよ。
