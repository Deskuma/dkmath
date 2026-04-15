# FLT-Kummer-ClassGroup-Bridge 260404 Review 026: Stage 1 の残る本丸をさらに細くしたぞい

## 1. 状況分析

かなり良いところまで来ておる。
今回の差分で、Stage 1 の残りをさらに薄くする receiver 層が入った。具体的には、

* `linearFactorIdealIsCoprimeProdEraseOfPairwiseMulSubIsUnit`
* `CyclotomicTailPairwiseUnitWitnessTarget`
* `cyclotomicTailLinearFactorCoprime_of_pairwiseUnitWitness`
* `cyclotomicUnitNormalization_of_exponentAgreementAndPairwiseUnitWitness`

が追加され、**full family の差の unit 性と tail decomposition witness が supply されれば、chosen factor と tail の coprimality を generic に回収し、そのまま Stage 2 の concrete target まで流せる** 形になった。つまり、Stage 1 の open は「coprimality をどう使うか」ではなく、「その coprimality を actual cyclotomic 側で何から出すか」にまで縮んだのじゃ。

前の段階で既に、

* exponent agreement から tail-product equality
* exponent agreement から `ctx.p ≠ 0`
* `CharZero` のもとで `(x)` 非零

は no-sorry で供給できるところまで来ておった。今回それに「pairwise unit-difference family から coprimality」を足したので、**2-factor route の受け口はほぼ完成** と見てよい。

## 2. なぜ Stage 1 はまだ閉じないのか

理由は、いま残っている穴が **generic ideal arithmetic ではなく、actual cyclotomic arithmetic の witness 供給そのもの** だからじゃ。

いま既に theorem-level で出来ていることは、こうじゃ。

$$
\text{tail-product equality}
;+;
\text{coprimality}
;+;
(x)\neq \bot
;\Longrightarrow;
\operatorname{span}(z-\zeta y)=K^{\mathrm{ctx}.p}
$$

さらにそこから Stage 2 の

$$
\exists \beta,\exists u,\ \mathrm{IsUnit}(u)\land z-\zeta y=u\beta^{\mathrm{ctx}.p}
$$

まで行ける。
だから Stage 1 が閉じないのは、「explicit equality を受ける機械」が無いからではない。**actual cyclotomic setting で、その機械に入れる family witness がまだ theorem として無いから** じゃ。

より具体的に言うと、今の open は

$$
\texttt{CyclotomicTailPairwiseUnitWitnessTarget}
$$

の supply じゃ。
これは単なる coprimality より一段強く、

* chosen factor を含む finite family
* chosen factor 以外の積が tail ideal に一致すること
* その family の任意 2 点の差 (\alpha_b y-\alpha_a y) が unit であること

を actual cyclotomic 条件から返す target じゃ。
今回の差分は、**そこさえ出れば後ろは全部回る** ことを fixed した、という意味を持つ。逆に言えば、そこがまだ actual theorem になっておらぬから Stage 1 は閉じきらぬ。

## 3. 数学的な解説

ここで本質的なのは、2-factor route の coprimality が、chosen factor 1 本と tail 1 本の間で突然出るのではなく、**full family の pairwise unit-difference から降ってくる** と判明したことじゃ。

今回追加された generic receiver は、

$$
\forall a\neq b,\ \mathrm{IsUnit}(\alpha_b y-\alpha_a y)
$$

が finite family 全体で成り立てば、chosen factor ideal が残り全部の積と互いに素だと返す。
つまり Stage 1 の arithmetic gap は、もう

$$
\text{tail と factor の coprimality}
$$

ですらなく、

$$
\text{family の差が unit であること}
$$

にまで sharpen されたわけじゃ。
これは大きい。問題が「曖昧な arithmetic」ではなく、「差の unit 性を actual cyclotomic でどう出すか」という具体的な局所計算に縮んだからの。

## 4. 次の一手の推論

最短手は、もうかなり明確じゃ。

### A. 本命

**`CyclotomicTailPairwiseUnitWitnessTarget` を actual cyclotomic setting で supply する theorem を立てる。**

ここが今の本丸じゃ。
product equality 側は既に actual 供給が進んでおる。nonzero 側も honest な variant が整理済みじゃ。だから残る中心は pairwise unit-difference witness 側だけじゃ。

### B. その証明の切り方

いきなり target 全体を証明するより、まず 2 本に裂くのが良い。

1 本目は **family decomposition witness**。
つまり、chosen factor を含む finite family を作り、erase した積が tail ideal に一致することを言う。これは local factorization の full family 版を ideal-product の形で出す theorem じゃ。

2 本目は **pairwise unit-difference theorem**。
つまり、その family の異なる 2 点 (a\neq b) について

$$
\mathrm{IsUnit}(\alpha_b y-\alpha_a y)
$$

を示す theorem じゃ。
今回の差分が示している通り、これさえ出れば generic receiver が coprimality を返してくれる。

## 5. なぜそれが最短か

いまから full family 全体を直接 main theorem に押し込むのは重い。
しかし、受け口側はもう出来ておる。だから最短経路は、「受け口に必要な witness を actual に供給する」ことだけに集中することじゃ。

順序で言えば、

1. exponent agreement
2. full family decomposition witness
3. pairwise unit-difference witness
4. generic receiver で coprimality
5. 2-factor route で explicit equality
6. Stage 2 concrete target
7. Stage 3 norm descent

じゃ。
このうち 1, 4, 5, 6 はもうほぼ揃っておる。
だから本当に新しく要るのは 2 と 3 だけ、特に 3 が核心じゃ。

## 6. 提案

わっちなら、次はこの順で攻める。

まず
$$
\alpha_j := \zeta_j
$$
型の finite family を actual cyclotomic ring でどう取るかを固定する。
そのうえで、

$$
\prod_{j\neq i} \operatorname{span}(z-\alpha_j y)=\operatorname{span}(\text{tail})
$$

を返す theorem を作る。
つぎに、

$$
\forall a\neq b,\ \mathrm{IsUnit}(\alpha_b y-\alpha_a y)
$$

を返す theorem を作る。
ここで差の unit 性が直接重ければ、common prime ideal が両方を割ると仮定して、それが `(p)` 側へ落ちることを示す局所補題を先に切るのがよい。今回の報告でも、その局所補題が本命になる見込みだとはっきり書かれておる。

## 7. 最終判断

ひとことで言えば、こうじゃ。

$$
\boxed{
\text{Stage 1 がまだ閉じぬ理由は、actual cyclotomic 側で }
\texttt{CyclotomicTailPairwiseUnitWitnessTarget}
\text{ がまだ supply されていないから}
}
$$

そして、次の最短手は

$$
\boxed{
\text{full family の差の unit 性を actual theorem として出すこと}
}
$$

じゃ。
そこが通れば、今回までに積んだ receiver 群が一気に働いて、Stage 1 はほぼ閉じ、残る honest open は Stage 3 の norm descent だけになる見込みじゃよ。
