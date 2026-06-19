# Stage 1 の deep cyclotomic targets が両方埋まった

うむ、これは **かなり大きい戦果** じゃ。
いまの差分を見るかぎり、**target 1 も filled したので、Stage 1 の deep cyclotomic targets は 2 本とも埋まった** と読んでよい。
target 2 は前回の norm route で `integerInZetaMinusOneIdealDivisibleByP_fill` が入っており 、今回さらに

* `liesOver_of_dvd_span_prime`
* `primeOverPEqualsZetaMinusOne_fill`

が追加され、target 1 の
$$
P \mid (p),\ P\ \text{prime}
\;\Longrightarrow\;
P = (\zeta-1)
$$
側も ring-of-integers specialization で埋まった、という整理じゃ。

## 戦況

戦況を率直に言えば、**Stage 1 は “構造待ち” の段を抜けた**。
前までは

* \(y \in P\) 分岐は閉じた
* \(P \mid (p)\) 分岐は 2 target 待ち

という状態じゃった。
いまはその 2 target が両方埋まったので、`chosenLinearFactor_isCoprime_with_other_of_firstCase_of_pack` に入れるべき deep assumptions が actual theorem に置き換わった、と見てよい。

つまり、Stage 1 の戦場そのものはもう

$$
\text{generic machinery}
\quad\text{vs}\quad
\text{deep cyclotomic targets}
$$

ではなく、**既に作ってある theorem 群を actual specialization として接続する最終配線** の段に入ったのぅ。

## 解説

今回の `primeOverPEqualsZetaMinusOne_fill` は、かなり良い一手じゃ。
特に `Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal` を import し、`eq_span_zeta_sub_one_of_liesOver'` を使う方針は筋が良い。
`liesOver_of_dvd_span_prime` により

$$
P \mid (p)
$$

から `LiesOver` を作り、そこから

$$
P = (\zeta-1)
$$

を得る構図は、target 1 の本質をそのまま Mathlib の理論に接続しておる。
これは「target を仮定して進む」段から、「target 自体を mainline に降ろす」段へ移った、という意味を持つ。

さらに前回の target 2 fill は、norm で

$$
n \in (\zeta-1)
\Rightarrow
(\zeta-1)\mid n
\Rightarrow
N(\zeta-1)\mid N(n)
\Rightarrow
p \mid n
$$

を Lean に落としたものじゃった。
よって今は、ramification と norm の両輪がそろった状態じゃ。

## いま何が残っているか

ここが大事じゃ。
**残る honest open は、もう Stage 1 の deep target ではない。**

残りは主に 2 つじゃ。

ひとつは、今回埋まった fill theorems を使って、Stage 1 の coprimality theorem を **完全に仮定なしの actual theorem に落とす最終配線**。
つまり

$$
\texttt{chosenLinearFactor_isCoprime_with_other_of_firstCase_of_pack}
$$

へ、target 1 と target 2 の fill を実際に流し込むところじゃ。
これは新理論ではなく composition の仕事に近い。

もうひとつは、その coprimality を full family / tail 側へ押し上げて、既にある

* `cyclotomicLinearFactorSpanEqPow_of_tailFactorCoprime`
* `cyclotomicUnitNormalization_of_tailFactorCoprimeRoute`

へ接続し、Stage 2 まで雪崩のように流すことじゃ。
ここまで行けば、残る本丸は **Stage 3 の norm descent** にかなり集中するはずじゃ。

## ひとことで総括

$$
\boxed{
\text{戦況は優勢。}
\text{Stage 1 の deep targets 2 本は埋まり、残りは “配線して流す” 段に入った}
}
$$

じゃよ。
これはかなり良い。
もう「証明の核が足りない」のではなく、**できた核を mainline に接続して Stage 2 まで押し流す段** じゃ。
