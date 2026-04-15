# FLT-Kummer-ClassGroup-Bridge-260404 の Stage 1 の完成度について

確認したぞい。
結論から言うと、**Stage 1 は「coprimality leg は完了」、ただし「Stage 1 全体の public target はまだ未完」** じゃ。

`RegularPrimeRoute.lean` 側の最新コメント同期でも、現実の残 open は **Stage 1 の存在形 boundary target** と **Stage 3 の norm descent** に寄っている、と明記されておる。つまり、ぬしの報告の方向は概ね正しい。

さらに直前までの戦果として、

* target 1 fill `primeOverPEqualsZetaMinusOne_fill`
* target 2 fill `integerInZetaMinusOneIdealDivisibleByP_fill`
* `noPrimeOrY_of_firstCase_of_coprime`
* `chosenLinearFactor_isCoprime_with_other_of_firstCase_of_pack`

まで揃っており、**Stage 1 の coprimality leg 自体は concrete に完成** しておる。

ただし、ここで大事な留意点がある。
アップロードされた最新 `CyclotomicPrincipalization.lean` を見ると、`CyclotomicIdealPthPowerTarget` は **まだ `True` の placeholder** のままで、`cyclotomicIdealPthPower_of_stage1Split` も `trivial`、`cyclotomicIdealPthPower_of_classGroupPTorsionFree` は実質まだ中身が無い。
ゆえに、**Stage 1 の数学的コアは終わっていても、Stage 1 の public API としての完成はまだ**、という判定になるのじゃ。

なので、質問にそのまま答えるならこうじゃ。

## 判定

* **Stage 1 の coprimality 部分**
  完了と見てよい。

* **Stage 1 全体**
  まだ完了とは言い切れぬ。
  理由は、存在形 boundary を実際に supply する theorem が、まだ `CyclotomicIdealPthPowerTarget` に昇格しきっておらぬからじゃ。

* **残り作業が報告どおりか**
  ほぼその通りじゃ。
  ただし、より正確に言うと「Stage 1 全体」ではなく、**Stage 1 から存在形 boundary target を concrete に供給する最終配線** が残っておる、という言い方が一番合う。

## 作業指示

わっちなら、次はこの順で進める。

### 1. Stage 1 の最終出力 theorem を 1 本立てる

狙いは、first-case pack から直接

$$
\texttt{CyclotomicLinearFactorIdealPthPowerTarget}
$$

を返す theorem じゃ。
名前はたとえば

$$
\texttt{cyclotomicLinearFactorIdealPthPower_of_firstCase_of_pack}
$$

のようなものがよい。

中身としては、既に揃っておる

* `chosenLinearFactor_isCoprime_with_other_of_firstCase_of_pack`
* target 1 fill
* target 2 fill
* exponent agreement
* tail-product equality
* `(x)` nonzero
* linear-factor nonzero
* torsion kill

を **composition で繋ぐだけ** に近いはずじゃ。

### 2. その直後に Stage 2 へ流す theorem を立てる

つまり、

$$
\texttt{cyclotomicUnitNormalization_of_firstCase_of_pack}
$$

のような theorem を作る。
これは `cyclotomicUnitNormalization_of_existsLinearFactorIdealPthPower` あるいは `...of_spanEqPow...` 系へ流し込むだけで済むはずじゃ。

ここまで行けば、**Stage 1 は実質 finished** と言ってよい。

### 3. その後に Stage 3 へ入る

残る honest open は、もう `CyclotomicNormDescentTarget` の concrete 化じゃ。
最新の同期コメントでも、現実の残 open はそこに寄っていると整理されておる。

## 提案

わっちの提案は 1 つじゃ。

$$
\boxed{
\text{いまは `CyclotomicIdealPthPowerTarget` を abstract なまま眺めるのでなく、}
\text{first-case pack } \Rightarrow \text{ existence boundary}
\Rightarrow \text{ Stage 2}
\text{ を一気に配線する}
}
$$

つまり、**「Stage 1 finished か？」の答えを、target の comment ではなく theorem 1 本で確定させる** のじゃ。
それが通れば、次の話題はもう Stage 3 だけになる。

必要なら次に、わっちがその composition の具体的な依存順を theorem 名で並べて、実装順の checklist にして渡すぞい。
