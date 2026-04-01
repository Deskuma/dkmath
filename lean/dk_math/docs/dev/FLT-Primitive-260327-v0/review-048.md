# review: equality of diffPow divisibility and ModEq targets

うむ、かなりよい整理じゃ。
今回の差分で、残る局所核はさらに **可除性** だけでなく **合同条件** としても追えるようになった。つまり、最後の本丸は

$$
q \mid u^d - (u-1)^d
$$

そのものでも、

$$
(u-1)^d \equiv u^d \pmod q
$$

でも読める段に入った、ということじゃ。

## 1. 今回なにが起きたか

新しく入った中心は次の 2 つじゃ。

* `ExceptionalBoundaryDatumPreparedDiffPowModEqOnWitnessTarget`
* `exceptional_boundary_datum_prepared_diffPow_on_witness_of_modEq`

前者は、これまでの差冪可除性 target

$$
q \mid u^d - (u-1)^d
$$

を、合同の形

$$
(u-1)^d \equiv u^d \pmod q
$$

で読む後段 target じゃ。
後者は、その合同版から divisibility 版へ戻す橋じゃな。

つまり今回の更新で、残る局所核は

$$
\text{diffPow divisibility}
$$

としても

$$
\text{diffPow ModEq}
$$

としても扱えるようになった。
これはかなり大きい。最後の一撃を「差を割る」として書くか、「両辺が合同」として書くか、表現の自由度が増えたからじゃ。

## 2. 何が前進したのか

前回の時点で、残核は already

$$
\texttt{ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget}
$$

すなわち

$$
q \mid u^d - (u-1)^d
$$

1 本まで縮んでおった。

今回その差冪 target に対して、さらに

$$
\texttt{ExceptionalBoundaryDatumPreparedDiffPowModEqOnWitnessTarget}
$$

が追加された。
そして `Nat.modEq_iff_dvd'` を

$$
(u-1)^d \le u^d
$$

の下で使うことで、合同版から divisibility 版を回収できると固定した。

つまり、いまや next body は

* 差を直接 (q) が割ると示してもよい
* まず合同
  [
  (u-1)^d \equiv u^d \pmod q
  ]
  を示してもよい

という二刀流になったわけじゃ。

## 3. いまの状況分析

いまの証明地形は、かなり細く、そして見通しよくなっておる。

### 3.1. すでに閉じた部分

* arithmetic witness concrete
  [
  q \mid x+1,\ \neg q \mid x
  ]
* witness-aware CFBRC existence への還元
* residual sum への還元
* diffPow divisibility への還元
* diffPow ModEq から divisibility への橋
* そこから mainline / packet descent へ戻る wrapper 群

ゆえに、下流の配線はもう十分に揃っておる。
新数学は下流にはなく、最後の diffPow / ModEq の本文だけに残っておる。

### 3.2. 残っている本丸

残る本丸は、いまやこのどちらかじゃ。

$$
\texttt{ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget}
$$

または

$$
\texttt{ExceptionalBoundaryDatumPreparedDiffPowModEqOnWitnessTarget}
$$

の concrete 本体。
履歴でも、次はこのどちらかの本体を切ると明記されておる。

とはいえ、読み筋としては後者、つまり合同版から攻めるほうが自然に見えるの。

## 4. なぜ合同版が有利か

今回の差分から見ると、賢狼は **ModEq 版から攻めるのがよい** と見る。

理由は単純で、最終的に示したい差冪可除性

$$
q \mid u^d - (u-1)^d
$$

は、しばしば直接よりも

$$
(u-1)^d \equiv u^d \pmod q
$$

のほうが扱いやすいからじゃ。
特に、Wieferich 条件や (q \mid x+1) から何らかの合同変形を作るなら、「差を割る」より「両辺が合同」のほうが自然に書けることが多い。

今回の theorem 配線も、それを後押ししておる。
まず合同版 target を立てて、それを divisibility 版に戻し、そこから全部 downstream を閉じる形になっておるからな。

## 5. 今回の差分の価値

今回の価値は 3 つある。

### 5.1. 残核が “差” と “合同” の両方で読めるようになった

これが最大じゃ。
最後の局所核をどちらの言葉で攻めるか、自由度ができた。

### 5.2. `Nat.modEq_iff_dvd'` による橋が固定された

つまり、合同版を示せば divisibility 版は自動で回収できる。
これで合同 route が正式な main route 候補になった。

### 5.3. next body がさらに書きやすくなった

可除性を直接示すのが重い場合でも、まず合同条件を立てればよい。
これは proof exploration 上、かなりありがたい。

## 6. いまの局面を一言で

一言で言えば、

$$
\text{残る未解決核は diffPow だが、いまや ModEq 版として攻めてもよい}
$$

じゃ。
そして設計としては、むしろ

$$
(u-1)^d \equiv u^d \pmod q
$$

から入る方が自然に見えてきた段じゃな。

## 7. 次にやること

次の一手は、かなり明快じゃ。

### 7.1. まず ModEq target の concrete 本体を書く

意識としては、こうじゃな。

```lean
theorem exceptional_boundary_datum_prepared_diffPow_modEq_on_witness
    : ExceptionalBoundaryDatumPreparedDiffPowModEqOnWitnessTarget := by
  intro d x u q hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x
  ...
```

ここで目標は

$$
(u-1)^d \equiv u^d \pmod q
$$

だけじゃ。

### 7.2. そのあと divisibility 版へ落とす

これはもう bridge があるので、本文でやる必要はない。
合同版が立てば、divisibility 版も mainline も packet descent も流れる。

## 8. 総括

今回の差分を総括すると、

**差冪 divisibility target をさらに `Nat.ModEq` 版へ落とし、残る local kernel を合同条件としても追えるようにした。
よって current proof file の next body は、`ExceptionalBoundaryDatumPreparedDiffPowModEqOnWitnessTarget` の concrete 本体として書くのが自然な段に入った。**

ということじゃ。
かなりよい。
もう最後の局所核は、差の可除性ではなく「両辺が合同」として見えるところまで来たの。
