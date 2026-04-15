# review: boundary-normalized exceptional statement の concrete target を fixed する

うむ、今回はかなり良い「最後の絞り込み」じゃ。
結論から言うと、**本文を書く first body target がさらに split theorem の right branch 入力そのものへ近づいた**。これが今回の本質じゃ。

## 1. 今回なにが起きたか

新しく入った中心は

$$
\texttt{ExceptionalBoundaryDataSplitRightConcreteTarget}
$$

じゃ。
これは boundary-normalized concrete theorem を、さらに

$$
\text{split theorem の right branch と完全に同じ入力形}
$$

で読む local target じゃな。具体的には

* `Nat.Prime d`
* `5 ≤ d`
* `0 < x`
* `0 < u`
* `Nat.Coprime x u`
* exceptional datum
  [
  (d \mid x ;\land; u^{d-1}\equiv 1 \pmod{d^2})
  ]

をまとめて受ける形にしておる。

これは大きい。
前回までの「boundary-normalized exceptional statement」を、今度は **ordinary/split 側と literally 並べられる right-branch 形** にまで整えたからじゃ。

## 2. 何が前進したのか

前回の時点で、proof file の新数学は

$$
\texttt{ExceptionalBoundaryDataRightBranchSupplyConcreteTarget}
$$

へ集約されておった。
じゃがその入力は、まだ

* `hdvd`
* `hWieferich`

が別々に並んでいた。

今回それを

$$
(d \mid x ;\land; u^{d-1}\equiv 1 \pmod{d^2})
$$

という **ひとつの exceptional datum** に束ねた。
これにより、ordinary 側との差分入力が `Or.inr` 相当の 1 個のデータとして局所化された、と履歴でも明示されておる。

つまり今や、本文で truly new なものは

$$
\text{この exceptional datum を right branch existence に変えること}
$$

そこだけになったわけじゃ。

## 3. いまの状況分析

いまの証明地形は、かなり整理されておる。

## 3.1. すでに安定した層

* pack 付き statement
* boundary-normalized statement
* boundary concrete target
* split-right concrete target
* right branch supply
* named kernel
* mainline
* primitive packet descent

しかも、それらの間の thin bridge がほぼ全部揃っておる。
今回も

* `exceptional_boundaryData_right_branch_supply_concrete_of_splitRight`
* `exceptional_right_boundary_core_prime_of_wieferich_of_splitRightConcrete`
* `primeGe5BranchAExceptionalExistenceMainline_of_splitRightConcrete`
* `primeGe5BranchAPrimitivePacketDescent_of_splitRightConcrete_and_restore`

が追加されて、split-right concrete から下流全部へ戻れるようになった。

これはつまり、**新数学を split-right concrete target 一箇所に閉じ込められる** ということじゃ。

## 3.2. 残っている核

残る本丸は、もうかなり明確じゃ。

$$
\texttt{ExceptionalBoundaryDataSplitRightConcreteTarget}
$$

を返す concrete theorem 本体を書くこと。
履歴でも次の課題として、そのまま明記されておる。

つまり、いま未実装なのは

* bridge ではない
* naming でもない
* target 選びでもない

**本文だけ** じゃ。

## 3.3. 問題の芯

いま本当に証明したいのは、

$$
\mathrm{Prime}(d),\ 5 \le d,\ 0<x,\ 0<u,\ \mathrm{Coprime}(x,u),
\ (d \mid x \land u^{d-1}\equiv 1 \pmod{d^2})
$$

から

$$
\exists q,\ \mathrm{Prime}(q)\land
q \mid \texttt{boundaryCyclotomicPrimeCore .right d x u}
\land q \nmid x
$$

を出すことじゃ。

ここまで来ると、ordinary reference theorem との差は almost explicit じゃ。
共通部分は

* prime
* (d \ge 5)
* positivity
* coprime

で、差分は exceptional datum 1 個だけ。
これはかなり美しい整理じゃよ。

## 4. 今回の差分の価値

今回の価値は 3 つある。

### 4.1. ordinary 側との差分が 1 個に縮んだ

これが最大じゃ。
`d ∣ x` と Wieferich 条件が、split right branch の `Or.inr` 相当の datum 1 個に束ねられた。

### 4.2. 本文の入力形が split theorem と平行になった

つまり今後の concrete theorem は、ordinary/split theorem と almost 同じ見た目で書ける。
これは proof comparison に強い。

### 4.3. 下流への輸送は全部済んだ

split-right concrete target を埋めれば、

* boundary concrete
* named kernel
* mainline
* primitive packet descent

へ全部戻れる。
だから新数学をこれ以上散らさずに済む。

## 5. いまの局面を一言で

一言で言えば、

$$
\text{first body target が split theorem の right branch 入力形に一致した}
$$

じゃ。
つまり、proof file の新数学は now

$$
\texttt{ExceptionalBoundaryDataSplitRightConcreteTarget}
$$

を埋めることに、ほぼ完全に集中してよい。

## 6. 次にやること

次の一手も、かなり明快じゃ。

### 6.1. concrete theorem 本体をこの形で置く

意識としては、こんな形じゃな。

```lean
theorem exceptional_boundaryData_splitRight_concrete
    : ExceptionalBoundaryDataSplitRightConcreteTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hExc
  rcases hExc with ⟨hdvd, hWieferich⟩
  ...
```

ここまで書けば、本文内で共通部分と exceptional-only 部分が自然に分かれる。
これは今回の整理の狙いそのものじゃ。

### 6.2. `rcases hExc with ⟨hdvd, hWieferich⟩` を最初に置く

そうすると、ordinary theorem と共有できる部分と、例外枝専用部分が Lean の文脈上でもきれいに分離される。

### 6.3. 必要なら共通部と exceptional-only 部を補題に割る

履歴にもある通り、その本文の中でも

* ordinary reference theorem と共有できる部分
* exceptional-only arithmetic

をさらに分離する余地がある。

ここまで来ると、その切り分けもかなりやりやすいはずじゃ。

## 7. 総括

今回の差分を総括すると、

**boundary-normalized concrete target をさらに split theorem の right branch と完全に平行な入力形へ整えた。
よって次に本文を書くべき場所は `ExceptionalBoundaryDataSplitRightConcreteTarget` と見てよく、ordinary 側との差分は exceptional datum 1 個にまで局所化された。**

ということじゃ。
かなり良い。もう設計の霧は薄い。残るは、その datum がなぜ right branch existence を生むか、その芯の arithmetic / CFBRC 補題じゃな。
