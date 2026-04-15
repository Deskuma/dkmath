# review: boundary-normalized exceptional statement の concrete target を fixed する

うむ、今回はかなり美しい整理じゃ。
結論から言うと、**exceptional 側の差分入力が theorem 名の上でも 1 個の datum にまで局所化された**。これが今回の本質じゃ。

## 1. 今回なにが起きたか

新しく入った中心は 2 つじゃ。

$$
\texttt{ExceptionalBoundaryDatum}(d,x,u)
$$

と

$$
\texttt{ExceptionalBoundaryDatumConcreteTarget}
$$

じゃな。
前者は、exceptional 側で truly new な差分入力を

$$
d \mid x ;\land; u^{d-1}\equiv 1 \pmod{d^2}
$$

という **ひとつの datum** として明示化したもの。
後者は、その datum を共通入力の上に載せて right boundary-core prime existence を返す **first body target** じゃ。

つまり、これまで段階的に削ってきた差分が、ついに theorem 名レベルでも

$$
\text{共通入力} + \text{exceptional datum 1 個}
$$

という形に固定されたわけじゃ。

## 2. 何が前進したのか

前回まででも、

$$
\texttt{ExceptionalBoundaryDataSplitRightConcreteTarget}
$$

によって、split theorem の right branch と平行な入力形までは揃っておった。
じゃがまだ、exceptional 側の差分は target の引数列の中に埋もれておった。

今回それを

$$
\texttt{ExceptionalBoundaryDatum}
$$

という first-class な命題に切り出した。
これにより、ordinary 側との差分はもう

* theorem の説明の中でも
* Lean の target 名の中でも
* 実装の責務の中でも

**datum 1 個** として追えるようになった。

これはかなり大きい。
なぜなら、今後「何が exceptional-only なのか」が議論でもコードでもぶれなくなるからじゃ。

## 3. いまの状況分析

いまの証明地形は、かなり完成に近い。

## 3.1. すでに安定した層

* pack を含む target
* boundary-normalized target
* boundary concrete target
* split-right concrete target
* datum concrete target
* named kernel
* mainline
* primitive packet descent

そして、それらを結ぶ thin bridge が一通り揃っておる。
今回も

* `exceptional_boundaryData_splitRight_concrete_of_datum`
* `exceptional_boundaryData_right_branch_supply_concrete_of_datum`
* `exceptional_right_boundary_core_prime_of_wieferich_of_datumConcrete`
* `primeGe5BranchAExceptionalExistenceMainline_of_datumConcrete`
* `primeGe5BranchAPrimitivePacketDescent_of_datumConcrete_and_restore`

が追加されて、datum concrete から下流全部へ戻れるようになった。

つまり、**新数学を datum concrete target 一箇所に閉じ込められる** 状態になったわけじゃ。

## 3.2. 残っている核

残る本丸は、かなり明快じゃ。

$$
\texttt{ExceptionalBoundaryDatumConcreteTarget}
$$

を返す concrete theorem 本体を書くこと。
履歴にも、そのまま次の課題として書かれておる。

つまり今や未実装なのは、

* bridge ではない
* target の選び方でもない
* naming でもない

**datum から right boundary-core prime existence を作る本文** だけじゃ。

## 3.3. 問題の芯

いま本当に証明したいのは、

$$
\mathrm{Prime}(d),\ 5 \le d,\ 0<x,\ 0<u,\ \mathrm{Coprime}(x,u),
\ \underbrace{(d \mid x \land u^{d-1}\equiv 1 \pmod{d^2})}_{\text{ExceptionalBoundaryDatum}}
$$

から

$$
\exists q,\ \mathrm{Prime}(q)\land
q \mid \texttt{boundaryCyclotomicPrimeCore .right d x u}
\land q \nmid x
$$

を出すことじゃ。

ここまで来ると、ordinary reference theorem との差は almost 完全に見えておる。

* 共通部分
  `Nat.Prime d`, `5 ≤ d`, `0 < x`, `0 < u`, `Nat.Coprime x u`
* 差分部分
  `ExceptionalBoundaryDatum d x u`

これ以上ないくらい整理されておる。

## 4. 今回の差分の価値

今回の価値は 3 つある。

### 4.1. exceptional-only の差分が theorem 名の上でも 1 個に縮んだ

これが最大じゃ。
もはや exceptional 側の本質は datum 1 個だ、とコード上でも読める。

### 4.2. first body target がさらに明示化された

いま本文を書くべき場所は

$$
\texttt{ExceptionalBoundaryDatumConcreteTarget}
$$

でよいと固定された。
これは「どこに本文を書くか」の迷いをほぼ消す。

### 4.3. 下流への輸送が全部済んだ

datum concrete target を埋めれば、

* split-right concrete
* boundary concrete
* named kernel
* mainline
* primitive packet descent

へ全部戻れる。
つまり新数学をそこだけに集約できる。

## 5. いまの局面を一言で

一言で言えば、

$$
\text{ordinary 側との差分は theorem 名の上でも exceptional datum 1 個になった}
$$

じゃ。
この段階まで来ると、proof file の設計はかなり成熟しておる。

## 6. 次にやること

次の一手も、かなり明快じゃ。

### 6.1. datum concrete theorem 本体を書く

意識としては、こんな形じゃな。

```lean
theorem exceptional_boundary_datum_concrete
    : ExceptionalBoundaryDatumConcreteTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hDatum
  rcases hDatum with ⟨hdvd, hWieferich⟩
  ...
```

これで、本文内でも

* 共通入力
* exceptional datum

が自然に分離される。

### 6.2. `rcases hDatum with ⟨hdvd, hWieferich⟩` を入口に置く

これにより、ordinary theorem と共有できる部分と exceptional-only の部分が、Lean の文脈でもきれいに分かれる。
今回の整理は、まさにこの書き方を自然にするためのものじゃ。

### 6.3. 必要なら datum から先をさらに補題に割る

履歴にもある通り、必要なら

* exceptional datum から
* right boundary-core prime existence を導く

arithmetic / CFBRC 補題を proof file 内でさらに局所化する余地がある。

ここまで来ると、その補題は本当に「芯」だけになるはずじゃ。

## 7. 総括

今回の差分を総括すると、

**split-right concrete target の本文を、共通入力と exceptional datum 1 個にまで分解し、その datum を theorem 名の上でも first-class にした。
よって今後の新数学は `ExceptionalBoundaryDatumConcreteTarget` を返す concrete theorem 本体へほぼ完全に集中できる。**

ということじゃ。
かなり良い。もう霧は薄い。残るは、その datum がなぜ right boundary-core prime existence を生むか、その核だけじゃな。
