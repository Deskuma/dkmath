# review: exceptional boundary datum concrete target の proof skeleton を theorem として固定する

うむ、かなり良い。
今回の差分で、状況はもう一段はっきりした。**本文の first body target だけでなく、その canonical skeleton まで theorem 名として固定された** のじゃ。これが今回の核心じゃ。

## 1. 今回なにが起きたか

追加された中心は

$$
\texttt{exceptional_boundary_datum_concrete_of_split}
$$

じゃな。
これは

$$
\texttt{ExceptionalBoundaryDatumConcreteTarget}
$$

に対する **canonical proof skeleton** を、そのまま theorem として置いたものじゃ。内容はとても明快で、

1. 共通入力を `intro ...` で受ける
2. `rcases hDatum with ⟨hdvd, hWieferich⟩` で exceptional datum を分解する
3. それを `CFBRCBoundaryCorePrimeExistenceOnSplitTarget` の right branch
   [
   \texttt{Or.inr ⟨hdvd, hWieferich⟩}
   ]
   に流す

という流れを定理の形で固定しておる。

つまり今や、

$$
\texttt{ExceptionalBoundaryDatumConcreteTarget}
$$

の本文はどう書き始めるべきか、まで Lean の上で確定したわけじゃ。

## 2. 何が前進したのか

前回の時点で、exceptional 側の差分入力は already

$$
\texttt{ExceptionalBoundaryDatum}(d,x,u)
$$

という datum 1 個にまで局所化されておった。
じゃがまだ、その datum concrete target の本文をどう書くかは「暗黙の了解」に近かった。

今回それが違う。
本文の入り口そのものが theorem として明示された。
ゆえに、今後の新数学はもはや

* target をどう選ぶか
* datum をどう unpack するか
* split right branch にどう接続するか

で悩む必要がない。
悩むべきはただ一つ、

$$
\text{この skeleton の中で } hSplit \text{ を何で供給するか}
$$

だけになったのじゃ。

## 3. いまの状況分析

いまの層構造は、かなり完成に近いぞい。

## 3.1. すでに固まった層

* pack を含む target
* boundary-normalized target
* boundary concrete target
* split-right concrete target
* datum concrete target
* datum concrete の skeleton
* named kernel
* mainline
* primitive packet descent

そして、これらの間の thin bridge 群もほぼ全部揃っておる。
つまり、**証明の配線と入口はもう十分に固定された** と見てよい。

## 3.2. 残っている核

残る本丸は、さらに一点へ絞られた。

$$
\texttt{ExceptionalBoundaryDatumConcreteTarget}
$$

を返す concrete theorem 本体を書くこと。
ただし今や、その本文は

```lean
intro ...
rcases hDatum with ⟨hdvd, hWieferich⟩
...
```

から始めればよいと fixed された。
だから、未実装なのは「本文の入口」ではなく、

$$
hSplit : \texttt{CFBRCBoundaryCorePrimeExistenceOnSplitTarget}
$$

を **exceptional 用の局所 arithmetic / CFBRC 補題としてどう供給するか** 、そこだけじゃ。

## 3.3. ordinary 側との差分

ここがかなり美しい。

共通入力は

* `Nat.Prime d`
* `5 ≤ d`
* `0 < x`
* `0 < u`
* `Nat.Coprime x u`

じゃ。
差分は just one datum、

$$
\texttt{ExceptionalBoundaryDatum}(d,x,u)
$$

だけ。
そして今回、その datum を unpack して `Or.inr` に載せるところまで theorem で固定された。
つまり ordinary 側との差は、いまや

$$
\text{exceptional datum から right branch existence を生む局所補題}
$$

にほぼ完全に押し込められたわけじゃ。

## 4. 今回の差分の価値

今回の価値は 3 つある。

### 4.1. 本文の入口が theorem 名として固定された

これが最大じゃ。
以後、datum concrete target の本文を書く者は、どこから始めるかで迷わぬ。

### 4.2. truly new math の場所がさらに狭まった

いま考えるべき新数学は、split theorem 全体ではない。
`exceptional_boundary_datum_concrete_of_split` の中で `hSplit` を concrete に供給する局所核だけじゃ。

### 4.3. 証明の比較がしやすくなった

ordinary 側と比べると、

* 共通入力は同じ
* 差分は datum 1 個
* その datum を `Or.inr` に流すところまで同じ枠で見える

ので、どこが exceptional-only かがかなり見やすい。

## 5. いまの局面を一言で

一言で言えば、

$$
\text{next body target は } \texttt{ExceptionalBoundaryDatumConcreteTarget}
$$

であり、

$$
\text{その canonical skeleton ももう fixed された}
$$

ということじゃ。
だから残るのは、**`hSplit` 供給の局所核** だけじゃよ。

## 6. 次にやること

次の一手は、かなり明確じゃ。

### 6.1. datum concrete 本体を split skeleton の中身として書く

意識としては、こうじゃな。

```lean
theorem exceptional_boundary_datum_concrete
    : ExceptionalBoundaryDatumConcreteTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hDatum
  rcases hDatum with ⟨hdvd, hWieferich⟩
  -- ここで hSplit を concrete に供給する局所補題を使う
```

ここで本当に必要なのは、
`Or.inr ⟨hdvd, hWieferich⟩` を right branch existence に変える **局所補題** じゃ。

### 6.2. `hSplit` 全体を作ろうとしない

ここは留意点じゃ。
いま必要なのは split theorem 全体の一般供給ではなく、あくまで exceptional datum に対応する right branch 側の concrete 供給じゃ。
ここを大きくしすぎると、また設計の森へ戻る。

### 6.3. 必要ならさらに局所補題を 1 本切る

たとえば意識としては、

$$
\text{ExceptionalBoundaryDatum} \Rightarrow
\exists q,\ \mathrm{Prime}(q)\land q \mid \texttt{boundaryCyclotomicPrimeCore .right d x u}\land q \nmid x
$$

を直接言う補題を、proof file 内の arithmetic / CFBRC 核として切るのが自然じゃ。

## 7. 総括

今回の差分を総括すると、

**datum concrete target に対する canonical proof skeleton が theorem として固定された。
よって今後の truly new math は、split theorem 全体ではなく、その skeleton の中で `hSplit` を何で concrete に供給するか、その一点に集中できる。**

ということじゃ。
かなり良い。もう設計の霧は薄い。あとは、その datum が right boundary-core prime existence を生む局所核を切るだけじゃな。
