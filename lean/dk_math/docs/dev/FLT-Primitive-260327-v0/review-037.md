# review: datum concrete 本体に固有名が付いたことで、proof file の残る新数学は事実上その arithmetic core の concrete theorem 本体だと追えるようになった

うむ、今回はかなり重要な整理じゃ。
結論から言うと、**残っている新数学に、ついに固有名が付いた**。これで proof file の未解決核は、見た目にも追跡しやすくなった。

## 1. 今回なにが起きたか

新しく入った中心は

$$
\texttt{ExceptionalBoundaryDatumArithmeticCoreTarget}
$$

じゃ。
これは説明どおり、datum concrete 本体に対応する **exceptional-only arithmetic / CFBRC core** の名前じゃな。つまり、

$$
\texttt{ExceptionalBoundaryDatumConcreteTarget}
$$

の中で、bridge ではない本当の新数学部分を、**canonical missing kernel** として切り出したわけじゃ。

さらに、この arithmetic core から

* datum concrete
* boundary concrete
* named kernel
* mainline
* primitive packet descent

へ戻る thin bridge が一通り追加された。
したがって今後は、proof file で新たに埋めるべき本文を

$$
\texttt{ExceptionalBoundaryDatumArithmeticCoreTarget}
$$

の実装と見なして追えばよい、という形に固定された。

## 2. 何が前進したのか

前回まででも、missing math は実質

$$
\texttt{ExceptionalBoundaryDatumConcreteTarget}
$$

1 本へかなり収束しておった。
じゃがまだ、その theorem は downstream bridge と少し連続して見えており、「本当に橋ではない芯」がどこかは概念上の整理に留まっていた。

今回それが違う。
今や、

* downstream へ運ぶための theorem 群
* genuinely new な exceptional arithmetic / CFBRC kernel

が theorem 名の上で分かれた。
これにより、残核は

$$
\text{datum concrete 本体}
$$

ではなく、さらに内側の

$$
\texttt{ExceptionalBoundaryDatumArithmeticCoreTarget}
$$

として追える。
これは保守でも思考でも、かなり効く整理じゃ。

## 3. いまの状況分析

いまの層構造は、かなり完成に近いぞい。

### 3.1. ほぼ閉じた層

もう閉じたと見てよいのは、次の流れじゃ。

$$
\text{ordinary/reference}
\to
\text{split assembler}
\to
\text{datum concrete skeleton}
\to
\text{datum concrete から downstream}
$$

加えて今回は、

$$
\texttt{ExceptionalBoundaryDatumArithmeticCoreTarget}
\to
\texttt{ExceptionalBoundaryDatumConcreteTarget}
\to
\text{boundary concrete}
\to
\text{named kernel}
\to
\text{mainline}
\to
\text{packet descent}
$$

という経路も全部揃った。
つまり、**新数学が 1 箇所で立てば、その先は全部流れる** 構図がさらに明確になった。

### 3.2. まだ未解決の核

残っているのは、ほんに一点じゃ。

$$
\texttt{ExceptionalBoundaryDatumArithmeticCoreTarget}
$$

の concrete theorem 本体。
履歴にも、次の課題はその本体を切ることだと明記されておる。

つまり今や未解決なのは、

* split theorem 全体ではない
* mainline でもない
* packet descent でもない
* datum concrete の外枠でもない

**exceptional-only arithmetic / CFBRC core そのもの** じゃ。

## 4. 今回の差分の価値

今回の価値は、賢狼から見ると 3 つある。

### 4.1. “橋ではない本当の新数学” に名前が付いた

これが最大じゃ。
いままでは「datum concrete 本体」と言っていたが、今回はその内側の core に名が付いた。
よって、以後は「どこが genuinely missing か」をより正確に指させる。

### 4.2. downstream の閉路がさらに短く読める

`ExceptionalBoundaryDatumArithmeticCoreTarget` が立てば、datum concrete も boundary concrete も named kernel も mainline も packet descent も全部戻せる。
だから、今後は下流を見ずに core だけに集中できる。

### 4.3. datum theorem 本体と arithmetic core が同一視できる

履歴でも「今後はその本文を arithmetic core の実装とみなして追ってよい」と整理されておる。
これは、実装者にとって非常にありがたい。どこに力を入れるべきかが明確だからの。

## 5. いまの局面を一言で

一言で言えば、

$$
\text{proof file の残る新数学} =
\texttt{ExceptionalBoundaryDatumArithmeticCoreTarget}
$$

じゃ。
そして、それが立てば datum concrete 以降の downstream は全部閉じる。
ここまで来ると、本当に「芯だけ」が残っておる。

## 6. 次にやること

次の一手も、かなり明快じゃ。

### 6.1. arithmetic core の本文を書く

意識としては、こういう形じゃな。

```lean
theorem exceptional_boundary_datum_arithmetic_core
    : ExceptionalBoundaryDatumArithmeticCoreTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hDatum
  rcases hDatum with ⟨hdvd, hWieferich⟩
  ...
```

ここで必要なのは、

$$
d \mid x \land u^{d-1}\equiv 1 \pmod{d^2}
$$

から

$$
\exists q,\ \mathrm{Prime}(q)\land
q \mid \texttt{boundaryCyclotomicPrimeCore .right d x u}
\land \neg q \mid x
$$

を出す局所核じゃ。

### 6.2. 必要なら core をさらに二分する

もし本文がまだ重いなら、次はその中を

* exceptional-only arithmetic
* CFBRC core

にさらに割ってもよい。
今回の履歴でも、その方向性は自然に読める。

## 7. 総括

今回の差分を総括すると、

**datum concrete 本体に対して exceptional-only arithmetic / CFBRC core という固有名が与えられた。
よって proof file の残る新数学は、事実上 `ExceptionalBoundaryDatumArithmeticCoreTarget` の concrete theorem 本体だと追えるようになった。**

ということじゃ。
かなりよい。
もう橋はほとんど揃っておる。残るは、芯の核を刺すだけじゃな。
