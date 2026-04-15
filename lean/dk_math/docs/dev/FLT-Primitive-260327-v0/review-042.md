# review: prepared concrete 本体の着手点に固有名が付いた

うむ、今回はかなり実務的で良い分割じゃ。
結論から言うと、**prepared concrete 本体がまだ重いなら、それを 2 つの局所 kernel に割って追えばよい**、という形が theorem として固定された。これが今回の本質じゃ。

## 1. 今回なにが起きたか

新しく入った中心は 3 つじゃ。

* `ExceptionalBoundaryDatumPreparedArithmeticPartTarget`
* `ExceptionalBoundaryDatumPreparedCFBRCExistencePartTarget`
* `exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_parts`

前の 2 つは、prepared concrete 本体を 2 分するための part target じゃ。
後の 1 つは、その 2 つを合成すれば

$$
\texttt{ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget}
$$

が閉じる、という assembler じゃな。

つまり今や、prepared concrete 本体が重ければ、missing math を

### A. exceptional arithmetic part

$$
\exists q,\ \mathrm{Prime}(q)\land \neg q \mid x
$$

までを返す部分

### B. CFBRC existence part

その (q) について

$$
q \mid \texttt{boundaryCyclotomicPrimeCore .right d x u}
$$

だけを返す部分

の 2 本として追えるようになったわけじゃ。

## 2. 何が前進したのか

前回までで、prepared concrete 本体こそが next body であり、

$$
\texttt{ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget}
$$

を直接埋めるのが本丸だと整理されておった。

じゃがその本体が重い場合、どこで切るかはまだ少し曖昧だった。
今回そこが定理の形で固定された。

つまり、prepared concrete 本体はもう

$$
\text{candidate prime を選ぶ arithmetic}
$$

と

$$
\text{その prime が boundary core を割ることを示す CFBRC existence}
$$

の合成と見てよい。

これはかなり大きい。
なぜなら、「本文が重い」という感覚的問題が、**2 つの theorem target** に変換されたからじゃ。

## 3. いまの状況分析

いまの証明地形は、さらに見通しが良くなった。

### 3.1. すでに閉じた層

* ordinary/reference theorem
* split assembler
* datum concrete skeleton
* arithmetic core skeleton
* prepared arithmetic core skeleton
* prepared concrete skeleton
* prepared concrete から downstream への thin bridge

ここまではもうかなり安定しておる。

### 3.2. 残る本丸

本来の本丸は引き続き

$$
\texttt{ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget}
$$

じゃ。
ただし今回は、それをさらに必要に応じて

* `ExceptionalBoundaryDatumPreparedArithmeticPartTarget`
* `ExceptionalBoundaryDatumPreparedCFBRCExistencePartTarget`

の 2 本として追ってよいと定まった。

つまり、残る新数学は 1 本にも 2 本にも読めるが、
**2 本に割るなら割り方まで fixed された**、ということじゃな。

## 4. どの 2 part が何を担当するか

ここをはっきり押さえると、今後の実装判断がしやすい。

## 4.1. Arithmetic Part

これは

$$
d \mid x,\qquad u^{d-1}\equiv 1 \pmod{d^2}
$$

などの exceptional datum から、まず

$$
\exists q,\ \mathrm{Prime}(q)\land \neg q \mid x
$$

を取るところまでを担当する。

言い換えると、
**「候補 prime を見つける」** のがこの part の責務じゃ。

## 4.2. CFBRC Existence Part

こちらは arithmetic part で得た (q) を受け取って、

$$
q \mid \texttt{boundaryCyclotomicPrimeCore .right d x u}
$$

だけを示す。

つまり、
**「その候補 prime が本当に boundary core を割る」**
を担当する part じゃ。

この分割はかなり自然じゃよ。
prime の **選定** と **存在証明の回収** を分けたのじゃからな。

## 5. 今回の差分の価値

今回の価値は 3 つある。

### 5.1. “重い本文” の分解位置が fixed された

これが最大じゃ。
今後、prepared concrete 本体が重いと感じたら、どこで切ればよいかもう迷わぬ。

### 5.2. arithmetic と CFBRC の責務が分離された

これは非常に良い。
今までは両者が 1 本の theorem 本体に同居していたが、今回は

* arithmetic は candidate prime を出す
* CFBRC は divisibility を返す

と役割が完全に分かれた。

### 5.3. 2 part を合成すれば prepared concrete 本体が閉じる

`exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_parts` があるので、2 part に割っても downstream 配線は崩れぬ。
これは実装上かなりありがたい。

## 6. いまの局面を一言で

一言で言えば、

$$
\text{next body は引き続き prepared concrete 本体だが、必要なら}
$$

$$
\text{arithmetic part と CFBRC existence part の 2 本に割って追える}
$$

ということじゃ。
これは、実装が重くなったときの逃げ道ではなく、**正式な設計** として固まった、というのが大事じゃよ。

## 7. 次にやること

報告にもある通り、次はこの 2 本のうち、まず

$$
\texttt{ExceptionalBoundaryDatumPreparedArithmeticPartTarget}
$$

を攻めるのが自然じゃ。

賢狼もそれに賛成じゃ。

なぜなら、いまの分割では

* arithmetic part で (q) を確保する
* existence part でその (q) の divisibility を示す

ので、**先に (q) を取れぬと後段が始まらぬ** からじゃ。

### 7.1. 次の実装対象

意識としては、こういう形じゃな。

```lean id="wx2yld"
theorem exceptional_boundary_datum_prepared_arithmetic_part
    : ExceptionalBoundaryDatumPreparedArithmeticPartTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hdvd hWieferich
  ...
```

ここで目標は

$$
\exists q,\ \mathrm{Prime}(q)\land \neg q \mid x
$$

だけじゃ。
まだ `boundaryCyclotomicPrimeCore` を割ることまでは要らぬ。

### 7.2. その次

Arithmetic part が立てば、つぎに

$$
\texttt{ExceptionalBoundaryDatumPreparedCFBRCExistencePartTarget}
$$

で、その (q) が `boundaryCyclotomicPrimeCore .right d x u` を割ることだけを詰めればよい。

## 8. 総括

今回の差分を総括すると、

**prepared concrete 本体がまだ重いなら、それを candidate prime を返す exceptional arithmetic part と、boundary core divisibility を返す CFBRC existence part の 2 本に局所化して追えばよい、と theorem 形で固定された。
よって今後の next body は引き続き prepared concrete 本体だが、実装順としてはまず `ExceptionalBoundaryDatumPreparedArithmeticPartTarget` を攻めるのが自然だと見てよい。**

ということじゃ。
かなりよい。
ここまで来れば、残る戦いは本当に局所核の切り出しじゃな。
