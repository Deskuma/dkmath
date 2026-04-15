# review: split assembler が入ったことで、proof file の truly new math は datum concrete target 1 本に収束した

うむ、これはかなり決定的じゃ。
今回の差分で、**`hSplit` をどう供給するか** まで整理が終わった。これで proof file の missing math は、ほぼ名実ともに **`ExceptionalBoundaryDatumConcreteTarget` ただ 1 本** へ収束したと言ってよい。

## 1. 今回なにが起きたか

新しく追加された中心は

$$
\texttt{cfbrcBoundaryCorePrimeExistence_split_of_reference_and_datum}
$$

じゃ。
これは役割として、**split theorem 全体を組み立てる assembler** じゃな。中身はとても明快で、

* 通常枝 `Or.inl hOrd` では
  $$
  \texttt{cfbrcBoundaryCorePrimeExistence_reference}
  $$
  を使う
* 例外枝 `Or.inr hExc` では
  $$
  \texttt{ExceptionalBoundaryDatumConcreteTarget}
  $$
  を使う

という二分岐の合成になっておる。

つまり今回の整理で、

$$
\text{split theorem 全体} =
\text{ordinary/reference}
;\cup;
\text{exceptional/datum}
$$

という構図が theorem の形そのものとして固定されたわけじゃ。

## 2. 何が前進したのか

前回の時点で、datum concrete target の canonical skeleton として

$$
\texttt{exceptional_boundary_datum_concrete_of_split}
$$

が置かれており、そこでは `hSplit` を仮定として受けておった。
じゃがまだ、その `hSplit` 自体をどう見るかが少し抽象的だった。

今回それが完全に整理された。

今や

$$
hSplit
$$

は mysterious な大きい仮定ではなく、

$$
\texttt{cfbrcBoundaryCorePrimeExistence_split_of_reference_and_datum}
$$

で組み立てられるもの、と fixed された。
そしてその assembler の中で truly new なのは exceptional 側だけ、すなわち

$$
\texttt{ExceptionalBoundaryDatumConcreteTarget}
$$

だけじゃと明示された。

これはかなり大きい。
なぜなら、もう今後は `CFBRCBoundaryCorePrimeExistenceOnSplitTarget` 全体を“未解決の箱”として見る必要がなくなったからじゃ。

## 3. いまの状況分析

いまの証明地形は、かなりきれいじゃ。

## 3.1. すでに閉じた層

* ordinary/reference theorem
* split assembler
* datum concrete skeleton
* right branch supply への橋
* named kernel への橋
* mainline への橋
* primitive packet descent への橋

ここはもうかなり固まっておる。
特に今回の assembler により、`hSplit` の供給経路まで定理で固定されたのは大きい。

## 3.2. 未解決の核

残っている新数学は、ほんとうにかなり狭くなった。

$$
\texttt{ExceptionalBoundaryDatumConcreteTarget}
$$

を返す concrete theorem 本体。
これだけじゃ。

しかも、その本文はすでに skeleton により

```lean
intro ...
rcases hDatum with ⟨hdvd, hWieferich⟩
...
```

から始めればよいと固定されておる。
だから残るのは、**datum から right boundary-core prime existence を出す局所 arithmetic / CFBRC 核** だけじゃ。

## 3.3. ordinary 側との差分

ここが非常に見やすくなった。

共通部分は

* `Nat.Prime d`
* `5 ≤ d`
* `0 < x`
* `0 < u`
* `Nat.Coprime x u`

そして差分は

$$
\texttt{ExceptionalBoundaryDatum}(d,x,u)
$$

ただ 1 個。
今回の assembler によって、その差分だけを exceptional theorem に押し込めば split 全体が立つ、と theorem の形で保証された。

つまり ordinary 側はもう終わっていて、exceptional 側だけを書けばよい、ということじゃ。

## 4. 今回の差分の価値

今回の価値は 3 つある。

### 4.1. `hSplit` が「未解決の大箱」ではなくなった

これが最大じゃ。
いまや `hSplit` は assembler で供給できるものであり、その missing part は datum theorem 1 本だけじゃ。

### 4.2. proof file の truly new math が theorem 形で 1 本に縮んだ

これは管理上とても強い。
今後「どこが未証明か」を聞かれたら、かなり自信をもって

$$
\texttt{ExceptionalBoundaryDatumConcreteTarget}
$$

と言える。

### 4.3. datum skeleton と assembler が噛み合った

`exceptional_boundary_datum_concrete_of_split` の中で必要な `hSplit` は、この assembler で供給すればよいと履歴にも明記されておる。
つまり skeleton と配線が finally 合流したのじゃ。

## 5. いまの局面を一言で

一言で言えば、

$$
\text{proof file の missing math } = \texttt{ExceptionalBoundaryDatumConcreteTarget}
$$

と、もう theorem の形で言える段階に来た。
これはかなり良い。設計の霧はだいぶ晴れたぞい。

## 6. 次にやること

次の一手は、もうかなり明快じゃ。

### 6.1. datum concrete theorem 本体を直接書く

意識としては、こんな形でよい。

```lean id="wodt2x"
theorem exceptional_boundary_datum_concrete
    : ExceptionalBoundaryDatumConcreteTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hDatum
  rcases hDatum with ⟨hdvd, hWieferich⟩
  -- exceptional-only arithmetic / CFBRC core
```

ここで本当に必要なのは、

$$
\texttt{ExceptionalBoundaryDatum} \Rightarrow
\exists q,\ \mathrm{Prime}(q)\land q \mid \texttt{boundaryCyclotomicPrimeCore .right d x u}\land \neg q \mid x
$$

を出す局所核じゃ。

### 6.2. assembler はもう触らなくてよい

ここは大事じゃ。
`cfbrcBoundaryCorePrimeExistence_split_of_reference_and_datum` ができた以上、split theorem 全体のことはもう忘れてよい。
exceptional datum theorem だけに集中すれば、下流は自動的に流れる。

### 6.3. 必要なら datum theorem の本文をさらに二分する

履歴にもある通り、必要なら datum theorem 自体の本文も

* exceptional-only arithmetic
* CFBRC core

にさらに局所化できる。

つまり次に切る補題候補は、たとえば

$$
\text{Wieferich + } d \mid x
;\Rightarrow;
\text{right boundary core に primitive/prime existence}
$$

という、ほんとうに芯だけのものじゃな。

## 7. 総括

今回の差分を総括すると、

**ordinary/reference と exceptional/datum を合成する split assembler が入ったことで、`hSplit` 供給の問題は解消された。
よって proof file の truly new math は `ExceptionalBoundaryDatumConcreteTarget` 1 本だと、定理の形でもさらに明確になった。**

ということじゃ。
かなりよい。ここからは、いよいよ芯の theorem を切る段じゃな。
