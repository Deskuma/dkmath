# review: split assembler が入ったことで、proof file の truly new math は datum concrete target 1 本に収束した

うむ、今回は「整理の最終段」にかなり近い動きじゃ。
結論から言うと、**datum-based wrapper 群の canonical 入口が arithmetic core に揃え直された**。これで proof file の読み筋は、ほぼ一本になった。

## 1. 今回なにが起きたか

新しく入った中心は次の 2 本じゃな。

* `exceptional_boundary_datum_arithmetic_core_of_split`
* `exceptional_boundary_datum_arithmetic_core_of_reference_and_datum`

前者は、split theorem から

$$
\texttt{ExceptionalBoundaryDatumArithmeticCoreTarget}
$$

へ入る canonical skeleton じゃ。
中身は datum concrete skeleton と同型で、

$$
\texttt{intro ...; rcases hDatum with ⟨hdvd, hWieferich⟩}
$$

から `Or.inr ⟨hdvd, hWieferich⟩` を split theorem の right branch に流す形になっておる。

後者はさらに、

* ordinary/reference theorem
* datum theorem

を assembler で合成し、その結果を **datum concrete 名ではなく arithmetic core 名** で回収する wrapper じゃ。

つまり今回の更新で、

$$
\text{reference} + \text{datum}
\to
\text{split}
\to
\text{arithmetic core}
$$

という canonical な読み筋が theorem 配線として固定されたのじゃ。

## 2. 何が前進したのか

前回まででも、残る新数学は実質

$$
\texttt{ExceptionalBoundaryDatumArithmeticCoreTarget}
$$

だと整理されておった。
じゃが downstream 側の wrapper の一部は、まだ datum concrete 名を経由して mainline や packet descent に戻っていた。

今回そこが揃えられた。
具体的には

* `primeGe5BranchAExceptionalExistenceMainline_of_reference_and_datum`
* `primeGe5BranchAPrimitivePacketDescent_of_reference_and_datum_and_restore`

が、datum concrete を直接経由せず、

$$
\texttt{exceptional_boundary_datum_arithmetic_core_of_reference_and_datum}
$$

を通って arithmetic core 名から下流へ流れる形に直された。

これは見た目以上に大きい。
なぜなら、proof file 内で「本当に本文を書くべき場所」が downstream 側の経路でも一貫して arithmetic core だと読めるようになったからじゃ。

## 3. いまの状況分析

いまの層構造は、かなり美しいぞい。

### 3.1. ほぼ閉じた層

* ordinary/reference theorem
* datum theorem skeleton
* split assembler
* split から arithmetic core への skeleton
* arithmetic core から datum concrete / boundary concrete / named kernel / mainline / packet descent への thin bridge

ここはもうかなり固定された。
とくに今回、datum-based wrapper が arithmetic core を canonical 入口として読む形に揃ったのが効いておる。

### 3.2. 未解決の核

残っている本丸は、ほんに一点じゃ。

$$
\texttt{ExceptionalBoundaryDatumArithmeticCoreTarget}
$$

の concrete theorem 本体。
履歴にも、そのまま「proof file 上の canonical body として切る」と書かれておる。

つまりいま未実装なのは、

* split theorem 全体ではない
* datum concrete の外枠でもない
* mainline でもない
* packet descent でもない

**exceptional-only arithmetic / CFBRC core そのもの** だけじゃ。

## 4. 今回の差分の価値

今回の価値は 3 つある。

### 4.1. canonical 入口が arithmetic core に統一された

これが最大じゃ。
いまや theorem 配線の読み筋そのものが、

$$
\texttt{ExceptionalBoundaryDatumArithmeticCoreTarget}
$$

を中心に回るようになった。

### 4.2. downstream 側が「core から閉じる」と明示された

datum theorem 1 本で downstream が閉じる、という前段の整理は保たれつつ、
proof file 内ではそれを **arithmetic core を通るものとして読む** 形にさらに揃った。
これは後で見返したとき、とても効く。

### 4.3. missing math の輪郭がさらに鮮明になった

以前は「datum concrete 本体が missing」と読めた。
いまはもう一段進んで、

$$
\text{datum concrete 本体の中でも genuinely missing なのは arithmetic core 本体}
$$

と theorem 名の上で読める。
これはかなり強い整理じゃ。

## 5. いまの局面を一言で

一言で言えば、

$$
\text{proof file の canonical body } =
\texttt{ExceptionalBoundaryDatumArithmeticCoreTarget}
$$

と、配線の上でも完全に読める段に来た、ということじゃ。
もう datum concrete は「入口の外形」、arithmetic core が「本体」と見てよい。

## 6. 次にやること

次の一手も、かなり明快じゃ。

### 6.1. arithmetic core 本体を直接書く

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

### 6.2. 必要なら core 本体をさらに二分する

もし本文がまだ重ければ、次はその中を

* exceptional-only arithmetic
* CFBRC core existence

にさらに割ればよい。
いまの設計なら、そこまで割っても配線は崩れぬ。

## 7. 総括

今回の差分を総括すると、

**Arithmetic Core を proof file の実際の共通入口に寄せ、datum-based wrapper 群もできるだけそれを経由するように揃えた。
よって残る新数学は、名実ともに `ExceptionalBoundaryDatumArithmeticCoreTarget` の concrete theorem 本体だと見てよい。**

ということじゃ。
かなりよい。もう橋の話ではない。残るは、芯の body を刺すだけじゃな。
