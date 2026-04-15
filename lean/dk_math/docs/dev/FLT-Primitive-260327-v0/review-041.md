# review: prepared concrete 本体の着手点に固有名が付いた

うむ、今回はかなり **「本文を書く瞬間」** に寄った整理じゃ。
結論から言うと、**prepared concrete 本体の “書き始め” まで theorem 名として固定された**。これが今回の本質じゃ。

## 1. 今回なにが起きたか

今回の中心は次の 4 本じゃな。

* `exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_split`
* `exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_reference_and_datum`
* `primeGe5BranchAExceptionalExistenceMainline_of_preparedArithmeticCore`
* `primeGe5BranchAExceptionalExistenceMainline_of_preparedConcrete`

このうち一番大事なのは

$$
\texttt{exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_split}
$$

じゃ。
これは、prepared concrete theorem 名に対する **canonical proof skeleton** をそのまま theorem として置いたものじゃな。中身は非常に明快で、

```lean
intro d x u hd_prime hd_ge hx hu hcop hdvd hWieferich
```

から入り、そのまま split theorem の right branch へ流す形を固定しておる。

つまり今や、次に書く本文は

* どの theorem 名に置くか
* どの仮定列から始めるか
* 最初に何をするか

まで含めて、ほぼ完全に見えるようになったわけじゃ。

## 2. 何が前進したのか

前回までで、

$$
\texttt{ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget}
$$

という **prepared body の concrete theorem 名** は fixed されておった。

じゃがまだ、「では実際に本文をどこから書き始めるのか」は、設計上の了解に少し依っておった。
今回それが違う。

いまは

$$
\texttt{exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_split}
$$

があるので、prepared concrete 本体は **この skeleton を差し替える作業** と見なせる。

これはかなり効く整理じゃ。
もう「どう始めるか」で迷う必要がないからの。

## 3. いまの状況分析

いまの証明地形は、かなり仕上がっておる。

### 3.1. ほぼ閉じた層

* ordinary/reference theorem
* split assembler
* datum concrete skeleton
* arithmetic core skeleton
* prepared arithmetic core skeleton
* prepared concrete theorem 名
* prepared concrete skeleton
* そこから mainline / packet descent への thin bridge

今回さらに

* `primeGe5BranchAExceptionalExistenceMainline_of_preparedArithmeticCore`
* `primeGe5BranchAExceptionalExistenceMainline_of_preparedConcrete`

が入ったので、prepared core / prepared concrete から mainline へ戻る道もはっきりした。

つまり、**prepared concrete が立てば mainline まで一直線** と見てよい。

### 3.2. 未解決の核

残っている本丸は、いよいよかなり一点じゃ。

$$
\texttt{ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget}
$$

の concrete theorem 本体。
履歴にも、そのまま「次の課題」として明記されておる。

つまりいま未解決なのは、

* theorem 名の整理でもない
* downstream 配線でもない
* `hDatum` の unpack でもない
* mainline への復元でもない

**prepared concrete body そのもの** だけじゃ。

## 4. 今回の差分の価値

今回の価値は 3 つある。

### 4.1. 本文の開始点が theorem 名で固定された

これが最大じゃ。
いまや prepared concrete 本体は、

$$
\texttt{exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_split}
$$

を見れば、どこから書き始めるか一目で分かる。

### 4.2. prepared concrete から mainline までの道が見える

これは実務上かなりありがたい。
proof body を差し替えたあと、その成果が mainline にどう届くかを毎回頭で辿らずに済む。

### 4.3. 残る新数学がさらに “本文だけ” になった

いま考えるべきことは、ほんにこれだけじゃ。

$$
d \mid x,\qquad u^{d-1}\equiv 1 \pmod{d^2}
$$

から

$$
\exists q,\ \mathrm{Prime}(q)\land
q \mid \texttt{boundaryCyclotomicPrimeCore .right d x u}
\land \neg q \mid x
$$

を出すこと。

もう設計も命名も、ほぼ外へ押し出された。

## 5. いまの局面を一言で

一言で言えば、

$$
\text{next concrete body } =
\texttt{ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget}
$$

であり、しかもその本文は

$$
\texttt{exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_split}
$$

から書き始めればよい、と theorem 名の上でも fixed された、ということじゃ。

## 6. 次にやること

次の一手も、かなり明快じゃ。

### 6.1. prepared concrete 本体を差し替える

意識としては、こうじゃな。

```lean
theorem exceptional_boundary_datum_prepared_arithmetic_core_concrete
    : ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hdvd hWieferich
  ...
```

ここで必要なのは、split theorem を仮定することではなく、
その right branch existence を **局所 arithmetic / CFBRC core** から直接生むことじゃ。

### 6.2. まだ重ければ、本体内部をさらに二分する

もしこれでも重いなら、最後に残るのは

* exceptional arithmetic 補題
* CFBRC existence 補題

の二分じゃろう。
いまの設計なら、そこまで割っても全体の読み筋はまったく崩れぬ。

## 7. 総括

今回の差分を総括すると、

**prepared concrete theorem 名に対する canonical proof skeleton が置かれたことで、proof file でいま直接追うべき着手点は `exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_split` から始まる本文だと明確になった。
よって残る本丸は、名実ともに `ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget` の concrete 本体だと見てよい。**

ということじゃ。
かなりよい。
もう橋の話ではなく、本文そのものの戦いに入っておるな。
