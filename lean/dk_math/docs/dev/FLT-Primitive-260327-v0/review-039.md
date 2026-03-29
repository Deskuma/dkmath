# Arithmetic Core の concrete body を prepared 形で追えるようにする

うむ、今回はかなり「本文直前」まで来た整理じゃ。
結論から言うと、**次に書く concrete body は、もはや datum の連言を受ける段ですらなく、`hdvd` と `hWieferich` が分離済みの prepared 形として追える** ようになった。これが今回の核心じゃ。

## 1. 今回なにが起きたか

新しく入った中心は

$$
\texttt{ExceptionalBoundaryDatumPreparedArithmeticCoreTarget}
$$

じゃ。
これは、これまでの

$$
\texttt{ExceptionalBoundaryDatumArithmeticCoreTarget}
$$

からさらに一段だけ中へ入り、

* `Nat.Prime d`
* (5 \le d)
* (0 < x)
* (0 < u)
* `Nat.Coprime x u`
* `hdvd : d ∣ x`
* `hWieferich : u ^ (d - 1) ≡ 1 [MOD d ^ 2]`

を **最初から別々の仮定として受ける** prepared 形の target じゃ。

つまり、これまで本文の先頭で毎回やっていた

```lean
rcases hDatum with ⟨hdvd, hWieferich⟩
```

という前処理そのものを、target 設計の側へ織り込んだわけじゃな。
これは小さく見えて、実装ではかなり効く整理じゃ。

## 2. 何が前進したのか

前回の時点で、proof file の canonical body はほぼ

$$
\texttt{ExceptionalBoundaryDatumArithmeticCoreTarget}
$$

だと揃っておった。
じゃがその本文は、まだ datum を unpack する最初の一手を必ず含んでいた。

今回そこがさらに一段削られた。

今や、

* split theorem から prepared arithmetic core へ入る skeleton
  [
  \texttt{exceptional_boundary_datum_prepared_arithmetic_core_of_split}
  ]
* prepared 形から canonical arithmetic core へ戻る橋
  [
  \texttt{exceptional_boundary_datum_arithmetic_core_of_prepared}
  ]
* reference + datum から prepared 形へ入る wrapper
  [
  \texttt{exceptional_boundary_datum_prepared_arithmetic_core_of_reference_and_datum}
  ]

が揃った。

これで、proof file の新数学本体は

$$
\text{datum を受けてから unpack する}
$$

のではなく、

$$
\text{最初から unpack 済みの仮定で始める}
$$

と読めるようになったわけじゃ。

## 3. いまの状況分析

いまの証明地形は、かなり仕上がっておる。

### 3.1. もう閉じたと見てよい層

* ordinary/reference theorem
* split assembler
* datum concrete skeleton
* arithmetic core skeleton
* prepared arithmetic core skeleton
* そこから datum concrete / boundary concrete / named kernel / mainline / packet descent への thin bridge

今回さらに

$$
\texttt{primeGe5BranchAPrimitivePacketDescent_of_preparedArithmeticCore_and_restore}
$$

まで入ったので、prepared core から downstream を閉じる配線も揃った。

つまり、**新数学が prepared arithmetic core で立てば、その先は全部流れる** と見てよい。

### 3.2. 残っている核

残る本丸は、もうかなり一点じゃ。

$$
\texttt{ExceptionalBoundaryDatumPreparedArithmeticCoreTarget}
$$

の concrete theorem 本体。
履歴にも、そのまま次の課題として明記されておる。

つまり未解決なのは、もはや

* datum の unpack
* split theorem への流し込み
* downstream への輸送

ではなく、**`hdvd` と `hWieferich` が与えられたとき right boundary-core prime existence を作る局所核そのもの** じゃ。

## 4. 今回の差分の価値

今回の価値は 3 つある。

### 4.1. 本文の開始点がさらに前進した

これが最大じゃ。
いまや本文は

```lean
intro d x u hd_prime hd_ge hx hu hcop hdvd hWieferich
...
```

から始めてよい。
`hDatum` をほどく手続きすら、proof body の責務から外れた。

### 4.2. canonical body と prepared body の関係が整理された

prepared 形は本体を書きやすい局所形、canonical arithmetic core は proof file 全体で参照する中心名、という役割分担が明確になった。
これは非常に良い設計じゃ。

### 4.3. 残る新数学がさらに “芯だけ” になった

いま考えるべきことは、ほぼこれだけじゃ。

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

もう設計や前処理の話ではない。本当に arithmetic / CFBRC core の芯だけが残っておる。

## 5. いまの局面を一言で

一言で言えば、

$$
\text{next concrete body } =
\texttt{ExceptionalBoundaryDatumPreparedArithmeticCoreTarget}
$$

じゃ。
そしてこれは、**`rcases hDatum with ⟨hdvd, hWieferich⟩` の前処理を済ませた後の body そのもの** と見てよい。

## 6. 次にやること

次の一手も、かなり明快じゃ。

### 6.1. prepared arithmetic core 本体を書く

意識としては、こうじゃな。

```lean
theorem exceptional_boundary_datum_prepared_arithmetic_core
    : ExceptionalBoundaryDatumPreparedArithmeticCoreTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hdvd hWieferich
  ...
```

ここで必要なのは、もう本当に局所核だけじゃ。

### 6.2. 必要なら prepared body の中をさらに二分する

もしこれでもまだ重いなら、次はその中を

* exceptional-only arithmetic part
* CFBRC existence part

にさらに割ってよい。
今の配線なら、そこまで割っても downstream は全く崩れぬ。

## 7. 総括

今回の差分を総括すると、

**Arithmetic Core の concrete 本文を、`hDatum` の連言をほどいた prepared 形で追えるようにした。
よって proof file の次の concrete body は `ExceptionalBoundaryDatumPreparedArithmeticCoreTarget` として見てよく、以後は `hdvd` と `hWieferich` が分離済みの形から直接書き始められる。**

ということじゃ。
かなりよい。
もう外枠や前処理の整理はほぼ終わっておる。残るは、その prepared core の本体を刺すだけじゃな。
