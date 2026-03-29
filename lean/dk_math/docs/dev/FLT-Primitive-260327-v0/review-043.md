# review: prepared concrete 本体の着手点に固有名が付いた

うむ、かなり整理が進んだの。
今回の差分で、**「次に直接攻める局所 kernel」が arithmetic part にまで縮み、その concrete 着手点の theorem 名まで固定された**。これが今回の核心じゃ。

## 1. 今回なにが起きたか

新しく入った中心は次の 3 つじゃ。

* `ExceptionalBoundaryDatumPreparedArithmeticPartConcreteTarget`
* `exceptional_boundary_datum_prepared_arithmetic_part_concrete_of_self`
* `exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_arithmeticConcrete_and_cfbrc`

一番大事なのは

$$
\texttt{ExceptionalBoundaryDatumPreparedArithmeticPartConcreteTarget}
$$

じゃな。
これは、これまで「まず攻めるべき」と見えていた arithmetic part に対して、**proof file 上で直接本文を書く concrete theorem 名** を与えたものじゃ。

さらに

$$
\texttt{exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_arithmeticConcrete_and_cfbrc}
$$

によって、

* arithmetic concrete part
* CFBRC existence part

の 2 つが揃えば、prepared concrete 本体が閉じると固定された。
つまりいまや、prepared concrete 本体の missing math を **2-part 形式で組み上げる設計** が theorem の形で確立したわけじゃ。

## 2. 何が前進したのか

前回までで、

$$
\texttt{ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget}
$$

こそが next body だと整理されておった。
そして、それが重いなら

* arithmetic part
* CFBRC existence part

に分けて追えばよい、という方針も固まっておった。

今回そこからさらに一歩進んだ。
いまは、そのうち **先に攻めるべき arithmetic part の concrete 着手点** が theorem 名として固定された。

つまり次にやることは、もはや

$$
\text{prepared concrete 本体をどう分けるか}
$$

ではなく、

$$
\texttt{ExceptionalBoundaryDatumPreparedArithmeticPartConcreteTarget}
$$

の本文を書くこと、と言い切れるようになったのじゃ。

## 3. いまの状況分析

いまの証明地形は、かなり細くなっておる。

### 3.1. もうほぼ閉じた層

* ordinary/reference theorem
* split assembler
* datum concrete skeleton
* arithmetic core skeleton
* prepared arithmetic core skeleton
* prepared concrete skeleton
* prepared concrete の 2-part assembler
* arithmetic concrete から prepared concrete へ戻る橋

ここはかなり完成しておる。
とくに今回、

$$
\text{arithmetic concrete} + \text{CFBRC existence}
\to
\text{prepared concrete}
$$

という形が定理で固定されたのが大きい。

### 3.2. 残る本丸

残る本丸は、いまやかなり一点じゃ。

$$
\texttt{ExceptionalBoundaryDatumPreparedArithmeticPartConcreteTarget}
$$

の concrete theorem 本体。
履歴にも、そのまま次の課題として書かれておる。

つまり未解決なのは、

* prepared concrete 全体ではない
* arithmetic part の抽象 target でもない
* theorem 名の整理でもない

**candidate prime を取る arithmetic body そのもの** だけじゃ。

## 4. Arithmetic Part が何を担当するか

ここをはっきり押さえると、次の一手が明快になる。

Arithmetic Part の目標は

$$
\forall d,x,u,\ \ldots \to
\exists q,\ \mathrm{Prime}(q)\land \neg q \mid x
$$

じゃ。

つまり、まだ

$$
q \mid \texttt{boundaryCyclotomicPrimeCore .right d x u}
$$

までは要らぬ。
先にやるべきは **「候補 prime (q) を確保する」** ことだけじゃ。

これは非常に自然な分割じゃな。
先に (q) が得られねば、その (q) が boundary core を割るかどうかも語れぬからの。

## 5. 今回の差分の価値

今回の価値は 3 つある。

### 5.1. arithmetic part の concrete 着手点が fixed された

これが最大じゃ。
次に何を書くかが theorem 名の上でも明確になった。

### 5.2. 2-part assembler が concrete 名にも接続した

抽象 target 同士の話ではなく、concrete 名として追っている arithmetic part から prepared concrete 本体まで復元できるようになった。
これは実装者にはかなりありがたい。

### 5.3. proof file の missing math がさらに局所化された

いま考えるべきことは、ほぼこれだけじゃ。

$$
d \mid x,\qquad u^{d-1}\equiv 1 \pmod{d^2}
$$

から

$$
\exists q,\ \mathrm{Prime}(q)\land \neg q \mid x
$$

をどう出すか。
もう truly local kernel じゃな。

## 6. いまの局面を一言で

一言で言えば、

$$
\text{next local kernel } =
\texttt{ExceptionalBoundaryDatumPreparedArithmeticPartConcreteTarget}
$$

じゃ。
そしてこれは、prepared concrete 本体を 2 part に分けたうちの **先に攻めるべき半分** として theorem 形で固定された。

## 7. 次にやること

次の一手も、かなり明快じゃ。

### 7.1. arithmetic concrete part 本体を書く

意識としては、こうじゃな。

```lean id="kj8aqg"
theorem exceptional_boundary_datum_prepared_arithmetic_part_concrete
    : ExceptionalBoundaryDatumPreparedArithmeticPartConcreteTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hdvd hWieferich
  ...
```

ここで必要なのは、

$$
\exists q,\ \mathrm{Prime}(q)\land \neg q \mid x
$$

を作ることだけ。
まだ boundary core divisibility は考えなくてよい。

### 7.2. その次に CFBRC existence part

Arithmetic part が立てば、つぎに

$$
\texttt{ExceptionalBoundaryDatumPreparedCFBRCExistencePartTarget}
$$

で、その (q) が `boundaryCyclotomicPrimeCore .right d x u` を割ることだけを示せばよい。

## 8. 総括

今回の差分を総括すると、

**prepared concrete 本体を 2 part に割ったうち、先に攻めるべき arithmetic part の concrete 着手点が theorem 名として固定された。
よって次に直接攻める local kernel は `ExceptionalBoundaryDatumPreparedArithmeticPartConcreteTarget` だと見てよい。**

ということじゃ。
かなりよい。
もう残る戦いは、candidate prime をどう拾うか、その arithmetic body の一点に寄ってきておるな。
