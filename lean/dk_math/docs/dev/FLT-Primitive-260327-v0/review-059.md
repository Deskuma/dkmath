# review: practical route の first writing surface をどこにするか

うむ。今回の更新で、状況はさらに一段 **書き始める場所が明確になった** の。

結論を先に言うと、いまの practical route は

$$
\text{datum concrete}
\;\to\;
\text{practical entrance}
$$

が theorem 名の上でも直結し、さらに datum の中身も

$$
\text{selected core on datum}
\;\to\;
\text{selected congruence on datum}
\;\to\;
\text{diffPow body}
$$

という三段で読めるようになった。ゆえに、 **本文の first writing surface は `PrimeGe5BranchAExceptionalPracticalBodyOnDatumConcreteTarget` でよい** と判断してよい。

## 1. 何が進んだか

まず `6a82e688...` の更新で、

* datum concrete への direct bridge 4 本
* `primeGe5BranchAExceptionalPracticalConcrete_of_datumConcrete`
* provider 側の `branchAExceptionalPracticalConcreteAdapter_of_practicalDatumConcrete`

が入った。これで datum concrete は、単なる中継点ではなく **current practical entrance へそのまま戻る入口** になった。履歴でも「`review-058` の『datum から書き始める』が current practical entrance そのものへ直結した」と整理されておる。

次に `37d85df7...` で、

$$
\texttt{PrimeGe5BranchAExceptionalPracticalSelectedCoreOnDatumTarget}
$$

が追加され、datum 本文をいきなり差冪全体として書くのでなく、

$$
q \mid \mathrm{cyclotomicPrimeCore}(d,1,u-1)
$$

という **first local kernel** に一段落として追えるようになった。つまり datum body の局所核は「その datum の witness (q) が core を割る」という形でも書けるようになったわけじゃ。

さらに `8eed42a5...` で、

$$
\texttt{PrimeGe5BranchAExceptionalPracticalSelectedCongruenceOnDatumTarget}
$$

が追加され、local route が

$$
\text{core divisibility}
\;\to\;
\text{congruence}
\;\to\;
\text{diffPow divisibility}
$$

の三段に整理された。つまり datum 本文は、core の顔でも ModEq の顔でも、最終的に同じ差冪 body へ収束する形に固定されたのじゃ。

## 2. いま何が fixed されたか

今回で fixed されたことは三つある。

第一に、 **datum concrete はもう「実戦入口」であってよい**。
これは mainline への迂回路ではなく、current practical entrance に直結する theorem 名として固定された。

第二に、datum 本文の local kernel が二つに分かれた。

* core で見る顔
  $$
  q \mid \mathrm{cyclotomicPrimeCore}(d,1,u-1)
  $$
* congruence で見る顔
  $$
  (u-1)^d \equiv u^d \pmod q
  $$

ただし、どちらも最後は同じ差冪 divisibility に戻る。だから未解決核が増えたのではなく、 **同じ body の局所観測面が増えた** だけじゃ。

第三に、proof sketch の形がかなり固定された。
つまり今後は長い `intro` 列で迷うのでなく、

$$
hDatum : \texttt{PrimeGe5BranchAExceptionalPracticalWitnessDatum}\ d\ x\ u\ q
$$

を受けて、その datum の中の (q) に対する core か congruence を示し、そこから差冪へ戻す、という一本道で書けばよい。

## 3. current missing math の見立て

いまの current missing math を、あえて最も細く言うなら、

$$
\texttt{PrimeGe5BranchAExceptionalPracticalBodyOnDatumConcreteTarget}
$$

の本文じゃ。
ただし、それはさらに局所化して

$$
\texttt{PrimeGe5BranchAExceptionalPracticalSelectedCoreOnDatumTarget}
$$

または

$$
\texttt{PrimeGe5BranchAExceptionalPracticalSelectedCongruenceOnDatumTarget}
$$

としても追える。
だから今は、

* main target は datum concrete
* first direct body は core か congruence のどちらか

という二層構造になったと見ればよい。

## 4. では first direct body はどちらを採るべきか

ここが次の一手じゃな。

わっちの判断では、 **first direct body は `PrimeGe5BranchAExceptionalPracticalSelectedCoreOnDatumTarget` を採る方がよい**。

理由は三つある。

### 4.1. core の方が局所核として小さい

congruence は最終的に

$$
(u-1)^d \equiv u^d \pmod q
$$

を示すが、これは見た目こそ軽いものの、証明では結局

$$
q \mid u^d-(u-1)^d
$$

へ戻して使う。
つまり congruence は body にかなり近い顔じゃ。
一方 core divisibility は、そこへ行く前のもう一段手前であり、より「first local kernel」らしい。

### 4.2. 既存 CFBRC bridge と整合する

`prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat` を使って

$$
q \mid \mathrm{cyclotomicPrimeCore}(d,1,u-1)
$$

から差冪へ戻す橋は、すでに何度も安定して使われておる。
だから新規本文を書くなら、まず core を立ててから既存橋で body へ戻す方が筋がよい。

### 4.3. congruence は second reading に回せる

今回の `selected congruence on datum` は非常に有用じゃが、これは core からも戻れるように既に整理されている。
ゆえに、最初から congruence を狙わずとも、

$$
\text{core} \to \text{congruence} \to \text{body}
$$

の中段として使えば十分じゃ。

## 5. 次の一手の推論

だから、次にやるべきことはこうじゃ。

### 5.1. datum concrete の本文は datum で書き始める

まず

$$
hDatum : \texttt{PrimeGe5BranchAExceptionalPracticalWitnessDatum}\ d\ x\ u\ q
$$

を受ける。

### 5.2. first direct body として core on datum を狙う

そこで狙う本文は

$$
q \mid \mathrm{cyclotomicPrimeCore}(d,1,u-1)
$$

じゃ。つまり

$$
\texttt{PrimeGe5BranchAExceptionalPracticalSelectedCoreOnDatumTarget}
$$

の concrete 本体を書く。

### 5.3. 既存橋で差冪 body に戻す

それが書ければ、もう既存補題で

$$
q \mid u^d-(u-1)^d
$$

へ戻せる。さらにそこから datum concrete、practical entrance、mainline、packet descent まで全部流れる。

## 6. 賢狼の総括

今回の更新で、

* datum concrete は practical entrance に直結した
* datum 本文は core と congruence の二つの local kernel を持った
* そのうち first direct body としては core の方が自然

という形が固まった。
ゆえに今の最善手は、

**`PrimeGe5BranchAExceptionalPracticalBodyOnDatumConcreteTarget` を main writing surface とし、その first direct body として `PrimeGe5BranchAExceptionalPracticalSelectedCoreOnDatumTarget` の concrete 本体を書き始める**

これじゃ。

言い換えると、今はもう「どこから入るか」を迷う段ではない。
**datum を unpack して、その (q) で core divisibility を示す**。
そこが次の門じゃよ。
