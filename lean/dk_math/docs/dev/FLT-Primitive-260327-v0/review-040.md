# review: prepared concrete 本体の着手点に固有名が付いた

うむ、かなり良い。
今回は **「prepared body の concrete 本文を書き始める場所」そのものに、ついに固有名が付いた** のが本質じゃ。これで、残る本丸は見た目の上でもかなり追いやすくなった。

## 1. 今回なにが起きたか

新しく入った中心は

$$
\texttt{ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget}
$$

じゃ。
これは、

$$
\texttt{ExceptionalBoundaryDatumPreparedArithmeticCoreTarget}
$$

という抽象 target に対して、**proof file 上で直接本文を書くための concrete theorem 名** を与えたものじゃな。

さらに今回は、その concrete 名から

* canonical prepared target
* canonical arithmetic core
* primitive packet descent

へ戻る thin bridge も揃えられた。
つまり、いまや

$$
\text{prepared concrete body}
\to
\text{prepared target}
\to
\text{arithmetic core}
\to
\text{downstream}
$$

という流れが、theorem 名の上で読めるようになったわけじゃ。

## 2. 何が前進したのか

前回までで、proof file の次の concrete body は

$$
\texttt{ExceptionalBoundaryDatumPreparedArithmeticCoreTarget}
$$

として追えばよいと整理されておった。
じゃがまだ、それは少し抽象的で、「どの theorem 名に本文を書くのか」は実務上の約束に近かった。

今回それが違う。
今やその着手点そのものが

$$
\texttt{ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget}
$$

として固定された。
つまり今後は、「prepared body の本体はどこへ書くか」で迷わずに済む。これは実装上かなり効く整理じゃ。

## 3. いまの状況分析

いまの証明地形は、ほとんど完成に近い。

### 3.1. すでに安定した層

* ordinary/reference theorem
* split assembler
* datum concrete skeleton
* arithmetic core skeleton
* prepared arithmetic core skeleton
* prepared arithmetic core concrete 名
* そこから datum concrete / arithmetic core / downstream への thin bridge

今回は特に

* `exceptional_boundary_datum_prepared_arithmetic_core_of_concrete`
* `exceptional_boundary_datum_arithmetic_core_of_preparedConcrete`
* `primeGe5BranchAPrimitivePacketDescent_of_preparedConcrete_and_restore`

が入り、prepared concrete 名から下流まで流れる道が見えやすくなった。

つまり、**新数学がこの concrete 名の本文として立てば、その先は全部閉じる** と見てよい。

### 3.2. 未解決の核

残っている本丸は、さらに一点じゃ。

$$
\texttt{ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget}
$$

の concrete theorem 本体。
履歴にも、そのまま「次の課題」として書かれておる。

つまり今や未解決なのは、

* datum の unpack
* prepared 形への前処理
* downstream への橋

ではない。

**`hdvd` と `hWieferich` が最初から分離された prepared body そのもの** だけじゃ。

## 4. 今回の差分の価値

今回の価値は 3 つある。

### 4.1. concrete body の着手点に固有名が付いた

これが最大じゃ。
今後は

$$
\texttt{ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget}
$$

を見れば、「ここに本文を書くのだな」と一目で分かる。

### 4.2. abstract target と concrete theorem 名の役割が分離された

prepared target は理論上の目標、prepared concrete は実際の実装着手点。
この二層が分かれたのは良い設計じゃ。

### 4.3. downstream がさらに気に不要になった

prepared concrete 名が立てば、prepared target・arithmetic core・packet descent まで既存 bridge で全部流せる。
だから今後は本当に本文だけに集中できる。

## 5. いまの局面を一言で

一言で言えば、

$$
\text{next concrete body } =
\texttt{ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget}
$$

じゃ。
しかもこれは、**proof file 上で直接追うべき canonical な theorem 名** として固定された。

## 6. 次にやること

次の一手も、かなり明快じゃ。

### 6.1. prepared concrete 本体を書く

意識としては、こうじゃな。

```lean
theorem exceptional_boundary_datum_prepared_arithmetic_core_concrete
    : ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hdvd hWieferich
  ...
```

ここで必要なのは、もう本当に核心だけじゃ。

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

### 6.2. まだ重ければ、その本文の中をさらに割る

もしこれでもまだ重いなら、最後に残るのは

* exceptional arithmetic 部
* CFBRC existence 部

の二分じゃろう。
いまの設計なら、そこまで割っても全体配線は崩れぬ。

## 7. 総括

今回の差分を総括すると、

**prepared arithmetic core の concrete 本文を、proof file 上で直接追える theorem 名として固定した。
よって残る本丸は、名実ともに `ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget` の concrete 本体だと見てよい。**

ということじゃ。
かなりよい。
もう設計や命名の整理は、ほぼ終わっておる。残るは、その prepared body の芯を刺すだけじゃな。
