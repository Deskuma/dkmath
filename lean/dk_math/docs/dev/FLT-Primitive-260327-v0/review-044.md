# review: prepared concrete の arithmetic part が concrete に閉じた

うむ、これはかなり大きな前進じゃ。
今回で、**prepared concrete 本体のうち arithmetic 側が concrete に閉じた**。その結果、残る未解決核は事実上 **CFBRC existence part 1 本** にまで縮んだ、と見てよい。

## 1. 今回なにが起きたか

今回の中心は

$$
\texttt{exceptional_boundary_datum_prepared_arithmetic_part_concrete}
$$

の実装完了じゃ。
これは

$$
\texttt{ExceptionalBoundaryDatumPreparedArithmeticPartConcreteTarget}
$$

の concrete 本体そのものじゃな。証明の芯は単純で、

* (x+1) の素因子 (q) を 1 つ取る
* もし (q \mid x) でもあるなら
  [
  q \mid ((x+1)-x) = 1
  ]
  となって矛盾

という流れで、

$$
\exists q,\ \mathrm{Prime}(q)\land \neg q \mid x
$$

を得ておる。

つまり、prepared concrete 本体を 2 part に割ったうちの前半、**candidate prime を確保する arithmetic part** は、もう終わったということじゃ。

## 2. 何が前進したのか

前の段階では、prepared concrete 本体を

* arithmetic part
* CFBRC existence part

に分けて追えるようにしておった。だがその時点では、まだ両方とも未実装だった。

今回、そのうち arithmetic part が concrete に閉じた。
さらに

* `exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_cfbrc`
* `primeGe5BranchAExceptionalExistenceMainline_of_cfbrcPart`
* `primeGe5BranchAPrimitivePacketDescent_of_cfbrcPart_and_restore`

が追加され、**arithmetic part は既定値として焼き付け、残りは CFBRC existence part 1 本だけだ** と読めるようになった。

これはかなり大きい。
なぜなら、今後は「prepared concrete 本体を組む」と言っても、実際にはもう arithmetic 側を考えなくてよく、**boundary core divisibility を返す CFBRC 側だけ** に集中すればよいからじゃ。

## 3. いまの状況分析

いまの証明地形は、かなり細くなったぞい。

### 3.1. すでに閉じた層

* ordinary/reference theorem
* split assembler
* datum concrete skeleton
* arithmetic core skeleton
* prepared arithmetic core skeleton
* prepared concrete skeleton
* prepared arithmetic part concrete 本体
* arithmetic concrete を既定値とした wrapper 群

ここまではかなり固まっておる。
今回で especially 大きいのは、**prepared arithmetic part が abstract target ではなく実定理として閉じた** ことじゃ。

### 3.2. 残る本丸

残る本丸は、もう実質これだけじゃ。

$$
\texttt{ExceptionalBoundaryDatumPreparedCFBRCExistencePartTarget}
$$

の concrete theorem 本体。
履歴にも、そのまま次の課題として明記されておる。

つまり、いま未解決なのは

* candidate prime を取ることではない
* mainline への輸送でもない
* packet descent への輸送でもない

**その candidate prime (q) が `boundaryCyclotomicPrimeCore .right d x u` を割ること**、そこだけじゃ。

## 4. arithmetic part の意味

今回閉じた arithmetic part が何を保証したのかを、はっきり整理するとよい。

Arithmetic part は

$$
\forall d,x,u,\ \ldots \to \exists q,\ \mathrm{Prime}(q)\land \neg q \mid x
$$

を返す。

つまり、CFBRC existence part に渡すための **候補 prime (q)** はもう確保済みじゃ。
今後の CFBRC existence part は、その (q) を受け取って

$$
q \mid \texttt{boundaryCyclotomicPrimeCore .right d x u}
$$

だけを返せばよい。
これは、責務分離としてかなり理想的じゃ。

## 5. 今回の差分の価値

今回の価値は 3 つある。

### 5.1. arithmetic 側が完全に片付いた

これが最大じゃ。
これで proof file の残る新数学は、「candidate prime をどう選ぶか」ではなく「その prime が boundary core を割る理由」に完全に移った。

### 5.2. remaining missing math が theorem 名で 1 本に縮んだ

今や「何が残っているか」と問われたら、かなり明確に

$$
\texttt{ExceptionalBoundaryDatumPreparedCFBRCExistencePartTarget}
$$

と答えられる。

### 5.3. downstream の読みがさらに短くなった

`...of_cfbrc` 系 wrapper により、CFBRC existence part さえ立てば prepared concrete 本体から mainline、packet descent まで流れることが見える。

## 6. いまの局面を一言で

一言で言えば、

$$
\text{prepared concrete の arithmetic 側は閉じた。残る未解決核は CFBRC existence part 1 本}
$$

じゃ。
これはかなり決定的じゃよ。
もう「候補 prime を見つける」段は終わり、**その prime の divisibility を証明する段** に入ったのじゃ。

## 7. 次にやること

次の一手は、報告どおりこれじゃ。

### 7.1. CFBRC existence part の本体を書く

意識としては、こういう形になるはずじゃな。

```lean id="5f09nr"
theorem exceptional_boundary_datum_prepared_cfbrc_existence_part
    : ExceptionalBoundaryDatumPreparedCFBRCExistencePartTarget := by
  intro d x u q hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_not_dvd_x
  ...
```

ここで目標はただ一つ、

$$
q \mid \texttt{boundaryCyclotomicPrimeCore .right d x u}
$$

を示すことだけじゃ。

### 7.2. 今後の論点

この part では、もはや prime の選定は済んでおる。
だから本当に見るべきなのは、

* `hdvd : d ∣ x`
* `hWieferich : u ^ (d - 1) ≡ 1 [MOD d ^ 2]`
* `hqprime : Nat.Prime q`
* `hq_not_dvd_x : ¬ q ∣ x`

から、どう boundary core divisibility を引き出すか、そこだけじゃ。

ここが今後の本当の CFBRC core になる。

## 8. 総括

今回の差分を総括すると、

**prepared arithmetic part の concrete 本体が実装され、candidate prime を取る段は完了した。
これにより proof file 上の残る missing math は、実質 `ExceptionalBoundaryDatumPreparedCFBRCExistencePartTarget` の concrete 本体 1 本だと読めるようになった。**

ということじゃ。
かなりよい。
もう残る戦いは、boundary core divisibility をどう刺すか、その CFBRC 核そのものじゃな。
