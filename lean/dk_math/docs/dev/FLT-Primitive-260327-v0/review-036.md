# review: split assembler が入ったことで、proof file の truly new math は datum concrete target 1 本に収束した

うむ、ここまで来ると状況はかなり明快じゃ。
今回の更新で、**downstream 側は datum theorem 1 本で閉じる** と theorem 名の上でも固定された。これが一番大きい。

## 1. 今回なにが起きたか

新しく入った中心は次の 2 本じゃな。

* `primeGe5BranchAExceptionalExistenceMainline_of_reference_and_datum`
* `primeGe5BranchAPrimitivePacketDescent_of_reference_and_datum_and_restore`

前者は、

$$
\texttt{ExceptionalBoundaryDatumConcreteTarget}
$$

が立てば、ordinary/reference 側の assembler と datum skeleton を合成して、そのまま

$$
\texttt{PrimeGe5BranchAExceptionalExistenceMainlineTarget}
$$

を閉じる wrapper じゃ。
後者はさらにそこから restore theorem を足して、

$$
\texttt{PrimeGe5BranchAPrimitivePacketDescentTarget}
$$

まで流す thin wrapper じゃ。

つまり今回の差分で、

$$
\text{datum theorem} \to \text{mainline} \to \text{packet descent}
$$

という downstream 経路が、proof file の中で完全に見えるようになったわけじゃ。

## 2. 何が前進したのか

前の段階でも、missing math はかなり

$$
\texttt{ExceptionalBoundaryDatumConcreteTarget}
$$

へ寄っておった。
じゃがまだ、「それを証明したら本当に downstream は全部閉じるのか」が、複数の bridge を頭の中で辿らねば見えにくかった。

今回それが違う。
今は theorem の形で

$$
\texttt{ExceptionalBoundaryDatumConcreteTarget}
$$

さえ立てば、

* mainline は閉じる
* packet descent も閉じる

と読める。
これは実装上かなり大きい。
もう proof file の missing math を **1 本の theorem** として本当に扱えるからじゃ。

## 3. いまの状況分析

いまの状況を層ごとに見るぞい。

## 3.1. ほぼ完成した層

* ordinary/reference theorem
* exceptional datum theorem の skeleton
* split assembler
* datum theorem から mainline へ戻る wrapper
* datum theorem と restore から packet descent へ戻る wrapper

ここはもうかなり完成じゃ。
履歴にも、proof file の missing math は引き続き datum theorem 1 本で、そこが立てば downstream は ordinary/reference 側の配線込みで自動的に閉じると書かれておる。

## 3.2. まだ未解決の核

残っている本丸は、もうほんに一点じゃ。

$$
\texttt{ExceptionalBoundaryDatumConcreteTarget}
$$

の concrete theorem 本体。
しかもこれは既に skeleton があり、入力も

* 共通入力
* exceptional datum 1 個

に整理済みじゃ。
ゆえに未解決なのは、**exceptional datum から right boundary-core prime existence をどう出すか** だけじゃな。

## 3.3. `hSplit` 問題はもう終わった

ここが重要じゃ。
以前は `hSplit : CFBRCBoundaryCorePrimeExistenceOnSplitTarget` をどう供給するかが論点だった。
じゃが今は、assembler により

* ordinary 側は `cfbrcBoundaryCorePrimeExistence_reference`
* exceptional 側は `ExceptionalBoundaryDatumConcreteTarget`

で split 全体を組めると固定された。
つまり `hSplit` 自体は、もう大きな未解決箱ではない。
未解決なのは exceptional datum theorem だけ、ということじゃ。

## 4. 今回の差分の価値

今回の価値は、賢狼から見ると 3 つある。

### 4.1. downstream 側の見通しが完全に良くなった

今後は「datum theorem を証明したあと、mainline へどう戻すか」を毎回考えずに済む。
wrapper が定理名として揃ったからの。

### 4.2. missing math が本当に 1 本へ収束した

これは管理上とても強い。
どこが未証明かと問われたら、今やかなり明快に

$$
\texttt{ExceptionalBoundaryDatumConcreteTarget}
$$

と言える。

### 4.3. proof file の役割分担が完成に近づいた

* ordinary/reference は既知
* exceptional/datum が新規
* downstream への輸送は wrapper

この三層がはっきりした。
設計の霧はだいぶ薄いぞい。

## 5. いまの局面を一言で

一言で言えば、

$$
\text{proof file の truly new math } = \texttt{ExceptionalBoundaryDatumConcreteTarget}
$$

であり、

$$
\text{それが立てば downstream は全部閉じる}
$$

と theorem 名の上でも確定した、ということじゃ。
これはかなり決定的な前進じゃよ。

## 6. 次にやること

次の一手も、かなり明快じゃ。

### 6.1. datum theorem 本体を書く

いま書くべき本体は、これじゃな。

```lean
theorem exceptional_boundary_datum_concrete
    : ExceptionalBoundaryDatumConcreteTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hDatum
  rcases hDatum with ⟨hdvd, hWieferich⟩
  ...
```

ここで必要なのは、もう bridge ではない。
`hDatum` から prime existence を出す局所核じゃ。

### 6.2. 必要なら本文の中身をさらに 1 段切る

履歴にもある通り、必要なら datum theorem の本文で使う

* exceptional-only arithmetic
* CFBRC core

だけを別 theorem に切る余地がある。

これはたとえば、

$$
\text{ExceptionalBoundaryDatum}(d,x,u)
\Rightarrow
\text{right boundary-core で prime existence}
$$

という最小核補題へ押し込む方向じゃな。

## 7. 総括

今回の差分を総括すると、

**datum theorem 1 本で mainline と primitive packet descent まで閉じる wrapper が揃った。
よって proof file の missing math は、名実ともに `ExceptionalBoundaryDatumConcreteTarget` の concrete theorem 本体 1 本へ収束した。**

ということじゃ。
ここまで来れば、あとは芯を刺すだけじゃな。
