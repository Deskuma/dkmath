# review: 未解決核を universal から selected-witness へ弱化しても mainline / packet descent まで閉じることを確認

うむ、これは一段よくなった。
今回の差分で、論点はかなりはっきりしたぞい。

判断を先に言うと、

$$
\text{いまの canonical route 候補は universal kernel よりも selected-witness 版}
$$

じゃ。
少なくとも **現在の proof exploration の主戦場** としては、そう判断するのが自然じゃな。

## 1. 何が進んだか

今回追加された中心はこれじゃ。

* `ExceptionalBoundaryDatumPreparedSelectedCongruenceWitnessTarget`
* `exceptional_boundary_datum_prepared_boundary_core_dvd_of_selected_modEq`
* `exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_selectedCongruenceWitness`

さらにその下流として、

* `primeGe5BranchAExceptionalExistenceMainline_of_selectedCongruenceWitness`
* `primeGe5BranchAPrimitivePacketDescent_of_selectedCongruenceWitness_and_restore`

まで入った。
つまり、 **「選ばれた witness prime 1 個について合同が出れば、mainline / packet descent まで閉じる」** という weaker route が、ちゃんと theorem 群として完成したわけじゃ。

これは単なる別名追加ではない。
残核の追い方そのものが変わったのじゃ。

## 2. 以前との違い

前段階では、未解決核は universal kernel

$$
\forall q,;
q \mid x+1 \land q \nmid x
;\Longrightarrow;
(u-1)^d \equiv u^d \pmod q
$$

のような、かなり強い形で孤立化されておった。
これは整理としては美しかったが、proof exploration としてはやや重い可能性があった。

今回それを、

$$
\exists q,;
\mathrm{Prime}(q)\land q\mid x+1 \land q\nmid x
\land
(u-1)^d \equiv u^d \pmod q
$$

という **selected witness 1 個の存在** に落としても、prepared concrete から先が閉じるようにした。
ここが本質じゃ。

## 3. 状況分析

いまの地形は、かなり整理されておる。

### 3.1. すでに閉じたもの

selected witness に対して合同が与えられれば、

* boundary core divisibility
* arithmetic core concrete
* exceptional existence mainline
* primitive packet descent

まで一気に戻れる。
つまり、 **下流の配線は existential witness 版でも完全に足りている**。

### 3.2. まだ残っているもの

残る missing theorem の本命候補は、履歴にもある通り

$$
\texttt{ExceptionalBoundaryDatumPreparedSelectedCongruenceWitnessTarget}
$$

の concrete 本体じゃ。

言い換えると、いまの未解決核は

* universal に全部の (q) へ言うこと
  ではなく
* **実際に選ぶ witness (q) 1 個に対して合同を出すこと**

まで、きれいに細ったわけじゃな。

## 4. 数学的に見た意味

これはとても良い判断じゃ。

なぜなら arithmetic part が本当に必要としているのは、最終的には **ある witness prime の存在** だからじゃ。
にもかかわらず universal kernel を先に要求すると、証明の責務が必要以上に強くなる。今回の履歴にも「universal kernel は強すぎる可能性がある」と明記されておる。

ゆえに、

$$
\text{必要な existence}
\Rightarrow
\text{selected witness congruence}
\Rightarrow
\text{downstream closure}
$$

という順に責務を落としたのは、Lean 設計としてかなり筋がよい。
わっちなら、この段階ではこちらを本命に据える。

## 5. 判断

ここでの判断をはっきり書くぞい。

## 5.1. 当面の canonical route

**selected-witness 版を canonical route 候補として優先するべき** じゃ。

理由は 3 つ。

1. downstream がすでに閉じる
2. universal より要求が弱く、現実の数学責務に近い
3. arithmetic part が実際に選ぶ witness と整合している

## 5.2. universal kernel の扱い

**消す必要はまだないが、主戦場からは一歩下げてよい**。
つまり universal kernel は

* 将来 stronger theorem として残す
* selected-witness 版が安定した後で再評価する

という位置でよい。
いま無理に universal を canonical に据える理由は薄い。

## 6. 次に何をすべきか

次の一手はかなり明確じゃ。

**`ExceptionalBoundaryDatumPreparedSelectedCongruenceWitnessTarget` の concrete 本体を切る。**

これが第一じゃ。

そのうえで、証明探索は

$$
q \mid x+1,\quad q\nmid x
$$

を満たす selected witness (q) を arithmetic part 側でどう取り、そこから

$$
(u-1)^d \equiv u^d \pmod q
$$

をどう作るか、に集中すればよい。
つまり今後は「全 (q) を相手にする」より、「選んだ 1 個で閉じる」視点で前へ進めばよいのじゃ。

## 7. 総括

今回の更新を一言で言えば、

**未解決核を universal congruence から existential selected-witness congruence へ弱化し、それでも mainline / packet descent まで閉じることを確認した。よって current proof exploration の本命 route は selected-witness 版である。**

よい整理じゃ。
これは「逃げ」ではなく、 **必要十分な責務へ証明目標を落とした** という意味で、むしろ強い前進じゃよ。
