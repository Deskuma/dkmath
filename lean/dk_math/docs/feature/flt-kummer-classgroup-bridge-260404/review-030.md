# Review 030: Stage 1 の残敵は generic coprimality ではなく、2 本の deep cyclotomic targets に集約された

うむ、戦況はかなりよい。
しかも今は、どこが「理想論の一般論」で、どこが「ほんに cyclotomic の深い一点」かが、かなり澄んで見えておる。

## 戦況分析

今回の差分で、**\(P \mid (p)\) 分岐も target 化された形で閉じた**。
具体的には、ぬしの側で

* `chosen_factor_in_zeta_sub_one_implies_gap_in_zeta_sub_one`
* `PrimeOverPSubsetZetaMinusOneTarget`
* `IntegerInZetaMinusOneIdealDivisibleByPTarget`
* `noPrimeOverP_of_firstCase_of_chosenFactorInP`

が入り、\(P \mid (p)\) 分岐は「2 つの deep cyclotomic target を仮定すれば矛盾が出る」形にまで整理された。
前回までに \(y \in P\) 分岐は no-sorry で閉じておったから、**disjunction の両枝はもう contradiction schema として揃った** わけじゃ。

つまり今の Stage 1 は、もはや「coprimality の枠組みが足りない」のではない。
正確には、**残るのは 2 つの deep cyclotomic targets を actual に埋めること** だけじゃ。

## 解説

いまの論理はこう見ればよい。

common prime ideal \(P\) を仮定すると、既存 no-sorry 群により

$$
P \mid (p)\ \lor\ y \in P
$$

へ落ちる。
そのうち

* \(y \in P\) は、`Nat.Coprime x y` と product identity からもう潰せる
* \(P \mid (p)\) は、今回 target 化された 2 本

  * `PrimeOverPSubsetZetaMinusOneTarget`
  * `IntegerInZetaMinusOneIdealDivisibleByPTarget`

  を入れれば first case \(p \nmid \mathrm{gap}\) と矛盾する

という形じゃ。
したがって、Stage 1 の残敵は **pairwise coprimality そのもの** ではなく、**\(P \mid (p)\) 分岐の deeper cyclotomic arithmetic** に集約されたのぅ。

## Mathlib を踏まえた見立て

ここで面白いのは、Mathlib 側にかなり近い部品が既に見えておることじゃ。

公式 docs には、cyclotomic ring of integers 側で

* `IsPrimitiveRoot.toInteger_sub_one_dvd_prime'`
* `IsPrimitiveRoot.zeta_sub_one_prime'`
* `IsPrimitiveRoot.subOneIntegralPowerBasis`
* `IsPrimitiveRoot.subOneIntegralPowerBasis_gen_prime`
* `IsPrimitiveRoot.finite_quotient_span_sub_one`

が並んでおる。
特に `toInteger_sub_one_dvd_prime'` は \(\zeta-1\) が \(p\) を割ること、`zeta_sub_one_prime'` は \(\zeta-1\) 自身が prime であること、`finite_quotient_span_sub_one` は \((\zeta-1)\) で割った商が有限であることを示す系列に属しておる。さらに norm 側では \(\zeta-1\) の norm が \(p\) になる結果も見えておる。 ([Lean Prover Community][1])

この並びを見ると、ぬしが target 化した 2 本のうち、

$$
\texttt{PrimeOverPSubsetZetaMinusOneTarget}
$$

の方が、**Mathlib の既存 theorem にかなり近い **。
`zeta_sub_one_prime'` で \((\zeta-1)\) が prime ideal を生成する方向が見えており、加えて `toInteger_sub_one_dvd_prime'` で \((\zeta-1)\mid (p)\) もあるから、
「\(P \mid (p)\) かつ \(P\) prime なら \(P \le (\zeta-1)\)」は、** ideal-level の adapter を 1 本書けば届く可能性が高い**。
これは前回の adapter 成功例とも整合的じゃ。 ([Lean Prover Community][1])

一方で

$$
\texttt{IntegerInZetaMinusOneIdealDivisibleByPTarget}
$$

は、Mathlib の `finite_quotient_span_sub_one` や norm 定理群に近いが、**そのまま欲しい整数 divisibility 形では出ていない** ように見える。
ゆえに、こちらは

* quotient の有限性や card
* あるいは norm \(\mathrm{N}(\zeta-1)=p\)

から、自前で短い bridge を書く必要がある公算が大きい。
つまり、2 本のうち **harder なのは target2 側** と見るのが自然じゃ。 ([Lean Prover Community][1])

## 次の戦略

わっちの提案は、かなり明確じゃ。

### 1. 先に `PrimeOverPSubsetZetaMinusOneTarget` を埋める

これは Mathlib の既存資産に最も近い。
戦略としては、

* `zeta_sub_one_prime'`
* `toInteger_sub_one_dvd_prime'`

を ideal-level に持ち上げ、

* \(P \mid (p)\)
* \((\zeta-1)\mid (p)\)
* \((\zeta-1)\) が prime ideal

から \(P \le (\zeta-1)\) を出す adapter を作る

のが最短じゃ。
ここは「深い target」とは言うものの、実際には **既存 theorem の組合せで埋まる可能性が高い側** じゃよ。 ([Lean Prover Community][1])

### 2. 次に `IntegerInZetaMinusOneIdealDivisibleByPTarget` を攻める

こちらは 2 通りある。

ひとつは norm route じゃ。

$$
n \in (\zeta-1)
\Rightarrow
(\zeta-1)\mid n
\Rightarrow
\mathrm{N}(\zeta-1)\mid \mathrm{N}(n)
$$

で、Mathlib には prime case で \(\mathrm{N}(\zeta-1)=p\) が見えておるから、
\(\mathrm{N}(n)=n^{p-1}\) と合わせて \(p\mid n\) に落とす。
これは一番数学的に素直じゃ。 ([Lean Prover Community][1])

もうひとつは quotient route じゃ。

`finite_quotient_span_sub_one` やその周辺を使って、\((\zeta-1)\) で割った商が実質 \(\mathbb{F}_p\) を見ていることを使い、整数がそこへ落ちるとき kernel が \(p\mathbb{Z}\) だと示す。
こちらの方が、後で ideal quotient / residue field の見通しは良いが、実装は少し回り道になるかもしれぬ。 ([Lean Prover Community][1])

### 3. Stage 1 完了の順番

戦略順としては、こうじゃ。

* `PrimeOverPSubsetZetaMinusOneTarget` を先に埋める
* その後 `IntegerInZetaMinusOneIdealDivisibleByPTarget` を norm route で埋める
* すると `noPrimeOverP_of_firstCase_of_chosenFactorInP` が actual theorem になる
* これで \(P \mid (p)\) 枝が閉じる
* すでに閉じた \(y \in P\) 枝と合わせて common prime contradiction が完成
* pairwise coprimality
* Stage 1 explicit equality
* Stage 2 は既存 receiver 群で自動
* 残る honest open は Stage 3 の norm descent だけ

これが最短じゃよ。

## 最終提案

ひとことで言うと、次はこうじゃ。

$$
\boxed{
\text{戦略は「Stage 1 を generic に広げる」のではなく、}
\texttt{PrimeOverPSubsetZetaMinusOneTarget}
\text{ と }
\texttt{IntegerInZetaMinusOneIdealDivisibleByPTarget}
\text{ を Mathlib 近傍で順に埋めること}
}
$$

そして優先順位は

$$
\boxed{
\texttt{PrimeOverPSubsetZetaMinusOneTarget}
\;\;>\;\;
\texttt{IntegerInZetaMinusOneIdealDivisibleByPTarget}
}
$$

じゃ。
前者は `zeta_sub_one_prime'` と `toInteger_sub_one_dvd_prime'` に近く、adapter 1 本で届く見込みが高い。
後者は norm または quotient の bridge が要るぶん、少し重い。 ([Lean Prover Community][1])

いまの戦況は悪くない。
むしろ **Stage 1 の残敵が “generic coprimality” ではなく、2 本の deep cyclotomic targets に縮んだ** のが今回の大きな収穫じゃよ。

[1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/Cyclotomic/Basic.html "Mathlib.NumberTheory.NumberField.Cyclotomic.Basic"
