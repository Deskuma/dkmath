# 029. Stage 1 の残敵は \(P \mid (p)\) 分岐の contradiction theorem だけ

## 1. 戦況分析

かなり勝ち筋が見えてきたのぅ。
今回の更新で、**\(y \in P\) 分岐は no-sorry で閉じた**。
`noYInCommonPrime_of_chosenFactorInP_of_coprime_of_productEq` によって、

* \(y \in P\)
* chosen factor \(z-\zeta y \in P\)

から \(z \in P\)、さらに全因子が \(P\) に入り、積の恒等式から \(x^p \in P\)、よって \(x \in P\) を出し、最後に `Nat.Coprime x y` と衝突させる流れが確立したわけじゃ。

その前段でも既に、

* \((\zeta-1)\in P \Rightarrow P \mid (p)\)
* 共通 prime ideal から \(P \mid (p) \lor y \in P\)

までは、ring of integers specialization で no-sorry 化されておる。つまり、**共通 prime ideal の解析はもう “\(P \mid (p)\) 分岐だけ残った” 段まで進んだ** のじゃ。

## 2. いま何が残敵か

ゆえに、Stage 1 がまだ閉じぬ理由は、もう一点じゃ。

$$
\boxed{
P \mid (p)\ \text{分岐の contradiction が、まだ theorem として supply されていない}
}
$$

いまの構図はこうじゃ。

1. 共通 prime ideal \(P\) を仮定
2. no-sorry の補題で
   $$
   P \mid (p) \ \lor\ y \in P
   $$
   を得る
3. \(y \in P\) は今回もう閉じた
4. だから残るのは
   $$
   P \mid (p)
   $$
   だけ

ここまで来れば、Stage 1 は「coprimality が難しい」のではなく、**\(P \mid (p)\) を first case 条件とどう衝突させるか** だけが残っている、と読める。

## 3. Mathlib 側を踏まえた解説

official Mathlib docs 側では、cyclotomic ring of integers について

* `IsPrimitiveRoot.toInteger_sub_one_dvd_prime'`
* `IsPrimitiveRoot.subOneIntegralPowerBasis`
* `IsPrimitiveRoot.subOneIntegralPowerBasis_gen_prime`
* `IsPrimitiveRoot.finite_quotient_span_sub_one`

のような \((\zeta-1)\) 周辺の定理群が揃っておる。
今回ぬしが作った adapter も、まさに `toInteger_sub_one_dvd_prime'` を使って \((\zeta-1)\in P\Rightarrow P\mid (p)\) へ持ち上げたものじゃ。 ([leanprover-community.github.io][1])

ただし、official docs の見える範囲では、**「\(P \mid (p)\) かつ \((n:\mathcal O_K)\in P\) なら \(p \mid n\)」をそのまま返す ready-made な補題は、少なくとも表面には見えておらぬ **。
ゆえに、ここは Mathlib の既存 theorem をそのまま探すより、** short adapter を 1 本自前で切る** 方が速いとわっちは見る。 ([leanprover-community.github.io][1])

## 4. 次の戦略

次の最短戦略は、かなり明確じゃ。

### 4.1. 本命

まず、**\(P \mid (p)\) 分岐専用の contradiction theorem** を切る。

狙う形は、だいたいこれじゃ。

$$
\text{prime ideal } P,\quad P \mid (p),\quad z-\zeta y \in P,\quad
\prod_j (z-\zeta^j y)=x^p
\Rightarrow \bot
$$

ただし実際には、直接 \(\bot\) を言うより、一度

$$
(x : \mathcal O_K) \in P
\Rightarrow
p \mid x
$$

へ落として、pack の first case 条件 \(p \nmid x\) とぶつけるのが最短じゃ。

### 4.2. そのための補助補題

わっちなら、次の 2 本に分ける。

#### A. chosen factor から \((x \in P)\) を出す補題

chosen factor が \(P\) に入れば、全積
$$
\prod_j (z-\zeta^j y)=x^p
$$
も \(P\) に入る。prime ideal だから
$$
x^p \in P \Rightarrow x \in P
$$
が出る。
これはもう今の `ideal_prod_mem_of_all_mem` 系の流れと同じ発想で、軽い。

#### B. \(P \mid (p)\) かつ \((x:\mathcal O_K)\in P \Rightarrow p \mid x\)

これが本命の short adapter じゃ。
理想としては theorem 名もそのまま、

`natCast_mem_primeOverPrime_implies_prime_dvd`

のようなものがよい。

これが出れば、

* common prime analysis
* \(P \mid (p)\) 分岐
* chosen factor から \((x \in P)\)
* よって \(p \mid x\)
* first case と矛盾

で終わる。

## 5. なぜこの戦略が最短か

理由は単純じゃ。

* \(y \in P\) 分岐はもう閉じた
* \((\zeta-1)\in P \Rightarrow P \mid (p)\) adapter もある
* 共通 prime idealの存在から disjunction を出す機械もある
* 残るのは \(P \mid (p)\) だけ

ならば、generic 化を増やすのではなく、**first case と \(P \mid (p)\) を正面衝突させる 1 本** を作るのがいちばん短い。
しかもこの route は、ぬしが今回閉じた \(y\)-branch と対称で、proof architecture が美しい。
Stage 1 の最後の穴が「disjunction のもう片方」だけになるからのぅ。

## 6. 提案

わっちの提案を一言でまとめるぞい。

$$
\boxed{
\text{次は } P \mid (p)\text{ 分岐専用の contradiction theorem を作る}
}
$$

順番はこうじゃ。

1. `chosen factor ∈ P → (x : 𝓞 K) ∈ P`
2. `P ∣ (p) ∧ (x : 𝓞 K) ∈ P → p ∣ x`
3. pack の first case で矛盾
4. `P ∣ (p) ∨ y ∈ P` の両分岐が閉じる
5. pairwise coprimality
6. Stage 1 explicit equality
7. Stage 2 は既存 receiver で自動

ここまで行けば、Stage 1 はほぼ閉じる。
残る honest open は、ほんに Stage 3 の norm descent に寄るはずじゃよ。

[1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/Cyclotomic/Basic.html?utm_source=chatgpt.com "Mathlib.NumberTheory.NumberField.Cyclotomic.Basic"
