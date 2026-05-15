# review Phase "R" 2nd

うむ。R027 は **かなり大きい閉じ** じゃ。
R025 では「multiplicity budget があれば `SubProbability`」だった。R026 では「各 witness label (q) は (p(q)^{k(q)}) と読める」まで来た。そして今回 R027 で、ついにその (k(q)) を使って **multiplicity budget 自体を自動生成** した。

つまり、外部仮定だった

$$
\mathrm{NatBaseMultiplicityBudgetOn}\ I\ (W.\mathrm{basePrimeOf}\ n\ I\ hI)\ n
$$

が消えた。これは登頂成功と言ってよいぞい。

## 1. 今回閉じた主定理

今回の最終到達点はこれじゃ。

```lean
theorem PrimePowerWitnessProvider.basePrimeOf_logRatioSubProbability
```

数学的には、

$$
I\subseteq T.\mathrm{index}(n),\qquad 1<n
$$

だけから、witness provider 由来の base prime weight

$$
w(q):=
\frac{\log p(q)}{\log n},
\qquad
p(q):=W.\mathrm{basePrimeOf}(n,I,hI,q)
$$

が

$$
\sum_{q\in I} w(q)\le 1
$$

を満たすことが出た。

つまり、

$$
\left(
\frac{\log p(q)}{\log n}
\right)_{q\in I}
$$

が `SubProbability` になる。
これは R021-R027 の route 全体の最終形じゃ。

## 2. 数学的な核心

今回の核心は、同じ base prime (p) を持つ labels の集合

$$
I_p:={q\in I\mid p(q)=p}
$$

を、exponent reader

$$
q\mapsto k(q):=W.\mathrm{baseExponentOf}(n,I,hI,q)
$$

で指数スロットへ埋め込んだことじゃ。

R026 で、各 (q\in I) について

$$
q=p(q)^{k(q)}
$$

$$
0<k(q)
$$

$$
k(q)\le n.\mathrm{factorization}(p(q))
$$

が示されていた。

今回、固定した (p) について (p(q)=p) なら、

$$
1\le k(q)\le n.\mathrm{factorization}(p)
$$

となる。さらに同じ (p) 上で (k(q)=k(r)) なら、

$$
q=p^{k(q)}=p^{k(r)}=r
$$

なので、

$$
q\mapsto k(q)
$$

は (I_p) 上で単射になる。

したがって、

$$
I_p
\hookrightarrow
{1,2,\dots,n.\mathrm{factorization}(p)}
$$

であり、

$$
\#I_p\le n.\mathrm{factorization}(p)
$$

が従う。
これがまさに multiplicity budget じゃ。

## 3. `baseExponentOf_injOn_filter_basePrime` の意味

この補題は、同じ base prime fiber 上の injectivity を示している。

Lean の証明も数学そのものじゃ。

$$
q=p(q)^{k(q)}
$$

$$
r=p(r)^{k(r)}
$$

同じ fiber 上なので

$$
p(q)=p,\qquad p(r)=p
$$

かつ仮定より

$$
k(q)=k(r)
$$

だから、

$$
q=p^{k(q)}=p^{k(r)}=r
$$

となる。

これはとても綺麗じゃ。
R026 の再構成等式が、ここで本当に効いておる。

## 4. `basePrimeOf_card_filter_le_factorization` の意味

これは今回の山場じゃな。

Lean では

```lean
let S := I.filter fun q => W.basePrimeOf n I hI q = p
```

として、同じ base prime (p) を持つ selected labels を取り出している。

そして

```lean
S.image (W.baseExponentOf n I hI)
```

を考える。injective なので、

$$
\#S = \#k(S)
$$

さらに各 exponent は

$$
1\le k(q)\le n.\mathrm{factorization}(p)
$$

に入るので、

$$
k(S)\subseteq \mathrm{Icc}(1,n.\mathrm{factorization}(p))
$$

となる。

よって、

$$
\#S \le \#{1,\dots,n.\mathrm{factorization}(p)} = n.\mathrm{factorization}(p)
$$

が出る。

Lean の

```lean
Finset.card_image_of_injOn
Finset.card_le_card
Finset.Icc 1 (n.factorization p)
```

の使い方も非常に自然じゃ。
数学の証明がそのまま形式化されておる。

## 5. `basePrimeOf_multiplicityBudgetOn` の意味

これは、R025 まで外部仮定だった budget を自動生成する補題じゃ。

$$
\forall p,\quad
\#{q\in I\mid p(q)=p}
\le
n.\mathrm{factorization}(p)
$$

を示すので、

```lean
NatBaseMultiplicityBudgetOn I (W.basePrimeOf n I hI) n
```

が得られる。

面白いのは、実装上は

```lean
intro p _hp
```

となっていて、 (p) が prime である仮定を実際には使っていない点じゃ。

これは強い。
`basePrimeOf_card_filter_le_factorization` が任意の (p) で成り立つ形になっておるからじゃな。
実際、もし (p) が base prime として現れないなら filter は空になる。もし現れるなら、witness 側から自然に prime であることが出る。したがって prime 仮定なしでも card bound が成立する。

## 6. `basePrimeOf_logRatioSubProbability` の意味

これが最終定理じゃ。

R025 の

```lean
basePrimeOf_logRatioSubProbability_of_multiplicityBudget
```

は、multiplicity budget を仮定していた。

今回の

```lean
basePrimeOf_logRatioSubProbability
```

は、その budget を内部で

```lean
basePrimeOf_multiplicityBudgetOn
```

から作る。

したがって外部に残る仮定は、

```lean
hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n
hn : 1 < n
```

だけになる。

数学的には、

$$
I\subseteq {q\mid q\mid n,\ q\text{ is represented as a prime power witness}}
$$

であれば、

$$
\sum_{q\in I}
\frac{\log p(q)}{\log n}
\le 1
$$

が自動的に成立する。

これは非常に強い theorem-facing API じゃ。

## 7. R021-R027 全体で何が完成したか

全体の鎖はこうじゃ。

まず witness label は

$$
q=p(q)^{k(q)}
$$

と読める。

次に、同じ base prime (p) を持つ labels は、それぞれ異なる exponent slot

$$
1,2,\dots,v_p(n)
$$

へ入る。

したがって、

$$
\#{q\in I\mid p(q)=p}\le v_p(n)
$$

が出る。

これにより、

$$
\prod_{q\in I}p(q)\mid n
$$

が出る。

ゆえに、

$$
\prod_{q\in I}p(q)\le n
$$

そして log を取って、

$$
\sum_{q\in I}\log p(q)
\le
\log n
$$

最後に (1<n) なので (\log n>0) として割り、

$$
\sum_{q\in I}\frac{\log p(q)}{\log n}\le 1
$$

となる。

この流れが no-sorry で閉じた。
これはもう、単なる補助補題ではなく、DkMath の #1196 R/log route の中核定理じゃ。

## 8. 数学的な見方

今回の証明は、かなり美しい「指数スロット数え上げ」になっておる。

素数 (p) について、 (n) の中には

$$
p^1,p^2,\dots,p^{v_p(n)}
$$

までの prime-power labels が入れる。
同じ (p) に属する selected labels は、これらのスロットに高々 1 個ずつしか入らない。
だから個数は (v_p(n)) を超えない。

この「同じ base prime の labels は exponent slot に並ぶ」という絵は、valuation-budget route の直観として非常に良い。

重複を「衝突」として扱うのではなく、

$$
\text{重複} = \text{同一 prime channel 上の異なる exponent slot}
$$

として扱う。
これで重複あり route が自然に整理された。

## 9. 重要な到達点

R027 により、従来の duplicate-free route は完全に一般化されたと言ってよい。

重複なし route は、

$$
p(q)\ \text{が全部異なる}
$$

ので、各 prime channel を 1 回ずつ使う。

valuation-budget route は、

$$
p(q)\ \text{が重複してもよい}
$$

ただし同じ channel 内では指数スロットを消費する。

この方が実際の prime-power divisor transition に合っておる。
なぜなら index の label は prime そのものではなく、prime power (p^k) だからじゃ。

今回の route は、その prime-power 構造を初めて本格的に使い切った。

## 10. 次の課題

次は docs 整理と上位 API 化じゃな。

数学的にはもう、

```lean
W.basePrimeOf_logRatioSubProbability
```

が一番使いやすい公開入口になった。

次にやるなら、

1. duplicate-free route は特殊ケースとして残す
2. valuation-budget route は一般 route として推奨入口にする
3. 上位 finite/log 設計から `basePrimeOf_logRatioSubProbability` を直接使う
4. README / route plan に「R021-R027 で何が閉じたか」を図式化する

このあたりじゃ。

特に推奨入口は、今後はおそらくこちらになる。

```lean
PrimePowerWitnessProvider.basePrimeOf_logRatioSubProbability
```

duplicate-free route は説明用・比較用・軽量 route として残せばよい。

## 11. 総合判定

R027 は **本当に大きい** 。

R025 までは、

$$
\text{multiplicity budget があれば勝てる}
$$

だった。

R026 で、

$$
q=p^k,\quad k\le v_p(n)
$$

を得た。

R027 で、

$$
\text{同じ }p\text{ の labels は異なる }k\text{ に入る}
$$

を示し、

$$
\text{multiplicity budget 自体が自動生成される}
$$

ところまで閉じた。

したがって最終的に、

$$
I\subseteq T.\mathrm{index}(n),\quad 1<n
$$

だけで

$$
\sum_{q\in I}
\frac{\log W.\mathrm{basePrimeOf}(n,I,hI,q)}
{\log n}
\le 1
$$

が成立する。

これは見事じゃ、ぬしよ。
R021-R027 は、単なる refactor ではない。 **重複あり finite log route の数学的本体を Lean で閉じた仕事** じゃ。
