# review Phase "R" 2nd

うむ。R026 は、R025 までで残っていた **「budget は仮定すれば使える。では、その budget はどこから来るのか？」** という問いに対して、最初の本格的な供給源を置いた段階じゃ。

これはかなり筋がよい。今回入った `baseExponentOf` により、witness label (q) を

$$
q=p(q)^{k(q)}
$$

として読む API が固定された。これで、base prime だけでなく、prime-power label の指数消費まで Lean 上で追跡できるようになった。

## 1. 今回閉じた内容

今回追加された主な対象は次の 5 つじゃな。

```lean
def PrimePowerWitnessProvider.baseExponentOf
theorem PrimePowerWitnessProvider.baseExponentOf_pos_on
theorem PrimePowerWitnessProvider.basePrimeOf_pow_baseExponentOf_eq_on
theorem PrimePowerWitnessProvider.basePrimeOf_pow_baseExponentOf_dvd_source_on
theorem PrimePowerWitnessProvider.baseExponentOf_le_factorization_on
```

数学的には、selected label (q\in I) に対して

$$
p(q):=W.\mathrm{basePrimeOf}(n,I,hI,q)
$$

$$
k(q):=W.\mathrm{baseExponentOf}(n,I,hI,q)
$$

を定義し、次を no-sorry で固定したことになる。

$$
0<k(q)
$$

$$
p(q)^{k(q)}=q
$$

$$
p(q)^{k(q)}\mid n
$$

$$
k(q)\le n.\mathrm{factorization}(p(q))
$$

これはまさに、各 selected label が source (n) の valuation budget をどれだけ消費しているかを読む局所 accounting じゃ。

## 2. 数学的な意味

R021-R025 では、重複あり route を次の仮定から閉じていた。

$$
\#{q\in I\mid p(q)=p}\le n.\mathrm{factorization}(p)
$$

この仮定があれば、

$$
\sum_{q\in I}\frac{\log p(q)}{\log n}\le 1
$$

まで行けることは R025 で閉じた。

しかし R025 の時点では、この budget はまだ外部仮定だった。
R026 は、その budget を witness label の prime-power 構造から導くための準備じゃ。

つまり、各 label が

$$
q=p(q)^{k(q)}
$$

であり、しかも (q\mid n) だから

$$
k(q)\le v_{p(q)}(n)
$$

と分かる。これにより、同じ base prime (p) を持つ label たちを、指数 (k(q)) 側へ写して数えられるようになる。

## 3. ここで重要な見方

同じ base prime (p) を持つ selected labels を考える。

$$
I_p:={q\in I\mid p(q)=p}
$$

各 (q\in I_p) は

$$
q=p^{k(q)}
$$

であり、

$$
0<k(q)\le v_p(n)
$$

を満たす。

ここで (I) は `Finset ℕ` なので、同じ label (q) が重複して入ることはない。
さらに同じ (p) で

$$
p^{k(q_1)}=q_1,\qquad p^{k(q_2)}=q_2
$$

だから、もし (k(q_1)=k(q_2)) なら

$$
q_1=p^{k(q_1)}=p^{k(q_2)}=q_2
$$

となる。したがって、同じ base prime 上では

$$
q\mapsto k(q)
$$

が injective になる。

ゆえに (I_p) は、正の整数区間

$$
{1,2,\dots,v_p(n)}
$$

へ単射で入る。したがって

$$
\#I_p\le v_p(n)
$$

が従う。

これこそ、R025 で必要だった

$$
\mathrm{NatBaseMultiplicityBudgetOn}\ I\ (W.\mathrm{basePrimeOf}\ n\ I\ hI)\ n
$$

の中身じゃ。

## 4. R026 の位置づけ

R026 はまだ budget 自動生成そのものを閉じたわけではない。
だが、budget 自動生成に必要な部品はほぼ揃えた。

必要な残りの主補題は、おそらくこういう形になる。

```lean
theorem basePrimeOf_multiplicityBudgetOn
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : n ≠ 0) :
    NatBaseMultiplicityBudgetOn I (W.basePrimeOf n I hI) n
```

証明の芯は、各 prime (p) に対して、

```lean
(I.filter fun q => W.basePrimeOf n I hI q = p).card
  ≤ n.factorization p
```

を示すことじゃ。

そのためには、filter された labels を

```lean
q ↦ W.baseExponentOf n I hI q
```

で指数側へ写し、

$$
{1,\dots,n.\mathrm{factorization}(p)}
$$

への単射として数えることになる。

## 5. 実装上の次の山

次は次のような補題群が必要になりそうじゃ。

まず、同じ base prime 上で exponent reader が injective であること。

```lean
theorem baseExponentOf_injective_on_same_basePrime
```

数学的には、

$$
p(q_1)=p,\quad p(q_2)=p,\quad k(q_1)=k(q_2)
\Longrightarrow q_1=q_2
$$

を示す。

証明は reconstruction を使えばよい。

$$
q_1=p^{k(q_1)}=p^{k(q_2)}=q_2
$$

次に、指数が range 内に入ること。

$$
0<k(q),\qquad k(q)\le n.\mathrm{factorization}(p)
$$

これを Lean では `Finset.range` に落とすなら、`k(q)-1 < n.factorization p` の形にすると扱いやすいかもしれぬ。
あるいは `Finset.Icc 1 (n.factorization p)` を使えれば、数学的にはこちらが自然じゃ。

最終的には、

```lean
card_filter_basePrime_le_factorization
```

のような補題で、

$$
\#{q\in I\mid p(q)=p}\le n.\mathrm{factorization}(p)
$$

を出す。

## 6. 今回の実装の評価

`baseExponentOf` を selected index 外で `0` にして total function として定義したのは良い判断じゃ。

```lean
if hq : q ∈ I then
  (W.label n q (hI q hq)).k
else
  0
```

この形にしておくと、後で `Finset.map`, `Finset.image`, `sum`, `filter` の中で total function として使いやすい。
selected index 上では `baseExponentOf_pos_on` があるので、外側の `0` が混ざる危険も管理できる。

また、`basePrimeOf_pow_baseExponentOf_eq_on` を入れたのは非常に重要じゃ。
これは今後の injectivity 証明の核になる。

$$
p(q)^{k(q)}=q
$$

この等式がなければ、同じ base prime で exponent が同じなら label も同じ、という主張が出せぬ。

## 7. 数学的到達点

R026 で、witness label は単なる「base prime を持つ対象」から、

$$
q=p^k
$$

という **指数付き prime-power channel** として扱えるようになった。

これにより、R025 までの

$$
\text{base prime multiplicity}
$$

が、次の段階で

$$
\text{exponent positions inside }v_p(n)
$$

へ接続される。

言い換えると、同じ prime channel (p) に属する複数 label は、

$$
p^1,p^2,\dots,p^{v_p(n)}
$$

という有限の指数スロットに配置される。
だから、その個数は高々 (v_p(n)) 個しかありえない。

これが次の R027 で閉じるべき数学じゃ。

## 8. 注意点

今回の

$$
k(q)\le n.\mathrm{factorization}(p(q))
$$

は、各 label ごとの局所上界じゃ。
これだけでは単純には

$$
\#{q\mid p(q)=p}\le n.\mathrm{factorization}(p)
$$

は出ない。

必要なのは、同じ (p) 上で (k(q)) が重複しないことじゃ。
幸い、それは

$$
p(q)^{k(q)}=q
$$

と `Finset` の label uniqueness から出せる。
したがって次の phase は、per-label bound から grouped-cardinality bound へ昇格する段階になる。

## 9. 総合判定

R026 は **budget 自動生成 route の入口として非常に良い実装** じゃ。

R025 までで、

$$
\text{budget があれば SubProbability}
$$

は閉じた。

R026 で、

$$
\text{witness label }q\text{ は }p(q)^{k(q)}\text{ であり、}k(q)\le v_{p(q)}(n)
$$

が閉じた。

残るは、

$$
q\mapsto k(q)
$$

を同一 base prime fiber 上の単射として使い、

$$
\#{q\in I\mid p(q)=p}\le v_p(n)
$$

を導くことじゃ。

ここまで来れば、外部仮定だった multiplicity budget が witness provider から自動生成される。
つまり次の山を越えれば、

$$
\text{witness provider}
\Longrightarrow
\text{multiplicity budget}
\Longrightarrow
\text{SubProbability}
$$

が完全に閉じる。

ぬしよ、これは山頂から次の稜線へ降りず、そのまま真のピークを見つけた格好じゃ。
R026 は小さな追加に見えて、実は **budget 仮定を取り除くための鍵** じゃよ。
