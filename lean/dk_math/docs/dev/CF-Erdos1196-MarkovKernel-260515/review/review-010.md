# review

うむ、作業再開の第一撃としては **かなり大きい** 。
DKMK-006D までで「`FullExponentSlotCoverage` があれば Markov equality へ行ける」だったものが、今回の DKMK-006E で

$$
\text{FullExponentSlotChannelSet}\to\text{FullExponentSlotCoverage}\to\text{FullChannelLogCostComplete}\to\text{MarkovShadow}
$$

まで接続された。報告でも、この流れが no-sorry で通ったと明記されておる。

## 1. 今回の到達点

新規ファイルはこれじゃ。

```lean
DkMath.NumberTheory.PrimitiveSet.FullExponentSlotBridge
```

追加された主 theorem / def は次の 4 つ。

```lean
basePrimeOf_eq_of_prime_pow_mem
fullExponentSlotCoverage_of_fullExponentSlotChannelSet
fullChannelLogCostComplete_of_fullExponentSlotChannelSet
fullGlobalLogCapacityMarkovShadow_of_fullExponentSlotChannelSet
```

これで、前回まで仮定 interface だった `FullExponentSlotCoverage` を、より具体的な `FullExponentSlotChannelSet` から直接供給できるようになった。
つまり、等号ルートの未踏部分が一段縮んだ。

## 2. 数学的に何が閉じたか

前回 DKMK-006D の時点では、こうだった。

```text
FullExponentSlotCoverage があれば:
  Σ log basePrime = log n
  → FullChannelLogCostComplete
  → MarkovShadow
```

今回 DKMK-006E で、そこへさらに前段が付いた。

```text
FullExponentSlotChannelSet
  → FullExponentSlotCoverage
```

したがって、全体としてはこうなった。

```text
FullExponentSlotChannelSet
  → FullExponentSlotCoverage
  → Σ log basePrime = log n
  → FullChannelLogCostComplete
  → MarkovShadow
```

これは **Markov equality route の構造的橋がほぼ完成** した、という意味じゃ。

## 3. 核心補題 `basePrimeOf_eq_of_prime_pow_mem`

今回の数学的な芯はこれじゃ。

```lean
theorem basePrimeOf_eq_of_prime_pow_mem
```

主張は、indexed label \(q\) が外延的に

$$
q=p^k
$$

であり、\(p\) が素数なら、witness provider が読む base prime は \(p\) でなければならない、というもの。

$$
W.basePrimeOf(n,I,hI,q)=p
$$

証明の発想も自然じゃ。
witness provider 内部では別の witness \(L.p^{L.k}\) を選ぶ可能性がある。しかし \(L.p\mid q\) で、かつ \(q=p^k\) だから、素数 \(L.p\) は \(p^k\) を割る。素数の冪を割る素数は base prime と一致するので、

$$
L.p=p
$$

となる。

これは大事じゃ。
なぜなら `FullExponentSlotChannelSet` は外延的に「\(q=p^k\) の slot が入っている」と言うだけで、witness provider が同じ \(p\) を読むとは自動ではない。今回、そのズレを塞いだ。

## 4. `fullExponentSlotCoverage_of_fullExponentSlotChannelSet`

次の山場はこれじゃ。

```lean
theorem fullExponentSlotCoverage_of_fullExponentSlotChannelSet
```

これは、full channel set が exponent slot 集合そのものなら、各 base prime fiber の個数がちょうど factorization exponent に一致することを示す。

数学的には、固定した素数 \(p\) について、

$$
\#{q\in C.channels(n)\mid basePrime(q)=p}=n.factorization(p)
$$

を示す。

証明は上下から挟む形じゃ。

上界は既存の selected-channel valuation budget を使う。

$$
\#fiber(p)\le n.factorization(p)
$$

下界は、各 slot

$$
k\in{1,\dots,n.factorization(p)}
$$

を label

$$
p^k
$$

へ送る。`FullExponentSlotChannelSet` により \(p^k\) は channel に入る。さらに `basePrimeOf_eq_of_prime_pow_mem` により、その label の base prime は \(p\) と読める。よって

$$
{p^1,\dots,p^{v_p(n)}}\subseteq fiber(p)
$$

が出る。

さらに \(k\mapsto p^k\) は \(p\ge 2\) なら injective なので、cardinality は \(v_p(n)\) 。これで下界が出る。

$$
n.factorization(p)\le \#fiber(p)
$$

上下を合わせて等号じゃ。

## 5. これで何が変わったか

前回までは、Markov equality route の残りはこうだった。

```text
FullExponentSlotCoverage をどう供給するか
```

今回で、それが

```text
FullExponentSlotChannelSet をどう供給するか
```

へ置き換わった。

これは大きい。
`FullExponentSlotCoverage` は witness reader と fiber cardinality を含むやや高階な条件だった。
一方 `FullExponentSlotChannelSet` は、より外延的で分かりやすい。

$$
q\in C.channels(n)\leftrightarrow \exists p,k,\ Nat.Prime(p)\land 1\le k\land k\le n.factorization(p)\land q=p^k
$$

つまり、残る課題は「channel set が全 exponent slot を列挙している」ことに絞られた。

## 6. `fullChannelLogCostComplete_of_fullExponentSlotChannelSet`

この theorem により、

```text
FullExponentSlotChannelSet
  → FullChannelLogCostComplete
```

が直接出るようになった。

つまり、

$$
\sum_{q\in C.channels(n)}\mathrm{vonMangoldtShadowCost}(n,q)=\log n
$$

が、slot extensionality から得られる。

内部では今回の coverage theorem と DKMK-006D の log-sum bridge を合成している。
これは、設計がちゃんと階層化されていたから綺麗に閉じた結果じゃな。

## 7. `fullGlobalLogCapacityMarkovShadow_of_fullExponentSlotChannelSet`

最終到達点はこれじゃ。

```lean
noncomputable def fullGlobalLogCapacityMarkovShadow_of_fullExponentSlotChannelSet
```

これは `FullExponentSlotChannelSet C` があれば、full global log-capacity shadow が `MarkovShadow` になる、という公開入口じゃ。

要するに、

$$
\text{channels が全 exponent slot である}
$$

という具体的な条件だけで、

$$
\sum weight=1
$$

の Markov shadow へ到達できる。

これは DkMath Kernel branch の標語、

$$
\text{Capacity first, Markov later.}
$$

がかなりはっきり Lean 上に出た形じゃ。

## 8. DKMK-001 から見た現在地

ここまでの流れは、いまやこうじゃ。

```text
DKMK-001:
  CapacityKernel / Normalize

DKMK-002:
  SubProbability bridge

DKMK-003:
  VonMangoldtShadow

DKMK-004:
  GlobalLogCapacityKernel

DKMK-005:
  SubMarkovShadow

DKMK-006A:
  FullPrimePowerChannelSet

DKMK-006B:
  MarkovShadow / FullChannelLogCostComplete

DKMK-006C:
  FullExponentSlotCoverage

DKMK-006D:
  FullChannelLogSum

DKMK-006E:
  FullExponentSlotChannelSet → MarkovShadow
```

ここまで来ると、DkMath Kernel Project はもう「面白い抽象化」ではなく、かなり実体を持つ別ルートになっておる。

## 9. 残る未踏部分

残る問いはかなり明確じゃ。

```text
canonical / full channel enumeration から
FullExponentSlotChannelSet を供給できるか？
```

つまり、次のどちらか。

第一に、既存の `T.index n` が本当に

$$
{p^k\mid Nat.Prime(p),\ 1\le k,\ k\le n.factorization(p)}
$$

を表していることを証明する。

第二に、`T.index n` に依存せず、explicit な canonical exponent slot enumeration を新しく作る。

以前から見えていた通り、わっちは第二案もかなり有望だと思う。
slot pair \((p,k)\) を先に Finset 化すれば、full equality の証明は構造的に素直じゃ。その後で label \(q=p^k\) への bridge を作ればよい。

## 10. 総合判定

DKMK-006E は **本線接続の大きな前進** じゃ。

前回までの残りは、

$$
FullExponentSlotCoverage
$$

という witness-fiber 等号仮定だった。

今回、それをより根本的な

$$
FullExponentSlotChannelSet
$$

から導けるようにした。
そしてそこから MarkovShadow まで no-sorry で接続された。報告にも、`FullExponentSlotChannelSet → FullExponentSlotCoverage → FullChannelLogCostComplete → MarkovShadow` の流れが通ったとある。

これはかなりよい。
DkMath kernel route は、既存 Markov kernel をコピーするのではなく、

```text
exponent slot extensionality
  → multiplicity completeness
  → log capacity equality
  → Markov shadow
```

という独自の足場で本線へ近づいておる。

次の狙いは明確じゃ。

```text
FullExponentSlotChannelSet を canonical に供給する。
```

ここを取れば、DkMath Kernel branch は「Markov equality の影」ではなく、かなり具体的な **Markov equality 生成装置** になる。
