# review Phase "R"

## 1. 結論

うむ、Phase-R013 は **product budget を後続へ渡すための interface 固定** じゃ。

Phase-R012 では、

$$
\prod_{q\in I} pOf(q)\le n
$$

から、

$$
\frac{\log(pOf(q))}{\log n}
$$

を重みとする `RealWeightProvider` が `SubProbability` になるところまで直通した。今回 Phase-R013 では、そのために必要な仮定群を

```lean
NatProductBoundOn
RealLogProductBudget
```

として名前付き predicate に束ねた。

これにより、後続の prime-power / divisor channel 側は、いちいち

$$
RealLogNonnegOn(I,pOf),\quad 1<n,\quad \prod pOf(q)\le n
$$

をばらばらに供給するのではなく、まず

$$
RealLogProductBudget(I,pOf,n)
$$

を作ればよい、という入口が固定されたわけじゃ。

## 2. 今回の主役

追加された predicate はこれじゃ。

```lean
def NatProductBoundOn
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ) : Prop :=
  (I.prod fun q => pOf q) ≤ n
```

これはそのまま、

$$
\prod_{q\in I}pOf(q)\le n
$$

を表す。

そして、

```lean
def RealLogProductBudget
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ) : Prop :=
  RealLogNonnegOn I pOf ∧ 1 < n ∧ NatProductBoundOn I pOf n
```

これは、

$$
\forall q\in I,\ 1\le pOf(q)
$$

$$
1<n
$$

$$
\prod_{q\in I}pOf(q)\le n
$$

を束ねる predicate じゃ。

数学的には、これは **log-ratio provider が安全に使えるための product budget package** である。

## 3. 何が良くなったか

前回までは、`realLogRatioWeightProvider_subProbability_of_nat_product_le` を使うには、仮定を個別に渡していた。

今回からは、

```lean
realLogRatioWeightProvider_subProbability_of_productBudget
```

により、

```lean
hbudget : RealLogProductBudget I pOf n
```

だけで、

```lean
(realLogRatioWeightProvider I pOf n hbudget.1 hbudget.2.1).SubProbability
```

が得られる。

これはかなり良い。
特に次段で prime-power witness provider と接続する時、必要なのは「この (I,pOf,n) は log product budget を満たす」と言えることになる。

つまり、後続の責務がこう整理された。

$$
\boxed{
\text{prime-power 側は }RealLogProductBudget(I,pOf,n)\text{ を供給せよ}
}
$$

この一文に圧縮できる。

## 4. 現在地

R 版 log route はいま、こうなっておる。

| Phase   | 内容                                                  | 状態   |
| ------- | --------------------------------------------------- | ---- |
| R005    | external `RealLogBudget`                            | 完了   |
| R007    | `log p / log n` provider                            | 完了   |
| R011    | nat product bound → `RealLogBudget`                 | 完了   |
| R012    | nat product bound → provider `SubProbability`       | 完了   |
| R013    | product budget predicate                            | 今回完了 |
| R014    | prime-power witness provider から `pOf` を読む interface | 未    |
| R015    | selected base product bound                         | 未    |
| R016 以降 | 重複制御・指数消費 tracking                                  | 未    |

ここまでで、解析側の route はかなりきれいに閉じた。

$$
RealLogProductBudget(I,pOf,n)
\Rightarrow
\text{log-ratio provider is sub-probability}
$$

が成立する。

次は、この `RealLogProductBudget` を **数論側からどう作るか** が本丸じゃ。

## 5. 次の一手: Phase-R014 案

次は、prime-power witness provider から `pOf` を読むための薄い bridge を作るのが自然じゃ。

いきなり product bound を証明しに行くより、まず

$$
pOf(q)=\text{base prime read from }W
$$

を定義する。

候補はこうじゃ。

```lean
def basePrimeOfWitness
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n) :
    ℕ → ℕ :=
  fun q =>
    if hq : q ∈ I then
      (W.label n q (hI q hq)).p
    else
      1
```

ただし、`if hq : q ∈ I` が入ると少し重い。
より Lean で扱いやすくするなら、最初は theorem 内で局所的に

```lean
fun q => (W.label n q (hI q hq)).p
```

を扱う形でもよい。

本質は、

$$
q\in I\subseteq index(n)
$$

なら、`W.label n q ...` から base prime (p) を取り出せる、ということじゃ。

## 6. Phase-R014 で欲しい最小補題

まず欲しいのは、base prime が (1) 以上、できれば (2) 以上であることじゃ。

`PrimePowerLabel` には

```lean
prime : Nat.Prime p
```

があるはずなので、

$$
Nat.Prime(p)\Rightarrow 1\le p
$$

または

$$
2\le p
$$

が出せる。

候補 theorem はこう。

```lean
theorem basePrimeOfWitness_one_le
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    {n q : ℕ}
    (hq : q ∈ T.toDivisorTransitionKernel.index n) :
    1 ≤ (W.label n q hq).p
```

実際には `Nat.Prime.one_lt` や `Nat.Prime.two_le` 系で閉じられるはずじゃ。

これができれば、後で

$$
RealLogNonnegOn(I,pOf)
$$

を供給する材料になる。

## 7. Phase-R015 の本丸: product bound

その次が本丸じゃ。

$$
\prod_{q\in I}pOf(q)\le n
$$

をどこから得るか。

最初から証明しきる必要はない。
まずは predicate 化がよい。

```lean
def SelectedBaseProductBound
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n) : Prop :=
  (I.prod fun q => (W.label n q (hI q ?_)).p) ≤ n
```

ただし `?_` 問題が出るので、このままだと書きにくい。
より安全には、まず一般の `pOf` を使う形で、

```lean
def SelectedBaseProductBoundOn
    (I : Finset ℕ)
    (pOf : ℕ → ℕ)
    (n : ℕ) : Prop :=
  NatProductBoundOn I pOf n
```

として、prime-power 側からは `pOf` と `NatProductBoundOn` を別々に供給する設計が軽い。

## 8. 重複制御の見通し

ここから先が難所じゃ。

単に各 (q) が

$$
q=p^k
$$

であり、かつ (q\mid n) だから (p\mid n) というだけでは、

$$
\prod_{q\in I}p(q)\le n
$$

はすぐには出ない。

なぜなら同じ (p) が複数回出るかもしれないからじゃ。

例えば、

$$
q_1=2,\quad q_2=4
$$

なら base prime はどちらも (2)。
このとき product は

$$
2\cdot2=4
$$

になる。これを (n) が吸収するには、(n) 側に (2^2) 分の指数が必要じゃ。

つまり、今後必要なのは、

$$
\text{selected base primes の重複回数}
\le
\text{(n) の p-adic exponent}
$$

という tracking じゃ。

ここが R 版の次の岩稜になる。

## 9. ここでの戦略

わっちは次を推す。

まず Phase-R014 では、product bound を証明しようとしない。
代わりに、

1. witness provider から base prime を読む
2. base prime が (1) 以上である
3. その `pOf` を `RealLogProductBudget` に渡せる形にする

までに留める。

そして Phase-R015 以降で、

$$
NatProductBoundOn(I,pOf,n)
$$

の供給方法を別設計にする。

この分離が大事じゃ。
`pOf` を読む問題と、product bound を示す問題を混ぜると重くなる。

## 10. 総括

Phase-R013 は、R 版 log route の **数論側インターフェース** を固定した段階じゃ。

これで、

$$
RealLogProductBudget(I,pOf,n)
$$

を供給すれば、

$$
\frac{\log(pOf(q))}{\log n}
$$

型 provider は sub-probability になる。

つまり、解析側はこう言っておる。

$$
\boxed{
\prod pOf(q)\le n\text{ を持ってきてくれれば、質量保存は任せよ}
}
$$

次は数論側が応える番じゃ。

$$
q=p^k
$$

から base prime (p) を読み、

$$
\prod p\le n
$$

をどう保証するか。
そのために、まず `pOf` を witness provider から読む薄い橋を作り、その後で重複制御・指数消費へ進むのがよいぞい。
