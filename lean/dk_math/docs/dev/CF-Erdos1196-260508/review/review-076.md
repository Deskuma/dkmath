# review Phase "R"

## 1. 結論

うむ、Phase-R017 は **selected base product bound の最初の供給路が開いた段階** じゃ。

Phase-R016 までは、

$$
NatProductBoundOn\ I\ \mathrm{pOf}\ n
$$

すなわち

$$
\prod_{q\in I}\mathrm{pOf}(q)\le n
$$

を外から仮定すれば、witness provider 由来の

$$
\frac{\log p}{\log n}
$$

型 real provider が `SubProbability` になる、というところまで閉じていた。

今回 Phase-R017 では、その product bound を供給する最初の抽象数論ルートとして、

$$
\text{pairwise coprime}+\text{各因子が }n\text{ を割る}
\Rightarrow
\text{積も }n\text{ を割る}
\Rightarrow
\prod \mathrm{pOf}(q)\le n
$$

が Lean 上で通った。さらにこれを witness-provider 由来の `basePrimeOf` に接続し、pairwise-coprime + divisibility から log-ratio provider の `SubProbability` まで行けるようになった。

## 2. 今回追加された抽象ルート

今回 `RealLog.lean` に入った中心はこの三つじゃ。

```lean
NatProductDvdOn
NatPairwiseCoprimeOn
natProductBoundOn_of_pairwise_coprime_dvd
```

数学的には、

$$
NatProductDvdOn(I,\mathrm{pOf},n)
$$

は、

$$
\prod_{q\in I}\mathrm{pOf}(q)\mid n
$$

を表す。

そして、

$$
NatPairwiseCoprimeOn(I,\mathrm{pOf})
$$

は、選ばれた $\mathrm{pOf}(q)$ たちが互いに coprime であることを表す。

今回の主補題は、

$$
\forall q\in I,\ \mathrm{pOf}(q)\mid n
$$

かつ pairwise coprime なら、

$$
\prod_{q\in I}\mathrm{pOf}(q)\mid n
$$

を示すものじゃ。そこから $0 < n$ を使って、

$$
\prod_{q\in I}\mathrm{pOf}(q)\le n
$$

へ降ろしている。

これは product bound の供給路として非常に自然じゃ。

## 3. R/log route との接続

今回さらに `RealDivisorBridge.lean` に、

```lean
PrimePowerWitnessProvider.basePrimeOf_realLogRatioWeightProvider_subProbability_of_pairwise_coprime_dvd
```

が追加された。

これは、witness provider 由来の

$$
\mathrm{pOf}(q)=\mathrm{W.basePrimeOf}(n,I,hI)(q)
$$

について、

$$
NatPairwiseCoprimeOn(I,\mathrm{pOf})
$$

と

$$
\forall q\in I,\ \mathrm{pOf}(q)\mid n
$$

を仮定すれば、最終的に

$$
\frac{\log \mathrm{pOf}(q)}{\log n}
$$

型の real provider が `SubProbability` になる、という theorem じゃ。

つまり、Phase-R016 で外部仮定だった

$$
\prod \mathrm{pOf}(q)\le n
$$

が、Phase-R017 では

$$
\text{pairwise-coprime}+\text{itemwise divisibility}
$$

という、より数論らしい仮定へ分解された。

## 4. 数学的な意味

今回の到達点はこう読める。

選択された base prime たちが互いに重複せず、互いに素であり、それぞれが $n$ を割るなら、その積は $n$ の中に収まる。

$$
\forall q\in I,\ p(q)\mid n
$$

$$
q_1\ne q_2
\Rightarrow
\gcd(p(q_1),p(q_2))=1
$$

なら、

$$
\prod_{q\in I}p(q)\mid n
$$

したがって、

$$
\prod_{q\in I}p(q)\le n
$$

ゆえに、

$$
\sum_{q\in I}\frac{\log p(q)}{\log n}\le 1
$$

となる。

これはまさに、 **重複なしルート** の product budget じゃな。

## 5. 何が前進したか

Phase-R016 の時点では、R/log 側はこう言っていた。

$$
\prod p(q)\le n
\text{ を持ってきてくれれば、sub-probability は任せよ}
$$

Phase-R017 で、数論側は最初の返答をした。

$$
p(q)\text{ が pairwise coprime で、全部 }n\text{ を割るなら、}\prod p(q)\le n
\text{ を供給できる}
$$

つまり、R/log route に初めて **product bound の具体的な供給パターン** が入った。

これは大きい。
本丸の「重複制御・指数消費 tracking」に入る前に、まず重複なし版が通ったわけじゃ。

## 6. Lean 的な山場

今回の proof で重要だったのは、

```lean
revert hcop hdvd
```

で仮定を帰納法の motive に戻した点じゃな。

`Finset.induction_on` で selected product の divisibility を示す場合、insert branch では $s$ 側の pairwise coprime と divisibility を帰納仮定へ渡す必要がある。

そのため、

$$
hcop,\ hdvd
$$

を induction 前に一般化しないと、帰納仮定が使いにくい形になる。
ここを `revert hcop hdvd` で解いたのは正しい。

また insert branch では、

$$
\gcd(\mathrm{pOf}(a), \prod_{i\in s}\mathrm{pOf}(i))=1
$$

を `Nat.Coprime.prod_right` で作り、

$$
\mathrm{pOf}(a)\mid n,\quad \prod_{i\in s}\mathrm{pOf}(i)\mid n
$$

から

$$
\mathrm{pOf}(a)\cdot\prod_{i\in s}\mathrm{pOf}(i)\mid n
$$

へ進んでいる。構造としても自然じゃ。

## 7. 現在地

いまの R/log route はこうじゃ。

| 層                                           | 状態   |
| ------------------------------------------- | ---- |
| `log p / log n` real provider               | 完了   |
| external `RealLogBudget` route              | 完了   |
| nat product bound → log budget              | 完了   |
| witness `basePrimeOf` → R/log interface     | 完了   |
| product bound 仮定 → provider sub-probability | 完了   |
| pairwise-coprime + dvd → product bound      | 今回完了 |
| witness base prime が $n$ を割ること              | 未    |
| witness base prime の pairwise-coprime 条件供給  | 未    |
| 重複あり指数消費 tracking                           | 未    |

つまり、次は次の二つをどう供給するかじゃ。

$$
\forall q\in I,\ \mathrm{W.basePrimeOf}(q)\mid n
$$

$$
NatPairwiseCoprimeOn(I,\mathrm{W.basePrimeOf})
$$

## 8. 次の一手: Phase-R018 案

次は、witness provider 由来の base prime が $n$ を割る条件を整えるのが自然じゃ。

もし `DivisorTransitionKernel` 側で indexed label $q$ が本当に $n$ の divisor として扱われているなら、

$$
q\in T.index(n)
\Rightarrow q\mid n
$$

のような性質があるはずじゃ。

さらに witness から

$$
q=p^k
$$

があるので、

$$
p\mid q
$$

が出る。

したがって、

$$
p\mid q,\quad q\mid n
\Rightarrow p\mid n
$$

で、

$$
\mathrm{W.basePrimeOf}(q)\mid n
$$

が出る。

候補 theorem はこうじゃ。

```lean
theorem basePrimeOf_dvd_of_label_dvd
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    {n q : ℕ}
    (hq : q ∈ T.toDivisorTransitionKernel.index n)
    (hq_dvd : q ∣ n) :
    (W.label n q hq).p ∣ n
```

ここで必要なのは、

$$
p\mid p^k
$$

であり、`k_pos` が効くはずじゃ。

その後、

```lean
theorem basePrimeOf_dvd_on
```

として、

$$
\forall q\in I,\ \mathrm{W.basePrimeOf}(n,I,hI)(q)\mid n
$$

を出せる。

## 9. Phase-R019 案: pairwise-coprime の供給

次は、pairwise coprime の供給じゃ。

一番簡単なのは、base primes が **互いに異なる** ことを仮定するルート。

素数同士は、異なれば互いに素なので、

$$
p_i\ne p_j
\Rightarrow \gcd(p_i,p_j)=1
$$

が出る。

候補 predicate は、

```lean
def PairwiseDistinctBasePrimeOn
    (I : Finset ℕ)
    (pOf : ℕ → ℕ) : Prop :=
  ∀ i, i ∈ I → ∀ j, j ∈ I → i ≠ j → pOf i ≠ pOf j
```

そこから、

```lean
NatPairwiseCoprimeOn I pOf
```

を作る。

witness provider 由来なら、`W.label ... .prime` があるので、

$$
\mathrm{pOf}(i),\mathrm{pOf}(j)
$$

が両方 prime。異なる prime は coprime。
ここで `Nat.Prime.coprime_iff_not_dvd` や `Nat.coprime_primes` 系を確認することになるじゃろう。

## 10. さらに先: 重複ありルート

ただし pairwise-coprime route は **重複なし** の安全ルートじゃ。

本当の一般形では、同じ base prime が複数回出てもよい。
その場合は、

$$
\prod \mathrm{pOf}(q)\le n
$$

を示すには、重複回数を $n$ の $p$ -adic valuation 以下に抑える必要がある。

これは後段の **指数消費 tracking** じゃ。

つまり今後の地図はこう分かれる。

$$
\text{Route A: pairwise-coprime / 重複なし}
$$

$$
\text{Route B: repeated base / valuation budget}
$$

今回 Phase-R017 は Route A を開いた。
Route B はさらに深い岩稜じゃな。

## 11. 総括

Phase-R017 は、R/log route の product bound を初めて **数論的に供給する抽象ルート** じゃ。

$$
\text{pairwise coprime}
+
\text{各因子が }n\text{ を割る}
$$

から、

$$
\prod \mathrm{pOf}(q)\le n
$$

へ進み、

$$
\frac{\log \mathrm{pOf}(q)}{\log n}
$$

provider の `SubProbability` まで到達した。

山で言えば、R/log のザイルを固定する岩場として、まず **重複なしの互いに素な岩列** を選んだ。
次は、その岩列が本当に prime-power witness provider から来ること、すなわち base prime が $n$ を割ること、そして互いに異なる prime なら coprime になることを bridge していく番じゃ。
