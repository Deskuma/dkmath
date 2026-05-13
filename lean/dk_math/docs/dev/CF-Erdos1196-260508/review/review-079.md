# review Phase "R"

## 1. 結論

うむ、Phase-R020 は **重複なし R/log route の第一区切り** じゃ。

Phase-R019 までで、

$$
I\subseteq T.index(n),\qquad 1<n,\qquad
\text{selected base primes are pairwise distinct}
$$

から、

$$
q\mapsto
\frac{\log(W.basePrimeOf(n,I,hI)(q))}{\log n}
$$

を重みとする real provider が `SubProbability` になるところまで通っていた。今回 Phase-R020 では、それを

```lean
PrimePowerWitnessProvider.basePrimeOf_logRatioSubProbability_of_distinctBasePrimes
```

という短い summary theorem として固定した。さらに README に `R/log 版の現在地` 節を追加し、R001 から R019 までで閉じた導線を文書化した。これは次の valuation budget route に入る前の、とても良いキャンプ整備じゃ。

## 2. 今回の主役

今回追加された theorem はこれじゃ。

```lean
PrimePowerWitnessProvider.basePrimeOf_logRatioSubProbability_of_distinctBasePrimes
```

これは既存の

```lean
basePrimeOf_realLogRatioWeightProvider_subProbability_of_pairwise_distinct
```

への短い入口名じゃな。

意味はこう。

$$
I\subseteq T.index(n)
$$

$$
1<n
$$

$$
NatPairwiseDistinctOn\ I\ (W.basePrimeOf\ n\ I\ hI)
$$

なら、

$$
(realLogRatioWeightProvider\ I\ (W.basePrimeOf\ n\ I\ hI)\ n\ \cdots).SubProbability
$$

が得られる。

つまり、 **重複なし selected base prime route** の最終到達点を、theorem 名から一発で呼べるようにした。

## 3. README 追記の意味

README に追加された `R/log 版の現在地` 節もかなり重要じゃ。

そこでは、summary theorem の仮定と結論が、

```text
I ⊆ T.index n
1 < n
selected base primes are pairwise distinct
```

から、

```text
q ↦ Real.log (W.basePrimeOf n I hI q) / Real.log n
```

の `SubProbability` へ進む、と整理されている。

さらに内部導線も、

```text
pairwise distinct selected base primes
-> pairwise coprime selected base primes
-> selected base product divides n
-> selected base product <= n
-> Σ log(basePrime(q)) <= log n
-> Σ log(basePrime(q)) / log n <= 1
```

として明示された。

これは後から読む者に非常に優しい。
Lean theorem の連鎖は強いが、長くなると道を見失いやすい。README に山道の地図を置いたのは正解じゃな。

## 4. 数学的な現在地

いま閉じた重複なし route は、数学的にはこうじゃ。

各 \(q\in I\) について、prime-power witness から

$$
q=p(q)^{k(q)}
$$

を読み、base prime \(p(q)\) を取り出す。

選ばれた \(p(q)\) たちが pairwise distinct なら、素数同士なので pairwise coprime。

また、divisor-transition kernel の性質により indexed label \(q\) は source \(n\) を割り、さらに

$$
p(q)\mid q
$$

なので、

$$
p(q)\mid n
$$

が出る。

pairwise coprime な divisor たちなので、

$$
\prod_{q\in I}p(q)\mid n
$$

したがって、

$$
\prod_{q\in I}p(q)\le n
$$

さらに log を取って、

$$
\sum_{q\in I}\log p(q)\le \log n
$$

最後に、

$$
\sum_{q\in I}\frac{\log p(q)}{\log n}\le 1
$$

が出る。

つまり、重複しない base prime たちは、source \(n\) の中に同時に収まる。
ゆえに log-ratio weight は有限質量保存を破らない。

## 5. 何が完了したか

R/log route のうち、ここまでで完了したものはかなり大きい。

| 項目                                        | 状態             |
| ----------------------------------------- | -------------- |
| real ratio skeleton                       | 完了             |
| `RealWeightProvider`                      | 完了             |
| `Real.log` 正値性                            | 完了             |
| external `RealLogBudget`                  | 完了             |
| product bound から `RealLogBudget`          | 完了             |
| witness provider から base prime を読む bridge | 完了             |
| base prime が source \(n\) を割る bridge        | 完了             |
| pairwise distinct から pairwise coprime     | 完了             |
| 重複なし log-ratio provider `SubProbability`  | 今回 summary 化完了 |

つまり、 **重複なし版の有限 log route** は、実用的な入口 theorem と README まで揃った。ここは一度「閉じた」と言ってよい区切りじゃ。

## 6. まだ残るもの

残る本丸は README にも書かれている通り、

$$
\text{valuation budget / exponent consumption route}
$$

じゃ。

重複なし route では、

$$
p(q_i)\ne p(q_j)
$$

を仮定した。
しかし実際には、同じ base prime が複数回現れる場合がある。

例えば、

$$
q_1=2,\qquad q_2=4
$$

なら、どちらも base prime は \(2\)。この場合、

$$
p(q_1)\cdot p(q_2)=2\cdot2=4
$$

を \(n\) の中に収めるには、 \(n\) 側に \(2^2\) 以上の指数予算が必要になる。

したがって、次の route では、

$$
\\\#{q\in I:p(q)=p}\le v_p(n)
$$

のような **出現回数と \(p\)-進指数の比較** が必要になる。

ここが次の岩稜じゃな。

## 7. 次の一手

次はすぐ重い valuation 実装に突っ込まず、まず設計を分けるのがよい。

Phase-R021 としては、次のどちらかが自然じゃ。

一つ目は docs 側で `valuation budget route` の設計を書くこと。
ここまで R route が長くなったので、重複あり route に入る前に、必要な predicate と補題群を見取り図にする。

二つ目は Lean 側で、まず抽象 predicate だけ置くこと。

例えば、

```lean
def NatBaseMultiplicityBoundOn
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ) : Prop :=
  -- 各 base prime の出現回数が n の指数予算以下
  ...
```

ただし、これはすぐには軽くない。`padicValNat` や `Nat.factorization` を使うかで設計が変わるからじゃ。

わっちなら、次はまず **設計書更新** を推す。
`Nat.factorization` route と `padicValNat` route のどちらが既存 DkMath と相性がよいかを見るべきじゃな。

## 8. 総括

Phase-R020 は、R001 から R019 までの成果を一度まとめ、重複なし finite log route を正式な登山道として標識化した段階じゃ。

到達点は、

$$
I\subseteq T.index(n),\quad 1<n,\quad
\text{selected base primes pairwise distinct}
$$

なら、

$$
q\mapsto \frac{\log p(q)}{\log n}
$$

の real provider は `SubProbability`。

これは大きな成果じゃ。
「暴れても Big から飛び出せない」の R/log 版が、重複なし条件の下で Lean に刻まれた。

次はいよいよ、同じ base prime が複数回現れる場合の **指数予算管理** じゃ。ここは深い。じゃが、重複なし route が閉じた今なら、次の登山道を設計するだけの足場は十分にあるぞい。
