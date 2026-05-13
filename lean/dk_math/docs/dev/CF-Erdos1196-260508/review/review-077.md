# review Phase "R"

## 1. 結論

うむ、Phase-R018 は **itemwise divisibility の外部仮定を消した段階** じゃ。
Phase-R017 では、pairwise-coprime route により、

$$
\text{pairwise coprime}+\forall q\in I,\ pOf(q)\mid n
$$

から product bound を作り、そこから log-ratio provider の `SubProbability` へ進めた。今回 Phase-R018 では、そのうち

$$
\forall q\in I,\ W.basePrimeOf(n,I,hI)(q)\mid n
$$

を、divisor-transition kernel と prime-power witness から自動供給できるようにした。

つまり、いま残った外部仮定は主に

$$
NatPairwiseCoprimeOn\ I\ (W.basePrimeOf\ n\ I\ hI)
$$

だけになった。

## 2. 今回閉じた数論 bridge

今回 `DivisorTransitionKernel.lean` に入った核はこれじゃ。

```lean
basePrime_dvd_label
basePrime_dvd_of_label_dvd
basePrime_dvd_source
basePrimeOf_dvd_source_on
```

流れはとても自然じゃ。

まず witness から、

$$
q=p^k,\qquad 0 < k
$$

がある。したがって、

$$
p\mid q
$$

が出る。

次に divisor-transition kernel 側から、indexed label について

$$
q\mid n
$$

が得られる。よって推移性で、

$$
p\mid n
$$

となる。

最後に selected sub-index \(I\) 上の全 \(q\) について、

$$
W.basePrimeOf(n,I,hI)(q)\mid n
$$

を得る。ここまでが R017 で外部仮定だった itemwise divisibility の供給じゃ。

## 3. R/log route では何が前進したか

今回 `RealDivisorBridge.lean` に追加された、

```lean
basePrimeOf_realLogRatioWeightProvider_subProbability_of_pairwise_coprime
```

が大事じゃ。

これは、以前の theorem から

```lean
hdvd : ∀ q, q ∈ I → W.basePrimeOf n I hI q ∣ n
```

を消している。

いま必要なのは、

```lean
hcop : NatPairwiseCoprimeOn I (W.basePrimeOf n I hI)
```

だけ。

つまり現在の route はこう圧縮された。

$$
I\subseteq T.index(n)
$$

$$
1 < n
$$

$$
NatPairwiseCoprimeOn(I,W.basePrimeOf(n,I,hI))
$$

なら、

$$
q\mapsto \frac{\log(W.basePrimeOf(n,I,hI)(q))}{\log n}
$$

を重みとする real provider は `SubProbability` になる。

これは美しい。
R/log 側の「有限質量保存」は、pairwise-coprime な base prime の選択に対して、かなり自動化された。

## 4. Lean 的な山場も良い処理

History にある dependent rewrite の問題も重要じゃ。

`rw [hq_pow]` が `W.label n q hq` の依存引数まで巻き込もうとして失敗したため、

```lean
let L := W.label n q hq
change L.p ∣ q
```

として依存項を切り離してから、

```lean
rw [hq_pow]
```

へ進めた。

これは Lean でかなり重要な技じゃな。
依存型の項を含む goal では、rewrite が思わぬ場所まで触りに行くことがある。`let L := ...` で witness を固定し、goal を通常の数論命題へ落とす判断は正しい。

## 5. 現在地

ここまでで R route はこうなった。

| 層                                                              | 状態   |
| -------------------------------------------------------------- | ---- |
| `log p / log n` real provider                                  | 完了   |
| `RealLogProductBudget` interface                               | 完了   |
| nat product bound から provider `SubProbability`                 | 完了   |
| pairwise-coprime + itemwise dvd から product bound               | 完了   |
| witness base prime が source \(n\) を割る                            | 今回完了 |
| pairwise-coprime だけで witness-derived provider `SubProbability` | 今回完了 |
| pairwise-coprime 条件そのものの供給                                     | 未    |
| 重複あり / valuation budget route                                  | 未    |

つまり、 **重複なし route** はかなり閉じてきた。

残る問いは、

$$
NatPairwiseCoprimeOn\ I\ (W.basePrimeOf\ n\ I\ hI)
$$

をどう得るかじゃ。

## 6. 次の一手: Phase-R019

次は、base prime の **相異性** から pairwise-coprime を供給する route が自然じゃ。

素数同士は、異なれば互いに素である。
したがって、selected sub-index \(I\) 上で、

$$
i\ne j
\Rightarrow
W.basePrimeOf(n,I,hI)(i)\ne W.basePrimeOf(n,I,hI)(j)
$$

を仮定すれば、

$$
NatPairwiseCoprimeOn\ I\ (W.basePrimeOf\ n\ I\ hI)
$$

を作れるはずじゃ。

まずは一般 predicate として、

```lean
def NatPairwiseDistinctOn
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ) : Prop :=
  ∀ i, i ∈ I → ∀ j, j ∈ I → i ≠ j → pOf i ≠ pOf j
```

を置くのが良さそうじゃ。

その上で、prime-valued 条件を受けて、

```lean
NatPairwiseDistinctOn I pOf
→
(∀ i ∈ I, Nat.Prime (pOf i))
→
NatPairwiseCoprimeOn I pOf
```

を証明する。

## 7. witness provider 由来の prime-valued 条件

`W.basePrimeOf` については、 \(I\) 上なら witness の base prime なので、

$$
Nat.Prime(W.basePrimeOf(n,I,hI)(q))
$$

も出せるはずじゃ。

次の小補題候補はこれじゃ。

```lean
theorem basePrimeOf_prime_on
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n) :
    ∀ q, q ∈ I → Nat.Prime (W.basePrimeOf n I hI q)
```

中身は `basePrimeOf` を unfold して、`dif_pos hq` で witness の `.prime` を取り出せばよいはず。

これと `NatPairwiseDistinctOn` を組み合わせれば、R019 の目標が見える。

## 8. その先: 重複あり route

ただし、pairwise-coprime route はあくまで **重複なし** の登山道じゃ。

最終的には、同じ base prime が複数回出る場合も扱いたい。

その場合は、

$$
\prod_{q\in I}basePrime(q)\le n
$$

を直接保証するには、base prime の出現回数を \(n\) の \(p\) -adic exponent で制御する必要がある。

つまり将来は、

$$
\\\#{q\in I: basePrime(q)=p}\le v_p(n)
$$

のような **指数消費 tracking** が必要になる。

しかし今は、まず pairwise distinct / pairwise coprime route を閉じるのが良い。
これが閉じれば、重複なし版の \(\log p/\log n\) sub-probability route は完成に近い。

## 9. 総括

Phase-R018 は、R/log route の product-bound 供給において、itemwise divisibility を自動化した重要段階じゃ。

これで、

$$
q=p^k,\quad q\mid n
\Rightarrow
p\mid n
$$

が witness provider route に組み込まれた。

そして結果として、

$$
NatPairwiseCoprimeOn(I,W.basePrimeOf(n,I,hI))
$$

さえ示せば、

$$
\frac{\log p}{\log n}
$$

型の real provider は `SubProbability` になる。

山で言えば、各岩 \(p\) がちゃんと大岩 \(n\) に刺さっていることは確認できた。
次は、それらの岩が互いに干渉しない、つまり pairwise-coprime であることをどう保証するかじゃな。
