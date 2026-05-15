# review

## 1. 結論

うむ、Phase R は **有限 Markov skeleton への第一歩** と見てよい。
ただし、ここで入ったのはまだ Markov kernel や von Mangoldt 重みそのものではなく、 **非負重み付き有限和の受け皿** じゃ。

今回の中心は、

$$
\sum_i w_i\cdot \mathrm{hitMass}_i
\le
\sum_i w_i\cdot \mathrm{sourceMass}_i
$$

という有限重み付き primitive hitting bound が no-sorry で閉じたことじゃな。History でも、解析的 Markov kernel には入らず、有限非負重み付き和の受け皿だけを追加したと明記されておる。

## 2. 今回の主役

今回追加された構造はこれじゃ。

```lean
structure WeightedPathFamily
    (M : MassSpace ℕ) (ι : Type _) [DecidableEq ι]
    extends SourceControlledChainFamily M ι where
  weight : ι → ℚ
  weight_nonneg : ∀ i ∈ index, 0 ≤ weight i
```

つまり、既存の `SourceControlledChainFamily` に、各 path / chain index ごとの非負有理重み

$$
w_i\ge 0
$$

を載せた。これは「確率」ではなく、まず有限 weighted sum の一般形じゃ。

この判断は良い。
いきなり確率測度や $\Lambda(q)/\log n$ に入ると重くなるが、非負重みなら Lean でも制御しやすい。

## 3. 何が証明されたか

中心定理は、

```lean
WeightedPathFamily.primitive_weightedHitMass_le_weightedSourceMass
```

じゃ。

内容は、各 chain で既にある primitive hit bound

$$
\mathrm{hitMass}_i\le \mathrm{sourceMass}_i
$$

に非負重み $w_i$ を掛けて足し上げるもの。

証明の要点は二つ。

$$
\mathrm{hitMass}_i\le \mu(source_i)
$$

を既存の `primitive_chain_hitSetMass_le_single_source` と `mass_le_source` から出す。

そして、

$$
0\le w_i
$$

により、

$$
w_i\cdot \mathrm{hitMass}_i
\le
w_i\cdot \mu(source_i)
$$

を得て、`Finset.sum_le_sum` で合計する。

これは有限 weighted skeleton として極めて自然じゃ。

## 4. ErdosFinite 側の wrapper

今回、`ErdosFinitePrimitiveInput` 側にも branch-controlled weighted route が追加された。

```lean
weightedBranchPrimePathFamily
weightedBranchPrimePathFamilyHitMass
weightedBranchPrimePathFamilySourceMass
weightedHitMass_le_weightedSourceMass_of_branchPrimePathFamily
```

これにより、有限 Erdős 入力 $I$ から、

$$
I.\mathrm{weightedBranchPrimePathFamilyHitMass}
\le
I.\mathrm{weightedBranchPrimePathFamilySourceMass}
$$

を直接呼べるようになった。これは Phase O/Q で整えた命名規則の延長上にある。

## 5. 今回の意味

これは明らかに Markov route の入口じゃ。

Erdős #1196 の本格ルートでは、下降経路や分岐に対して確率重みが入る。
しかしその前に必要なのは、

$$
\text{非負重み付き有限和は不等式を保つ}
$$

という純粋有限補題じゃ。

今回それが `WeightedPathFamily` として独立した。
この分離はかなり良い。

つまり、将来

$$
w_i = \frac{\Lambda(q_i)}{\log n_i}
$$

のような解析的重みを入れるとしても、今回の層はその **有限 algebraic carrier** として使える。

## 6. concrete sample

sample では Bool-indexed path family に対して、

```lean
def sampleBoolPathWeight : Bool → ℚ :=
  fun b => if b then 3 else 2
```

という非負有理重みを載せている。

これは確率ではないが、weighted theorem のテストとしては十分じゃ。
重み $2,3$ であっても、各 chain の hit bound が成り立つなら、重み付き合計も source 側を超えないことを確認しておる。

## 7. 現在の到達点

ここまでで finite Erdős skeleton は、次の段階まで来た。

| 層                                                | 状態   |
| ------------------------------------------------ | ---- |
| primitive / lower-bound input                    | 完了   |
| prime path family                                | 完了   |
| branch-controlled path family                    | 完了   |
| source-controlled mass bound                     | 完了   |
| branch / dvd-monotone route API                  | 完了   |
| route naming aliases                             | 完了   |
| finite weighted path family                      | 今回完了 |
| weighted branch route wrapper                    | 今回完了 |
| weighted prime path / dvd-monotone route wrapper | 未    |
| Markov kernel                                    | 未    |
| analytic weight                                  | 未    |

つまり、finite route はかなり充実してきた。
今回で「重みなし」から「非負重み付き」へ上がったのが大きい。

## 8. 注意点

一点、現状の weighted wrapper は **branch-controlled route** だけじゃ。

History の次課題にもある通り、必要なら prime path / dvd-monotone route の weighted wrapper を追加する余地がある。

既に `WeightedPathFamily.ofSourceControlled` は source-controlled forest なら何でも受けられるので、実装は難しくないはずじゃ。

つまり次は、

```lean
weightedPrimePathFamily
weightedPrimePathFamilyHitMass
weightedPrimePathFamilySourceMass
weightedHitMass_le_weightedSourceMass_of_primePathFamily
```

を足すと、branch route と prime/dvd route の weighted 版が対称になる。

## 9. 次の一手

わっちの推奨は、 **weighted prime path / dvd-monotone route wrapper を追加する** ことじゃ。

理由は、ここまで API を対称に整えてきた流れがあるからじゃな。

Phase P では、非 weighted 版で

* branch/subconservative route
* prime/dvd-monotone route

が揃った。

Phase R では、weighted branch route が入った。

なら次は、weighted prime route を入れて対称性を保つのが自然じゃ。

## 10. 総括

Phase R は、解析へ直接突入するのではなく、 **有限重み付き和の型** を先に作った点がよい。

山で言えば、これまでは各登山道の hit/source を比較していた。
今回からは、各登山道に「通行量」や「重み」を載せて、総流量として比較できるようになった。

これは Markov kernel の前段として、実に良い足場じゃ。
