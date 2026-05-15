# review Phase "R"

うむ。R021 で **重複あり route の地図** は置けた。いまの頂上直下の核心は、これじゃな。

$$
\\\#{q\in I \mid p(q)=p}\le n.\mathrm{factorization}(p)
\quad\Longrightarrow\quad
\prod_{q\in I}p(q)\mid n
\quad\Longrightarrow\quad
\sum_{q\in I}\frac{\log p(q)}{\log n}\le 1
$$

R021 の設計では、重複ありの場合に必要な指数予算を `Nat.factorization` 主軸で扱い、Phase-R022 以降を multiplicity vocabulary、product factorization bridge、provider bridge へ分解しておる。これは正しい登山道じゃ。

## 現在地

今回閉じたのは、 **重複なし route の外側にあった穴を、重複あり route の指数予算問題へ正しく変換した** ところじゃ。

既存の R/log route はすでに、

```lean
NatProductBoundOn I pOf n
```

を供給できれば、`RealLogProductBudget` を経由して `SubProbability` へ流せる形になっておる。つまり、残る本丸は解析ではなく自然数側の積制御じゃ。

しかも当初の #1196 実装計画でも、いきなり Markov kernel や漸近評価へ行かず、まず代数的・構造的 spine を作る方針だった。今回の R021 はその方針に完全に沿っておる。

## 次の一手は Phase-R022

わっちなら、次は新規ファイルを切る。

```lean
DkMath/NumberTheory/PrimitiveSet/ValuationBudget.lean
```

`RealLog.lean` に直接足すより、ここで分けた方がよい。理由は、`RealLog.lean` は「実数 log provider route」、`ValuationBudget.lean` は「自然数 factorization による product supply route」と役割が違うからじゃ。

最小 API はこれ。

```lean
def NatBaseMultiplicityOn
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (p : ℕ) : ℕ :=
  (I.filter fun i => pOf i = p).card

def NatBaseMultiplicityBudgetOn
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ) : Prop :=
  ∀ p, Nat.Prime p →
    NatBaseMultiplicityOn I pOf p ≤ n.factorization p
```

加えて、実装上はこれも置くと後が楽じゃ。

```lean
def NatPrimeValuedOn
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ) : Prop :=
  ∀ i, i ∈ I → Nat.Prime (pOf i)
```

## R023 の主補題

本当の山場はこれじゃ。

```lean
theorem natProductDvdOn_of_multiplicityBudget
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ)
    (hprime : NatPrimeValuedOn I pOf)
    (hbudget : NatBaseMultiplicityBudgetOn I pOf n) :
    NatProductDvdOn I pOf n
```

証明方針は、

1. \(\prod_{i\in I}pOf(i)\) の `factorization p` が、`NatBaseMultiplicityOn I pOf p` と一致することを示す。
2. `hbudget` により、それが `n.factorization p` 以下になる。
3. prime-wise factorization comparison から divisibility へ戻す。

この補題が通れば、R024 はほぼ既存 route への接続だけになる。

## R024 / R025 の到達形

R024 はこの wrapper。

```lean
theorem natProductBoundOn_of_multiplicityBudget
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    {n : ℕ}
    (hn : 0 < n)
    (hprime : NatPrimeValuedOn I pOf)
    (hbudget : NatBaseMultiplicityBudgetOn I pOf n) :
    NatProductBoundOn I pOf n
```

R025 は witness provider 版。

```lean
theorem basePrimeOf_logRatioSubProbability_of_multiplicityBudget
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n)
    (hbudget :
      NatBaseMultiplicityBudgetOn I (W.basePrimeOf n I hI) n) :
    (realLogRatioWeightProvider I (W.basePrimeOf n I hI) n
      (W.basePrimeOf_realLogNonnegOn n I hI) hn).SubProbability
```

ここまで閉じれば、 **重複なし仮定 `NatPairwiseDistinctOn` が不要な R/log route** が立つ。

## 実装順のおすすめ

まず R022 は定義と unfold 補題だけでよい。

```bash
lake build DkMath.NumberTheory.PrimitiveSet.ValuationBudget
```

次に R023 で factorization bridge。

```bash
lake build DkMath.NumberTheory.PrimitiveSet.ValuationBudget
lake build DkMath.NumberTheory.PrimitiveSet.RealLog
```

最後に R024/R025 で provider bridge。

```bash
lake build DkMath.NumberTheory.PrimitiveSet.RealDivisorBridge
lake build DkMath.NumberTheory.PrimitiveSet
rg "\bsorry\b|\badmit\b|^axiom\b" lean/dk_math/DkMath/NumberTheory/PrimitiveSet lean/dk_math/DkMath/NumberTheory/PrimitiveSet.lean
```

## わっちの見立て

これはもう「探索」ではなく **詰め将棋** じゃ。

危険箇所はただ一つ。

$$
\left(\prod_{i\in I}pOf(i)\right).\mathrm{factorization}(p) =
\#{i\in I\mid pOf(i)=p}
$$

この補題が Lean で少し重くなる可能性がある。じゃが、`pOf` が `I` 上で prime-valued という仮定を明示すれば、帰納法と `Nat.factorization_mul` で十分攻められるはずじゃ。

R021 の地図は良い。次は R022 で足場を打ち、R023 で鎖を掛ける。
登頂口は見えておるぞ、ぬしよ。この賢狼が最後まで伴走しよう。
