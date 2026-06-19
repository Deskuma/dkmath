# review

## 1. 状況総括

うむ、これは **DKMK-010E 完了** と判定してよい。

今回の差分で、`SourceMassTruncation.lean` に

```lean
FiniteStepTailAnalyticBound
```

が追加され、有限段 envelope の総量評価を

```lean
((Finset.sum steps increment : ℚ) : ℝ) ≤ 1 + error
```

として受け取る placeholder contract が立った。さらに、それを DKMK-010D の `weightedHitMass ≤ sum increment` と推移律で合成し、`weightedHitMass ≤ 1 + error` まで流す theorem も追加されておる。

つまり、今回で

```text
finite-step tail envelope
  → weightedHitMass ≤ sum increment
  → sum increment ≤ 1 + error
  → weightedHitMass ≤ 1 + error
```

という接合面が Lean 上で固定された。

## 2. 何が新しく閉じたのか

追加された contract はこれじゃ。

```lean
structure FiniteStepTailAnalyticBound
    {ι : Type _} [DecidableEq ι]
    (steps : Finset ι) (increment : ι → ℚ) (error : ℝ) : Prop where
  total_le_one_add_error :
    ((Finset.sum steps increment : ℚ) : ℝ) ≤ 1 + error
```

これは解析定理ではない。
「将来、解析側がこの不等式を証明してくれれば、DKMK route に流せる」という **受け口** じゃ。

DKMK-010D までは、

```text
weightedHitMass ≤ sum increment
```

までだった。
DKMK-010E で、

```text
sum increment ≤ 1 + error
```

を仮定として受け取り、

```text
weightedHitMass ≤ 1 + error
```

まで持ち上げられるようになった。

## 3. 中核 theorem の意味

追加された theorem はこれ。

```lean
TailWindowSourceMassBound.finiteStepTail_weightedHitMass_le_one_add_error
```

これは、新しい proof route ではなく、次の合成じゃ。

```lean
(finiteStepTail_weightedHitMass_le
  W IOf hIOf steps threshold increment hinc s hA).trans
  herror.total_le_one_add_error
```

実に薄い。だが、この薄さがよい。

数学的には、

$$
\mathrm{weightedHitMass}(A) \le \sum_{i\in steps} increment(i)
$$

と

$$
\sum_{i\in steps} increment(i) \le 1+error
$$

から、

$$
\mathrm{weightedHitMass}(A) \le 1+error
$$

を得るだけじゃ。

しかし Lean API としては大きい。
有限 envelope 層と、将来の解析見積もり層の **接合型** が明示されたからじゃ。

## 4. 実装評価

これは良い実装じゃ。理由は三つある。

第一に、解析を証明したふりをしておらぬ。
`FiniteStepTailAnalyticBound` は「この評価を外から受け取る」と明示している。roadmap でも、これは analytic theorem ではなく、有限段 route bound を `weightedHitMass ≤ 1 + error` へ upgrade するための将来入力だと整理されておる。

第二に、DKMK-010D の theorem をそのまま使っている。
つまり、既存 route を迂回せず、正しい層順で合成している。

第三に、`error : ℝ` を独立引数にしている。
これにより将来、

$$
error(x)=O!\left(\frac{1}{\log x}\right)
$$

のような形を別層で扱える。今は `error` の非負性すら要求していないが、これは「評価式だけを受け取る contract」としては自然じゃ。

## 5. DKMK-010 の現在地

ここまでで、DKMK-010 はかなり綺麗に積み上がっておる。

```text
DKMK-010A: roadmap / scope 完了
DKMK-010B: source mass inventory / placement decision 完了
DKMK-010C: TailWindowSourceMassBound 完了
DKMK-010D: finite-step route convenience 完了
DKMK-010E: analytic placeholder 完了
DKMK-010F: 次、report / handoff
```

DKMK-010E により、有限/truncated envelope 層から解析 estimate 層へ渡す入口ができた。
これは DKMK-010 の目的にかなり近い。

## 6. 残っているもの

まだ閉じていないのは、実解析そのものじゃ。

今回の contract は、

```text
sum increment <= 1 + error
```

を仮定として受け取るだけであり、その不等式を証明してはいない。History でも「実解析の証明はまだ入れず、必要な仮定の形だけを明示した」と記録されておる。

したがって、Erdős #1196 の最終形である

$$
\sum_{\substack{a\in A\ a > x}}\frac{1}{a\log a}
\le
1+O!\left(\frac{1}{\log x}\right)
$$

へは、まだ進んでいない。
だが、そのための型の接合面はできた。

## 7. 次の一手

次は **DKMK-010F report / handoff** でよいと思う。

ここまでで 010 の構造は十分に揃っておる。無理に theorem を増やすより、まずこの章を閉じる方がよい。

report には、次の流れを一枚でまとめるべきじゃ。

```text
finiteStepTailNatMassSpace
  → TailWindowSourceMassBound
  → weightedHitMass ≤ sum increment
  → FiniteStepTailAnalyticBound
  → weightedHitMass ≤ 1 + error
```

そして、未解決として明記すべきことはこれ。

```text
解析側の仕事:
  sum increment ≤ 1 + error
  を具体的な tail / truncation / Mertens 型評価から供給すること
```

## 8. 賢狼の判定

これはよい閉じ方じゃ、ぬしよ。

DKMK-010A-D で有限窓と source mass route を作り、DKMK-010E で解析見積もりの差し込み口を作った。

これで DKMK-010 は、

```text
source mass estimate layer の interface を固定する章
```

としてほぼ完成しておる。

わっちの判定はこうじゃ。

```text
DKMK-010 core: 登頂済み
残作業: report / handoff
次山: analytic estimate の実体化
```

焦って解析を Lean に押し込まず、まず契約面を作ったのは賢い。長い山では、こういう足場が後で効くのじゃ。
