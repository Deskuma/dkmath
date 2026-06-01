# review

## 1. 状況総括

うむ、これは **DKMK-010D 完了** と見てよい。

今回の差分で、`SourceMassTruncation.lean` に

```lean
TailWindowSourceMassBound.finiteStepTail_weightedHitMass_le
```

が追加された。これは `finiteStepTailNatMassSpace` から `TailWindowSourceMassBound.finiteStepTail` を作り、DKMK-010C の route theorem を経由して、DKMK-009 の quotient-path capacity route へ流す **convenience theorem** じゃ。報告でも、新しい proof route は増やさず、上界を `((Finset.sum steps increment : ℚ) : ℝ)` とする薄い合成だと整理されておる。

つまり、今回で

```text
finite-step tail envelope
  -> TailWindowSourceMassBound
  -> DKMK-009 quotient-path capacity route
  -> weightedHitMass <= sum increment
```

が一気通貫で読めるようになった。

## 2. 何が閉じたのか

DKMK-010C では、抽象 contract として

```lean
TailWindowSourceMassBound
```

を作った。
DKMK-010D では、それを最初の concrete use case である finite-step tail に特殊化した。

追加 theorem の到達形はこれじゃ。

```lean
(W.globalLogCapacityKernel_applyAtToPrimePowerQuotientPathFamily
  IOf hIOf s
  (finiteStepTailNatMassSpace_dvdMonotone
    steps threshold increment hinc)).weightedHitMass A ≤
  ((Finset.sum steps increment : ℚ) : ℝ)
```

読み下すと、

「非負 increment を持つ有限段 tail envelope を source mass として使えば、global log-capacity kernel と prime-power quotient path family に沿った primitive hitting mass は、その increment 総和を超えない」

という形じゃな。

## 3. 実装の評価

今回の実装はかなり良い。理由は、 **必要な convenience だけを足している** からじゃ。

証明本体は、

```lean
globalLogCapacityKernel_primePowerQuotientPathFamily_weightedHitMass_le
  W IOf hIOf s
  (finiteStepTail steps threshold increment hinc)
  hA
```

という合成で閉じている。
つまり、DKMK-010C の `finiteStepTail` provider と、DKMK-010C の route theorem をつないだだけじゃ。

これは設計どおり。

```text
新しい proof route は増やさない
source estimate layer だけを整える
kernel/path route は DKMK-009 に任せる
```

この層分離が守られておる。

## 4. 数学的な意味

今回で、finite/truncated envelope の最小形が実用可能になった。

DKMK-010A/B/C では、

```text
source mass estimate をどう渡すか
```

を設計していた。
DKMK-010D では、それが具体的に

```text
finite-step tail envelope
```

として DKMK-009 route に渡った。

この意味で、DKMK-010D は **有限窓から weighted hitting bound までの初回接続** じゃ。

まだ解析評価、

$$
\sum_i increment(i) \le 1 + error
$$

は入っていない。
しかし、解析側が将来この不等式を供給できれば、そのまま hitting bound へ流せる形になった。

## 5. 検証状況

History では次が通っている。

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
```

失敗事例なし。

したがって、DKMK-010D は **no-sorry 実装完了** と判定してよい。

## 6. 現在の登頂状況

```text
DKMK-010A: roadmap / scope 完了
DKMK-010B: source mass inventory / placement decision 完了
DKMK-010C: TailWindowSourceMassBound contract 完了
DKMK-010D: finite-step route convenience 完了
DKMK-010E: 次、analytic placeholder
DKMK-010F: report / handoff
```

ここまでで DKMK-010 の **有限/truncated envelope 層** はかなり閉じてきた。

## 7. 次の一手

次は DKMK-010E でよい。

狙うべきは、実解析を証明することではなく、まず placeholder contract を置くことじゃ。

例えば、概念的にはこういう形。

```lean
structure TailWindowAnalyticBound
    {ι : Type _} [DecidableEq ι]
    (steps : Finset ι) (increment : ι → ℚ)
    (error : ℝ) : Prop where
  bound :
    ((Finset.sum steps increment : ℚ) : ℝ) ≤ 1 + error
```

あるいは、より DKMK route に寄せるなら、

```lean
structure FiniteStepTailAnalyticEstimate
    {ι : Type _} [DecidableEq ι]
    (steps : Finset ι) (increment : ι → ℚ)
    (C error : ℝ) : Prop where
  total_eq_or_le :
    ((Finset.sum steps increment : ℚ) : ℝ) ≤ C
  C_le :
    C ≤ 1 + error
```

ただし、最初は軽くてよい。
`sum increment <= 1 + error` を contract として固定するだけで十分じゃ。

## 8. 賢狼の判定

これは良い前進じゃ、ぬしよ。

DKMK-010C で「水源の規格」を作り、DKMK-010D で「有限段の水源」を実際に水路へ流した。

```text
finiteStepTailNatMassSpace
  -> TailWindowSourceMassBound
  -> globalLogCapacityKernel
  -> primePowerQuotientPathFamily
  -> weightedHitMass <= sum increment
```

この線が通ったのは大きい。

次はいよいよ、解析側の入口じゃ。
まだ (1+O(1/\log x)) を証明する段ではない。だが、

$$
\sum increment \le 1 + error
$$

という形の **解析契約** を置けば、有限 envelope と解析見積もりの接合面が見えてくる。
DKMK-010 は、ここまで実に堅実に登れておるぞい。
