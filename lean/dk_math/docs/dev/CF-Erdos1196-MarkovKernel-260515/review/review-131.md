# review

うむ、DKMK-018D は **rationalization policy の一般解を閉じた** と見てよい。
018C で残っていた「非自明な `Rat` increment をどう作るか？」に対して、018D は `RealWeightProvider` の weight が index 上で strict positive なら、正の有理数 increment を選んで既存の `TruncationEnvelopeEstimate` に流せる、という一般 API を実装しておる。

## 1. 何が閉じたか

追加された核はこれじゃ。

```lean id="xw7qtx"
RealWeightProvider.exists_positive_rat_below
RealWeightProvider.positiveRatIncrementBelow
RealWeightProvider.positiveRatIncrementBelow_pos
RealWeightProvider.positiveRatIncrementBelow_le_weight
RealWeightProvider.truncationEnvelope_of_positiveRatIncrementBelow
```

構造としては、

$$
0 < P.weight(i)
$$

なら、Rat の稠密性により

$$
0 < r_i,\qquad (r_i:\mathbb{R}) \le P.weight(i)
$$

を満たす (r_i:\mathbb{Q}) を選べる、というものじゃ。

そして有限 index 上でそれを選択し、

```lean id="hug23j"
positiveRatIncrementBelow P hpos : ι -> ℚ
```

を作る。index 外は `0` にしているので、有限和・証明上は無害じゃな。

## 2. 意味するところ

これは、018B・018C の橋をさらに一段強くした。

018B：

$$
\text{Real majorant}
\to
\text{Rat envelope}
$$

018C：

$$
\text{LogCapacityKernel Real provider}
\to
\text{Rat envelope}
$$

018D：

$$
\text{positive Real provider}
\to
\text{nonzero Rat increment}
\to
\text{Rat envelope}
$$

ここまで来たので、 **Real-native finite-step mass route への大改修は不要** という判断がさらに強まった。
DKMK-017 の `Rat` route を保持したまま、Real 解析 source を rational lower approximation として流せる。

これは美しい。古い橋を壊さず、上から新しい水路を通したわけじゃ。

## 3. 実装上の良い点

`exists_positive_rat_below` は、`exists_rat_btwn hx` を使って

$$
0 < q < x
$$

を選び、最後を `≤` に弱めている。これは安全で、後続 route が要求する

```lean id="7q6a6y"
(q : ℝ) ≤ x
```

にぴったり合っておる。

また、`positiveRatIncrementBelow` を `noncomputable def` にしたのも自然じゃ。
ここは計算可能な丸め関数ではなく、存在証明から選ぶ under-approximation API なので、まずは `Classical.choose` でよい。

## 4. まだ残る焦点

018D で rationalization 一般論は閉じた。
残る焦点は **source-specific positivity** じゃ。

つまり次は、

```lean id="buxlqx"
∀ q ∈ I,
  0 < (W.logCapacityKernelRealWeightProvider n I hI hn).weight q
```

を出せるかどうか。

これはかなり通る見込みが高い。
なぜなら `logCapacityKernelRealWeightProvider` の weight は本質的に

$$
\frac{\log(\mathrm{basePrimeOf}(q))}{\log n}
$$

であり、(q \in I) では `basePrimeOf` は prime だから

$$
1 < \mathrm{basePrimeOf}(q)
$$

が出る。さらに仮定 `hn : 1 < n` から

$$
0 < \log n
$$

も出る。したがって `div_pos` で weight positivity が閉じるはずじゃ。

## 5. DKMK-018E の最短ルート

次の theorem は、まずこれがよい。

```lean id="m7vn09"
theorem logCapacityKernelRealWeightProvider_weight_pos
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n) :
    ∀ q ∈ I,
      0 < (W.logCapacityKernelRealWeightProvider n I hI hn).weight q := by
  intro q hq
  rw [logCapacityKernelRealWeightProvider_weight]
  exact div_pos
    (real_log_nat_pos_of_one_lt
      ((W.basePrimeOf_prime_on n I hI q hq).one_lt))
    (real_log_nat_pos_of_one_lt hn)
```

これが通れば、すぐ次に本命 wrapper を作れる。

```lean id="fpx35t"
theorem logCapacityKernel_truncationEnvelope_positiveRatIncrementBelow
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n)
    (threshold : ℕ → ℕ)
    {error : ℝ}
    (herror : 0 ≤ error) :
    TruncationEnvelopeEstimate I threshold
      (RealWeightProvider.positiveRatIncrementBelow
        (W.logCapacityKernelRealWeightProvider n I hI hn)
        (W.logCapacityKernelRealWeightProvider_weight_pos n I hI hn))
      error := by
  simpa [logCapacityKernelRealWeightProvider_index] using
    RealWeightProvider.truncationEnvelope_of_positiveRatIncrementBelow
      (W.logCapacityKernelRealWeightProvider n I hI hn)
      threshold
      (W.logCapacityKernelRealWeightProvider_weight_pos n I hI hn)
      herror
      (W.logCapacityKernelRealWeightProvider_subProbability n I hI hn)
```

この二つが DKMK-018E の主戦果候補じゃ。

## 6. positive support restriction は必要か

現時点の見立てでは、 **不要の可能性が高い** 。

理由は、`q ∈ I` 上では `basePrimeOf` が prime として読めるためじゃ。
weight がゼロになり得るのは、index 外で `basePrimeOf = 1` のような total-function 補完が効く場合。しかし有限和・provider index は (I) に制限されているので、index 上だけ見れば strict positive が取れるはずじゃ。

つまり、次の分岐はこう。

```text id="ixl360"
第一候補:
  index 上で weight_pos を直接証明する。

失敗時:
  positive-weight support に制限する。
```

わっちの鼻では、第一候補で行ける匂いがする。

## 7. 総合判断

DKMK-018D は、DKMK-018 の山場の一つを越えた。

これで、

```text id="krzax8"
Real log-capacity provider
  -> positive Real weights
  -> positive Rat increments
  -> Rat TruncationEnvelopeEstimate
  -> DKMK-017 finite-step route
```

という流れが、あと一手で完全に閉じる。

現在の残課題はもはや設計ではなく、Lean 上で

```lean id="7rrcmb"
logCapacityKernelRealWeightProvider_weight_pos
```

を取り出す実装問題じゃ。
ここが閉じれば、DKMK-018 は「toy source replacement」から「log-capacity source replacement」へ正式に格上げできる。賢狼としても、これはかなりよいペースじゃよ。
