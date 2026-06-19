# review

うむ、DKMK-018E は **かなり大きな区切り** じゃ。
結論から言えば、DKMK-018 の主目的だった **analytic source replacement** は、少なくとも最初の concrete route として閉じた、と見てよい。

## 1. 何が閉じたか

今回追加された theorem は二つ。

```lean id="8euxd1"
PrimePowerWitnessProvider.logCapacityKernelRealWeightProvider_weight_pos
PrimePowerWitnessProvider.logCapacityKernel_truncationEnvelope_positiveRatIncrementBelow
```

前者で、`logCapacityKernelRealWeightProvider` の weight が index `I` 上で strict positive であることを証明した。
理由は単純で美しい。

$$
q\in I
$$

なら `basePrimeOf q` は prime なので、

$$
1 < \mathrm{basePrimeOf}(q)
$$

が出る。よって

$$
0 < \log(\mathrm{basePrimeOf}(q)).
$$

さらに `hn : 1 < n` から

$$
0 < \log n
$$

も出る。したがって weight

$$
\frac{\log(\mathrm{basePrimeOf}(q))}{\log n}
$$

は `div_pos` で正になる。添付 diff でもこの構造そのままに `real_log_nat_pos_of_one_lt` と `div_pos` で閉じておる。

## 2. 018D の残課題が解消された

018D では、

```lean id="ac1c1m"
∀ i ∈ P.index, 0 < P.weight i
```

があれば、正の rational under-approximation を作れる、という一般 API を閉じた。

しかし、その時点では

```lean id="wd6rdc"
logCapacityKernelRealWeightProvider
```

に対して実際に strict positivity を出せるかが残っていた。

018E でそれが閉じた。
つまり、流れは完全にこうなった。

```text id="f4k3jt"
LogCapacityKernel Real provider
  -> strict positive Real weights
  -> positive Rat under-approximation
  -> TruncationEnvelopeEstimate
```

これは添付 roadmap でも、最初の concrete source replacement route が閉じた、と明記されておる。

## 3. positive support restriction が不要だった意味

ここは地味だが重要じゃ。

もし weight positivity が index 全体で出なければ、次は

```text id="9ju97y"
positive-weight support に index を制限する
```

という追加設計が必要だった。

しかし今回は不要だった。
`I` がすでに prime-power witness index の内側にあり、`basePrimeOf` が `I` 上で prime であるため、index 制限なしに positivity が閉じた。

これは API 設計としてかなり健全じゃ。
余計な support filter を増やさず、既存の witness structure だけで行けた。山道が分岐せず一本で済んだわけじゃな。

## 4. 数学的な到達点

ここまでで、DKMK-018 は次を達成した。

$$
\sum_{q\in I}\frac{\log p(q)}{\log n}\le 1
$$

という Real log-capacity source を、ただの Real theorem として置くのではなく、正の rational finite-step source に落として、

```lean id="g4h9qu"
TruncationEnvelopeEstimate I threshold increment error
```

へ接続できるようになった。

つまり、DKMK-017 で検証された

```text id="i3sl2d"
Rat finite-step route
```

に対して、DKMK-018 は

```text id="bhcatg"
toy geometric source ではなく
LogCapacityKernel 由来の analytic source
```

を供給できるところまで来た。

ここが大きい。
DKMK-017 は「道が通る」章。
DKMK-018 は「本命の水を流す」章。
そして 018E で、最初の本命水路が本当に開通した。

## 5. 今すぐ次にやるべきこと

次は二択じゃ。

### 5.1. DKMK-018F として weighted-hit route へ直結

`logCapacityKernel_truncationEnvelope_positiveRatIncrementBelow` で得た envelope を、

```lean id="xjxklw"
finiteStepTail_weightedHitMass_le_one_add_error
```

へ直接流す theorem を作る。

候補名はこうじゃ。

```lean id="240u8g"
PrimePowerWitnessProvider.logCapacityKernel_finiteStepTail_weightedHitMass_le_one_add_error
```

意味は、

```text id="3xngif"
LogCapacityKernel source
  -> positive Rat increment
  -> TruncationEnvelopeEstimate
  -> finite-step weighted-hit bound
```

まで一発で読む theorem。

これは DKMK-018 の到達点を、DKMK-017 route の最終 bound に接続する仕上げになる。

### 5.2. ここで DKMK-018 を milestone として総括

もう一つは、018E をもって

```text id="7i20cg"
Analytic Source Replacement milestone
```

として章を閉じること。

今の段階でも、roadmap 上の主題は十分に達成されておる。
添付 History の次課題にも、「この envelope を DKMK-017 の finite-step weighted-hit route に直接接続するか、DKMK-018 の milestone として整理するか」と書かれている。

## 6. わっちの推奨

わっちは **018F で一手だけ仕上げてから総括** を推す。

理由は、018E だと到達点がまだ

```lean id="4pamfp"
TruncationEnvelopeEstimate
```

で止まっておる。
もちろんこれは入口として十分だが、DKMK-017 の成果と完全に接続したと言うには、

```lean id="1ewf7y"
finiteStepTail_weightedHitMass_le_one_add_error
```

まで流した theorem があると見通しが格段に良くなる。

つまり 018F は新理論ではなく、 **章末の結線** じゃ。

## 7. 総合判断

DKMK-018E は、成功判定でよい。

閉じたもの：

```text id="ylzgg5"
LogCapacityKernel Real provider の positivity
positive Rat increment の自動選択
TruncationEnvelopeEstimate への concrete 接続
positive-support restriction 不要の確認
```

残るもの：

```text id="dd6gim"
weighted-hit bound への最終 wrapper
章全体の総括
```

ここまで来たら、DKMK-018 はかなり美しい章になっておる。
A で候補を探し、B で型の谷に橋を架け、C で本命 provider を通し、D で rationalization を解き、E で positivity を閉じた。

賢狼から見ても、これは良い登山じゃ。
次の 018F は、山頂に旗を立てる一手になるぞい。
