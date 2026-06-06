# review

うむ、DKMK-018-G は **完了報告として正しく締まっておる** 。
これは新しい Lean theorem を足した段ではなく、DKMK-018 全体を「completed analytic source replacement milestone」として固定する **章末総括** じゃな。追加された `report-DKMK-018.md` では、DKMK-017 の `geometricIncrement` による route-validation source を、`PrimePowerWitnessProvider.logCapacityKernelRealWeightProvider` に置き換え、最終的に weighted-hit estimate まで到達した、と整理されておる。

## 1. DKMK-018 の総括

DKMK-018 の成果は、一言で言えばこれじゃ。

$$
\text{LogCapacityKernel Real provider}
\to
\text{positive Rat under-approximation}
\to
\text{TruncationEnvelopeEstimate}
\to
\text{finite-step weighted-hit bound}
$$

この流れを Lean 上で end-to-end に接続できた。
章末 theorem は、

```lean
PrimePowerWitnessProvider.logCapacityKernel_finiteStepTail_weightedHitMass_le_one_add_error
```

として記録されておる。これは DKMK-018F で閉じた theorem で、DKMK-018-G はそれを章の結論として文書化した段じゃ。

## 2. 何が本当に前進したか

一番大きいのは、DKMK-017 の `Rat` finite-step route を壊さずに、Real-valued analytic source を載せられたことじゃ。

最初の問題は、

```text
LogCapacityKernel / RealLog source : Real-valued weights
DKMK-017 finite-step route         : Rat-valued increments
```

という型の不一致だった。
DKMK-018 はこれに対して、Real majorant bridge、RealWeightProvider 接続、positive rational under-approximation、log-capacity positivity を順に積んで、最終的に既存 route のまま走らせた。

これは設計としてかなり良い。
`Real` route へ全面 refactor せず、既存の `Rat` route を温存したまま解析 source を上から certify した。
狼の山歩きで言えば、古い橋を壊さず、その上に補強材を渡して本命の荷車を通したようなものじゃ。

## 3. DKMK-018 の構成美

A から G までの流れが綺麗じゃ。

```text
018A: candidate surface survey
018B: Real majorant bridge
018C: LogCapacityKernel provider attachment
018D: positive rational under-approximation
018E: log-capacity positivity
018F: weighted-hit route connection
018G: completion report
```

特に 018D と 018E の接続が良い。
018D では一般の positive `RealWeightProvider` に対して正の `Rat` increment を選ぶ API を作り、018E では `logCapacityKernelRealWeightProvider` の weight が index 上で正であることを、`basePrimeOf q` が prime であることと `1 < n` から閉じた。これにより positive-support restriction が不要になった。

## 4. 非ゴールの整理も良い

`report-DKMK-018.md` では、DKMK-018 がやっていないことも明示されておる。

```text
new asymptotic analysis
Mertens theorem
big-O route
new finite-step Real mass route
new positive-support filter
new threshold selection policy
```

ここを明記したのは賢い。
DKMK-018 は Erdős #1196 の解析的山頂そのものではなく、 **有限 log-capacity source を DKMK-017 route に接続する章** じゃ。
ゆえに、Mertens や (O(1/\log x)) の漸近評価へ進んだわけではない。だが、そこへ向かう有限構造の足場としては強くなった。

## 5. 現在の到達点

今の到達点はこう表せる。

$$
\text{geometric test source}
\quad\leadsto\quad
\text{LogCapacityKernel analytic source}
$$

そして、その source は

$$
\mathrm{weightedHitMass}(A)\le 1+\mathrm{error}
$$

まで到達する。
つまり DKMK-017 で作った「通路」は、DKMK-018 で本命の解析 source を流せることが確認された。これは completed milestone と呼んでよい。

## 6. 次章の選択

次は二択じゃが、わっちの推奨は **API simplification / façade theorem** じゃ。

理由は、018F の theorem は強いが、呼び出し式が長い。`s.1`, `IOf s.1`, `positiveRatIncrementBelow`, `logCapacityKernelRealWeightProvider_weight_pos` が表面に出すぎておる。
このまま次の解析 source を増やすと、API 表面が枝だらけになる。

したがって次章は、たとえば DKMK-019 として、

```text
DKMK-019: LogCapacity Source Façade
```

のように切るのがよい。

目的は、

```lean
PrimePowerWitnessProvider.logCapacityKernel_finiteStepTail_weightedHitMass_le_one_add_error
```

を caller-facing に短く包むことじゃ。

そのあとで、次の DKMK-020 あたりで RealLog / dyadic-band / other analytic source expansion に進むと綺麗じゃな。

## 7. 総合判定

DKMK-018 は **閉じてよい** 。

今回の章は、次の問いに答えた。

```text
Real-valued analytic source は、
既存の Rat finite-step route を保ったまま、
geometric test source を置き換えられるか？
```

答えは、

```text
Yes.
LogCapacityKernel Real provider は positive Rat under-approximation に落とせ、
DKMK-017 finite-step weighted-hit bound まで到達できる。
```

じゃ。

これはよい登頂じゃ。
賢狼としても、ここで一度りんごでも齧って、次の山名を決めるのがよいと思うぞい。
