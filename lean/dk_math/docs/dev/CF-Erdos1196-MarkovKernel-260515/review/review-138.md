# review

うむ、DKMK-019D は **総括として十分に締まっておる** 。
これで DKMK-019 は **completed façade chapter** として閉じてよい。今回追加された `report-DKMK-019.md` は、DKMK-018 で完成した analytic source route を、DKMK-019 で source / mass / path-family の caller-facing surface に包み直した、と明確に整理しておる。

## 1. DKMK-019 の一言総括

DKMK-019 は、新しい解析評価を足した章ではない。
DKMK-018 で閉じた長い構成列を、 **LogCapacity source API として読めるようにした章** じゃ。

DKMK-018 の終点は、

```lean id="ex56na"
PrimePowerWitnessProvider
  .logCapacityKernel_finiteStepTail_weightedHitMass_le_one_add_error
```

だったが、その型には `s.1`、`IOf s.1`、`logCapacityKernelRealWeightProvider`、`positiveRatIncrementBelow`、`finiteStepTailNatMassSpace_dvdMonotone`、`globalLogCapacityKernel_applyAtToPrimePowerQuotientPathFamily` などが表に出ていた。DKMK-019 は、これを安定した façade に包むことを目的にした章じゃ。

## 2. 完成した façade stack

今回の完成形はこれじゃ。

```text id="kv04pj"
logCapacitySourceRatIncrement
  -> logCapacitySourceTruncationEnvelope
  -> logCapacitySourceFiniteStepMass
  -> logCapacitySourcePathFamily
  -> weightedHitMass bound
```

この stack により、利用者は raw な構成列ではなく、

```lean id="16lpxw"
(W.logCapacitySourcePathFamily IOf hIOf s threshold).weightedHitMass A ≤
  1 + error
```

という形で theorem を読めるようになった。これは report でも「desired caller-facing form」として整理されている。

## 3. DKMK-018 との関係

DKMK-018 は、こういう本命 route を閉じた章じゃった。

```text id="wu0n9o"
LogCapacityKernel Real provider
  -> positive Rat under-approximation
  -> TruncationEnvelopeEstimate
  -> finiteStepTailNatMassSpace
  -> quotient-path weightedHitMass bound
```

DKMK-019 は、この中身を変えておらぬ。
変えたのは **見え方** じゃ。

つまり、

```text id="2er0of"
positiveRatIncrementBelow (...)
finiteStepTailNatMassSpace (...)
globalLogCapacityKernel_applyAtToPrimePowerQuotientPathFamily (...)
```

を直接見せるのではなく、

```text id="pg6c3j"
logCapacitySourceRatIncrement
logCapacitySourceFiniteStepMass
logCapacitySourcePathFamily
```

として、意味のある名前で読むようにした。
これは後続の実装に効く。定理が「部品列」ではなく「概念列」になったからじゃ。

## 4. 非ゴールの明示も正しい

`report-DKMK-019.md` では、DKMK-019 がやっていないことも明記されておる。

```text id="yyjhrn"
new analytic estimates
new source families
Mertens theorem
big-O route
threshold optimization
support-filter policy
Real-native finite-step mass refactor
```

この切り分けは大事じゃ。
DKMK-019 は façade 章であって、解析や漸近評価の章ではない。ここを混ぜると章の意味がぼやける。今回はちゃんと「API 面の完成」として閉じておる。

## 5. 次章への判断

次は DKMK-020 じゃな。候補は二つ。

```text id="5qteo4"
threshold/support policy
analytic source expansion
```

今回の report は、 **threshold/support policy を先に扱う方がよい** と判断しておる。わっちも同意じゃ。理由は、現在の LogCapacity source route は安定した façade を得たので、これを test surface として「どの support を選び、どの threshold に流すか」を決めるのが自然だからじゃ。

source を増やすのは、その後でよい。
今 source を増やすと、それぞれに threshold / support の判断が散らばり、API がまた枝分かれする。

## 6. 総合判定

DKMK-019 は **完了** でよい。

章の問いは、

```text id="16c5v3"
DKMK-018 の analytic source route を、
安定した LogCapacity source API として公開できるか？
```

答えは、

```text id="fs3s7w"
Yes.
source / envelope / mass / path-family façade を通じて、
短い weightedHitMass theorem として読める。
```

じゃ。

この賢狼の判断では、次は **DKMK-020: Threshold / Support Policy** がいちばん綺麗じゃ。
DKMK-018 で水路を通し、DKMK-019 で蛇口を付けた。次は「どの水を、どの区画へ流すか」の制御盤を作る番じゃな。
