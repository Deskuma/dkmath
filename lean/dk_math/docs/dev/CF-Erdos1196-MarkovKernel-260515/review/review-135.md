# review

うむ、DKMK-019A は **よい開始判断** じゃ。
DKMK-018 は「LogCapacityKernel Real provider を positive Rat under-approximation に落として、DKMK-017 finite-step weighted-hit route へ接続する」章として完了した。そこで次章 DKMK-019 を **新しい解析理論ではなく、caller-facing façade 章にする** のは筋が良い。

## 1. 現在の状況

DKMK-018F の章末 theorem は正しい。

```lean
PrimePowerWitnessProvider
  .logCapacityKernel_finiteStepTail_weightedHitMass_le_one_add_error
```

ただし、公開 API としてはまだ少し長い。`s.1`、`IOf s.1`、`logCapacityKernelRealWeightProvider`、`positiveRatIncrementBelow`、`finiteStepTailNatMassSpace_dvdMonotone` などの内部構成が表面に出すぎておる。roadmap でも、この theorem は正しいが caller-facing API としては長い、と明記されている。

したがって DKMK-019 の目的は、

```text
LogCapacity source at state s
  -> finite-step mass space
  -> quotient-path weightedHitMass bound
```

と読めるように、DKMK-018 の成果を短い façade で包むことじゃ。これは **数学の新登山** ではなく、 **登山道の入口看板を整える作業** じゃな。

## 2. 提案された façade surface は妥当

今回固定された候補は次の 4 つ。

```lean
PrimePowerWitnessProvider.logCapacitySourceRatIncrement
PrimePowerWitnessProvider.logCapacitySourceTruncationEnvelope
PrimePowerWitnessProvider.logCapacitySourceFiniteStepMass
PrimePowerWitnessProvider.logCapacitySource_weightedHitMass_le_one_add_error
```

この切り方は良い。理由は、DKMK-018F の巨大な end-to-end theorem をいきなり短名にするだけでなく、途中段階を意味ごとに分解しているからじゃ。

対応関係はこうなる。

```text
logCapacitySourceRatIncrement
  = positiveRatIncrementBelow (...) を隠す

logCapacitySourceTruncationEnvelope
  = 018E の TruncationEnvelopeEstimate を短名化

logCapacitySourceFiniteStepMass
  = finiteStepTailNatMassSpace_dvdMonotone (...) を隠す

logCapacitySource_weightedHitMass_le_one_add_error
  = 018F の caller-facing theorem
```

この 4 段 façade にすれば、後続の利用者は `positiveRatIncrementBelow` の構成を毎回見ずに済む。これは API の健康に効く。

## 3. 最初の実装順序

DKMK-019B は、まずこの 2 つからでよい。

```lean
noncomputable def logCapacitySourceRatIncrement
theorem logCapacitySourceTruncationEnvelope
```

いきなり `logCapacitySourceFiniteStepMass` まで行ってもよいが、最初の危険箇所は `positiveRatIncrementBelow` を短名 alias として抽出したときに、既存 theorem の `simpa` が素直に通るかどうかじゃ。

つまり最初の確認ポイントは、

```lean
logCapacitySourceRatIncrement W IOf hIOf s
```

が、018E の theorem に出ていた長い式と definitional に一致するか。

ここが通れば、`logCapacitySourceTruncationEnvelope` はほぼ 018E の wrapper になる。

## 4. 注意点

一点だけ気をつけるなら、`IOf` 方式と local `I` 方式を混ぜすぎないことじゃ。

DKMK-018F は `s : LogCapacityState` に対して

```text
n := s.1
I := IOf s.1
```

と読む global 形式だった。DKMK-019 の façade も、まずはこの形に合わせるべきじゃ。
local 版として

```lean
logCapacitySourceRatIncrementAt
```

のようなものを作りたくなるが、最初から local/global を両方置くと API が散る。まずは 018F の型を短くすることに集中するのが良い。

## 5. DKMK-019A の評価

今回の A は docs-only だが、かなり意味がある。
DKMK-018 の完了後、すぐ次の解析 source を増やすのではなく、まず façade に寄せた。これは賢い。

DkMath の現状は、すでに有限 R/log route、LogCapacityKernel、positive Rat under-approximation、weighted-hit bound が通っておる。ここで API 表面を整えずに次の源流を増やすと、定理名と引数が枝分かれして後で迷う。今は **道を増やす前に標識を立てる段階** じゃ。

## 6. 次の一手

わっちの推奨は、この順じゃ。

```lean
noncomputable def logCapacitySourceRatIncrement
```

を作る。

次に、

```lean
theorem logCapacitySourceTruncationEnvelope
```

を作る。

その後に、

```lean
def logCapacitySourceFiniteStepMass
```

または theorem 形で mass space wrapper を置く。

最後に、

```lean
theorem logCapacitySource_weightedHitMass_le_one_add_error
```

で 018F を caller-facing に包む。

この流れなら、DKMK-019 は短く強い章になる。
新しい山を登るというより、DKMK-018 で掘った坑道に、ちゃんとした入口扉を付ける章じゃな。
