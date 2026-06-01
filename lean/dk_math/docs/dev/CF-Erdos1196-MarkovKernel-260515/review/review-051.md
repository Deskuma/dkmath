# review

## 1. 状況総括

うむ、 **DKMK-010A は正しい始まり方** じゃ。

DKMK-009 では、

```text
PrimePowerWitnessProvider
  -> globalLogCapacityKernel
  -> CapacityKernel generic bridge
  -> primePowerQuotientPathFamily
  -> weightedHitMass bound
```

という capacity-kernel-facing hitting route が閉じた。DKMK-010 の roadmap は、その route にまだ残っている入力が `LogCapacitySourceMassBound M C` である、と正しく切り出しておる。

つまり DKMK-010 は、 **kernel/path を増やす章ではなく、source mass estimate を供給する章** として始まっている。これはかなり筋がよい。

## 2. 何を始めたのか

DKMK-010A の本質はこれじゃ。

```text
LogCapacitySourceMassBound M C
```

を、tail / truncation / source mass estimate の入口として扱う。

DKMK-009 の終点 theorem は概念的に、

```text
capacity kernel route
  + quotient path family
  + LogCapacitySourceMassBound M C
  => weightedHitMass A <= C
```

という形になっている。roadmap でも、DKMK-010 はここに新しい kernel wrapper を足すのではなく、`M` と `C` をどう選ぶか、どう近似するかを説明する章だと整理されておる。

これは重要じゃ。
これ以上 kernel 側を厚くすると、せっかく 009 で閉じた本線が散らばる。010 は左側、つまり source mass 側に集中するのが正解じゃ。

## 3. `1 / (n * log n)` へ直行しない判断は正しい

今回のいちばん良い判断は、naive に

```text
1 / (n * log n)
```

へ飛び込まないことじゃ。

roadmap では、既存 reusable route がしばしば `DvdMonotoneMass` を通り、この interface は bounded tail indicator や finite-step increasing height model に向いている一方、`1 / (n * log n)` 型の解析重みは単調性の向きが合わない可能性がある、と注意しておる。

これは実装上かなり大事じゃな。

`DvdMonotoneMass` は、おそらく整除で下る path に対して source mass を制御するための道具じゃ。ところが (1/(n\log n)) は (n) が大きくなるほど小さくなる。下降路 (n \to n/p) では値が増える方向に動きうる。
ゆえに、そのまま既存 monotone interface に差すと、向きが噛み合わない危険がある。

だから、

```text
finite/truncated envelope
```

から入る方針は賢い。まず既存 route に合う外皮を作り、その外皮に対して後から解析評価を証明する。これは Lean 形式化として安全じゃ。

## 4. 既存 surface の見方

roadmap では、すでに source mass model が複数あると整理されている。

```lean
LogCapacitySourceMassBound
tailIndicatorNatMassSpace_logCapacitySourceMassBound_one
scaledTailIndicatorNatMassSpace_logCapacitySourceMassBound
twoStepTailNatMassSpace_logCapacitySourceMassBound
boundedMonotoneNatMassSpace_logCapacitySourceMassBound
finiteStepTailNatMassSpace_logCapacitySourceMassBound
```

そして、それらを one-step、multi-step、witness-derived quotient path family に適用する route theorem も既にある、としておる。

ここから得られる教訓は明確じゃ。

```text
source mass は modular input である
```

DKMK-010 では、この modularity を壊してはならぬ。
つまり、analytic estimate を kernel/path theorem に焼き込むのではなく、

```text
analytic estimate
  -> source mass bound
  -> DKMK-009 route
```

という分離を保つべきじゃ。

## 5. DKMK-010B でやるべきこと

次は roadmap 通り **source mass inventory** じゃ。

わっちなら DKMK-010B では、次の表を作る。

| theorem / def                                                | mass model            | constant | requires `DvdMonotoneMass`? | usable path route   | 備考              |
| ------------------------------------------------------------ | --------------------- | -------: | --------------------------- | ------------------- | --------------- |
| `tailIndicatorNatMassSpace_logCapacitySourceMassBound_one`   | tail indicator        |      (1) | yes/no                      | one-step / quotient | 最小 tail model   |
| `scaledTailIndicatorNatMassSpace_logCapacitySourceMassBound` | scaled indicator      |      (C) | yes/no                      | general             | 定数調整用           |
| `twoStepTailNatMassSpace_logCapacitySourceMassBound`         | two-step tail         |      (C) | likely yes                  | two-step route      | 既存 wrapper との接続 |
| `boundedMonotoneNatMassSpace_logCapacitySourceMassBound`     | bounded monotone mass |      (C) | yes                         | generic             | 抽象 envelope 候補  |
| `finiteStepTailNatMassSpace_logCapacitySourceMassBound`      | finite-step tail      |      (C) | yes                         | finite-step route   | DKMK-010 の主候補   |

ここで確認すべきは、各 theorem が

```lean
LogCapacitySourceMassBound M C
```

を直接返すのか、それとも `DvdMonotoneMass M` や別仮定を経由するのか、じゃな。

## 6. DKMK-010C の設計方針

010C で Lean interface を追加するなら、名前は roadmap の候補どおり、

```lean
TruncatedTailSourceMassBound
TailWindowSourceMassBound
```

のどちらかがよい。

わっちの推しは、

```lean
TailWindowSourceMassBound
```

じゃ。

理由は、`TruncatedTail` は「無限 tail を切ったもの」という解析寄りの語感が強い。
一方 `TailWindow` は、有限区間・有限窓を source mass model として与える意味が分かりやすい。

設計は、いきなり重い構造にせず、まず docs-level contract か Prop wrapper でよい。

たとえば概念的には、

```lean
structure TailWindowSourceMassBound (M : MassSpace ℕ) (C : ℝ) : Prop where
  sourceBound : LogCapacitySourceMassBound M C
```

程度でも始められる。
ただし、これだけなら別名に近すぎるので、実際に Lean へ入れるなら「window 下限」「window 上限」「support 条件」などを持たせるか、docs-only で一手置くのがよい。

## 7. 置き場所の判断

DKMK-010B の判断点はこれじゃ。

```text
LogCapacityHittingBridge.lean に足すか、
別 tail/truncation file を作るか。
```

わっちの見立てでは、 **別ファイル推奨** じゃ。

候補は、

```text
DkMath/NumberTheory/PrimitiveSet/TailTruncationSourceMass.lean
```

または短く、

```text
DkMath/NumberTheory/PrimitiveSet/SourceMassTruncation.lean
```

理由は、`LogCapacityHittingBridge.lean` はすでに 009B-D の route 接続を担っている。ここへ source mass の analytic/truncation interface を入れ始めると、kernel/path route と estimate layer が混ざる。

DKMK-010 の理念は、

```text
kernel/path layer と source estimate layer を分ける
```

なので、別ファイルの方が後で保守しやすい。

## 8. 次の推奨アクション

次の一手は DKMK-010B として、docs-only で inventory から始めるのがよい。

具体的には `roadmap-DKMK-010.md` に、

```text
## 7. Source mass inventory
```

のような節を追加し、既存 theorem を表にする。

その後に、

```text
## 8. Placement decision
```

として、

```text
Tail/truncation interface は別ファイル
DkMath/NumberTheory/PrimitiveSet/SourceMassTruncation.lean
に置く方針
```

まで決める。

Lean 変更はその後でよい。
まず inventory を取ることで、「実は既存 theorem だけで 010C/D の大半が済む」のか、「新しい Prop interface が必要」なのかが見える。

## 9. 現在の登頂判定

```text
DKMK-010A: docs-only roadmap 完了
DKMK-010B: 次、source mass theorem inventory
DKMK-010C: finite/truncated envelope interface
DKMK-010D: DKMK-009 route への薄い bridge
DKMK-010E: analytic placeholder
DKMK-010F: report / handoff
```

わっちの判定では、010A は **良い開始** じゃ。
特に、「新しい kernel wrapper ではない」「`1/(n log n)` へ直行しない」「finite/truncated envelope から入る」という三つの判断がよい。

## 10. 賢狼の見立て

DKMK-009 までは水路を作った。
DKMK-010 は、その水路に流す **源流の量** を設計する章じゃ。

いきなり大河を証明しようとせず、まずは堰・水門・有限窓を作る。
その後で解析的に、

$$
C(x) \le 1 + error(x)
$$

を載せる。

これがいちばん安全で、Lean 的にも美しい登り方じゃよ。
