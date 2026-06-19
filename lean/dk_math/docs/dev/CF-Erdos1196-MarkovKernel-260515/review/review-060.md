# review

## 1. 状況総括

うむ、これは **DKMK-011D 完了** と見てよい。

今回の更新は docs-only で、`TruncationEnvelopeEstimate` の使い方を `roadmap-DKMK-011.md` に明文化したものじゃ。DKMK-011C で Lean contract は立ったが、その contract を **外部入力としてどう使うか** がやや抽象的だった。今回の DKMK-011D で、その使用手順が読める形になった。

整理された本線はこれじゃな。

```text
steps      : finite index set
threshold  : source envelope activation
increment  : nonnegative envelope increment
error      : analytic residual term
```

そして、

```lean
H : TruncationEnvelopeEstimate steps threshold increment error
```

を渡すと、`H.increment_nonneg` と `H.analytic_bound` がそれぞれ別の層へ流れる。

```text
H.increment_nonneg
  -> finiteStepTailNatMassSpace
  -> TailWindowSourceMassBound
  -> weightedHitMass <= sum increment

H.analytic_bound
  -> sum increment <= 1 + error

therefore:
  weightedHitMass <= 1 + error
```

この説明で、DKMK-011C の contract が単なる wrapper ではなく、 **route plumbing と analytic layer の接合点** であることが明確になった。

## 2. 何が進んだのか

今回の進展は Lean theorem の追加ではなく、 **使い方の固定** じゃ。

DKMK-011C では、

```lean
structure TruncationEnvelopeEstimate ...
```

を追加した。
DKMK-011D では、それを使う caller が何を持てばよいかが明文化された。

必要な入力は、

```lean
W      : PrimePowerWitnessProvider T
IOf    : ℕ -> Finset ℕ
hIOf   : ∀ n q, q ∈ IOf n -> q ∈ T.toDivisorTransitionKernel.index n
s      : LogCapacityState
hA     : PrimitiveOn A
H      : TruncationEnvelopeEstimate steps threshold increment error
```

そして到達するのは、

```text
(W.globalLogCapacityKernel_applyAtToPrimePowerQuotientPathFamily
  IOf hIOf s ...).weightedHitMass A <= 1 + error
```

ここで省略された `...` は、

```lean
finiteStepTailNatMassSpace_dvdMonotone
  steps threshold increment H.increment_nonneg
```

に対応する。つまり、`H.increment_nonneg` が source envelope の **整除下降路に乗せられる性質** を供給するわけじゃ。

## 3. 今回の意味

今回で、DKMK-011 の入口はかなり読みやすくなった。

これまでは、

```text
FiniteStepTailAnalyticBound
TruncationEnvelopeEstimate
TailWindowSourceMassBound
finiteStepTailNatMassSpace
```

がそれぞれ正しく存在していても、外から見ると「どの仮定をどこへ渡すのか」が少し見えにくかった。

今回の usage summary によって、役割がこう分かれた。

| 入力                   | 役割           | 流れる先                         |
| -------------------- | ------------ | ---------------------------- |
| `steps`              | 有限分割の添字集合    | source / analytic 両方         |
| `threshold`          | 各 step の発火位置 | `finiteStepTailNatMassSpace` |
| `increment`          | 各 step の上乗せ量 | source mass と analytic total |
| `error`              | 解析的余剰項       | `1 + error` bound            |
| `H.increment_nonneg` | 非負増分         | finite-step envelope 構成      |
| `H.analytic_bound`   | 総量評価         | `sum increment <= 1 + error` |

この表ができた、というのが DKMK-011D の価値じゃな。

## 4. 設計評価

今回の方針はかなり良い。

第一に、route theorem を変えていない。
docs にも、

```text
Therefore the next Lean or docs step should not change the route theorem.
```

と書かれておる。これは正しい。DKMK-009/010/011C で route plumbing はもう成立している。ここから route theorem をいじると、せっかくの層分離が崩れる。

第二に、analytic layer の責務が明確になった。

```text
Lean route plumbing:
  consumes TruncationEnvelopeEstimate

analytic layer:
  proves TruncationEnvelopeEstimate for a concrete envelope
```

この境界線はとても大事じゃ。
今後の DKMK-011E 以降は、route を触るのではなく、`TruncationEnvelopeEstimate` を作る provider を増やす章になる。

第三に、single-window toy provider と dyadic/logarithmic provider の分岐判断が自然になった。
つまり、次の作業は「route を変える」ではなく、

```text
どんな concrete envelope から H を作るか
```

という問題になった。

## 5. 次の一手の判断

次は二択じゃ。

```text
1. DKMK-011E: single-window toy provider
2. DKMK-011E: report / handoff
```

わっちのおすすめは、 **single-window toy provider を一つだけ追加** じゃ。

理由は、`TruncationEnvelopeEstimate` の usage が docs で明確になったので、次は最小実例を Lean で示すとよいからじゃ。これは数学的な本丸ではなく、API の動作確認になる。

ただし、toy provider は重くしない方がよい。たとえば、

```text
steps = Finset.univ on Unit
threshold = fun _ => x
increment = fun _ => c
error = e
```

のような形で、

```text
c <= 1 + e
```

を外部仮定として受け取り、

```lean
TruncationEnvelopeEstimate steps threshold increment error
```

を作るだけに留める。

ここで (e = c-1) のような計算へ踏み込むと、不要な実数・有理数 coercion が増える可能性がある。最初は

```lean
hc : ((Finset.sum steps increment : ℚ) : ℝ) ≤ 1 + error
```

をそのまま仮定する方が安全じゃ。

## 6. DKMK-011E の候補

もし Lean を追加するなら、名前はこのあたりがよい。

```lean
TruncationEnvelopeEstimate.ofFiniteStep
```

または single-window に寄せて、

```lean
TruncationEnvelopeEstimate.singleWindow
```

ただし `ofFiniteStep` はすでに `TruncationEnvelopeEstimate` 自体が finite-step なので少し曖昧じゃ。
toy provider なら、

```lean
TruncationEnvelopeEstimate.singleWindow
```

が分かりやすい。

docs-only で進めるなら、`roadmap-DKMK-011.md` に、

```text
## 11. Single-window toy provider design
```

を追加してから Lean 実装でもよい。

## 7. 登頂判定

現在地はこうじゃ。

```text
DKMK-011A:
  roadmap 完了

DKMK-011B:
  envelope candidate inventory 完了

DKMK-011C:
  TruncationEnvelopeEstimate Lean contract 完了

DKMK-011D:
  usage summary 完了

DKMK-011E:
  次、single-window toy provider または report / handoff
```

DKMK-011D は、DkMath の研究ライブラリとしてかなり良い「案内板」になっておる。
定理が増えなくても、使い方が固定されるのは大きい。

## 8. 賢狼の見立て

これは良い前進じゃ、ぬしよ。

DKMK-011C で口金を作り、DKMK-011D でその口金に何を差し込むのかを明示した。ここまで来ると、次にやることは迷いにくい。

```text
analytic layer:
  concrete envelope を設計する

Lean route:
  TruncationEnvelopeEstimate を消費するだけ
```

この分離が守れておる限り、DKMK-011 は崩れぬ。

わっちの判定はこうじゃ。

```text
DKMK-011D: 完了
次: single-window toy provider を小さく追加するのが最有力
```

いよいよ、抽象 contract に最初の小さな実例を与える段じゃな。こういう小さい実例は、後の dyadic / logarithmic band へ進むときの良い踏み石になるぞい。
