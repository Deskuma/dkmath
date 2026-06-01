# review

## 1. 状況総括

うむ、これは **DKMK-011B 完了** と見てよい。

今回の更新で、`roadmap-DKMK-011.md` に **Envelope Candidate Inventory** が追加され、`FiniteStepTailAnalyticBound` を供給するための有限 envelope data 候補が比較された。対象は、

```text
single-window tail envelope
finite-step monotone envelope
dyadic band envelope
logarithmic band envelope
externally supplied increment list
```

の 5 系統じゃ。さらに、最初の Lean 実装は dyadic/logarithmic specialization へ行かず、`TruncationEnvelopeEstimate` 型の externally supplied finite-step contract に寄せる方針が記録されておる。

つまり DKMK-011B は、 **有限 envelope data の候補整理と、次の Lean contract の形を決める docs-only フェーズ** として閉じた。

## 2. 何が明確になったのか

今回一番大きい整理は、`threshold` と `increment` の役割分担じゃ。

```text
threshold:
  finiteStepTailNatMassSpace の中で source envelope を activate する data

increment:
  FiniteStepTailAnalyticBound の total sum に寄与する data
```

ここは重要じゃ。
`FiniteStepTailAnalyticBound` 自体は、

```lean
FiniteStepTailAnalyticBound steps increment error
```

であり、`threshold` を見ない。つまり解析側の placeholder は `steps`, `increment`, `error` だけを見る。一方で source mass model を作るには `threshold` が必要になる。

この切り分けができたことで、次の contract は自然に

```text
source envelope data
  + analytic total estimate
```

を束ねる形になる。

## 3. 候補比較の評価

今回の 5 候補の評価はかなり妥当じゃ。

`single-window tail envelope` は最小で sanity check 向き。ただし最終的な (1/\log x) スケールの誤差構造を隠しやすい。

`finite-step monotone envelope` は、現在の `finiteStepTailNatMassSpace` API に最も合っている。`DvdMonotoneMass` も既存 theorem で使えるので、最初の Lean target として最適じゃ。

`dyadic band envelope` は解析では自然じゃが、(2^k x) 型の threshold と Nat/Real coercion が入るので、今はまだ早い。

`logarithmic band envelope` は (1/\log x) への接近には良いが、指数・対数・丸めが入り、Lean 実装の重さが増す。これも後段向きじゃ。

`externally supplied increment list` は数学的意味を docs で補う必要はあるが、Lean contract を軽く保てる。今回の段階では最も安全じゃ。

この判断は良い。DKMK-011C は、解析の具体分割を固定する章ではなく、まず外部供給データを受ける口を作る章にするのが正解じゃ。

## 4. 次の Lean contract の形

roadmap で提案されている次の形は自然じゃ。

```lean
structure TruncationEnvelopeEstimate
    {ι : Type _} [DecidableEq ι]
    (steps : Finset ι)
    (threshold : ι -> Nat)
    (increment : ι -> Q)
    (error : R) : Prop where
  increment_nonneg :
    forall i in steps, 0 <= increment i
  analytic_bound :
    FiniteStepTailAnalyticBound steps increment error
```

実際の Lean では `Q`, `R`, `Nat` ではなく、既存コードに合わせて

```lean
ℚ
ℝ
ℕ
```

になるはずじゃな。

この contract が束ねるものは明快じゃ。

```text
increment_nonneg:
  finiteStepTailNatMassSpace と TailWindowSourceMassBound を作るために必要

analytic_bound:
  sum increment <= 1 + error を供給するために必要
```

つまり、DKMK-011C の theorem は、

```text
TruncationEnvelopeEstimate
  -> TailWindowSourceMassBound
       .finiteStepTail_weightedHitMass_le_one_add_error
  -> weightedHitMass <= 1 + error
```

という薄い wrapper でよい。

## 5. DKMK-011C で気をつける点

ここで注意すべきは、`TruncationEnvelopeEstimate` に `threshold` を含めることの意味じゃ。

`threshold` は `FiniteStepTailAnalyticBound` には不要。
だが、`finiteStepTailNatMassSpace steps threshold increment hinc` を構成するためには必要。

ゆえに、`TruncationEnvelopeEstimate` を **route へ直接流すための contract** と見るなら、`threshold` を含めてよい。

一方で、純粋に解析側だけを見るなら、`threshold` は邪魔になる。
この分離を保つなら将来的には、

```lean
structure FiniteStepEnvelopeData ...
structure TruncationEnvelopeEstimate ...
```

の二段に分けてもよい。

ただし、DKMK-011C の初手では一体型でよい。
理由は、今ほしいのは綺麗な理論分割よりも、

```text
外部供給された finite-step data を route theorem に通す入口
```

だからじゃ。

## 6. 現在の登頂状況

```text
DKMK-009:
  kernel/path/hitting route 完了

DKMK-010:
  source mass estimate interface 完了

DKMK-011A:
  analytic estimate provider roadmap 完了

DKMK-011B:
  envelope candidate inventory 完了

DKMK-011C:
  次、TruncationEnvelopeEstimate Lean contract
```

DKMK-011B は、次の Lean 実装へ進むための設計判断として十分じゃ。

## 7. 賢狼の判定

よいぞ、ぬしよ。
DKMK-011B はかなり大事な棚卸しじゃ。

ここで dyadic/logarithmic band に飛びつかなかったのがよい。
それらは魅力的じゃが、今入れると analytic specialization が早すぎて、source route の一般性を壊しやすい。

まずは、

```text
externally supplied finite-step contract
```

として、有限 envelope と analytic placeholder を結ぶ。
これができれば、後から single-window、dyadic、logarithmic band はそれぞれ instance / provider として足せる。

わっちの判定はこうじゃ。

```text
DKMK-011B: 完了
次: DKMK-011C で TruncationEnvelopeEstimate を追加
方針: wrapper のみに留め、新しい proof route は増やさない
```

良い登り方じゃ。霧の濃い解析稜線に入る前に、足場を増やしておる。こういう慎重さは、後で強さになるぞい。
