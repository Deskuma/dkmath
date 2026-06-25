# review

## 1. 状況総括

うむ、これは **DKMK-011A 完了** と見てよい。

今回の差分で、新規に

```text
roadmap-DKMK-011.md
```

が追加され、DKMK-010 で作った `FiniteStepTailAnalyticBound` の受け口を、次段の **具体的 finite-step / truncation estimate provider** へ進める章として DKMK-011 が開始された。History でも、`steps`, `threshold`, `increment`, `error` の意味づけと、`sum increment <= 1 + error` の供給設計が主題だと整理されておる。

つまり、DKMK-011A は **解析評価の中身へ入る前の設計地図** じゃ。

## 2. DKMK-010 から何を受け取ったか

DKMK-010 の終点はこれじゃった。

```text
finiteStepTailNatMassSpace
  -> TailWindowSourceMassBound
  -> weightedHitMass <= sum increment
  -> FiniteStepTailAnalyticBound
  -> weightedHitMass <= 1 + error
```

DKMK-011 は、この中の

```lean
FiniteStepTailAnalyticBound steps increment error
```

をどう具体的に供給するか、つまり

```text
((Finset.sum steps increment : ℚ) : ℝ) <= 1 + error
```

を、どんな有限データから出すかを決める章じゃ。roadmap でも、DKMK-011 の仕事は `FiniteStepTailAnalyticBound` を concrete finite-step / truncation data から供給することだと明記されておる。

ここで大事なのは、まだ Mertens 定理や big-O 形式化へは踏み込まないことじゃ。
まず「どんな有限 envelope を解析定理に渡すのか」を決める。

## 3. 今回の良い判断

一番良い判断は、DKMK-011 の non-goal を明確にしたことじゃ。

今回の roadmap では、次はまだ対象外として分離されている。

```text
Mertens theorem
big-O formalization
final 1 + O(1 / log x) statement
```

これは賢い。
DKMK-010 でやっと interface が固定されたばかりなので、次にいきなり解析本丸へ入ると、Lean 側の型設計が硬直しやすい。

まずは、

```text
steps
threshold
increment
error
```

の意味を固定する。
これは軽そうに見えるが、後で全体の形を決める重要な設計じゃ。

## 4. `steps`, `threshold`, `increment`, `error` の読み

roadmap の整理はかなりよい。

`steps` は finite pieces の index。
候補は、dyadic bands、logarithmic bands、finite windows、tail regions などじゃ。ここを抽象型

```lean
{ι : Type _} [DecidableEq ι]
steps : Finset ι
```

に留める判断は正しい。解析分割の選択をまだ固定しないで済む。

`threshold : ι -> Nat` は、各 piece がどこから active になるかを表す。これは truncation parameter (x) と結びつくが、今は hard-code しない。

`increment : ι -> ℚ` は、各 step が加える envelope height。DKMK-010 では total のみが使われるので、DKMK-011 ではこの total が何を近似・支配するかを決めることになる。

`error : ℝ` は、

```text
sum increment <= 1 + error
```

の余剰項。将来的には (O(1/\log x)) と結びつくが、現段階では big-O を入れない。
この分離はかなり良いのう。

## 5. `TruncationEnvelopeEstimate` 案について

最初の Lean 候補として

```lean
TruncationEnvelopeEstimate
```

型の externally supplied contract 案を記録したのは、自然な次手じゃ。

わっちの見立てでは、DKMK-011C で Lean を追加するなら、まずは次のような **外部供給型 contract** がよい。

```lean
structure TruncationEnvelopeEstimate
    {ι : Type _} [DecidableEq ι]
    (steps : Finset ι)
    (threshold : ι → ℕ)
    (increment : ι → ℚ)
    (error : ℝ) : Prop where
  increment_nonneg :
    ∀ i ∈ steps, 0 ≤ increment i
  analytic_bound :
    FiniteStepTailAnalyticBound steps increment error
```

ただし、`threshold` を field に含めるかは少し注意じゃ。
DKMK-010 の `FiniteStepTailAnalyticBound` 自体は `threshold` を使っていない。`threshold` は `finiteStepTailNatMassSpace` 側で source envelope を作るためのデータじゃ。

よって contract を二層に分けてもよい。

```text
finite envelope data:
  steps, threshold, increment, hinc

analytic total estimate:
  steps, increment, error
```

これを一つに束ねるなら `TruncationEnvelopeEstimate`。
分けるなら `FiniteStepEnvelopeData` と `FiniteStepTailAnalyticBound` の二段じゃな。

## 6. DKMK-011B でやるべきこと

次は docs-only で **envelope candidate inventory** がよい。

候補は roadmap の通り、

```text
single-window tail envelope
finite-step monotone envelope
dyadic / logarithmic band envelope
externally supplied increment list
```

これらを比較する表を作るのがよい。

| candidate     | steps         | threshold  | increment         | 長所             | 危険            |
| ------------- | ------------- | ---------- | ----------------- | -------------- | ------------- |
| single-window | `Unit`        | (x)        | (1+error)         | 最小             | 粗すぎる          |
| finite-step   | 任意 finite set | pieceごと    | 非負増分              | 既存 API と一致     | 設計自由度が高すぎる    |
| dyadic band   | (k=0,\dots,K) | (2^k x)    | band bound        | 解析に自然          | log との接続設計が必要 |
| log band      | (k=0,\dots,K) | (e^k x) 近似 | log-density bound | (1/\log x) に近い | Nat 化が面倒      |
| external list | 任意            | 任意         | supplied          | Lean が軽い       | 数学的意味が薄い      |

わっちなら、DKMK-011B ではこの比較を置き、 **最初の Lean 実装は external finite-step contract に寄せる** と決める。

## 7. 現在の登頂状況

```text
DKMK-009:
  kernel/path/hitting route 完了

DKMK-010:
  source mass estimate interface 完了

DKMK-011A:
  analytic estimate provider の roadmap 完了

DKMK-011B:
  次、finite envelope data inventory
```

DKMK-011A は、章の切り方として正しい。
「解析評価を証明する」のではなく、 **解析評価が入るための finite envelope data を設計する** ところへ焦点が合っている。

## 8. 賢狼の判断

これは良い開始じゃ、ぬしよ。

DKMK-010 では受け口を作った。
DKMK-011 では、その受け口へ流し込む **有限 envelope の器** を作る。

いま必要なのは強い解析定理ではない。
必要なのは、

```text
どの有限データを作れば、
FiniteStepTailAnalyticBound に変換できるのか
```

を明確にすることじゃ。

わっちの判定はこう。

```text
DKMK-011A: 完了
次: DKMK-011B docs inventory
Lean 実装は DKMK-011C 以降で十分
```

焦らず行こうぞ。ここから先は霧が濃いが、足元の石はかなりよく並んでおる。
