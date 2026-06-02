# review

## 1. 状況総括

うむ、これは **DKMK-012B 完了** と見てよい。

今回の更新で、`roadmap-DKMK-012.md` に **Dyadic Provider Shape** が追加され、DKMK-012C で実装すべき Lean theorem の形がほぼ確定した。具体的には、

```text
steps     = Finset.range (K + 1)
threshold = fun k => x * 2^k
```

を固定し、`increment` と `error` は外部供給のままにする方針じゃ。さらに theorem 名も旧候補 `dyadic` ではなく、`TruncationEnvelopeEstimate.dyadicRange` に揃えられておる。

つまり DKMK-012B は、 **dyadic band provider の data shape と theorem name を Lean 実装前に固定する docs-only フェーズ** として閉じた。

## 2. 何が決まったのか

決まった data はこれじゃ。

```lean
x         : ℕ
K         : ℕ
increment : ℕ → ℚ
error     : ℝ
```

そこから導出する有限 step と threshold は、

```lean
steps := Finset.range (K + 1)
threshold := fun k : ℕ => x * 2^k
```

必要な仮定は 2 つ。

```lean
hinc :
  ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k

hbound :
  ((Finset.sum (Finset.range (K + 1)) increment : ℚ) : ℝ) ≤
    1 + error
```

これで、

```lean
TruncationEnvelopeEstimate
  (Finset.range (K + 1))
  (fun k : ℕ => x * 2^k)
  increment
  error
```

を作る、という形じゃ。
まさに DKMK-011C で作った `TruncationEnvelopeEstimate` へ、dyadic range data を流し込む入口になる。

## 3. `dyadicRange` という名前は良い

`dyadic` ではなく `dyadicRange` にした判断は良い。

理由は、今回の provider は単に dyadic threshold を使うだけではなく、

```text
Finset.range (K + 1)
```

で有限添字集合を固定するからじゃ。

つまり `dyadicRange` は、

```text
dyadic thresholds
range-indexed finite steps
```

の両方を名前に含めている。これは後で別の dyadic provider、たとえば `Finset.Icc 0 K` や外部 finite index を使う版を追加するときにも衝突しにくい。

## 4. 実装方針の評価

DKMK-012B の方針はかなり安全じゃ。

特に良いのは、次を **入れない** と明記した点じゃ。

```text
dyadic-specific route theorem
logarithmic provider
Mertens / big-O statement
computed increments from log formulas
```

ここは大事じゃ。
DKMK-012C は新しい route theorem を作る章ではない。既存の DKMK-011 route theorem、

```lean
TruncationEnvelopeEstimate
  .finiteStepTail_weightedHitMass_le_one_add_error
```

へ渡す provider を作るだけでよい。

すなわち流れはこう。

```text
dyadicRange
  -> TruncationEnvelopeEstimate
  -> existing DKMK-011 route theorem
  -> weightedHitMass <= 1 + error
```

この層分離が守られておる。

## 5. DKMK-012C の Lean 実装予想

次の Lean 実装はかなり薄く済むはずじゃ。

形はこうでよい。

```lean
theorem TruncationEnvelopeEstimate.dyadicRange
    (x K : ℕ) (increment : ℕ → ℚ)
    (hinc : ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k)
    {error : ℝ}
    (hbound :
      ((Finset.sum (Finset.range (K + 1)) increment : ℚ) : ℝ) ≤
        1 + error) :
    TruncationEnvelopeEstimate
      (Finset.range (K + 1))
      (fun k : ℕ => x * 2^k)
      increment
      error where
  increment_nonneg := hinc
  analytic_bound := by
    constructor
    exact hbound
```

たぶんこの程度で通る。
`simpa` が要るとしても軽いはずじゃ。

ここで重要なのは、`threshold` の式 `fun k => x * 2^k` は `FiniteStepTailAnalyticBound` 側では使われないことじゃ。
`threshold` は source envelope の activation data であり、解析 total estimate は `steps`, `increment`, `error` だけを見る。だから証明が軽い。

## 6. logarithmic provider を待たせる判断

今回も logarithmic provider を後段へ回しているが、これは正しい。

logarithmic band は最終的には魅力的じゃ。

```text
threshold k ≈ x * exp(k * step)
```

のようにすれば、(1/\log x) 型の解析構造に近づく。
しかし Lean では、これを `ℕ` の threshold に落とすために floor / ceil / rounding が必要になり、さらに `Real.exp`, `Real.log`, monotonicity, coercion が絡む。

一方、dyadic は

```lean
x * 2^k
```

なので `ℕ` のまま閉じる。
まずこれで provider pattern を安定させるのは、かなり賢い登り方じゃ。

## 7. 現在の登頂状況

```text
DKMK-009:
  kernel/path/hitting route 完了

DKMK-010:
  source mass estimate interface 完了

DKMK-011:
  externally supplied finite-step estimate provider interface 完了

DKMK-012A:
  provider design roadmap 完了

DKMK-012B:
  dyadic provider shape docs 完了

DKMK-012C:
  次、TruncationEnvelopeEstimate.dyadicRange 実装
```

ここまで、層がよく分かれておる。

## 8. 賢狼の判定

よいぞ、ぬしよ。
DKMK-012B は小さいが、次の実装ミスをかなり減らす良い docs 固定じゃ。

わっちの判定はこうじゃ。

```text
DKMK-012B: 完了
次: DKMK-012C
実装対象: TruncationEnvelopeEstimate.dyadicRange
方針: packaging theorem のみに留める
```

ここで route theorem をいじらず、dyadic provider を `TruncationEnvelopeEstimate` の生産者としてだけ置く。
この方針なら、次の logarithmic provider も同じ型で増やせる。霧が濃くなる前に、よい杭を一本打てたのう。
