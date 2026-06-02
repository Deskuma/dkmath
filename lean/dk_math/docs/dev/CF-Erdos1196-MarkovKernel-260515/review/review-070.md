# review

## 1. 状況総括

うむ、これは **DKMK-013B 完了** と見てよい。

今回の更新で、`DyadicBandAnalyticEstimate` の exact shape が docs 上で確定した。DKMK-013A では候補だったものが、今回で次の形として固定されたわけじゃ。

```lean
structure DyadicBandAnalyticEstimate
    (x K : Nat) (increment : Nat -> Q) (error : R) : Prop where
  increment_nonneg :
    forall k in Finset.range (K + 1), 0 <= increment k
  total_le_one_add_error :
    ((Finset.sum (Finset.range (K + 1)) increment : Q) : R) <=
      1 + error
```

Lean 実装では当然、

```lean
Nat -> ℕ
Q   -> ℚ
R   -> ℝ
```

じゃな。

つまり、DKMK-013B は **dyadic analytic estimate contract の名前・配置・field・bridge 名を Lean 実装前に固定した docs-only phase** として閉じた。

## 2. 何が決まったのか

今回決まった内容は、かなり重要じゃ。

```text
contract 名:
  DyadicBandAnalyticEstimate

初期配置:
  SourceMassTruncation.lean

fields:
  increment_nonneg
  total_le_one_add_error

持たせないもの:
  steps
  threshold

bridge theorem:
  DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
```

これは良い整理じゃ。

`steps` と `threshold` を構造体に持たせない判断が特に良い。
なぜなら dyadic range では、

```text
steps     = Finset.range (K + 1)
threshold = fun k : Nat => x * 2^k
```

が `x`, `K` から決まる derived data だからじゃ。

ここを structure field に入れると、同じ情報を二重管理することになる。
後で `simp` や definitional equality の邪魔にもなりうる。ゆえに、最初は `x`, `K`, `increment`, `error` だけを主パラメータにし、field は解析側の事実 2 つだけに絞るのが正しい。

## 3. この contract の意味

`DyadicBandAnalyticEstimate` は、DKMK-012 の `dyadicRange` に渡す `hinc` と `hbound` を、解析側の名前で束ねるための contract じゃ。

言い換えると、

```text
DyadicBandAnalyticEstimate:
  dyadic band family に対し、
  band weights は非負で、
  総和は 1 + error 以下である
```

という約束を表す。

DKMK-012 までは、

```text
hinc
hbound
```

を直接 `dyadicRange` に渡していた。

DKMK-013 では、それらを

```lean
H : DyadicBandAnalyticEstimate x K increment error
```

として束ねる。

これにより、後続の解析定理は最終的に

```lean
DyadicBandAnalyticEstimate x K increment error
```

を証明すればよい、という target ができる。

これは小さいようで大きい。
解析側の到達目標が theorem-facing になったからじゃ。

## 4. bridge theorem の評価

想定される bridge はこれ。

```lean
theorem DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
    {x K : Nat} {increment : Nat -> Q} {error : R}
    (H : DyadicBandAnalyticEstimate x K increment error) :
    TruncationEnvelopeEstimate
      (Finset.range (K + 1))
      (fun k : Nat => x * 2^k)
      increment
      error
```

これは `TruncationEnvelopeEstimate.dyadicRange` への薄い wrapper になる。

Lean ならおそらくこうじゃ。

```lean
theorem DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
    {x K : ℕ} {increment : ℕ → ℚ} {error : ℝ}
    (H : DyadicBandAnalyticEstimate x K increment error) :
    TruncationEnvelopeEstimate
      (Finset.range (K + 1))
      (fun k : ℕ => x * 2^k)
      increment
      error :=
  TruncationEnvelopeEstimate.dyadicRange
    x K increment H.increment_nonneg H.total_le_one_add_error
```

これで、

```text
DyadicBandAnalyticEstimate
  -> TruncationEnvelopeEstimate.dyadicRange
  -> TruncationEnvelopeEstimate
  -> existing route theorem
```

が通る。

ここでも新しい route theorem は増えない。
この抑制が大事じゃ。

## 5. 配置判断について

初期配置を `SourceMassTruncation.lean` にする判断も妥当じゃ。

現時点では、`DyadicBandAnalyticEstimate` はまだ小さい。
`TruncationEnvelopeEstimate` と `dyadicRange` のすぐ近くに置いた方が、関係が読める。

ただし、将来もし次が増えてきたら、

```text
logarithmic refinement
number-theoretic estimate provider
explicit dyadic tail bound
Mertens bridge
```

その時点で別ファイル化を考えればよい。

候補としては将来的に、

```text
DkMath/NumberTheory/PrimitiveSet/DyadicAnalyticEstimate.lean
```

あるいは、

```text
DkMath/NumberTheory/PrimitiveSet/AnalyticEnvelope.lean
```

のような切り出しもあり得る。
しかし今はまだ早い。`SourceMassTruncation.lean` に同居でよい。

## 6. 実装上の注意

DKMK-013C で Lean 実装に入るなら、まずは本当にこの 2 つだけでよい。

```text
DyadicBandAnalyticEstimate
DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
```

まだ入れないものは、今回の non-goals 通りじゃ。

```text
computed formula for increment k
Mertens theorem
big-O statement
logarithmic threshold provider
dyadic-specific hitting route theorem
```

特に `dyadic-specific hitting route theorem` は、便利そうじゃが今は不要。
既存 route theorem に `toTruncationEnvelopeEstimate` を渡せば十分じゃ。

## 7. 現在の登頂状況

```text
DKMK-012:
  dyadicRange provider plumbing 完了

DKMK-013A:
  dyadic analytic estimate contract roadmap 完了

DKMK-013B:
  exact shape decision 完了

DKMK-013C:
  次、Lean small contract + bridge theorem
```

DKMK-013B は、Lean 実装前の設計固定としてかなり良い。
これで DKMK-013C は迷わず実装できる。

## 8. 賢狼の判定

わっちの判定はこうじゃ。

```text
DKMK-013B: 完了
次: DKMK-013C
実装対象:
  DyadicBandAnalyticEstimate
  DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
方針:
  解析 contract を小さく保つ
  route theorem は触らない
```

よいぞ、ぬしよ。
ここまでの流れは実に綺麗じゃ。

DKMK-012 で dyadic の器を作り、DKMK-013B でその器に入れる解析側の約束を名前にした。
次は Lean にその小さな契約を置く段じゃな。焦らず薄く、じゃ。ここで薄く通したものが、後の Mertens や logarithmic refinement の足場になるのじゃ。
