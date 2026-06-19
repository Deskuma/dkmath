# review

## 1. 状況総括

うむ、これは **DKMK-013A 完了** と見てよい。

今回の差分で、新規に

```text
roadmap-DKMK-013.md
```

が追加され、DKMK-013 が **dyadic tail upper envelope design** の章として開始された。History でも、DKMK-013 の主題は route theorem の変更ではなく、`increment` と `hbound` を供給する **abstract dyadic analytic estimate contract** の設計だと整理されておる。

DKMK-012 の終点は、

```text
dyadic range data
  -> TruncationEnvelopeEstimate.dyadicRange
  -> TruncationEnvelopeEstimate
  -> existing DKMK-011 route theorem
  -> weightedHitMass <= 1 + error
```

だった。DKMK-013 は、この中でまだ外部入力だった `increment` と `hbound` を、解析入力層として命名・契約化する章じゃ。

## 2. 何を始めたのか

DKMK-013A で立てた問いは明確じゃ。

```text
increment k をどう選ぶか
hbound をどう証明するか
```

ただし、ここでいきなり Mertens theorem や big-O に入るのではない。
まずは、

```text
dyadic analytic estimate contract
  -> increment nonnegativity
  -> total estimate
  -> TruncationEnvelopeEstimate.dyadicRange
```

という theorem-facing interface を作る。roadmap でも、最初の目標は final analytic theorem ではなく theorem-facing interface だと明記されておる。

これは DKMK-012F の引き継ぎにぴたり合っておる。

## 3. 候補 contract の評価

roadmap に置かれた候補はこれじゃ。

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

この形はとても自然じゃ。
なぜなら `TruncationEnvelopeEstimate.dyadicRange` が要求する `hinc` と `hbound` を、そのまま analytic-side contract として束ねているからじゃ。

つまり、

```text
DyadicBandAnalyticEstimate:
  analytic layer 側の約束

TruncationEnvelopeEstimate.dyadicRange:
  provider layer 側の包装

route theorem:
  route layer 側の消費
```

という三層がきれいに分かれる。

## 4. bridge theorem の意味

想定 bridge はこれ。

```lean
theorem DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
    (H : DyadicBandAnalyticEstimate x K increment error) :
    TruncationEnvelopeEstimate
      (Finset.range (K + 1))
      (fun k : Nat => x * 2^k)
      increment
      error
```

これは新しい数学ではなく、既存の

```lean
TruncationEnvelopeEstimate.dyadicRange
```

へ `H.increment_nonneg` と `H.total_le_one_add_error` を渡すだけの薄い wrapper になるはずじゃ。

だが、この wrapper は意味がある。
`dyadicRange` は provider-layer theorem であり、`hinc` / `hbound` をどう得たかを語らない。
`DyadicBandAnalyticEstimate` は、その `hinc` / `hbound` を「この dyadic band family には解析的上界がある」という名前で束ねる。

つまり、後続の解析定理は最終的に

```text
DyadicBandAnalyticEstimate x K increment error
```

を証明すればよい。これが stable target になる。

## 5. 境界線が守られている

今回の roadmap で一番良いのは、boundary がはっきりしていることじゃ。

DKMK-013 では次を変えない。

```text
TruncationEnvelopeEstimate
TruncationEnvelopeEstimate.dyadicRange
TruncationEnvelopeEstimate.finiteStepTail_weightedHitMass_le_one_add_error
DKMK-009/010/011/012 route theorems
```

これは正しい。
route layer はもう完成している。DKMK-013 は analytic-input layer を増やす章じゃ。

わっちの目から見ても、ここで route theorem に手を入れない判断は賢い。酒を飲んでも忘れぬほど大事な境界じゃよ。

## 6. DKMK-013B で決めるべきこと

次の DKMK-013B は、roadmap 通り **exact shape review** がよい。

決めるべき点は 4 つ。

```text
1. contract 名:
   DyadicBandAnalyticEstimate でよいか

2. 配置:
   SourceMassTruncation.lean に置くか、
   新ファイルに分けるか

3. bridge theorem 名:
   DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate でよいか

4. fields:
   hinc / hbound だけを持つか、
   steps / threshold など derived data も持つか
```

わっちの暫定判断はこうじゃ。

`contract 名` は `DyadicBandAnalyticEstimate` でよい。
`AnalyticEstimate` という語で、「route theorem ではなく解析入力側の契約」であることが出ている。

`配置` は、最初は `SourceMassTruncation.lean` でよいと思う。
まだ小さい contract なので、別ファイル化は早い。ただし DKMK-013 以降で logarithmic refinement や number-theoretic estimate が増えるなら、将来 `DyadicAnalyticEstimate.lean` のように分ける余地はある。

`bridge theorem 名` は `toTruncationEnvelopeEstimate` でよい。
読みやすいし、既存の route contract に変換する意味が明確じゃ。

`fields` は最初は `increment_nonneg` と `total_le_one_add_error` だけでよい。
`steps` と `threshold` は `x`, `K` から決まる derived data なので、構造に持たせる必要はない。増やすと依存が太る。

## 7. 次の Lean 実装予想

DKMK-013C で実装するなら、形はこうじゃろう。

```lean
structure DyadicBandAnalyticEstimate
    (x K : ℕ) (increment : ℕ → ℚ) (error : ℝ) : Prop where
  increment_nonneg :
    ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k
  total_le_one_add_error :
    ((Finset.sum (Finset.range (K + 1)) increment : ℚ) : ℝ) ≤
      1 + error

namespace DyadicBandAnalyticEstimate

theorem toTruncationEnvelopeEstimate
    {x K : ℕ} {increment : ℕ → ℚ} {error : ℝ}
    (H : DyadicBandAnalyticEstimate x K increment error) :
    TruncationEnvelopeEstimate
      (Finset.range (K + 1))
      (fun k : ℕ => x * 2^k)
      increment
      error :=
  TruncationEnvelopeEstimate.dyadicRange
    x K increment H.increment_nonneg H.total_le_one_add_error

end DyadicBandAnalyticEstimate
```

かなり薄い。
だが、この薄さがよい。DKMK-013A の目的通りじゃ。

## 8. 登頂状況

```text
DKMK-009:
  kernel/path/hitting route 完了

DKMK-010:
  source mass estimate interface 完了

DKMK-011:
  finite-step / truncation estimate interface 完了

DKMK-012:
  dyadic band provider plumbing 完了

DKMK-013A:
  dyadic analytic estimate contract roadmap 完了

DKMK-013B:
  次、exact shape review
```

ここまできれいに層が積まれておる。
まるで良い麦畑の畝じゃ。曲がっておらぬ。

## 9. 賢狼の判定

わっちの判定はこうじゃ。

```text
DKMK-013A: 完了
次: DKMK-013B exact shape review
方針: DyadicBandAnalyticEstimate を小さく保つ
禁止: Mertens / big-O / logarithmic provider への早すぎる突入
```

DKMK-013 は、ついに `increment` と `hbound` の中身に向かう入口じゃ。
ただし、まだ本丸の解析ではない。まずは解析側の約束を名前にする。ここを丁寧にやれば、後で dyadic tail upper envelope や logarithmic refinement を載せる時、迷わず進めるぞい。
