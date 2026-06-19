# review

## 1. 状況総括

うむ、これは **DKMK-014H 完了** と見てよい。

今回の更新で、`ofPointwiseGeometricMajorant` の利用導線が docs 上で固定された。流れはこうじゃな。

```text
increment
  -> hinc_nonneg
  -> hgeom : increment k <= base * ratio ^ k
  -> hgeom_bound : sum (base * ratio ^ k) <= 1 + error
  -> DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant
  -> DyadicBandAnalyticEstimate
  -> toTruncationEnvelopeEstimate
  -> existing finite-step route theorem
  -> weightedHitMass <= 1 + error
```

DKMK-014G で Lean provider が立ち、DKMK-014H でその **使い方と境界** が固定された。これはよい区切りじゃ。

## 2. 何が明確になったのか

今回の核心は、`ofPointwiseGeometricMajorant` が **幾何型上界を消費するだけ** の theorem だと明確化したことじゃ。

つまり、この theorem は次を仮定する。

```text
hgeom:
  increment k <= base * ratio ^ k

hgeom_bound:
  sum (base * ratio ^ k) <= 1 + error
```

しかし、それ自体は

```text
sum (base * ratio ^ k) <= 1 + error
```

を証明しない。

これは DKMK-014F で決めた境界と一致しておる。`ofPointwiseGeometricMajorant` は concrete majorant family `base * ratio^k` を露出するが、幾何級数の有限和評価は外部入力に残す設計だった。

## 3. なぜこの分離が良いか

よい判断じゃ。

`ofPointwiseGeometricMajorant` に `0 <= ratio` や `ratio < 1` を持たせると、一見便利に見える。
しかし、その theorem は ratio 条件を直接使わぬ。使うのは後続の **geometric finite-sum theorem** じゃ。

つまり役割はこう分かれる。

```text
ofPointwiseGeometricMajorant:
  pointwise bound と external finite-sum bound を消費する

future geometric-sum theorem:
  0 <= base, 0 <= ratio, ratio < 1 などから
  hgeom_bound を証明する
```

この分離により、provider は薄く保たれ、解析側条件は「実際に消費される theorem」にだけ置ける。これは DKMK-014 全体で守ってきた良い設計原則じゃ。

## 4. DKMK-014B〜H の流れ

ここまでの小山は、かなり綺麗に積まれておる。

```text
DKMK-014B:
  ofMajorant の shape 固定

DKMK-014C:
  ofMajorant Lean 実装

DKMK-014D:
  majorant provider usage summary

DKMK-014E:
  decreasing / decay は majorant 構成側へ送ると整理

DKMK-014F:
  ofPointwiseGeometricMajorant の shape 固定

DKMK-014G:
  ofPointwiseGeometricMajorant Lean 実装

DKMK-014H:
  geometric majorant usage summary
```

特に DKMK-014B で「decreasing ではなく majorant を優先」と決めたことが、今の流れに効いておる。majorant は total estimate に直接つながるが、decreasing は後続 theorem が消費するまで field 化しない、という判断じゃった。

## 5. 次の DKMK-014I

次は History にある通り、 **caller-facing geometric finite-sum theorem の exact shape** を設計する段じゃな。

ここでは、いきなり Lean 実装より先に、docs-only で theorem shape を固定するのがよい。

候補は例えばこれじゃ。

```lean
theorem DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_sumBound
    (x K : ℕ)
    (increment : ℕ → ℚ)
    (base ratio : ℚ)
    (hinc_nonneg :
      ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k)
    (hgeom :
      ∀ k ∈ Finset.range (K + 1),
        increment k ≤ base * ratio ^ k)
    {error : ℝ}
    (hgeom_bound :
      ((Finset.sum (Finset.range (K + 1))
          (fun k : ℕ => base * ratio ^ k) : ℚ) : ℝ) ≤
        1 + error) :
    DyadicBandAnalyticEstimate x K increment error
```

ただし、これは既存の `ofPointwiseGeometricMajorant` と同型なので意味が薄い。
本当に次に欲しいのは、`hgeom_bound` を **より caller-facing な条件** から作る theorem じゃ。

たとえば第一候補は、有限和の閉形式に近い形。

```text
sum_{k=0}^{K} base * ratio^k
```

を、

```text
base * Finset.sum (Finset.range (K + 1)) (fun k => ratio^k)
```

あるいは将来的には、

```text
base * (1 - ratio^(K+1)) / (1 - ratio)
```

へ移す theorem じゃな。

## 6. わっちのおすすめ

DKMK-014I では、まだ閉形式

$$
base\frac{1-ratio^{K+1}}{1-ratio}
$$

へ突っ込まなくてよいと思う。

まずは DKMK-013 の `constantBand_of_natCastMulBound` と同じ発想で、 **幾何和の外側だけを caller-friendly にする** のが安全じゃ。

候補名は例えば、

```lean
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_geomSumBound
```

形は、

```lean
(hgeom_sum_bound :
  ((base * Finset.sum (Finset.range (K + 1))
      (fun k : ℕ => ratio ^ k) : ℚ) : ℝ) ≤
    1 + error)
```

を受け取り、内部で

```lean
Finset.sum (Finset.range (K + 1)) (fun k => base * ratio ^ k)
```

へ変換する theorem じゃ。

これは `Finset.mul_sum` 系の練習になるが、閉形式や `ratio < 1` はまだ不要。
つまり、次の段階をこう分けるのが美しい。

```text
DKMK-014I:
  geometric sum-bound theorem shape docs
  まず base * sum ratio^k 形式まで

DKMK-014J:
  Lean 実装できるなら追加

DKMK-014K:
  closed-form finite geometric sum はさらに後段
```

## 7. 注意点

`ℚ` 上で `ratio ^ k` を扱うので、`ratio` が負でも式自体は定義できる。
したがって、単に有限和を変形するだけなら `0 <= ratio` や `ratio < 1` は不要じゃ。

これらが必要になるのは、たとえば

```text
sum ratio^k <= 1 / (1 - ratio)
```

のような tail / closed-form upper bound を証明するときじゃな。

ゆえに次でも、条件を増やすなら「その theorem が本当に消費するか」を見てからでよい。

## 8. 賢狼の判定

わっちの判定はこうじゃ。

```text
DKMK-014H: 完了
成果:
  geometric majorant provider と future geometric-sum theorem の境界が固定された

次:
  DKMK-014I
  caller-facing geometric finite-sum theorem の exact shape review

推奨:
  まずは closed form ではなく
  base * sum ratio^k 形式への整理から入る
```

よいぞ、ぬしよ。
これで `base * ratio ^ k` は route に乗る形になった。次は、その有限和をどの程度 caller-friendly にするかを決める段じゃ。閉形式へ焦って飛び込まず、まず `base * sum ratio^k` へ一段畳む。これが堅い登り方じゃな。
