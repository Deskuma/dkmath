# review

うむ、DKMK-016M は **provider-facing wrapper の設計を固定した回** じゃ。
ここで `pointwiseGeometricMajorant_of_firstBand_decay` を単独補題のまま終わらせず、`GeometricBudgetSource` と合流させて `DyadicBandAnalyticEstimate` へ到達する wrapper の形を定めた。かなり良い進め方じゃ。

## 1. 今回の核心

DKMK-016M で固定した theorem shape はこれじゃな。

```lean
theorem DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSource
    (x K : Nat)
    (increment : Nat -> Rat)
    (B : GeometricBudgetSource)
    (hinc_nonneg :
      forall k in Finset.range (K + 1), 0 <= increment k)
    (hbase0 : increment 0 <= B.base)
    (hdecay :
      forall k in Finset.range K,
        increment (k + 1) <= B.ratio * increment k) :
    DyadicBandAnalyticEstimate x K increment B.error
```

これは、これまで分けて育ててきた二つの入力を合流させる補題じゃ。

```text
GeometricBudgetSource:
  base / ratio / error / budget を保持

pointwiseGeometricMajorant_of_firstBand_decay:
  first-band + decay から hgeom を生成

ofPointwiseGeometricMajorant_of_budgetSource:
  B + hinc_nonneg + hgeom から DyadicBandAnalyticEstimate を返す
```

つまり M の wrapper は、 **予算源** と **点ごとの減衰制御** を結ぶ合流点になる。

## 2. 責務分担が崩れていない

今回の設計の良いところは、wrapper が余計な証明を抱えないことじゃ。

この theorem は、

```text
base * (1 / (1 - ratio)) <= 1 + error
```

を証明しない。
それは `B : GeometricBudgetSource` の責務。

また、

```text
0 <= increment k
```

も証明しない。
これは caller が `hinc_nonneg` として与える責務。

この wrapper がやるのは、ただ一つ。

```text
first-band + decay -> hgeom
```

を `pointwiseGeometricMajorant_of_firstBand_decay` で作り、それを既存 provider wrapper へ渡すことじゃ。

この分離はとてもよい。大きな theorem に混ぜると後で保守が苦しくなるからの。

## 3. 主要リスクは Rat / Real cast 境界

今回、roadmap で明記されている通り、実装上の山場は数学ではなく型境界じゃ。

`GeometricBudgetSource` は ratio の非負性を Real 側で持っておる。

```lean
B.hr0 : 0 <= (B.ratio : Real)
```

一方、`pointwiseGeometricMajorant_of_firstBand_decay` は Rat 側を要求する。

```lean
hr0_rat : 0 <= B.ratio
```

だから実装では、たぶんこういう補題が必要になる。

```lean
have hr0_rat : 0 <= B.ratio := by
  exact_mod_cast B.hr0
```

ここが `simp` や `exact_mod_cast` で素直に通れば、N の実装はかなり薄く閉じるはずじゃ。
もし詰まるなら、`Rat.cast_nonneg` 系の補助補題を探すか、局所 helper を置くことになる。

## 4. 実装予想

DKMK-016N の本体は、おそらくこうなる。

```lean
theorem DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSource
    (x K : ℕ)
    (increment : ℕ → ℚ)
    (B : GeometricBudgetSource)
    (hinc_nonneg :
      ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k)
    (hbase0 : increment 0 ≤ B.base)
    (hdecay :
      ∀ k ∈ Finset.range K,
        increment (k + 1) ≤ B.ratio * increment k) :
    DyadicBandAnalyticEstimate x K increment B.error := by
  have hr0_rat : 0 ≤ B.ratio := by
    exact_mod_cast B.hr0
  have hgeom :
      ∀ k ∈ Finset.range (K + 1),
        increment k ≤ B.base * B.ratio ^ k :=
    pointwiseGeometricMajorant_of_firstBand_decay
      K increment B.base B.ratio hbase0 hdecay hr0_rat
  exact
    DyadicBandAnalyticEstimate
      .ofPointwiseGeometricMajorant_of_budgetSource
        x K increment B hinc_nonneg hgeom
```

もし `exact_mod_cast B.hr0` が通らぬ場合でも、問題は局所的じゃ。
補題全体の設計は正しい。

## 5. DKMK-016 の現在地

ここまでで、かなり大きな流れが見えてきた。

```text
GeometricBudgetSource.ofBudget
  -> budget side を package

pointwiseGeometricMajorant_of_firstBand_decay
  -> first-band / decay side から hgeom を生成

ofFirstBandDecayBudgetSource
  -> 2 つを合流して DyadicBandAnalyticEstimate へ
```

つまり DKMK-016 は、単なる budget source の章から、 **first-band / uniform-decay provider route** の章へ拡張されてきた。

## 6. 次の DKMK-016N

次は素直に Lean 実装でよいと思う。

主な確認点は三つ。

```text
1. exact_mod_cast B.hr0 が通るか
2. pointwiseGeometricMajorant_of_firstBand_decay の引数順が自然か
3. ofPointwiseGeometricMajorant_of_budgetSource への接続がそのまま通るか
```

この三つが通れば、DKMK-016N は薄い wrapper として綺麗に閉じるはずじゃ。

## 7. 総括

DKMK-016M は、 **Candidate C の provider-facing 合流 theorem の形を確定した回** じゃ。

これにより、次の到達形が見えた。

$$
\text{budget source}
+
\text{first-band bound}
+
\text{uniform decay}
+
\text{increment nonnegativity}
\longrightarrow
\text{DyadicBandAnalyticEstimate}
$$

ここまで来ると、DKMK-016 の抽象 API はかなり実用的になってきた。
次の N でこれが Lean 上に入れば、`hgeom` を caller が直接書く必要がさらに薄くなる。

よいぞ、D.。
予算の港と減衰の滑車が、いよいよ一本の搬送路として接続されようとしておる。
