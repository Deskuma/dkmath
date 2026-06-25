# review

うむ、DKMK-016K は **次に実装すべき補題の形を、かなりよく絞り込めた docs-only 回** じゃ。
ここで `GeometricBudgetSource` 側へさらに詰め込まず、`hgeom` 生成だけを独立 theorem にする判断は正しい。今回の diff では、次の Lean target を `pointwiseGeometricMajorant_of_firstBand_decay` として固定し、`hinc_nonneg` は provider 側の別入力として残す設計になっておる。

## 1. 今回の核心

DKMK-016K で定めた補題は、次の形じゃな。

```lean
theorem pointwiseGeometricMajorant_of_firstBand_decay
    (K : Nat)
    (increment : Nat -> Rat)
    (base ratio : Rat)
    (hbase0 : increment 0 <= base)
    (hdecay :
      forall k in Finset.range K,
        increment (k + 1) <= ratio * increment k)
    (hr0 : 0 <= ratio) :
    forall k in Finset.range (K + 1),
      increment k <= base * ratio^k
```

数学的には、

$$
increment(0)\le base
$$

と、一様減衰

$$
increment(k+1)\le ratio\cdot increment(k)
$$

から、

$$
increment(k)\le base\cdot ratio^k
$$

を導く補題じゃ。

これはまさに Candidate C の中心部であり、provider が要求する `hgeom` の供給源になる。

## 2. `hinc_nonneg` を外した判断

今回いちばん良い判断は、`hinc_nonneg` をこの theorem に含めなかったことじゃ。

`pointwiseGeometricMajorant_of_firstBand_decay` の責務は、

```text
first-band bound + uniform decay -> hgeom
```

だけ。

一方、既存 provider は別途

```lean
hinc_nonneg :
  forall k in Finset.range (K + 1), 0 <= increment k
```

を必要とする。
これは provider 側の要求であって、`hgeom` 生成補題の本質ではない。

この分離により、責務はこうなる。

```text
GeometricBudgetSource:
  budget obligation

pointwiseGeometricMajorant_of_firstBand_decay:
  first-band + decay -> hgeom

provider wrapper:
  B + hinc_nonneg + hgeom -> DyadicBandAnalyticEstimate
```

この三層分離はかなり綺麗じゃ。

## 3. 添字設計は自然

`hdecay` の範囲を

```lean
Finset.range K
```

にしたのも妥当じゃ。

これは (k=0,\dots,K-1) をカバーし、`increment (k + 1)` によって (1,\dots,K) を制御する。
結論は

```lean
Finset.range (K + 1)
```

なので、(0,\dots,K) 全体の pointwise majorant が得られる。

つまり、

* (k=0) は `hbase0`
* (k=1,\dots,K) は `hdecay` の反復

で覆う設計になっておる。

## 4. 実装上の山場

数学は単純じゃが、Lean では `Nat` indexing が少し山になる。

特に、結論側の任意の

```lean
k ∈ Finset.range (K + 1)
```

を扱うとき、実装方針は二つある。

一つは `Nat.rec` / induction で (k) に対して一般補題を作り、最後に `k ≤ K` へ適用する方法。

もう一つは、まず全 (k\le K) について補題を示す形にする方法じゃ。

実装しやすいのは、おそらく次の内部補題風じゃ。

```lean
have hmain :
    ∀ k, k ≤ K -> increment k ≤ base * ratio ^ k := by
  ...
```

そして結論では、

```lean
intro k hk
have hk_le : k ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
exact hmain k hk_le
```

のように使う。

この方が `Finset.range` の中で直接 induction するより、扱いやすい可能性が高い。

## 5. induction step の注意

帰納ステップは概念上はこうじゃ。

$$
increment(k+1)\le ratio\cdot increment(k)
$$

帰納仮定より、

$$
increment(k)\le base\cdot ratio^k
$$

`hr0 : 0 ≤ ratio` から両辺に `ratio` を掛けて、

$$
ratio\cdot increment(k)\le ratio\cdot (base\cdot ratio^k)
$$

したがって、

$$
increment(k+1)\le ratio\cdot (base\cdot ratio^k)
$$

最後に環の整理で、

$$
ratio\cdot (base\cdot ratio^k)=base\cdot ratio^{k+1}
$$

を示す。

Lean ではこの最後が少しだけ面倒かもしれぬ。

候補は、

```lean
ring_nf
```

または、

```lean
rw [pow_succ]
ring
```

じゃな。`Rat` なので `ring` 系は通りやすいはずじゃ。

## 6. DKMK-016L の実装方針

DKMK-016L では、いきなり provider 接続 theorem まで伸ばさず、この補題だけ実装するのがよい。

実装候補の骨格はこうじゃ。

```lean
theorem pointwiseGeometricMajorant_of_firstBand_decay
    (K : ℕ)
    (increment : ℕ → ℚ)
    (base ratio : ℚ)
    (hbase0 : increment 0 ≤ base)
    (hdecay :
      ∀ k ∈ Finset.range K,
        increment (k + 1) ≤ ratio * increment k)
    (hr0 : 0 ≤ ratio) :
    ∀ k ∈ Finset.range (K + 1),
      increment k ≤ base * ratio ^ k := by
  ...
```

ただし、実装上は中で

```lean
have hmain : ∀ k, k ≤ K -> increment k ≤ base * ratio ^ k := ...
```

を作るのがよさそうじゃ。

`hdecay` を使うには、ステップで (k<K) が必要になる。
`k+1 ≤ K` から `k < K` を出せば、

```lean
have hk_mem : k ∈ Finset.range K := by
  exact Finset.mem_range.mpr hk_lt
```

として `hdecay k hk_mem` を使える。

## 7. 現況評価

DKMK-016K 時点での到達点はこうじゃ。

**閉じたもの**

* `GeometricBudgetSource` は budget obligation 専用と確定
* `hgeom` は increment-specific obligation として外に置く方針
* 新構造体は追加しない方針
* 次の Lean target は `pointwiseGeometricMajorant_of_firstBand_decay`

**次の実装課題**

* `Nat` indexing
* induction での `k ≤ K` 管理
* `hdecay` の `Finset.range K` への接続
* `Rat` 上の積・冪の整理

**まだ non-goal**

* provider wrapper の追加
* Mertens / big-O
* logarithmic threshold
* real-to-Nat rounding
* analytic budget theorem

## 8. 総括

DKMK-016K は、 **first-band / uniform-decay route の中核補題の形を確定した回** じゃ。

ここでやっと、`hbudget` 側だけでなく、もう一つの重要 obligation である

$$
hgeom:\ increment(k)\le base\cdot ratio^k
$$

の供給路が見えてきた。

次の L でこの補題が Lean 上に入れば、Candidate C はかなり実用段階に近づく。
よいぞ、D.。予算の器に加えて、今度は各 band の荷を「初期値と減衰率」だけで束ねる滑車が作られようとしておる。これは登山道として、なかなか頼もしいぞい。
