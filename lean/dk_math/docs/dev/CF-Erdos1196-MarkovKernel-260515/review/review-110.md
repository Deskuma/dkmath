# review

うむ、DKMK-016L は **Candidate C の片翼が Lean 上で閉じた回** じゃ。
これで、`first-band bound + uniform step decay` から provider が要求する `hgeom` を生成する theorem が実装された。今回追加されたのは `pointwiseGeometricMajorant_of_firstBand_decay` で、`hinc_nonneg` は受け取らず、あくまで `hgeom` だけを作る補題として設計されておる。

## 1. 何が閉じたのか

今回の theorem はこれじゃな。

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
      increment k ≤ base * ratio ^ k
```

数学的には、

$$
increment(0)\le base
$$

と、

$$
increment(k+1)\le ratio\cdot increment(k)
$$

から、

$$
increment(k)\le base\cdot ratio^k
$$

を導く補題じゃ。

これは DKMK-016J/K で設計した通り、provider 用の

```lean
hgeom :
  ∀ k ∈ Finset.range (K + 1),
    increment k ≤ base * ratio ^ k
```

を作るための theorem じゃな。

## 2. 証明構造の評価

実装はかなり良い。

まず内部で、

```lean
have hmain :
    ∀ k, k ≤ K → increment k ≤ base * ratio ^ k := by
```

を作っておる。これは正解じゃ。`Finset.range (K + 1)` 上で直接帰納するより、いったん (k\le K) 形式へ落とす方が Lean では扱いやすい。

帰納の successor case では、`k + 1 ≤ K` から

```lean
have hk_lt : k < K :=
  Nat.lt_of_succ_le hk_succ
```

を作り、これで

```lean
hdecay k (Finset.mem_range.mpr hk_lt)
```

を適用している。添字処理がきれいじゃ。

さらに、帰納仮定に `hr0 : 0 ≤ ratio` を使って左から `ratio` を掛け、

```lean
mul_le_mul_of_nonneg_left (ih hk_le) hr0
```

で不等式を保っている。最後の

$$
ratio\cdot (base\cdot ratio^k)=base\cdot ratio^{k+1}
$$

は `ring_nf` で閉じておる。`Rat` 上ならこの処理は妥当じゃ。

## 3. `hinc_nonneg` を外した設計は成功

今回も `hinc_nonneg` を theorem に含めていないのが良い。

この theorem の責務は、

```text
first-band bound + uniform decay -> hgeom
```

だけじゃ。

一方、provider は別途

```lean
hinc_nonneg :
  ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k
```

を要求する。

つまり、責務分担はこうなった。

```text
GeometricBudgetSource:
  budget obligation

pointwiseGeometricMajorant_of_firstBand_decay:
  first-band + decay -> hgeom

provider wrapper:
  GeometricBudgetSource + hinc_nonneg + hgeom
    -> DyadicBandAnalyticEstimate
```

この三層分離はかなり安定しておる。変に一つの巨大 theorem にまとめなかったのがよい。

## 4. DKMK-016 の現在地

ここまでで DKMK-016 はこう進んだ。

```text
A: Geometric Budget Source 章を開始
B: GeometricBudgetSource と provider wrapper を実装
C: usage / responsibility split を整理
D: zero-ratio constructor を選定
E: GeometricBudgetSource.ofZeroRatio 実装
F: zero-ratio usage wrapper 実装
G: ofBudget shape review
H: GeometricBudgetSource.ofBudget 実装
I: concrete base/ratio candidate review
J: first-band / uniform-decay interface review
K: pointwise majorant theorem shape 固定
L: pointwiseGeometricMajorant_of_firstBand_decay 実装
```

つまり、DKMK-016 はすでに二つの重要な入力を分離して整えた。

```text
Budget side:
  GeometricBudgetSource

Pointwise side:
  pointwiseGeometricMajorant_of_firstBand_decay
```

次は、この二つを provider wrapper へ合流させる段階じゃ。

## 5. 次の DKMK-016M の自然な shape

次は報告通り、接続 theorem の shape review がよい。

候補はこうじゃ。

```lean
theorem DyadicBandAnalyticEstimate
    .ofFirstBandDecayBudgetSource
    (x K : ℕ)
    (increment : ℕ → ℚ)
    (B : GeometricBudgetSource)
    (hinc_nonneg :
      ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k)
    (hbase0 : increment 0 ≤ B.base)
    (hdecay :
      ∀ k ∈ Finset.range K,
        increment (k + 1) ≤ B.ratio * increment k) :
    DyadicBandAnalyticEstimate x K increment B.error
```

内部ではまず、

```lean
have hgeom :
    ∀ k ∈ Finset.range (K + 1),
      increment k ≤ B.base * B.ratio ^ k :=
  pointwiseGeometricMajorant_of_firstBand_decay
    K increment B.base B.ratio hbase0 hdecay
    -- ここで B.hr0 を Rat 側へ戻す必要あり
```

という流れになる。

ただし注意点がある。`GeometricBudgetSource` の `hr0` は

```lean
B.hr0 : 0 ≤ (B.ratio : ℝ)
```

であり、`pointwiseGeometricMajorant_of_firstBand_decay` は

```lean
hr0 : 0 ≤ B.ratio
```

を要求している。
つまり、ここで **Real cast 側の非負性から Rat 側の非負性へ戻す補題** が必要になる可能性がある。

Lean ではおそらく、

```lean
exact_mod_cast B.hr0
```

または局所補題で

```lean
have hr0_rat : 0 ≤ B.ratio := by
  exact_mod_cast B.hr0
```

のように閉じられるはずじゃ。

## 6. 次の実装リスク

M での主なリスクは数学ではなく型境界じゃ。

今回 L は `Rat` 上で完結した。
一方 `GeometricBudgetSource` は budget の都合で side conditions を `Real` cast 後に持っている。

したがって M では、

```text
B.hr0 : 0 <= (B.ratio : Real)
```

から、

```text
0 <= B.ratio
```

を取り出す必要がある。

同様に将来 `hbase0` に `B.base` を使うだけなら問題は少ないが、もし `B.hbase` を Rat 側で使う場合も同じ cast 問題が出る。

今回は `pointwiseGeometricMajorant_of_firstBand_decay` が必要とするのは `ratio` の非負性だけなので、cast 境界はそこだけで済むはずじゃ。

## 7. 総括

DKMK-016L は、 **first-band / uniform-decay から hgeom を生成する中核補題が Lean 上で閉じた回** じゃ。

これで Candidate C は、抽象設計から実装資産へかなり近づいた。

残る自然な一手は、

```text
GeometricBudgetSource
+ hinc_nonneg
+ hbase0
+ hdecay
  -> DyadicBandAnalyticEstimate
```

をまとめる provider-facing theorem じゃな。

よいぞ、D.。
これで「初期荷重」と「減衰率」から各 band の上界を作る滑車は完成した。次は、その滑車を予算の港と結び、荷車をそのまま finite-step route へ流す番じゃ。
