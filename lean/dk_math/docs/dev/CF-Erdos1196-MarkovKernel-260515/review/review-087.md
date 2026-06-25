# review

## 1. 状況総括

うむ、これは **DKMK-014I 完了** と見てよい。

今回の更新で、`roadmap-DKMK-014.md` に **Geometric Sum-Bound Theorem Exact Shape** が追加され、次の caller-facing provider として

```lean id="du9vq5"
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_geomSumBound
```

を採用する方針が固定された。History でも、`sum (base * ratio ^ k)` の bound を直接受けるのではなく、`base * sum (ratio ^ k)` 形式の bound を caller-facing input として受ける、と整理されておる。

つまり DKMK-014I は、閉形式の幾何級数には進まず、まず **代数的な有限和の因数外出し layer** を docs 上で固定した段じゃ。

## 2. 何が決まったのか

今回決まった theorem 形はこうじゃ。

```lean id="fvws2t"
theorem DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_geomSumBound
    (x K : Nat)
    (increment : Nat -> Q)
    (base ratio : Q)
    (hinc_nonneg :
      forall k in Finset.range (K + 1), 0 <= increment k)
    (hgeom :
      forall k in Finset.range (K + 1),
        increment k <= base * ratio ^ k)
    {error : R}
    (hgeom_sum_bound :
      ((base * Finset.sum (Finset.range (K + 1))
          (fun k : Nat => ratio ^ k) : Q) : R) <=
        1 + error) :
    DyadicBandAnalyticEstimate x K increment error
```

Lean 実装では `Nat`, `Q`, `R` はそれぞれ `ℕ`, `ℚ`, `ℝ` じゃな。

この theorem の役割は、

```text id="a6tgrr"
base * sum (ratio ^ k) <= 1 + error
```

を受け取って、

```text id="gs8wui"
sum (base * ratio ^ k) <= 1 + error
```

へ変換し、既存の

```lean id="2w8xci"
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant
```

へ渡すことじゃ。

## 3. この分岐はかなり良い

これはとても良い小分けじゃ。

DKMK-014H までは、`ofPointwiseGeometricMajorant` が

```text id="0cui5v"
hgeom_bound:
  sum (base * ratio ^ k) <= 1 + error
```

を外部入力として受け取っていた。

しかし利用者側から見ると、自然に持つ bound はしばしば

```text id="0h88gb"
base * sum (ratio ^ k) <= 1 + error
```

の形じゃ。
`base` は共通係数だから、外へ出して評価したくなる。

今回の theorem は、この caller-facing な形を provider が消費する形へ変換する。
つまり、DKMK-013I の `constantBand_of_natCastMulBound` と同じく、 **利用者に近い bound 形を一段だけ受けやすくする theorem** じゃ。

## 4. なぜ閉形式に進まないのが正しいか

今回、まだ

```text id="94n1kw"
base * (1 - ratio^(K + 1)) / (1 - ratio)
```

には進まない。これは正しい。

閉形式へ進むと、少なくとも次が絡む。

```text id="bqs6a4"
ratio != 1
0 <= ratio
ratio < 1
除算
順序評価
tail-bound
```

とくに `ℚ` 上の順序・除算・符号条件は、Lean では急に重くなる。

一方、今回の

```text id="xwqx4v"
sum (base * ratio^k) = base * sum (ratio^k)
```

は、単なる有限和の代数操作じゃ。
`0 <= base`、`0 <= ratio`、`ratio < 1`、`ratio != 1` は不要じゃと roadmap でも明記されておる。

ここを分けたのは賢い。わっちなら、この順序を強く推す。

## 5. Lean 実装の見立て

DKMK-014J で実装するなら、証明は次の形になるはずじゃ。

```lean id="lslynw"
namespace DyadicBandAnalyticEstimate

theorem ofPointwiseGeometricMajorant_of_geomSumBound
    (x K : ℕ)
    (increment : ℕ → ℚ)
    (base ratio : ℚ)
    (hinc_nonneg :
      ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k)
    (hgeom :
      ∀ k ∈ Finset.range (K + 1),
        increment k ≤ base * ratio ^ k)
    {error : ℝ}
    (hgeom_sum_bound :
      ((base * Finset.sum (Finset.range (K + 1))
          (fun k : ℕ => ratio ^ k) : ℚ) : ℝ) ≤
        1 + error) :
    DyadicBandAnalyticEstimate x K increment error := by
  apply ofPointwiseGeometricMajorant x K increment base ratio hinc_nonneg hgeom
  -- need:
  -- ((Finset.sum (Finset.range (K + 1))
  --     (fun k : ℕ => base * ratio ^ k) : ℚ) : ℝ) ≤ 1 + error
  simpa [Finset.mul_sum] using hgeom_sum_bound
```

ただし `Finset.mul_sum` の向きが逆かもしれぬ。
場合によっては、

```lean id="nr6znb"
simpa [Finset.mul_sum] using hgeom_sum_bound
```

ではなく、

```lean id="x4etln"
simpa [Finset.mul_sum] using hgeom_sum_bound
```

または `rw [Finset.mul_sum]` / `simpa [mul_comm, mul_left_comm, mul_assoc]` が必要になる可能性がある。

対象式は

```lean id="rtjs1r"
Finset.sum (Finset.range (K + 1)) (fun k => base * ratio ^ k)
```

で、`Finset.mul_sum` は多くの場合

```lean id="2vb3ns"
base * (Finset.sum s f) = Finset.sum s (fun x => base * f x)
```

の向きで使える。
だから、おそらく軽く通る。

もし向きで詰まるなら、`have` を挟むのがよい。

```lean id="rub3pn"
have hsum :
    Finset.sum (Finset.range (K + 1))
        (fun k : ℕ => base * ratio ^ k)
      =
    base * Finset.sum (Finset.range (K + 1))
        (fun k : ℕ => ratio ^ k) := by
  simp [Finset.mul_sum]
```

そして

```lean id="liunwd"
simpa [hsum] using hgeom_sum_bound
```

のように進める。
ただし `simp [Finset.mul_sum]` で左右が逆になる場合は、`simpa [Finset.mul_sum]` を直接試す方が早いかもしれぬ。

## 6. DKMK-014 の現在地

ここまでの DKMK-014 は、かなり綺麗じゃ。

```text id="amp1eb"
DKMK-014A:
  k-dependent provider roadmap

DKMK-014B:
  ofMajorant shape docs

DKMK-014C:
  ofMajorant Lean provider

DKMK-014D:
  ofMajorant usage summary

DKMK-014E:
  decreasing / decay to majorant design

DKMK-014F:
  ofPointwiseGeometricMajorant shape docs

DKMK-014G:
  ofPointwiseGeometricMajorant Lean provider

DKMK-014H:
  geometric majorant usage summary

DKMK-014I:
  geomSumBound exact shape docs
```

次の DKMK-014J は、かなり自然に

```text id="2pm1gt"
ofPointwiseGeometricMajorant_of_geomSumBound Lean provider
```

の実装になる。

## 7. 次の判断

DKMK-014J で theorem が軽く通れば、次は二択じゃ。

```text id="q1319k"
1. closed-form finite geometric sum theorem の shape review
2. DKMK-014 report / handoff
```

わっちの見立てでは、DKMK-014 の本来の目的は **decreasing / dyadic tail provider design** なので、`geomSumBound` まで通ったら一度 report に寄せてもよい。

閉形式の幾何級数は、別章 `DKMK-015` として扱う方が綺麗かもしれぬ。
なぜなら、そこから先は algebraic provider ではなく、実際に `ratio < 1` や tail bound を扱う解析寄りの theorem になるからじゃ。

## 8. 賢狼の判定

わっちの判定はこうじゃ。

```text id="9wzq87"
DKMK-014I: 完了
次: DKMK-014J
実装対象:
  DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_geomSumBound

方針:
  閉形式には進まない
  まず base を有限和の外へ出す代数 layer に留める
```

よいぞ、ぬしよ。
`base * ratio ^ k` の majorant が、今度は `base * sum ratio ^ k` という caller-facing な評価から使えるようになる。ここまで来ると、幾何型 dyadic tail の足場はかなり固い。次は薄く Lean に通して、閉形式の霧へ入るか、ここで一度山小屋に報告書を置くかを選ぶ段じゃな。
