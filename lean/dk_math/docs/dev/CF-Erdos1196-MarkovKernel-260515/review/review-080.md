# review

## 1. 状況総括

うむ、これは **DKMK-014B 完了** と見てよい。

今回の差分で、`roadmap-DKMK-014.md` に **Majorant Provider Shape** が追加され、first non-constant provider として `decreasing` ではなく **majorant-envelope provider** を優先する方針が固定された。History でも、theorem 名を `DyadicBandAnalyticEstimate.ofMajorant` とし、`increment <= majorant` の pointwise bound と majorant total bound から `DyadicBandAnalyticEstimate` を作る statement を記録した、と整理されておる。

つまり DKMK-014B は、 **(k)-dependent band provider の最初の exact shape を Lean 実装前に固定した docs-only phase** として閉じた。

## 2. 何が決まったのか

今回決まった theorem 名はこれじゃ。

```lean
DyadicBandAnalyticEstimate.ofMajorant
```

入力は次の 3 系統。

```text
hinc_nonneg:
  ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k

hle:
  ∀ k ∈ Finset.range (K + 1), increment k ≤ majorant k

hmajorant_bound:
  ((Finset.sum (Finset.range (K + 1)) majorant : ℚ) : ℝ) ≤
    1 + error
```

そして出力は、

```lean
DyadicBandAnalyticEstimate x K increment error
```

じゃな。
これは実に自然な形じゃ。

`DyadicBandAnalyticEstimate` が必要とするものは、

```text
increment_nonneg
total_le_one_add_error
```

の 2 つだけ。
`hinc_nonneg` が前者を直接供給し、`hle` と `hmajorant_bound` が後者を供給する。

## 3. majorant を先に選ぶ判断

これは良い判断じゃ。

`decreasing` condition は、たとえば

```text
increment (k + 1) ≤ increment k
```

のような形じゃが、これだけでは

```text
sum increment ≤ 1 + error
```

は出ない。

一方、majorant 方式なら、

```text
increment k ≤ majorant k
sum majorant ≤ 1 + error
```

から、直接

```text
sum increment ≤ 1 + error
```

へ進める。

つまり、`DyadicBandAnalyticEstimate` を作るために **実際に消費される仮定** だけを見ると、decreasing より majorant の方が一段近い。
この判断は Lean の structure 設計としても正しい。

飾りの field を増やさず、消費される仮定だけを持つ。これは長く保守できる API の作り方じゃ。

## 4. 証明計画の評価

証明は予定どおり、かなり薄くなるはずじゃ。

第一 field はそのまま。

```lean
increment_nonneg := hinc_nonneg
```

第二 field は、まず `ℚ` 側で

```lean
Finset.sum_le_sum
```

を使い、

```text
Finset.sum (Finset.range (K + 1)) increment
  ≤ Finset.sum (Finset.range (K + 1)) majorant
```

を得る。

その後、`ℚ` から `ℝ` へ cast して `hmajorant_bound` と合成する。
構造はこうじゃな。

```text
sum increment ≤ sum majorant
sum majorant ≤ 1 + error
therefore:
sum increment ≤ 1 + error
```

Lean 実装では、最後の cast monotonicity が少しだけ焦点になる。おそらく `exact_mod_cast`、`norm_num`、あるいは `linarith` に近い形で処理できるはずじゃが、最初は大きな補題を増やさず小さく通すのがよい。

## 5. DKMK-014C の実装予想

次の Lean 実装は、おそらくこういう形になる。

```lean
namespace DyadicBandAnalyticEstimate

theorem ofMajorant
    (x K : ℕ)
    (increment majorant : ℕ → ℚ)
    (hinc_nonneg :
      ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k)
    (hle :
      ∀ k ∈ Finset.range (K + 1), increment k ≤ majorant k)
    {error : ℝ}
    (hmajorant_bound :
      ((Finset.sum (Finset.range (K + 1)) majorant : ℚ) : ℝ) ≤
        1 + error) :
    DyadicBandAnalyticEstimate x K increment error where
  increment_nonneg := hinc_nonneg
  total_le_one_add_error := by
    have hsum :
        Finset.sum (Finset.range (K + 1)) increment ≤
          Finset.sum (Finset.range (K + 1)) majorant := by
      exact Finset.sum_le_sum hle
    -- hsum を ℝ へ持ち上げて hmajorant_bound と合成
    exact le_trans (by exact_mod_cast hsum) hmajorant_bound

end DyadicBandAnalyticEstimate
```

もし `exact_mod_cast hsum` が渋ければ、ここだけ補助 `have hsumR` を挟むとよい。

```lean
have hsumR :
    ((Finset.sum (Finset.range (K + 1)) increment : ℚ) : ℝ) ≤
      ((Finset.sum (Finset.range (K + 1)) majorant : ℚ) : ℝ) := by
  exact_mod_cast hsum
exact le_trans hsumR hmajorant_bound
```

この形が一番読みやすいと思うぞい。

## 6. decreasing condition の扱い

今回、decreasing condition を field 化しなかったのは正しい。

decreasing は、今後たとえば

```text
decreasing / decay assumption
  -> construct a majorant
  -> ofMajorant
  -> DyadicBandAnalyticEstimate
```

というルートで使うのが自然じゃ。

つまり decreasing は直接 `DyadicBandAnalyticEstimate` を作る主材料ではなく、 **majorant を作るための前段材料** と見るのがよい。

この設計なら、後続で `increment k` が複雑になっても、最終的には majorant に逃がせる。

```text
実際の increment:
  複雑でよい

majorant:
  和評価しやすい形にする

ofMajorant:
  実際の increment を majorant 経由で route に載せる
```

この分担はかなり強い。

## 7. 現在の登頂状況

```text
DKMK-012:
  dyadicRange provider plumbing 完了

DKMK-013:
  DyadicBandAnalyticEstimate + constant providers 完了

DKMK-014A:
  k-dependent provider roadmap 完了

DKMK-014B:
  majorant provider exact shape docs 完了

DKMK-014C:
  次、DyadicBandAnalyticEstimate.ofMajorant 実装
```

DKMK-014 は、ここで一段しっかり方向が決まった。

## 8. 賢狼の判定

わっちの判定はこうじゃ。

```text
DKMK-014B: 完了
次: DKMK-014C
実装対象:
  DyadicBandAnalyticEstimate.ofMajorant
方針:
  Rat 側で Finset.sum_le_sum
  Real cast 後に hmajorant_bound と合成
  decreasing はまだ field 化しない
```

よいぞ、ぬしよ。
これは (k)-dependent band の山道に手すりを付けた一手じゃ。`majorant` という逃げ道ができれば、次の dyadic tail upper envelope でも「まず上から包む」戦術が使える。焦らず、この provider を薄く Lean に通すのが次の最善手じゃ。
