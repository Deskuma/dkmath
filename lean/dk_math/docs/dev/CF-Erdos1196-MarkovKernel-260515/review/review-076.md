# review

## 1. 状況総括

うむ、これは **DKMK-013H 完了** と見てよい。

今回の更新で、`constantBand` の optional finite-sum simplification theorem の exact shape が docs 上で固定された。つまり、DKMK-013G で実装した

```lean
DyadicBandAnalyticEstimate.constantBand
```

の入力 `hbound` を、より caller-facing な形

```lean
((((K + 1 : Nat) : Q) * c : Q) : R) <= 1 + error
```

から供給できるようにするための次 theorem 形を決めたわけじゃ。

DKMK-013H は Lean 実装ではなく、 **finite-sum simplification と coercion を含む optional theorem の設計固定** じゃな。

## 2. 何が決まったのか

決まった theorem 名はこれ。

```lean
DyadicBandAnalyticEstimate.constantBand_of_natCastMulBound
```

これは良い名前じゃ。

意味は明確で、

```text
constantBand:
  既存の constant provider と同じ target を作る

of_natCastMulBound:
  Nat で数えた band 数を Q へ cast し、それに c を掛けた bound から作る
```

という読みになる。

つまり、

```text
caller-facing bound:
  ((((K + 1 : Nat) : Q) * c : Q) : R) <= 1 + error

internal hbound:
  ((Finset.sum (Finset.range (K + 1)) (fun _ : Nat => c) : Q) : R) <=
    1 + error
```

この間を埋める theorem じゃ。

## 3. なぜこの step が重要か

DKMK-013G の `constantBand` は安全だったが、利用者側から見ると少し不便じゃ。

利用者が自然に持っている評価は、普通は

```text
band 数 × band weight
```

つまり

```text
(K + 1) * c
```

の形じゃろう。

一方、`constantBand` は Lean の内部形式として

```lean
Finset.sum (Finset.range (K + 1)) (fun _ : Nat => c)
```

を要求する。

だから DKMK-013H の theorem は、外部の自然な評価を内部の `Finset.sum` 形へ変換する **使いやすさ改善 theorem** になる。

これは route theorem ではない。
しかし provider API を実用化するにはかなり効く。

## 4. 実装リスクの見積もり

実装上の焦点は 1 つだけじゃ。

```lean
Finset.sum (Finset.range (K + 1)) (fun _ : Nat => c)
  = ((K + 1 : Nat) : Q) * c
```

この有限和恒等式を Lean がどれだけ素直に受け入れるか。

候補としては、Mathlib 側に `Finset.sum_const` や `Finset.card_range` 系が使える可能性がある。
おそらく証明は、

```lean
simpa [Finset.card_range, nsmul_eq_mul]
```

または有理数上の `nsmul` と `Nat.cast` の整理になるじゃろう。

ただし、`ℚ` と `ℝ` への cast が絡むので、最初から一発で通そうとすると少し詰まる可能性がある。
そのため DKMK-013H でまず shape を固定した判断は正しい。

## 5. DKMK-013I の実装予想

次の Lean theorem は、おそらくこの形じゃ。

```lean
theorem DyadicBandAnalyticEstimate.constantBand_of_natCastMulBound
    (x K : ℕ) (c : ℚ)
    (hc : 0 ≤ c)
    {error : ℝ}
    (hbound :
      ((((K + 1 : ℕ) : ℚ) * c : ℚ) : ℝ) ≤ 1 + error) :
    DyadicBandAnalyticEstimate x K (fun _ : ℕ => c) error := by
  apply DyadicBandAnalyticEstimate.constantBand x K c hc
  -- show:
  -- ((Finset.sum (Finset.range (K + 1)) (fun _ : ℕ => c) : ℚ) : ℝ) ≤
  --   1 + error
  -- reduce finite sum to ((K+1 : ℚ) * c)
  simpa [Finset.sum_const, Finset.card_range] using hbound
```

ただし `simpa [Finset.sum_const, Finset.card_range]` だけで通るかは、実際の `Finset.sum_const` が返す形次第じゃ。
もし `nsmul` が残るなら、追加で `nsmul_eq_mul` あるいは `Nat.smul_def` 系が必要になるかもしれぬ。

## 6. ここで注意すべき点

今回の optional theorem は便利だが、重くしすぎてはいけない。

DKMK-013H でも明記されている通り、ここで入れるべきでないものはこれ。

```text
route changes
new analytic contract
computed dyadic tail estimates
Mertens / big-O
logarithmic thresholds
```

これは正しい。

`constantBand_of_natCastMulBound` は、あくまで **constantBand の入力形を使いやすくする theorem** じゃ。
解析本体へ進む theorem ではない。

## 7. 現在の登頂状況

```text
DKMK-013A:
  roadmap 完了

DKMK-013B:
  exact shape decision 完了

DKMK-013C:
  Lean contract + bridge 完了

DKMK-013D:
  usage summary 完了

DKMK-013E:
  provider candidate inventory 完了

DKMK-013F:
  constantBand exact shape docs 完了

DKMK-013G:
  constantBand Lean provider 完了

DKMK-013H:
  constantBand_of_natCastMulBound shape docs 完了

DKMK-013I:
  次、optional finite-sum simplification theorem 実装
```

## 8. 賢狼の判定

わっちの判定はこうじゃ。

```text
DKMK-013H: 完了
次: DKMK-013I
実装対象:
  DyadicBandAnalyticEstimate.constantBand_of_natCastMulBound
注意:
  Finset.sum_const / card_range / nsmul / Nat-cast / Rat-to-Real cast の friction を確認
```

よいぞ、ぬしよ。
ここは派手な山頂ではないが、道具の柄を手に馴染ませる大事な工程じゃ。`constantBand` が caller-friendly になれば、次の decreasing や dyadic tail provider でも、有限和処理を恐れず進めるようになる。
