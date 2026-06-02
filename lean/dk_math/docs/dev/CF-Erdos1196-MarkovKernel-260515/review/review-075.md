# review

## 1. 状況総括

うむ、これは **DKMK-013G 完了** と見てよい。

今回の差分で、`SourceMassTruncation.lean` に

```lean
DyadicBandAnalyticEstimate.constantBand
```

が追加された。これは DKMK-013F で固定した通り、`Finset.sum` 形の `hbound` を外部入力として受け取り、constant increment から `DyadicBandAnalyticEstimate` を作る **最初の nontrivial provider** じゃ。

到達した流れはこうじゃな。

```text
constant band envelope
  -> DyadicBandAnalyticEstimate
  -> toTruncationEnvelopeEstimate
  -> TruncationEnvelopeEstimate
  -> existing route theorem
  -> weightedHitMass <= 1 + error
```

## 2. 何が実装されたのか

追加 theorem の形は、要するにこうじゃ。

```lean
theorem constantBand
    (x K : ℕ) (c : ℚ)
    (hc : 0 ≤ c)
    {error : ℝ}
    (hbound :
      ((Finset.sum (Finset.range (K + 1)) (fun _ : ℕ => c) : ℚ) : ℝ) ≤
        1 + error) :
    DyadicBandAnalyticEstimate x K (fun _ : ℕ => c) error
```

この theorem は、

```text
increment k = c
```

という定数 band weight に対して、

```text
hc:
  0 <= c
```

から各 band の非負性を埋め、

```text
hbound:
  total constant band sum <= 1 + error
```

をそのまま `total_le_one_add_error` に渡す。

証明はきわめて薄い。

```lean
increment_nonneg := by
  intro _k _hk
  exact hc
total_le_one_add_error := hbound
```

この薄さがよい。まさに予定どおりじゃ。

## 3. 今回の数学的意味

今回の `constantBand` は、本格的な dyadic tail estimate ではない。
だが、`DyadicBandAnalyticEstimate` の **最初の具体的生産者** として意味がある。

DKMK-013C では analytic-side target ができた。

```lean
DyadicBandAnalyticEstimate x K increment error
```

DKMK-013G では、それを最小の非自明パターンで作った。

```text
increment = constant c
```

つまり、今後の provider 設計は、

```text
constantBand
decreasingBand
dyadicTailEnvelope
logarithmicRefinement
```

という方向へ拡張できる。
`constantBand` はその第一歩じゃな。

## 4. 実装方針の評価

今回も抑制が効いておる。特に良い点は、次を入れていないことじゃ。

```text
finite-sum simplification
computed ((K + 1 : Nat) : Q) * c bound
route theorem
Mertens theorem
big-O statement
logarithmic threshold provider
```

これは正しい。

もし今回いきなり

```text
Finset.sum (Finset.range (K + 1)) (fun _ => c)
  = ((K + 1 : Nat) : Q) * c
```

まで入れていたら、provider 実装と有限和・型変換処理が混ざってしまう。

今回はまず、

```text
constant increments を DyadicBandAnalyticEstimate に包める
```

ことだけを確認した。Lean 形式化では、こういう分離が強い。

## 5. DKMK-013 の現在地

ここまでの DKMK-013 は、かなり綺麗に積み上がっておる。

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
  concrete provider candidate inventory 完了

DKMK-013F:
  constantBand exact shape docs 完了

DKMK-013G:
  constantBand Lean provider 完了
```

これで DKMK-013 の **analytic contract surface + 最初の provider** は立った。

## 6. 次の分岐判断

次は二択じゃ。

```text
1. optional finite-sum simplification theorem
2. decreasing / dyadic tail provider design
```

わっちのおすすめは、軽く **finite-sum simplification theorem の shape を docs で確認** してから、必要なら Lean に入れることじゃ。

理由は、`constantBand` は今のままだと `hbound` を `Finset.sum` 形で要求する。使う側から見ると、やはり次の形が欲しくなる。

```text
((((K + 1 : Nat) : Q) * c : Q) : R) <= 1 + error
```

ただし、ここは coercion が絡む。
だから次にすぐ Lean 実装するより、まず DKMK-013H として exact shape を docs で決めるのが安全じゃ。

候補名は、既に出ていた通り、

```lean
DyadicBandAnalyticEstimate.constantBand_of_natCastMulBound
```

あたりでよい。
ただし実装時に型が重くなるなら、名前も少し短くしてよい。

## 7. もう一つの進路

有限和簡約を後回しにして、次の provider design へ進む手もある。

```text
decreasing dyadic envelope
dyadic tail upper envelope
```

ただ、わっちの見立てでは、次へ進む前に一度 constantBand の使いやすさを上げる方がよい。
なぜなら、decreasing provider でも dyadic tail provider でも、結局は有限和評価と coercion が顔を出すからじゃ。

constant case で小さく練習しておくのは賢い。

## 8. 賢狼の判定

わっちの判定はこうじゃ。

```text
DKMK-013G: 完了
次: optional finite-sum simplification theorem の shape review 推奨
方針: route theorem は触らない
```

よいぞ、ぬしよ。
`DyadicBandAnalyticEstimate` は、これで抽象契約から最小 provider を持つ実用的な入口になった。

次は、有限和の簡約という小さな岩場じゃ。
派手ではないが、ここを丁寧に越えると、後の dyadic tail envelope がずっと登りやすくなるぞい。
