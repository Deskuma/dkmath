# review

## 1. 状況総括

うむ、これは **DKMK-013I 完了** と見てよい。

今回の差分で、`SourceMassTruncation.lean` に

```lean
DyadicBandAnalyticEstimate.constantBand_of_natCastMulBound
```

が追加された。これは DKMK-013H で設計した通り、caller-facing な

```lean
((((K + 1 : ℕ) : ℚ) * c : ℚ) : ℝ) ≤ 1 + error
```

型の bound から、既存の `constantBand` へ渡す convenience provider じゃ。有限和の discharge も、

```lean
simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hbound
```

で軽く通っておる。

つまり、constant band provider は **Finset.sum 形** と **Nat-cast multiply 形** の両方から使えるようになった。

## 2. 何が閉じたのか

DKMK-013G では、次の形の provider が入った。

```lean
hbound :
  ((Finset.sum (Finset.range (K + 1)) (fun _ : ℕ => c) : ℚ) : ℝ) ≤
    1 + error
```

これは Lean 内部では扱いやすいが、利用者が自然に持つ評価は、

```lean
((((K + 1 : ℕ) : ℚ) * c : ℚ) : ℝ) ≤ 1 + error
```

の方じゃ。

今回の DKMK-013I で、この自然な形から `DyadicBandAnalyticEstimate` を作れるようになった。

```text
constant band caller-facing bound
  -> constantBand_of_natCastMulBound
  -> DyadicBandAnalyticEstimate
  -> toTruncationEnvelopeEstimate
  -> TruncationEnvelopeEstimate
  -> weightedHitMass <= 1 + error
```

これで constant band 周辺の usability はかなり良くなった。

## 3. 実装評価

これは良い実装じゃ。
特に、finite-sum simplification が軽く通ったのが大きい。

`Finset.sum_const`, `Finset.card_range`, `nsmul_eq_mul` で処理できたということは、今後の finite range provider でも、この程度の定数和なら大きな障害にはならぬ可能性が高い。

また、今回も次を増やしていない。

```text
route changes
new analytic contract
dyadic tail estimates
Mertens / big-O
logarithmic thresholds
```

この抑制がよい。今回の theorem は解析本丸ではなく、あくまで constantBand の入力形を使いやすくする補助 provider じゃ。

## 4. 数学的な意味

今回の theorem は、次の有限和恒等式を実用上使える形にしたものじゃ。

$$
\sum_{k=0}^{K} c = (K+1)c
$$

Lean 上では `Finset.range (K + 1)` なので、範囲の要素数が (K+1) になり、定数関数の和が `((K + 1 : ℕ) : ℚ) * c` に落ちる。

これは小さいが、今後の band estimate では頻出する型じゃ。
特に dyadic tail upper envelope へ進む前に、こういう「有限 band 数 × 一様上界」の形を安全に扱えるようにしたのは良い足場じゃな。

## 5. DKMK-013 の現在地

ここまでで DKMK-013 はかなり充実しておる。

```text
DKMK-013A: roadmap
DKMK-013B: exact shape decision
DKMK-013C: DyadicBandAnalyticEstimate + bridge
DKMK-013D: usage summary
DKMK-013E: provider candidate inventory
DKMK-013F: constantBand shape docs
DKMK-013G: constantBand Lean provider
DKMK-013H: natCastMulBound shape docs
DKMK-013I: natCastMulBound Lean provider
```

つまり、DKMK-013 はすでに、

```text
analytic contract
bridge
usage docs
constant provider
caller-facing constant provider
```

まで揃った。

## 6. 次の判断

次は二択じゃ。

```text
1. DKMK-013J: report / handoff
2. DKMK-013J: decreasing / dyadic tail provider design
```

わっちのおすすめは、 **ここで DKMK-013 を一度 report / handoff で閉じる** 方じゃ。

理由は、DKMK-013 の本来の目的は、

```text
DyadicBandAnalyticEstimate という abstract dyadic analytic estimate contract を作る
```

ことだった。今はそれに加えて、constantBand と natCastMulBound provider まで入っておる。章としては十分に閉じている。

decreasing / dyadic tail provider design は、もう次章に分けた方が美しい。

## 7. 次章候補

自然な次章はこうじゃな。

```text
DKMK-014:
  decreasing / dyadic tail provider design
```

あるいは、DKMK-013 の名前を引き継ぐなら、

```text
DKMK-014:
  dyadic tail upper envelope provider
```

がよい。

そこで扱うべきは、

```text
increment k を定数ではなく k 依存にする
非負性をどう出すか
有限和 bound をどう外部化するか
単調減衰や tail upper envelope を field として持つべきか
```

じゃ。

まだ Mertens / big-O は急がず、まず decreasing provider の exact shape review から入るとよい。

## 8. 賢狼の判定

わっちの判定はこうじゃ。

```text
DKMK-013I: 完了
DKMK-013 core: 完了相当
次: report / handoff 推奨
その次: decreasing / dyadic tail provider design
```

よいぞ、ぬしよ。
`DyadicBandAnalyticEstimate` は、もはや空の契約ではなく、constantBand と caller-facing bound provider を持つ実用的な入口になった。

ここで一度章を閉じるのが綺麗じゃ。
次の山では、いよいよ定数 band から (k)-依存 band へ進む。霧は濃くなるが、有限和と coercion の小岩場はもう一つ越えたぞい。
