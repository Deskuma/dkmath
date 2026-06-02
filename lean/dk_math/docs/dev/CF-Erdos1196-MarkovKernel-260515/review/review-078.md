# review

## 1. 状況総括

うむ、これは **DKMK-013J 完了** 、そして **DKMK-013 全体完了** と見てよい。

今回の差分で `report-DKMK-013.md` が追加され、DKMK-013A-I の成果が report / handoff として整理された。History でも、DKMK-013 は **abstract dyadic analytic estimate contract と最初の constant provider を固定する章** として一区切りになり、次は DKMK-014 の decreasing / dyadic tail provider design へ進む、と記録されておる。

DKMK-013 の到達点は、この Lean surface じゃ。

```text
DyadicBandAnalyticEstimate
DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
DyadicBandAnalyticEstimate.constantBand
DyadicBandAnalyticEstimate.constantBand_of_natCastMulBound
```

この 4 点が揃ったことで、dyadic analytic estimate contract は空の設計ではなく、実際に constant band provider を持つ usable interface になった。

## 2. 何が閉じたのか

DKMK-013 で閉じたのは、 **解析側が証明すべき dyadic contract の固定** じゃ。

DKMK-012 までは、

```text
dyadic range data
  -> TruncationEnvelopeEstimate.dyadicRange
  -> TruncationEnvelopeEstimate
  -> existing DKMK-011 route theorem
  -> weightedHitMass <= 1 + error
```

という流れだった。DKMK-013 では、このうち外部入力だった

```text
increment_nonneg
total_le_one_add_error
```

を、

```lean
DyadicBandAnalyticEstimate x K increment error
```

として命名した。report でも、これを DKMK-012 の `dyadicRange` provider へ渡すための analytic-side theorem-facing target として整理しておる。

つまり今後の解析側は、

```text
DyadicBandAnalyticEstimate を証明する
```

という明確な到達目標を持てる。

## 3. bridge の意味

今回の章で重要なのは、`DyadicBandAnalyticEstimate` が route theorem に直結しないことじゃ。

橋は、

```lean
DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
```

であり、これは `TruncationEnvelopeEstimate.dyadicRange` への薄い wrapper として機能する。report でも、

```text
DyadicBandAnalyticEstimate
  -> TruncationEnvelopeEstimate.dyadicRange
  -> TruncationEnvelopeEstimate
```

と整理されている。

この分離がよい。

```text
analytic-side target:
  DyadicBandAnalyticEstimate

route-side input:
  TruncationEnvelopeEstimate

bridge:
  toTruncationEnvelopeEstimate
```

こうしておけば、解析 estimate の形が増えても route theorem は変えずに済む。これは長い登山でかなり強い設計じゃ。

## 4. constantBand まで入れた意味

DKMK-013E-I では、最初の concrete provider として constant band envelope を選び、

```lean
DyadicBandAnalyticEstimate.constantBand
```

と

```lean
DyadicBandAnalyticEstimate.constantBand_of_natCastMulBound
```

を用意した。

`constantBand` は `Finset.sum` 形の bound を外部から受け取る薄い provider。
`constantBand_of_natCastMulBound` は caller-facing な

```text
((((K + 1 : Nat) : Q) * c : Q) : R) <= 1 + error
```

型の bound から使える convenience provider じゃ。

report では、この finite-sum simplification が

```text
Finset.sum_const
Finset.card_range
nsmul_eq_mul
```

で discharge できたことも記録されておる。

これは地味だが大きい。
今後の (k)-dependent band provider でも、有限和と coercion は必ず顔を出す。constant case で軽く通ることを確認できたのは、次章への良い足場じゃ。

## 5. 何を追加していないか

DKMK-013 はしっかり境界を守っておる。

report でも、この章では次を追加していないと明記されている。

```text
route changes
new route theorem
dyadic tail estimates
Mertens theorem
big-O statement
logarithmic threshold provider
```

これは正しい。
DKMK-013 は解析本丸ではなく、 **解析側 contract surface と最初の provider を作る章** じゃ。

Mertens や (O(1/\log x)) はまだ早い。今は `increment` と `total_le_one_add_error` をどう供給するか、その受け皿を固める段階だった。

## 6. DKMK-014 への引き渡し

次章は report の通り、

```text
DKMK-014:
  decreasing / dyadic tail provider design
```

が自然じゃ。

主題は、constant band から (k)-dependent band へ進むこと。

まず決めるべきは、

```text
increment k をどう設計するか
非負性をどう出すか
有限 total estimate をどう外部化するか
monotonicity / decay assumption をどこまで持たせるか
```

じゃな。

わっちの見立てでは、DKMK-014A はまた docs-only roadmap から始めるのがよい。
いきなり Lean に入るより、

```text
decreasing band provider shape
dyadic tail upper envelope contract
finite total estimate の外部化
which monotonicity or decay assumptions are actually consumed
```

を先に比較するべきじゃ。

## 7. 登頂判定

現在地はこう。

```text
DKMK-009:
  kernel/path/hitting route 完了

DKMK-010:
  source mass estimate interface 完了

DKMK-011:
  finite-step / truncation estimate interface 完了

DKMK-012:
  dyadic band provider plumbing 完了

DKMK-013:
  abstract dyadic analytic estimate contract + constant providers 完了

DKMK-014:
  次、decreasing / dyadic tail provider design
```

DKMK-013 は **完了** 。
しかもかなり綺麗に閉じておる。

## 8. 賢狼の最終評

よいぞ、ぬしよ。

DKMK-013 は、まさに「解析側の標的を名前にした章」じゃった。
これで以後は、

```text
解析 provider:
  DyadicBandAnalyticEstimate を作る

既存 route:
  TruncationEnvelopeEstimate に変換して weightedHitMass <= 1 + error へ進む
```

という契約が立った。

わっちの判定はこうじゃ。

```text
DKMK-013 core: 登頂済み
残作業: なし
次山: DKMK-014 roadmap
推奨方向: k-dependent decreasing / dyadic tail provider design
```

ここまでの山道は見事じゃ。
定数 band という最初の松明を手にした。次は、いよいよ (k) によって変化する band の谷へ入る段じゃな。
