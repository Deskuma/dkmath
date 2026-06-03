# review

## 1. 状況総括

うむ、これは **DKMK-014E 完了** と見てよい。

今回の更新で、`roadmap-DKMK-014.md` に **Decreasing / Decay to Majorant Design** が追加され、decreasing / decay 情報を `DyadicBandAnalyticEstimate` の core field に直接入れず、 **majorant construction 側の材料として扱う** 方針が固定された。History でも、decreasing だけでは `sum increment <= 1 + error` を出せないため core provider field にしない、と明記されておる。

つまり DKMK-014E は、`ofMajorant` の次に進む前の **境界整理** として閉じた。

## 2. 何が決まったのか

今回の中心判断はこれじゃ。

```text
decreasing / decay:
  majorant を作る、または正当化する材料

majorant:
  有限和を評価する対象

ofMajorant:
  pointwise majorization と total majorant bound から
  DyadicBandAnalyticEstimate を作る bridge
```

これはかなり良い。

`DyadicBandAnalyticEstimate` の core は、最終的に

```text
increment_nonneg
total_le_one_add_error
```

だけを欲しておる。
だから decreasing や decay は、それ自体を field として抱え込むより、

```text
decreasing / decay assumptions
  -> hle : increment k <= majorant k
  -> hmajorant_bound : sum majorant <= 1 + error
  -> ofMajorant
```

という **前段 theorem** に閉じ込めるのが筋じゃ。

## 3. Candidate E1 の評価

`decreasing only` を退けた判断は正しい。

```text
increment (k + 1) <= increment k
0 <= increment k
```

だけでは、列の形状は分かる。
しかし、

```text
sum increment <= 1 + error
```

は出ない。

極端に言えば、単調減少していても初項が大きければ総和は大きい。
ゆえに decreasing は **形状情報** であって、total estimate そのものではない。

ここを core provider に入れない判断は、Lean API としても数学としても健全じゃ。

## 4. Candidate E2 の評価

`decay ratio with external total bound` は、かなり自然な中間案じゃ。

```text
0 <= increment k
increment (k + 1) <= r * increment k
increment k <= majorant k
sum majorant <= 1 + error
```

この場合、decay condition は `majorant` を作る根拠になる。
ただし、最終的な finite total estimate は依然として

```text
sum majorant <= 1 + error
```

として必要になる。

つまりこの候補も、最終的には `ofMajorant` に流れる。
この流れを固定できたのは DKMK-014E の大きな収穫じゃな。

## 5. Candidate E3 が本命

今回、preferred next Lean-facing shape を **explicit majorant construction theorem** に寄せたのは良い。

つまり次の段階では、`DyadicBandAnalyticEstimate` 自体を増やすのではなく、

```text
decreasing / decay assumptions
  -> construct or justify majorant
  -> call DyadicBandAnalyticEstimate.ofMajorant
```

という theorem を設計する。

この方針なら、今後 `majorant` の作り方が複数出ても、core route は変わらぬ。

```text
constant majorant
geometric majorant
dyadic tail majorant
logarithmic refined majorant
```

どれも最終的には `ofMajorant` へ流せる。
これは拡張性が高い。

## 6. DKMK-014 の現在地

ここまでで DKMK-014 は、かなり綺麗に進んでおる。

```text
DKMK-014A:
  k-dependent provider roadmap 完了

DKMK-014B:
  majorant provider exact shape docs 完了

DKMK-014C:
  DyadicBandAnalyticEstimate.ofMajorant 実装完了

DKMK-014D:
  majorant provider usage summary 完了

DKMK-014E:
  decreasing / decay to majorant design 完了

DKMK-014F:
  次、explicit majorant construction theorem exact shape
```

つまり、majorant provider 小章は実装・使用法・次段設計まで閉じた。
次は本当に「majorant をどう作るか」へ入る段じゃ。

## 7. DKMK-014F のおすすめ

次は docs-only で、 **explicit majorant construction theorem の exact shape** を決めるのがよい。

ただし、最初から幾何級数まで証明するのは重いかもしれぬ。
まずは、`increment` と `majorant` を別々に受けるのではなく、decay 由来の `majorant` を外から与え、その正当化をまとめる形が安全じゃ。

候補は例えばこう。

```lean
theorem DyadicBandAnalyticEstimate.ofMajorantBoundedBy
    (x K : ℕ)
    (increment majorant : ℕ → ℚ)
    (hinc_nonneg :
      ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k)
    (hdecay_or_bound :
      ∀ k ∈ Finset.range (K + 1), increment k ≤ majorant k)
    {error : ℝ}
    (hmajorant_bound :
      ((Finset.sum (Finset.range (K + 1)) majorant : ℚ) : ℝ) ≤
        1 + error) :
    DyadicBandAnalyticEstimate x K increment error
```

ただ、これは既に `ofMajorant` と同じなので、新 theorem としては弱い。

より意味のある次形は、 **majorant を具体的に構成する側** じゃ。

例えば、

```text
increment k <= base * ratio^k
sum (base * ratio^k) <= 1 + error
  -> DyadicBandAnalyticEstimate
```

のような shape じゃな。

Lean theorem 名候補なら、

```lean
DyadicBandAnalyticEstimate.ofGeometricMajorant
```

または、まだ幾何級数簡約をしないなら、

```lean
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant
```

が候補になる。

## 8. 注意点

ここで急いで入れない方がよいものは、今回の non-goals と同じじゃ。

```text
geometric-series lemmas
Mertens / big-O
logarithmic thresholds
real-to-Nat rounding
route theorem changes
```

特に幾何級数補題は、入れるなら別フェーズがよい。
まずは「幾何型 majorant をどう statement にするか」を決める。
そのあと、必要なら sum simplification theorem を追加する。

DKMK-013 の `constantBand` と同じ流れじゃな。まず外部 sum bound を受ける。その後、caller-facing な簡約 theorem を足す。あの登り方がここでも使える。

## 9. 賢狼の判定

わっちの判定はこうじゃ。

```text
DKMK-014E: 完了
次: DKMK-014F
推奨:
  explicit majorant construction theorem の exact shape review
方針:
  core provider は増やさない
  decreasing / decay は majorant 構成側で消費する
```

よいぞ、ぬしよ。
`ofMajorant` という手すりを置き、今回で decreasing / decay をその手すりにどう接続するかも見えた。次は、いよいよ `majorant` を具体的に作る小さな橋じゃ。焦らず、まず theorem shape を決めるのが賢い登り方じゃよ。
