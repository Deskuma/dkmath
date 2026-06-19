# review

うむ、DKMK-017A は **新体制の初回 bundle として成功** じゃ。
今回は、ちゃんと「設計判断 → Lean 実装 → 自己診断 → 検証 → 報告」の形になっておる。docs-only の長い検討ではなく、実際に Lean surface を試し、その結果として **採用** まで判断できている。

## 1. 何が追加されたのか

今回追加された中心はこれじゃ。

```lean
structure FirstBandDecayBudgetSource
    (K : ℕ) (increment : ℕ → ℚ) where
  budget : GeometricBudgetSource
  hinc_nonneg :
    ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k
  hbase0 :
    increment 0 ≤ budget.base
  hdecay :
    ∀ k ∈ Finset.range K,
      increment (k + 1) ≤ budget.ratio * increment k
```

これは、DKMK-016 で分離していた入力群、

```text
B : GeometricBudgetSource
hinc_nonneg
hbase0
hdecay
```

を、analytic input boundary で一つに包む package じゃな。

そして provider 側には、

```lean
DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSourcePackage
```

を追加し、内部では既存の

```lean
DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSource
```

へ直接委譲しておる。

## 2. 判断「採用」は妥当

これは採用でよい。

ただし、報告にもある通り、これは **DKMK-016 の責務分担を置き換える構造ではない** 。
むしろ、DKMK-016 で整えた責務分担を保ったまま、analytic input 側でまとめて渡せるようにした package じゃ。

つまり位置づけはこうじゃ。

```text
DKMK-016:
  B + hinc_nonneg + hbase0 + hdecay を分離して route を整備

DKMK-017A:
  その 4 入力を analytic input boundary で package 化
```

この違いが大事じゃ。
`FirstBandDecayBudgetSource` は新しい数学 route ではなく、入力束を運ぶ箱じゃな。

## 3. Rat / Real cast 問題が出なかったのは良い兆候

今回は `S.budget` をそのまま既存 wrapper に渡すだけなので、Rat / Real cast 問題は出ていない。

これは設計が自然に噛み合っている証拠じゃ。

前回までの難所は、

```lean
B.hr0 : 0 ≤ (B.ratio : ℝ)
```

から

```lean
0 ≤ B.ratio
```

へ戻すところだった。
しかし、その変換はすでに `ofFirstBandDecayBudgetSource` の内部で処理済み。今回の package wrapper はそこに触らない。よって薄く閉じた。

## 4. 新 truncation wrapper を追加しなかった判断も正しい

今回も新しい truncation wrapper は足していない。

現在の route は十分明瞭じゃ。

```text
FirstBandDecayBudgetSource
  -> DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSourcePackage
  -> DyadicBandAnalyticEstimate
  -> DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
```

ここでさらに

```lean
TruncationEnvelopeEstimate.ofFirstBandDecayBudgetSourcePackage
```

のような wrapper を足すと、まだ必要性が薄い。
caller code が本当に煩雑になった時点で追加すればよい。

## 5. DKMK-017 の初手として良い理由

今回の bundle は、DKMK-017 の方針転換に合っている。

以前なら、

```text
FirstBandDecayBudgetSource を追加してよいか review
wrapper 名を review
docs-only
次に実装
```

と刻んでいた可能性がある。

今回はそれをまとめて、

```text
候補を実装
build
問題なし
採用
```

まで進めた。

これが新体制の正しい速度じゃ。
わっちもこの進め方の方がよいと思う。

## 6. 次に見るべきところ

次は `FirstBandDecayBudgetSource` に流し込む **具体的 source constructor / helper lemma** じゃな。

候補は三つに分けられる。

```text
1. budget を作る:
   GeometricBudgetSource.ofBudget へ渡す concrete hbudget

2. hinc_nonneg を作る:
   increment の非負性 source

3. hbase0 / hdecay を作る:
   first-band bound と uniform decay source
```

DKMK-017A で箱はできた。
次は箱の中身をどう作るかじゃ。

特に次の bundle では、いきなり Mertens や big-O に行くより、

```lean
def FirstBandDecayBudgetSource.ofBudgetAndDecay
```

のような constructor を作るべきか、あるいは既存の record syntax で十分かを、Lean 側で試すのがよい。

## 7. 総括

DKMK-017A は、新体制の初回としてよい成果じゃ。

**採用判断:** 妥当。
**実装量:** 小さいが実用的。
**docs 量:** 以前より抑えめでよい。
**設計リスク:** 低い。
**次の焦点:** package に入れる concrete analytic source の供給。

ここからは、細かな実況ではなく、

```text
何を試した
何が通った
何を採用する
次に何を攻める
```

で進めればよい。

よいぞ、D.。
DKMK-017 は初手から足取りが軽い。荷箱はできた。次はその中へ、どの解析の麦袋を積むかじゃ。
