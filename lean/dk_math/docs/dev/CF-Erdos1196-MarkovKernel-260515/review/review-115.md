# review

うむ、DKMK-017 新体制、これは **正しい切り替え** じゃ。
これまでの DKMK-015/016 は API 境界を固める章だったので実況と文書検討が多くても意味はあった。だが DKMK-017 は、もう **Analytic Input Source** へ進む章。ここからは「小さな wrapper ごとに生中継」ではなく、 **実装 bundle 単位で結果を出す** 方がよい。

## 1. DKMK-017-00 の方針は妥当

今回追加された `roadmap-DKMK-017.md` は、まず作業粒度そのものを変える宣言になっておる。

新しい基本単位は、

```text
design decision
  -> Lean implementation attempts
  -> self-diagnosis from Lean errors
  -> verification
  -> concise report to reviewer
```

じゃな。これはとてもよい。
reviewer に毎回「この薄い constructor を足してよいか」「この wrapper 名でよいか」と聞くのではなく、局所的に決められるものは実装・検証まで走らせてから報告する方針になっている。

## 2. 相談すべき場面の切り分けも良い

roadmap では、事前 review が必要な場面を route-shape の変更に限定しておる。

たとえば、

```text
new structure を追加するか
assumption を API 境界のどちらへ置くか
Rat-side / Real-side surface を選ぶか
downstream wrapper を増やすか
analytic obligation を強めるか弱めるか
chapter scope を変えるか
```

こういう判断は相談に値する。
逆に、薄い constructor、既存 theorem の合成 wrapper、roadmap 済み helper lemma、Lean error による局所修正は、止まらず進める。これはかなり健全じゃ。

## 3. 最初の bundle target も良い

DKMK-017 の章目標は、DKMK-016 で残った三つの analytic input を扱うことじゃ。

```text
A. increment 0 <= B.base
B. increment (k + 1) <= B.ratio * increment k
C. (B.base : Real) * (1 / (1 - (B.ratio : Real))) <= 1 + B.error
```

これらは `DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSource` が消費する入力じゃな。

最初の候補として、

```lean
structure FirstBandDecayBudgetSource
    (K : Nat)
    (increment : Nat -> Rat) where
  budget : GeometricBudgetSource
  hinc_nonneg :
    forall k in Finset.range (K + 1), 0 <= increment k
  hbase0 :
    increment 0 <= budget.base
  hdecay :
    forall k in Finset.range K,
      increment (k + 1) <= budget.ratio * increment k
```

を実験対象にするのは筋がよい。
ただし roadmap 自身も認めている通り、これは DKMK-016 で避けた combined source package を再導入する形でもある。だから実験結果として、

```text
採用する
捨てて既存の四入力のままにする
A/B だけ package する
C 周辺 helper を先に作る
```

のどれがよいかを Lean と ergonomics で判断する、という方針がよい。

## 4. 「実況中継も意味はある。が、いまはその時ではない。」

実況中継は楽しい。わっちも、りんご酒片手に「今まさに Lean が通るか！？」と見守るのは嫌いではない。
しかし、今はまだ「Erdős #1196 が Lean で閉じる瞬間」ではない。ここは基盤整備と analytic input source の探索段階じゃ。

だから DKMK-017 では、

```text
細かい相談を減らす
docs-only を連発しない
Lean 実装と検証を bundle で進める
報告は結果中心にする
```

でよい。

わっちも今後この粒度に合わせる。
つまり、途中の小さな揺れを逐一大げさに語るより、

```text
何を試したか
何が通ったか
何が詰まったか
次に何を変えるべきか
```

を短く鋭く返す。

## 5. 現時点の評価

DKMK-017-00 は、実装ではなく **運用切り替えのコミット** としてよくできておる。

* 章題は `Analytic Input Source`
* docs-heavy 章から bundle-driven 章へ切り替え
* review が必要な場面を明文化
* 最初の bundle target を設定
* Mertens / big-O / threshold / rounding はまだ non-goal

ここまでで十分じゃ。

次はもう、長い review ではなく、最初の implementation bundle に進むべきじゃな。

## 6. 次の実作業方針

次の報告で見たいのは、この形じゃ。

```text
DKMK-017-A implementation bundle

試した target:
  FirstBandDecayBudgetSource か、その代替

結果:
  採用 / 棄却 / 縮小 / defer

Lean:
  追加 theorem / structure
  build 結果
  詰まった点

判断:
  次に進む route
```

これでよい。
詳しい実況は要らぬ。結果と判断があれば、わっちは十分に伴走できる。

よし、D.。新体制で行こう。
ここからは麦畑の畝を一本ずつ眺めるのでなく、刈り取った束を見て「収穫になったか」を判定する進め方じゃ。
