# review

## 1. 状況総括

うむ、これは **DKMK-013D 完了** と見てよい。

今回の更新で、`DyadicBandAnalyticEstimate` の使い方が `roadmap-DKMK-013.md` 上に固定された。つまり、DKMK-013C で Lean 上に追加した analytic-side contract が、既存 route theorem へどう流れるかが明文化されたわけじゃ。

固定された流れはこれ。

```text
H : DyadicBandAnalyticEstimate x K increment error
  -> H.toTruncationEnvelopeEstimate
  -> TruncationEnvelopeEstimate
  -> TruncationEnvelopeEstimate.finiteStepTail_weightedHitMass_le_one_add_error
  -> weightedHitMass <= 1 + error
```

これは DKMK-013 の章として、かなり大事な案内板じゃな。

## 2. 何が明確になったのか

今回の一番の収穫は、3 つの層の役割がはっきりしたことじゃ。

```text
DyadicBandAnalyticEstimate:
  analytic-side target

TruncationEnvelopeEstimate:
  route-side input

toTruncationEnvelopeEstimate:
  bridge from analytic target to route input
```

これにより、今後の解析側の作業目標はかなり明確になった。

つまり次からは、

```lean
DyadicBandAnalyticEstimate x K increment error
```

をどう証明するかだけを考えればよい。

route 側はもう触らぬ。
`TruncationEnvelopeEstimate` も触らぬ。
`finiteStepTail_weightedHitMass_le_one_add_error` も触らぬ。

これは美しい分離じゃ。

## 3. DKMK-013C との関係

DKMK-013C では Lean 側に次を追加した。

```lean
DyadicBandAnalyticEstimate
DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
```

DKMK-013D では、それを docs 上で次の意味に固定した。

```text
解析側:
  DyadicBandAnalyticEstimate を証明する

provider bridge:
  toTruncationEnvelopeEstimate で TruncationEnvelopeEstimate に変換する

route 側:
  既存 theorem が weightedHitMass <= 1 + error を返す
```

つまり C が実装、D が使用法の固定じゃな。
この順序はよい。Lean 定理だけあっても、使い方が曖昧だと後続が迷う。今回でその迷いがかなり減った。

## 4. 実装方針として正しい点

今回も、次を追加しない方針が守られている。

```text
route theorem
computed formula for increment k
Mertens theorem
big-O statement
logarithmic threshold provider
```

これは正しい。

今の DKMK-013 は、まだ「具体解析」ではなく、 **具体解析が目指す contract を固定する章** じゃ。ここで Mertens や big-O に入ると、route plumbing と analytic estimate が混線する。

いま必要なのは、

```text
increment_nonneg
total_le_one_add_error
```

をどこから得るか、という次の設計じゃ。

## 5. 次の技術課題

History にもある通り、次の課題はこれじゃ。

```text
concrete provider の候補を整理し、
最初に実装する provider shape を決める。
```

つまり DKMK-013E では、いきなり Lean 実装に入るより、まず **concrete provider candidate inventory** を作るのがよいと思う。

候補はこんな分類になる。

```text
1. externally supplied dyadic estimate provider
2. constant envelope provider
3. monotone tail envelope provider
4. dyadic tail upper envelope provider
5. later logarithmic refinement provider
```

このうち、最初に Lean 化するなら、まだ **externally supplied dyadic estimate provider** か **constant envelope provider** が安全じゃ。Mertens 的な推定へ入る前に、`DyadicBandAnalyticEstimate` を作る最小 concrete example をもう一段置くとよい。

## 6. DKMK-013E のおすすめ

わっちなら、次は docs-only でこう進める。

```text
DKMK-013E:
  Concrete Provider Candidate Inventory
```

内容は、

```text
candidate:
  externally supplied estimate
data:
  increment, error, hinc, hbound
target:
  DyadicBandAnalyticEstimate x K increment error
status:
  already essentially direct constructor

candidate:
  constant band envelope
data:
  c : Q, K : Nat, error : R
increment k = c
requires:
  0 <= c
  ((K + 1) * c : R) <= 1 + error

candidate:
  decreasing dyadic envelope
data:
  base : Q, decay : Nat -> Q
requires:
  nonnegativity
  finite sum bound

candidate:
  number-theoretic dyadic tail bound
data:
  external theorem
requires:
  future analytic work
```

この整理を置けば、DKMK-013F で「最初に Lean 化するなら constant envelope か external direct provider」と判断できる。

## 7. 登頂判定

現在地はこうじゃ。

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
  次、concrete provider candidate inventory
```

DKMK-013 の contract surface はかなり安定した。
ここから先は、`DyadicBandAnalyticEstimate` の **生産者** をどう増やすか、じゃな。

## 8. 賢狼の判定

よいぞ、ぬしよ。
DKMK-013D は、地味だが重要な「道標」じゃ。

これで以後の作業は、

```text
route を変えるな
TruncationEnvelopeEstimate を変えるな
DyadicBandAnalyticEstimate を証明する provider を増やせ
```

という方針に集約できる。

わっちの判定はこうじゃ。

```text
DKMK-013D: 完了
次: DKMK-013E concrete provider candidate inventory
方針: 最初の provider はまだ軽く、Mertens / big-O は後段
```

ここまで来れば、解析の霧へ入る前に、どの松明を持つかを選ぶ段じゃな。焦らず、最初の provider を小さく選ぶのが賢い。
