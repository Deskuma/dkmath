# review

## 1. 状況総括

うむ、これは **DKMK-012E 完了** と見てよい。

今回の更新で、`roadmap-DKMK-012.md` に **Increment / hbound Design** が追加され、`dyadicRange` が外部入力として受け取る

```text id="cwk2bv"
increment : Nat -> Q
hbound    : ((sum increment : Q) : R) <= 1 + error
```

の解析的意味が docs 上で固定された。

つまり DKMK-012E は、`dyadicRange` の plumbing から、次の **analytic input design** へ橋を渡した段階じゃ。

## 2. 何が明確になったのか

今回の一番大きい収穫は、`increment k` の読みが固定されたことじゃ。

```text id="70ru9w"
increment k:
  第 k dyadic band の analytic upper envelope を表す
  externally supplied rational band weight
```

つまり、`increment k` はまだ具体式ではない。

$$
\log
$$

や Mertens 型評価や big-O から直接計算される値ではなく、今の段階では **外部から供給される第 (k) band の上界重み** として扱う。

これにより、Lean 側では

```text id="qbag9s"
band 構造を受け取る
非負性を確認する
総和上界を仮定として受け取る
TruncationEnvelopeEstimate を作る
```

だけに集中できる。

## 3. `hinc` と `hbound` の役割分担

今回の整理は、`hinc` と `hbound` の役割を綺麗に分けておる。

```text id="synh35"
hinc:
  ∀ k ∈ Finset.range (K + 1), 0 <= increment k
```

これは finite-step source mass construction のための非負性じゃ。
`finiteStepTailNatMassSpace` を作るには、各 step の increment が非負である必要がある。

一方で、

```text id="apazxr"
hbound:
  ((Finset.sum (Finset.range (K + 1)) increment : Q) : R) <=
    1 + error
```

これは analytic total estimate。
有限個の dyadic band envelope の総量が (1+error) を超えない、という仮定じゃ。

つまり、

```text id="zjhyjb"
hinc    : source mass を作るための条件
hbound  : analytic bound を渡すための条件
```

という分離が固定された。

これは後続でかなり効くぞい。

## 4. 設計評価

今回の判断は堅い。

特によいのは、まだ次を入れていないことじゃ。

```text id="tu7npy"
increment k の具体式
Mertens estimate
big-O statement
logarithmic threshold provider
dyadic-specific hitting route theorem
```

この抑制は重要じゃな。

`dyadicRange` は provider layer の部品であり、解析評価そのものではない。
ここで Mertens や (O(1/\log x)) を混ぜると、せっかく DKMK-009 から積み上げてきた層分離が崩れる。

今回の DKMK-012E は、

```text id="c1n2ib"
provider plumbing:
  dyadicRange までで完了

analytic input:
  increment / hbound を外部供給として設計
```

という境界をはっきりさせた。これは良い。

## 5. candidate source の整理

今回、将来の `increment` / `hbound` の供給元として、次が分けられているのもよい。

```text id="x9bagq"
externally supplied band weights
dyadic tail upper envelope
later logarithmic refinement
concrete number-theoretic estimate
```

この分類は、後続の DKMK-013 以降を考える上で大事じゃ。

わっちの見立てでは、自然な進行はこうじゃな。

```text id="8cnq0z"
1. externally supplied band weights
   まずは抽象 provider として扱う

2. dyadic tail upper envelope
   dyadic 分割に沿った具体的上界を設計する

3. logarithmic refinement
   dyadic では粗い部分を log band へ移す

4. number-theoretic estimate
   Mertens / partial summation / explicit estimate と接続する
```

この順なら Lean の重さを段階的に制御できる。

## 6. DKMK-012 の現在地

ここまでで DKMK-012 はかなり一区切りに近い。

```text id="gmvb6f"
DKMK-012A:
  provider design roadmap 完了

DKMK-012B:
  dyadic provider shape docs 完了

DKMK-012C:
  TruncationEnvelopeEstimate.dyadicRange 実装完了

DKMK-012D:
  dyadicRange usage summary 完了

DKMK-012E:
  increment / hbound analytic input design 完了
```

つまり DKMK-012 は、

```text id="gwgcvq"
dyadic band provider の器
```

をほぼ作り終えた章になった。

## 7. 次の一手

次は二択じゃ。

```text id="bivlak"
1. DKMK-012F report / handoff
2. toy analytic provider を追加
```

わっちのおすすめは、 **DKMK-012F report / handoff** じゃ。

理由は、DKMK-012 は provider design の章として、すでに十分に閉じておるからじゃ。

* `dyadicRange` の data shape を決めた
* Lean provider を追加した
* usage summary を書いた
* `increment` / `hbound` の解析的意味を固定した

ここまで来たら、無理に toy analytic provider を追加しなくてもよい。
toy provider は DKMK-011E の `singleWindow` で既に存在している。DKMK-012 でさらに toy を増やすより、次章で **dyadic tail upper envelope** に進む方が筋がよい。

## 8. 次章候補

自然には、次はこうじゃな。

```text id="mswcn0"
DKMK-013:
  dyadic tail upper envelope design
```

主題は、

```text id="0u3sra"
increment k をどう選ぶか
hbound をどう出すか
```

になる。

ただし、まだ Mertens theorem へ直行せず、

```text id="qhvjcp"
abstract dyadic analytic estimate contract
```

を一段挟むのが安全じゃろう。

たとえば次章では、

```lean id="y4snnw"
structure DyadicBandAnalyticEstimate ...
```

のような contract を作り、それが `TruncationEnvelopeEstimate.dyadicRange` に流れる、という構図が候補になる。

## 9. 賢狼の判定

よいぞ、ぬしよ。

DKMK-012E は、地味だが重要な境界固定じゃ。

```text id="j52q19"
dyadicRange:
  band の器を作る

increment / hbound:
  解析側が供給する
```

この分離が明確になったことで、次にどこへ進むべきかが見える。

わっちの判定はこうじゃ。

```text id="rfq5p7"
DKMK-012E: 完了
DKMK-012 core: 完了に近い
次: report / handoff 推奨
その次: dyadic tail upper envelope design
```

この山はもう閉じてよい高さまで来ておる。焦って解析霧へ飛び込まず、ここで一度 report にして、次の DKMK-013 で `increment` の中身へ入るのが美しいと思うぞい。
