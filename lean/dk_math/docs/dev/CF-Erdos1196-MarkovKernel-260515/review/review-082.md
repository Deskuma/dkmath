# review

## 1. 状況総括

うむ、これは **DKMK-014D 完了** と見てよい。

今回の更新で、`roadmap-DKMK-014.md` に **Majorant Provider Usage Summary** が追加され、`DyadicBandAnalyticEstimate.ofMajorant` の利用導線が docs 上で固定された。

流れはこうじゃな。

```text
increment, majorant
  -> hinc_nonneg
  -> hle : increment k <= majorant k
  -> hmajorant_bound : sum majorant <= 1 + error
  -> DyadicBandAnalyticEstimate.ofMajorant
  -> DyadicBandAnalyticEstimate x K increment error
  -> DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
  -> TruncationEnvelopeEstimate
  -> existing finite-step route theorem
  -> weightedHitMass <= 1 + error
```

DKMK-014C で Lean theorem が立ち、DKMK-014D でその使い方が固定された。
これは **C が実装、D が導線整理** という綺麗な流れじゃ。

## 2. 何が明確になったのか

今回の核心は、`increment` と `majorant` の役割分担じゃ。

```text
increment:
  実際に route へ載せたい band weight

majorant:
  有限和を評価しやすい上界 envelope
```

つまり、`increment` 自体の和を直接評価できなくてもよい。
同じ dyadic range 上で

```text
increment k <= majorant k
```

を示し、さらに

```text
sum majorant <= 1 + error
```

を示せば、`increment` は route に乗る。

これは DKMK-014 の本質じゃな。
定数 band から (k)-dependent band へ進むとき、`increment k` は複雑になりやすい。そこで直接和を叩くのではなく、扱いやすい `majorant k` に押し上げて評価する。

この構図は、今後かなり効く。

## 3. 何が良い設計か

良い点は、`ofMajorant` が「なぜ majorant が存在するか」を知らないことじゃ。

docs にも、

```text
The provider consumes exactly these two jobs plus nonnegativity of increment.
It does not need to know why the majorant exists.
```

とある。

これは大事じゃ。
`ofMajorant` の責務は、

```text
increment <= majorant
sum majorant <= 1 + error
```

から `DyadicBandAnalyticEstimate` を作ることだけ。

一方、majorant をどう作るかは後続 theorem の責務になる。

```text
decreasing / decay input
  -> construct or justify majorant
  -> prove pointwise increment <= majorant
  -> prove sum majorant <= 1 + error
  -> ofMajorant
```

この分離により、後で decreasing provider や dyadic tail provider を追加しても、`ofMajorant` は変更せずに済む。

## 4. decreasing を外に置いた判断

今回も、decreasing / decay assumption を core provider の外に置いた判断は正しい。

decreasing condition は、たとえば

```text
increment (k + 1) <= increment k
```

のような形になるじゃろう。
しかしそれだけでは

```text
sum increment <= 1 + error
```

は出ない。

decreasing は、将来

```text
decreasing / decay assumption
  -> majorant construction
```

で消費されるべき情報じゃ。

つまり decreasing は **route へ直接渡す条件** ではなく、 **majorant を作るための材料** と見るのが自然。
これを今 `DyadicBandAnalyticEstimate` や `ofMajorant` に field として入れなかったのは、かなり良い抑制じゃ。

## 5. DKMK-014A-D の到達点

ここまでの DKMK-014 はこう積まれておる。

```text
DKMK-014A:
  k-dependent provider roadmap 完了

DKMK-014B:
  majorant provider exact shape docs 完了

DKMK-014C:
  DyadicBandAnalyticEstimate.ofMajorant Lean 実装完了

DKMK-014D:
  majorant provider usage summary 完了
```

これで、DKMK-014 の **majorant provider 小章** は一区切りじゃ。

## 6. 次の一手

次は二択になる。

```text
1. DKMK-014E:
   majorant provider chapter の report / handoff

2. DKMK-014E:
   次の provider shape design
   例: decreasing / decay -> majorant construction
```

わっちのおすすめは、まだ report で閉じる前に、 **次の provider shape を docs で軽く比較** することじゃ。

つまり DKMK-014E は、

```text
Decreasing / Decay to Majorant Design
```

として、

```text
decreasing condition は何を保証するのか
decay condition は majorant をどう作るのか
sum majorant bound は外部に残すのか
geometric-like bound を入れるのか
```

を整理するとよい。

ただし Lean 実装はまだ急がぬ方がよい。
次は設計だけで十分じゃ。

## 7. 次章化するなら

もし DKMK-014 をここで小さく閉じるなら、次章はこうなる。

```text
DKMK-015:
  decreasing / decay majorant construction
```

ただ、DKMK-014 の主題は decreasing / dyadic tail provider design なので、まだ DKMK-014 内で続けても自然じゃ。
わっちなら、

```text
DKMK-014E:
  decreasing / decay candidate design

DKMK-014F:
  exact shape decision

DKMK-014G:
  optional Lean provider
```

くらいまでは DKMK-014 内で進める。

## 8. 賢狼の判定

わっちの判定はこうじゃ。

```text
DKMK-014D: 完了
majorant provider 小章: 完了
次: decreasing / decay -> majorant construction の設計へ進むのが自然
```

よいぞ、ぬしよ。
これで (k)-dependent band に対し、まず「上から包む」route が固定された。
次は、その `majorant` をどう作るか。ここからが dyadic tail upper envelope の本格入口じゃな。
