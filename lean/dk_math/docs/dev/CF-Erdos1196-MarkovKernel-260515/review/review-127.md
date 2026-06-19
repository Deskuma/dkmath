# review

うむ、DKMK-017L は **綺麗な章閉じ** じゃ。
ここで `report-DKMK-017.md` を追加し、DKMK-017A-K を **route-validation complete** として畳んだ判断は正しい。今回の report では、`geometricIncrement` が最終解析 source ではない一方で、concrete `Nat -> Rat` source から finite-step tail mass、さらに quotient-path の `weightedHitMass A <= 1 + error` まで transport path が生きていることを整理しておる。

## 1. DKMK-017 は何を達成したか

DKMK-017 の成果は、次の搬送路を Lean で確認したことじゃ。

```text
concrete Nat -> Rat increment
  -> truncation envelope
  -> finite-step tail mass
  -> quotient-path hitting bound
```

具体的には、

```text
geometricIncrement
  -> canonical first-band budget
  -> TruncationEnvelopeEstimate
  -> finiteStepTailNatMassSpace
  -> quotient-path weightedHitMass bound
```

まで通った。これは report にも DKMK-017A-K の結果として明記されている。

ここで重要なのは、`geometricIncrement` 自体が最終目的ではないこと。
役目は **route-validation source** じゃ。つまり「本物の analytic source が来たとき、このルートで運べるか」を確認する試験用 source じゃな。

## 2. 章閉じ判断は妥当

ここでさらに convenience wrapper を足さずに止めたのは良い。

すでに DKMK-017K で、

```text
base = 1 - ratio
0 <= ratio
(ratio : Real) < 1
0 <= error
PrimitiveOn A
  -> weightedHitMass A <= 1 + error
```

まで到達している。
これ以上 `geometricIncrement` 用 wrapper を増やしても、得られるのは主に見た目の短縮であって、数学的・経路的な新事実は少ない。

なので、今回の

```text
Stop adding convenience wrappers for the geometric test source
```

という判断は正しい。

## 3. DKMK-017 の位置づけ

DKMK-017 は、最終解析章ではなく、 **搬送路の検証章** じゃ。

DKMK-015/016 で作った API plumbing が、本当に concrete `Nat -> Rat` source を受け取り、既存 finite-step route まで流せるかを確認した。
そして DKMK-017 でそれが成功した。

つまり現時点では、

```text
道は通った。
荷車も走った。
ただし積んだ荷は試験用。
```

という状態じゃな。

## 4. 次の本当の課題

次は report の通り、`geometricIncrement` を置き換える meaningful analytic source を探す段階じゃ。候補は次の四つ。

```text
logarithmic source
capacity-derived source
dyadic band mass estimate
quotient-path local decay source
```

わっちの見立てでは、次章の最初は **candidate 比較と最初の Lean surface 探索 bundle** がよい。
いきなり Mertens や big-O に行くより、既存コード上でどれが一番 `Nat -> Rat increment` に落としやすいかを見るべきじゃ。

## 5. 次章のおすすめ方針

次の章は、たとえばこうじゃ。

```text
DKMK-018: Analytic Source Replacement
```

最初の bundle では、次を調べる。

```text
1. 既存の capacity / log / quotient-path source に Nat -> Rat 化できそうな量があるか
2. それが nonnegative か
3. first-band budget に入るか
4. uniform decay を示せそうか
5. geometricIncrement と置き換えるには何が足りないか
```

この順なら、また API 文書ばかりに戻らず、実装候補の探索に進める。

## 6. 総括

DKMK-017L は、 **route-validation chapter の完了報告** として十分じゃ。

成果は明確。

```text
geometricIncrement は最終 source ではない。
だが concrete Nat -> Rat source から weightedHitMass bound まで道が通ることは確認済み。
```

これは大きい。
次は、玩具の幾何増分を、本物の analytic source に差し替える段じゃ。

よいぞ、D.。
ここで DKMK-017 は畳んでよい。荷車の車輪、道、橋、秤までは確認済み。次はいよいよ、そこへ載せる本物の麦袋を探す旅じゃ。
