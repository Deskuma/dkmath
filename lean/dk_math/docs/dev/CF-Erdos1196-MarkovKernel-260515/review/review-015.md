# review

うむ。DKMK-006J は **実装を進める回ではなく、ここまでの登頂を地図化して固定する回** じゃ。
これはとても良い区切りじゃよ。DKMK-001 から DKMK-006I までで増えた道具を、単なる履歴ではなく **次に迷わないための route map** として整理しておる。新規 report として `report-DKMK-001_to_006I.md` を追加し、route を canonical equality / selected inequality / future equivalence の三本に分けた、というのが今回の本体じゃ。

## 1. 今回の位置づけ

DKMK-006J では、新しい Lean interface は追加しておらぬ。
代わりに、ここまでの成果を次の三本に整理した。

```text
canonical equality route:
  canonicalExponentSlotLabels
  → FullChannelLogCostComplete
  → MarkovShadow

selected inequality route:
  selected IOf
  → log-capacity inequality
  → SubMarkovShadow

future equivalence route:
  external slot representation
  ≃ canonicalExponentSlotLabels
  with weight/cost preservation
```

これはかなり重要じゃ。
なぜなら DKMK-006F/G/I までで、道が増えすぎていたからじゃな。ここで三本に分けておかないと、次に外部 kernel が出てきたときに「これは MarkovShadow へ行くべきか、SubMarkovShadow のまま使うべきか、同型 bridge が必要か」が曖昧になる。

## 2. canonical equality route の整理

canonical equality route は、今の本線じゃ。

中心はこれ。

```lean
canonicalExponentSlotLabels n
```

これは

```text
{ p ^ k | Nat.Prime p, 1 ≤ k, k ≤ n.factorization p }
```

を表す canonical な full exponent-slot label set じゃ。

この route では、

```text
canonicalExponentSlotLabels
→ FullExponentSlotChannelSet
→ FullExponentSlotCoverage
→ FullChannelLogCostComplete
→ MarkovShadow
```

という流れがすでに閉じている。

つまり DkMath kernel の canonical reference model では、full log-capacity equality まで到達済み。
この route は「Markov kernel を最初から置く」のではなく、exponent slot と log cost から MarkovShadow を生成する道じゃ。

## 3. selected inequality route の整理

selected inequality route は、任意の selected channel set を扱う柔軟な道じゃ。

外部から、

```lean
IOf : ℕ → Finset ℕ
hIOf : ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n
```

を受け取り、一般には full channel とは限らない。

だから結論は、

$$
\sum weight\le 1
$$

であり、`SubMarkovShadow` のまま保持する。

これは非常によい判断じゃ。
全部を Markov equality に押し込まない。部分 channel を見る用途、hitting bound へ渡す用途、局所的な flow を見る用途では、むしろ inequality route のほうが自然じゃ。

## 4. future equivalence route の整理

三本目は、まだ未設計の将来 route じゃ。

現在の `CanonicalExponentSlotIndex T` は、かなり強い条件を要求する。

$$
T.toDivisorTransitionKernel.index(n)=canonicalExponentSlotLabels(n)
$$

この **等号一致** が示せるなら、それでよい。
しかし外部 kernel が自然数 label (q=p^k) そのものではなく、たとえば slot pair ((p,k)) や別表現を index として持つ場合、この等号 route にはそのまま乗らぬ。

その場合に必要になるのが、

```text
external slot representation
≃ canonicalExponentSlotLabels
with weight/cost preservation
```

という future equivalence route じゃ。

ただし、今回の判断は「先回りして作らない」。
これは正しい。必要になるまでは抽象 bridge を増やさない方がよい。

## 5. DKMK-006J の価値

今回の価値は、次の判断順序を固定したことじゃ。

```text
1. CanonicalExponentSlotIndex T を直接狙えるなら equality route に乗せる。
2. selected channel として十分なら SubMarkovShadow route のまま使う。
3. label 表現が等号一致しない場合だけ、weight-preserving equivalence bridge を設計する。
```

これは今後の実装でかなり効く。
特に「本線に乗せるべきもの」と「selected route のままでよいもの」を混ぜずに済む。

## 6. report の意味

新規 report は、単なるまとめではなく **分岐判断表** になっておる。

表では、

```text
canonicalExponentSlotKernel:
  canonical equality reference model
  → MarkovShadow

T with CanonicalExponentSlotIndex T:
  external equality bridge
  → MarkovShadow

selected IOf route:
  selected inequality route
  → SubMarkovShadow

sampleTen...:
  local toy / sanity check
  → global equality route には乗せない

non-equal external slot representation:
  future equivalence route
  → 未設計
```

と整理されている。

この表は、今後 `PrimitiveSet` 内に新しい kernel 候補が増えたときの分類基準になる。

## 7. 現在地の評価

DKMK-006J によって、DKMK-006 系はかなり綺麗に一区切りになった。

ここまでの成果はこうじゃ。

```text
CapacityKernel:
  保存核

SubMarkovShadow:
  selected inequality route

MarkovShadow:
  canonical full equality route

CanonicalExponentSlotIndex:
  外部 kernel を equality route へ接続する条件

KernelCandidateInventory:
  現候補の positive / negative 分類

report-DKMK-001_to_006I:
  三本の route map
```

これはもう「アイデア段階」ではない。
DkMath kernel route は、抽象核・canonical model・外部接続条件・候補分類・route map まで揃った。

## 8. 次の一手

わっちなら、ここで DKMK-006 系は一旦 **小締め** と見る。

次にやるなら二択じゃ。

第一は、具体的な外部 kernel がある場合に、

```lean
CanonicalExponentSlotIndex T
```

を狙う。

第二は、DkMath kernel route を primitive hitting / weighted path family 側に接続する準備に戻る。

どちらへ行くにしても、DKMK-006J の report が判断基準になる。

## 9. 総合判定

DKMK-006J は **登頂整理として成功** じゃ。

新しい theorem は増えていない。
しかし、これまで増やした theorem 群を「どう使うか」の地図ができた。

DkMath kernel project は今、次の三本立てとして安定した。

```text
canonical equality route:
  MarkovShadow へ行く本線

selected inequality route:
  SubMarkovShadow として使う柔軟路

future equivalence route:
  等号一致しない外部表現のための将来路
```

これはよい。
この整理があるから、次に外部 kernel や hitting 側の橋が出てきても、どの道へ入れるか迷わぬ。

賢狼としては、ここで一度りんごをかじってよいと思うぞい。
DKMK-001 から 006J までで、別尾根の登山道は十分に道標を持った。次は、その道を本線の primitive hitting / Erdős #1196 解析峰へどう戻すかじゃ。
