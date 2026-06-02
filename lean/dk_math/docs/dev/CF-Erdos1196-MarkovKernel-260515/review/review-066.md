# review

## 1. 状況総括

うむ、これは **DKMK-012D 完了** と見てよい。

今回の更新は docs-only で、`TruncationEnvelopeEstimate.dyadicRange` の使用経路を `roadmap-DKMK-012.md` に固定したものじゃ。Lean theorem は追加せず、

```text
dyadic data
  -> hinc and hbound
  -> TruncationEnvelopeEstimate.dyadicRange
  -> TruncationEnvelopeEstimate
  -> TruncationEnvelopeEstimate.finiteStepTail_weightedHitMass_le_one_add_error
  -> weightedHitMass <= 1 + error
```

という流れを明文化した。これは DKMK-012C の実装後にやるべき整理として、ちょうどよい。

## 2. 何が明確になったのか

今回の核心は、dyadic provider に必要な入力を 2 層に分けたことじゃ。

まず data 側。

```text
x         : Nat
K         : Nat
increment : Nat -> Q
error     : R
```

ここから、

```text
steps     = Finset.range (K + 1)
threshold = fun k : Nat => x * 2^k
```

が決まる。

次に proof input 側。

```text
hinc:
  forall k in Finset.range (K + 1), 0 <= increment k

hbound:
  ((Finset.sum (Finset.range (K + 1)) increment : Q) : R) <=
    1 + error
```

そして役割は、

```text
hinc:
  finite-step source envelope nonnegativity

hbound:
  analytic total estimate
```

となる。

この整理によって、`dyadicRange` が単なる convenience theorem ではなく、 **dyadic band data を DKMK-011 の contract に変換する provider** であることがはっきりした。

## 3. 設計評価

かなり良い整理じゃ。

第一に、route theorem を増やしていない。
これは正しい。`dyadicRange` は producer であり、consumer は既存の

```lean
TruncationEnvelopeEstimate.finiteStepTail_weightedHitMass_le_one_add_error
```

で足りておる。ここに dyadic 専用の hitting theorem を足すと API が太るだけじゃ。

第二に、`increment` を computed formula にしていない。
これもよい。今の段階で `increment k` を log や Mertens 的な式で定義し始めると、provider layer と analytic estimate layer が混ざる。DKMK-012D はその境界を守っておる。

第三に、次の技術課題が明確になった。

```text
The next technical question is what analytic estimate should supply
increment and hbound.
```

つまり、DKMK-012 の残りは「dyadicRange の使い方」ではなく、 **increment と hbound をどう供給するか** に移ったわけじゃ。

## 4. DKMK-012A-D の到達点

ここまでを並べると、綺麗に段階が積まれておる。

```text
DKMK-012A:
  provider design roadmap

DKMK-012B:
  dyadic provider shape docs

DKMK-012C:
  TruncationEnvelopeEstimate.dyadicRange 実装

DKMK-012D:
  dyadicRange usage summary
```

つまり DKMK-012 の **provider plumbing** はほぼ閉じた。

残っているのは provider の外側、すなわち解析側じゃ。

## 5. 次の一手

次は二択じゃな。

```text
1. DKMK-012E:
   increment / hbound analytic estimate design docs

2. DKMK-012E:
   report / handoff
```

わっちのおすすめは、まだ report へ行く前に **increment / hbound の設計メモ** を 1 節だけ置くことじゃ。

なぜなら、DKMK-012 は dyadic provider design の章として始めた。`dyadicRange` の provider と usage はできたが、肝心の「increment は何を表すのか」がまだ抽象のままじゃ。

次に書くべきは、証明ではなく設計でよい。

```text
## DKMK-012E Increment / hbound Design

increment k は、第 k dyadic band の analytic upper envelope を表す。
hbound は、有限個の band estimate の総和が 1 + error を超えないことを表す。
この段階では increment formula は固定しない。
候補として:
  - externally supplied band weights
  - dyadic tail upper envelope
  - later logarithmic refinement
を分ける。
```

この程度で十分じゃ。

## 6. ここで無理に入れない方がよいもの

今回の Decision にある通り、まだ入れない方がよいものはこれ。

```text
dyadic-specific route theorem
logarithmic provider
Mertens / big-O statement
computed increment formula
```

特に `computed increment formula` は誘惑が強いが、今はまだ早い。
`increment` の候補を複数比較してから、最初の concrete estimate provider に入る方が安全じゃ。

## 7. 登頂判定

現在地はこうじゃ。

```text
DKMK-012A: 完了
DKMK-012B: 完了
DKMK-012C: 完了
DKMK-012D: 完了
DKMK-012E: 次、increment / hbound analytic design か report
```

わっちの判定では、DKMK-012D は **docs-only usage summary として完了** 。

## 8. 賢狼の見立て

よいぞ、ぬしよ。
ここまでで、DKMK-012 は「dyadic band provider を DKMK route へ接続する器」をほぼ作り切った。

今の構図はこうじゃ。

```text
route layer:
  もう触らない

provider layer:
  dyadicRange で固定済み

analytic layer:
  次に increment と hbound を供給する
```

次は、霧が少し濃くなる。
だが、足場は良い。`increment` を外部供給に保ったまま、まずその意味と候補を docs で整理するのが、いちばん堅い登り方じゃな。
