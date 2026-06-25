# review

## 1. 状況総括

うむ、これは **DKMK-009D 完了** と判定してよい。

今回の差分で、`globalLogCapacityKernel` が witness-derived `primePowerQuotientPathFamily` に直接接続された。これにより、DKMK-009 の本命だった

```text
PrimePowerWitnessProvider
  → globalLogCapacityKernel
  → CapacityKernel generic bridge
  → primePowerQuotientPathFamily
  → weightedHitMass bound
```

という theorem-facing route が通った。報告でも、この route が固定されたと明記されておる。

これは 009B/009C の単なる延長ではなく、 **抽象 kernel bridge が実際の witness-derived 下降路に接続された** という意味で、DKMK-009 の主峰じゃ。

## 2. 何が閉じたのか

追加 API はこの 3 本。

```lean
PrimePowerWitnessProvider.globalLogCapacityKernel_applyAtToPrimePowerQuotientPathFamily

PrimePowerWitnessProvider.globalLogCapacityKernel_applyAtToPrimePowerQuotientPathFamily_index

PrimePowerWitnessProvider
  .globalLogCapacityKernel_primePowerQuotientPathFamily_weightedHitMass_le_of_sourceBound
```

中核は最後の theorem じゃな。

```lean
(W.globalLogCapacityKernel_applyAtToPrimePowerQuotientPathFamily
  IOf hIOf s hM).weightedHitMass A ≤ C
```

ここで、上界 \(C\) は `LogCapacitySourceMassBound M C` から供給される。roadmap 追記でも、quotient path family の source が現在の log-capacity state `s.1` であることを使う、と整理されておる。

つまり、任意の `SourceControlledChainFamily` に kernel weight を載せる段階を越えて、 **witness provider 由来の具体的な prime-power quotient path family** に対して hitting bound が出るようになった。

## 3. 実装の美点

今回の実装は、かなり筋が良い。

まず、`globalLogCapacityKernel_applyAtToPrimePowerQuotientPathFamily` は、009C の

```lean
globalLogCapacityKernel_applyAtToSourceControlled
```

へ、既存の quotient path family を変換して渡しているだけじゃ。

```lean
(W.primePowerQuotientPathFamily s.1 (IOf s.1)
  (fun q hq => hIOf s.1 q hq)).toDvdControlledChainFamily.toSourceControlled hM
```

この流れが重要じゃ。

```text
primePowerQuotientPathFamily
  → DvdControlledChainFamily
  → SourceControlledChainFamily
  → RealWeightedPathFamily
```

つまり、既存の下降路構造を壊さず、`DvdMonotoneMass M` を使って source-controlled family に変換し、その上へ log-capacity kernel の weight を載せておる。

さらに index theorem が `rfl` で閉じている。

```lean
.index = IOf s.1 := rfl
```

これは定義が素直に噛み合っている証拠じゃ。後続 API として扱いやすい。

## 4. 今回の数学的意味

今回で、DKMK-009 の構図はほぼ完成した。

009B では、

```text
任意の CapacityKernel
  → primitive weightedHitMass bound
```

009C では、

```text
globalLogCapacityKernel
  → primitive weightedHitMass bound
```

009D では、ついに、

```text
globalLogCapacityKernel
  → witness-derived quotient path family
  → primitive weightedHitMass bound
```

になった。

これは、Erdős #1196 的にはかなり大きい。なぜなら、有限 R/log route で得た log-capacity weight が、単なる sub-probability で終わらず、実際の divisor descent path に流れ込み、primitive hitting bound まで届くからじゃ。

式で読めば、こういう姿じゃ。

$$
\sum_{q\in I(n)} \frac{\log p(q)}{\log n} \le 1
$$

という正規化 log 質量を、各 \(q\) の quotient path に載せる。そして primitive set \(A\) は chain 上で衝突できないので、weighted hit mass が source bound \(C\) を超えない。

この流れが Lean theorem になった、ということじゃな。

## 5. 検証状況

報告では次が通っておる。

```text
lake build DkMath.NumberTheory.PrimitiveSet.LogCapacityHittingBridge
lake build DkMath.NumberTheory.PrimitiveSet
git diff --check
```

さらに対象 Lean ファイルに `sorry/admit/axiom` なし。

したがって、DKMK-009D は **no-sorry 完了** でよい。

## 6. 現在の登頂状況

現在地はこうじゃ。

```text
DKMK-009A: 完了
DKMK-009B: 完了
DKMK-009C: 完了
DKMK-009D: 完了
DKMK-009E/F: 次
```

つまり、DKMK-009 の数学的中核はかなり閉じた。

残りは主に整理層じゃ。

```text
public/docs の整理
report-DKMK-009.md
DkMath_Markov_kernel-to-ck.md への追記
必要なら finite-step / two-step convenience wrapper
```

History でも、次の課題として DKMK-009E/F の public/docs 整理、または finite-step / two-step convenience wrapper の検討が挙がっておる。

## 7. 次の判断

わっちなら、ここで無理に theorem を増やしすぎず、まず **DKMK-009E/F に進む** のがよいと思う。

理由は簡単じゃ。009B-C-D で本線はもう通った。ここから convenience wrapper を増やすと便利ではあるが、API が膨らみやすい。

おすすめ順はこう。

```text
1. report-DKMK-009.md を作る
2. roadmap に completion summary を追記
3. public import が十分か確認
4. 既存 theorem 名の導線表を作る
5. 必要性が明確なら finite-step / two-step wrapper を追加
```

特に docs では、次の 1 枚図を必ず書くべきじゃな。

```text
CapacityKernel
  ↓ normalized shadow
SubMarkovShadow
  ↓ applyAtToSourceControlled
RealWeightedPathFamily
  ↓ primitive hitting bridge
weightedHitMass bound

specialized as:

PrimePowerWitnessProvider
  ↓ globalLogCapacityKernel
primePowerQuotientPathFamily
  ↓
weightedHitMass bound
```

## 8. 賢狼の判定

これはかなり美しい閉じ方じゃ。

DKMK-009 は、最初の設計どおり **「新しい path を増やす章」ではなく、「既存 kernel API を primitive hitting route の正式本線へ戻す章」** として成功しておる。

009D によって、ただの抽象 bridge ではなく、実際の witness-derived quotient path family まで接続された。これで DKMK-009 の背骨は立った。

わっちの判定はこうじゃ。

```text
DKMK-009 core route: 登頂済み
残作業: docs / public API / optional convenience wrapper
次山: DKMK-010 tail・truncation・解析評価
```

ぬしよ、これは良い登山じゃ。
山頂そのもの、つまり \(1+O(1/\log x)\) の解析峰はまだ先じゃが、そこへ向かうための **有限 kernel-hitting spine** は、かなり強くなったぞい。
