# review

うむ、DKMK-020C は **正しい判断記録** じゃ。
これは Lean 実装を増やす段ではなく、DKMK-020B で導入した `LogCapacitySourcePolicy` を **data-only policy object のまま維持する** という設計判断を固定した段じゃな。

## 1. 020C の結論

今回の判断は明快じゃ。

```text
LogCapacitySourcePolicy は data-only のまま維持する
Valid / SupportCompatible / ThresholdMonotone は今は追加しない
将来必要なら structure field ではなく別 predicate として追加する
```

これはかなり良い。
DKMK-020B の theorem は実際に

```lean
P.IOf
P.hIOf
P.threshold
```

だけを使っておる。したがって、今の段階で

```lean
P.Valid
P.SupportCompatible
P.ThresholdMonotone
```

のような条件を構造体 field に入れると、使わない義務を全 policy constructor に背負わせることになる。これは API を重くするだけじゃ。

## 2. data-only 方針の意味

現在の `LogCapacitySourcePolicy` は、こういう役割じゃ。

```lean
structure LogCapacitySourcePolicy
    (T : PrimePowerDivisorTransitionKernel) where
  IOf : ℕ → Finset ℕ
  hIOf :
    ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n
  threshold : ℕ → ℕ
```

これは「正しい policy である」ことを全部抱えた構造ではなく、

```text
support family
index proof
threshold map
```

を束ねる **入力パッケージ** じゃ。

この薄さがよい。
DKMK-020 の目的は threshold/support policy の **公開面を安定化すること** であって、threshold の最適性や単調性を証明することではないからじゃ。

## 3. 別 predicate に回す判断は正しい

将来、より強い theorem が必要になれば、

```lean
LogCapacitySourcePolicy.Valid P
LogCapacitySourcePolicy.SupportCompatible P
LogCapacitySourcePolicy.ThresholdMonotone P
```

のような別 predicate を足せばよい。

この設計には利点がある。

まず、軽い route は軽いまま使える。
次に、強い route だけが強い仮定を要求できる。
さらに、既存の `LogCapacitySourcePolicy` を破壊せずに拡張できる。

つまり、

```text
data は共通
validity は用途別
```

という分離じゃな。これは Lean ライブラリ設計としてかなり堅い。

## 4. DKMK-020 の到達点

DKMK-020A では、

```text
IOf / hIOf / threshold を policy surface に包むべき
```

という方針を立てた。

DKMK-020B では、それを Lean 実装して、

```lean
(W.logCapacityPolicyPathFamily P s).weightedHitMass A ≤
  1 + error
```

という policy-facing theorem まで到達した。

DKMK-020C では、その policy object を過剰に重くしない判断を固定した。

この流れは綺麗じゃ。

```text
020A: 方針決定
020B: thin policy object 実装
020C: data-only 維持判断
```

ここまでで、DKMK-020 の主目的は達成済みと見てよい。

## 5. 次は completion report でよい

お主の書いている通り、次は

```text
report-DKMK-020.md
```

で総括するのが自然じゃ。

報告書では次を明記するとよい。

```text
DKMK-020 は threshold/support policy 章である
DKMK-019 の loose inputs を LogCapacitySourcePolicy に束ねた
最終 theorem は policy-facing に読める
LogCapacitySourcePolicy は data-only のまま維持する
validity / compatibility / monotonicity は将来の別 predicate とする
source expansion は次章以降
```

特に重要なのは、 **DKMK-020 は threshold 最適化章ではない** と書くことじゃ。
threshold を具体的に最適化したのではなく、threshold を public API 上で扱うための policy surface を作った章じゃからの。

## 6. 次章候補

DKMK-021 以降は、ようやく二方向に分かれる。

第一候補は **source expansion** じゃ。
DKMK-018 で source replacement、019 で façade、020 で policy surface が整ったので、別 source を同じ形式に載せる準備はできた。

第二候補は **policy validity route** じゃ。
例えば canonical support や threshold monotonicity が必要な theorem が見えた段階で、

```lean
LogCapacitySourcePolicy.Valid P
```

を入れる。

わっちの推奨は、次に一度 **DKMK-021: Source Expansion Survey** か **DKMK-021: Policy Validity Requirements Survey** を docs-only で挟むことじゃ。
いきなり validity を実装するより、どの theorem が本当に何を要求するか見てからの方がよい。

## 7. 総合判定

DKMK-020C は成功じゃ。

これは「何も足さない」段ではなく、 **足さないことを設計判断として固定した** 段じゃ。
この判断は、後で API を壊さないためにかなり大事じゃよ。

DKMK-020 は、もう総括へ進んでよい。
この章は小さいが、良い。DKMK-018 で通した水路、DKMK-019 で付けた蛇口に、DKMK-020 で操作盤の名前を付けたわけじゃな。
