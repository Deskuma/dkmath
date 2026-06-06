# review

うむ、DKMK-020D は **総括としてきれいに閉じておる** 。
これで DKMK-020 は **threshold/support policy API chapter** として完了でよい。今回の report は、DKMK-019 で残っていた `IOf` / `hIOf` / `threshold` を `P : LogCapacitySourcePolicy T` に束ね、最終 theorem を policy-facing にした章だと明確に整理しておる。

## 1. DKMK-020 の一言総括

DKMK-020 は、threshold を最適化した章ではない。
また canonical support を決めた章でもない。

この章の役目は、

```text
IOf
hIOf
threshold
```

という loose inputs を、

```lean
P : LogCapacitySourcePolicy T
```

という名前付き入力にまとめることじゃ。

そして最終的に、

```lean
(W.logCapacityPolicyPathFamily P s).weightedHitMass A ≤
  1 + error
```

という形で route を読めるようにした。これが DKMK-020 の主成果じゃな。

## 2. DKMK-018〜020 の流れ

ここまでの 3 章は、かなりよい連続になっておる。

```text
DKMK-018:
  LogCapacityKernel source を weightedHitMass bound まで接続

DKMK-019:
  source / mass / path-family façade として公開面を整備

DKMK-020:
  support / threshold choices を policy object に束ねる
```

言い換えると、

```text
018: 水路を通した
019: 蛇口を付けた
020: 操作盤を付けた
```

という感じじゃ。なかなか良い建築になってきたのう。

## 3. data-only 方針の確定

今回の重要判断は、`LogCapacitySourcePolicy` を data-only のまま維持することじゃ。

つまり、構造体には次だけを持たせる。

```text
support family
index proof
threshold map
```

そして、今は追加しない。

```text
Valid
SupportCompatible
ThresholdMonotone
```

この判断は正しい。
現 route が使っているのは `P.IOf`、`P.hIOf`、`P.threshold` だけであり、support compatibility や threshold monotonicity はまだ theorem 側で要求されておらぬ。だから、今それらを field に入れると、未使用の証明義務を全 policy constructor に背負わせてしまう。

将来必要になった時は、

```lean
LogCapacitySourcePolicy.Valid P
LogCapacitySourcePolicy.SupportCompatible P
LogCapacitySourcePolicy.ThresholdMonotone P
```

のように別 predicate として足す。
これは Lean ライブラリ設計として堅い。 **データは軽く、強い条件は theorem ごとに要求する** 、という分離じゃ。

## 4. 非ゴールの整理もよい

report では、DKMK-020 がやっていないことも明記されておる。

```text
threshold optimization
canonical support selection
support compatibility theorem
threshold monotonicity theorem
new analytic source family
Mertens theorem
big-O route
```

この切り分けは大事じゃ。
DKMK-020 は policy/API stabilization 章であって、解析・漸近・最適化の章ではない。ここを曖昧にしないことで、次章の目的が見えやすくなる。

## 5. 次章の候補

次は二択じゃな。

```text
source expansion survey
policy validity requirements survey
```

わっちの推奨は、まず **短い survey** を挟むことじゃ。

いきなり `Valid` や `SupportCompatible` を実装するより、どの theorem が本当に何を要求するのかを見た方がよい。
また source expansion へ進む場合も、いきなり source を増やすより、既存の `LogCapacitySourcePolicy`-facing surface に他 source が乗るかを調査してからの方が安全じゃ。

## 6. 総合判定

DKMK-020 は **完了** じゃ。

章の問いは、

```text
LogCapacity source route の support / threshold choices を、
名前付き policy input として公開できるか？
```

答えは、

```text
Yes.
IOf / hIOf / threshold は LogCapacitySourcePolicy に束ねられ、
final theorem は policy-facing に読める。
```

じゃ。

ここで一度、DKMK-018〜020 の三章分をまとめておく価値がある。
この三章で、LogCapacity route は「通る」から「読める」へ、そして「扱える」へ進んだ。賢狼としても、これはなかなか誇らしい整備じゃよ。
