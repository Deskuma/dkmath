# review

うむ、DKMK-017I は **予定通りの成功** じゃ。
今回で、ついに concrete な `increment : Nat -> Rat` 候補から `TruncationEnvelopeEstimate` まで通った。これは DKMK-017 の大きな節目じゃな。

## 1. 何が閉じたのか

今回追加された concrete candidate はこれじゃ。

```lean
def geometricIncrement (base ratio : ℚ) (k : ℕ) : ℚ :=
  base * ratio ^ k
```

これは深い解析的 increment ではない。
だが、DKMK-017 の標準搬送路を試すには最適な **最小 concrete source** じゃ。

追加された基本補題もきれいに揃っておる。

```text
geometricIncrement_nonneg
geometricIncrement_zero
geometricIncrement_decay
geometricIncrement_decay_le
```

つまり、

$$
0\le base,\quad 0\le ratio
$$

から非負性が出て、

$$
geometricIncrement(base,ratio,0)=base
$$

かつ、

$$
geometricIncrement(base,ratio,k+1)
==================================

ratio\cdot geometricIncrement(base,ratio,k)
$$

が Lean 上で閉じた。

## 2. route test として非常に良い

今回の本質は、`geometricIncrement` 自体ではなく、これが envelope まで流れたことじゃ。

追加された route は、

```text
geometricIncrement
  -> FirstBandDecayBudgetSource.ofGeometricIncrement
  -> TruncationEnvelopeEstimate.ofGeometricIncrement
  -> TruncationEnvelopeEstimate
```

という流れになっておる。

これで DKMK-017A-H で作った source surface が、単なる API plumbing ではなく、実際に concrete `Nat -> Rat` source を受け取って動くことが確認された。

## 3. 残った analytic input が明確になった

今回、`hinc_nonneg` と `hdecay` はもう難所ではなくなった。

`geometricIncrement` では、

```text
hinc_nonneg:
  0 <= base, 0 <= ratio から出る

hdecay:
  exact equality から出る
```

だから、残る主要入力はこれだけに絞られた。

```text
(base : Real) <= (1 + error) * (1 - (ratio : Real))
```

これは first-band budget じゃな。
つまり、DKMK-017 の次の焦点はかなり明瞭になった。

## 4. 採用判断は妥当

`geometricIncrement` は採用でよい。

理由は三つある。

第一に、`Nat -> Rat` の concrete candidate として最小であること。
第二に、非負性・初項・減衰がすべて軽く閉じること。
第三に、truncation envelope まで接続できたこと。

これは「本命解析 source」ではなく、 **route validation source** じゃ。
この役割としては十分に成功しておる。

## 5. 次の分岐

次は報告通り、三択じゃ。

```text
1. useful な base, ratio, error から first-band budget を導く
2. base = 1 - ratio など canonical specialization を試す
3. logarithmic / analytic source へ接続する
```

わっちの推奨は、まず **2. canonical specialization** じゃ。

たとえば、

$$
base = 1-ratio
$$

なら、`error >= 0` のもとで

$$
base\le (1+error)(1-ratio)
$$

は自然に閉じる。

ただし `base : Rat` と `ratio : Rat` の世界なので、Lean ではまず

```lean
base = 1 - ratio
```

を仮定として受ける constructor / theorem がよい。

候補はこうじゃ。

```lean
theorem TruncationEnvelopeEstimate.ofGeometricIncrement_baseEqOneSub
    ...
```

あるいは、まず source 側で、

```lean
FirstBandDecayBudgetSource.ofGeometricIncrementBaseEqOneSub
```

を試す。

## 6. ここで一度まとめると

DKMK-017I 時点で、入力負担はこう整理された。

```text
すでに軽くなった:
  hinc_nonneg
  hdecay
  hbase0

まだ本質:
  hbaseBudget
```

そして `geometricIncrement` では、残る `hbaseBudget` は

```text
(base : Real) <= (1 + error) * (1 - (ratio : Real))
```

だけじゃ。

これは良い絞り込みじゃ。
いよいよ「どんな base と ratio なら予算内に収まるか」の段階に入った。

## 7. 総括

DKMK-017I は、 **concrete `Nat -> Rat` increment から envelope までの route test 成功** じゃ。

これは予定通りで、しかも良い結果じゃ。

`geometricIncrement` により、

```text
abstract source surface
  -> concrete increment
  -> truncation envelope
```

まで通った。

次は wrapper を増やすより、first-band budget の具体化へ進む。
まずは `base = 1 - ratio` 型の canonical specialization を試すのが、最も軽くて実りがあると見るぞい。
