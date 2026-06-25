# review

うむ、DKMK-017E は **first-band bound の入力負担をかなり減らした bundle** じゃ。
ここまでの DKMK-017 では、`hbudget`、`hinc_nonneg`、`hdecay` の入力境界を軽くしてきた。今回ついに残っていた

```text
hbase0 : increment 0 <= base
```

にも手が入った、という位置づけじゃな。

## 1. 何が追加されたのか

追加された constructor は二つ。

```lean
FirstBandDecayBudgetSource.ofDenomClearedBudgetNatBounds
```

これは、DKMK-017C の denominator-cleared budget helper と、DKMK-017D の Nat-bound source helper を合成する wrapper じゃ。

もう一つが今回の主役。

```lean
FirstBandDecayBudgetSource.ofSelfBaseDenomClearedBudgetNatBounds
```

これは

```text
base := increment 0
```

と置くことで、

```text
hbase0 : increment 0 <= base
```

を `le_rfl` で閉じる constructor じゃ。報告でも、この self-base constructor では `hinc_nonneg 0 (Nat.zero_le K)` から `0 <= (increment 0 : Real)` を作り、`hbase0` は `le_rfl` で閉じたと整理されておる。

## 2. 採用判断は妥当

採用でよい。

理由は、`base := increment 0` は first-band / uniform-decay route の自然な基準点だからじゃ。

$$
increment(k)\le increment(0)\cdot ratio^k
$$

という形は、初期値と減衰率で全体を支配する、最も標準的な幾何減衰の読み方じゃ。

これにより caller は明示的な

```text
increment 0 <= base
```

を渡さなくてよくなる。

ただし重要なのは、報告にもある通り、budget obligation は消えないことじゃ。

代わりに、次を示す必要がある。

```text
(increment 0 : Real) <= (1 + error) * (1 - (ratio : Real))
```

つまり `hbase0` の負担は消えたが、その分 `budget proof` は first-band 自身に対する評価へ移った。

## 3. これは wrapper 過剰ではないか？

今回の constructor は、少し wrapper 寄りではある。
しかし、DKMK-017E については **有用な wrapper** と見てよい。

理由は二つ。

第一に、これまで別々だった DKMK-017C と DKMK-017D の surface を、実際の caller path に沿って結合している。

```text
denominator-cleared budget
+ Nat-bound nonnegativity
+ Nat-bound decay
  -> FirstBandDecayBudgetSource
```

第二に、`base := increment 0` という設計判断を API として固定している。これは単なる field forwarding ではなく、first-band route の標準形を表している。

ゆえに、これは DKMK-015/016 で多かった「薄すぎる便利 wrapper」とは少し違う。
実際に analytic caller の仮定数を減らしている。

## 4. 現在の caller route

今回の self-base constructor を使うと、caller 側の主要入力はかなり整理される。

```text
ratio : Rat
error : Real
hr0 : 0 <= (ratio : Real)
hr1 : (ratio : Real) < 1

hbaseBudget :
  (increment 0 : Real) <= (1 + error) * (1 - (ratio : Real))

hinc_nonneg :
  forall k, k <= K -> 0 <= increment k

hdecay :
  forall k, k < K -> increment (k + 1) <= ratio * increment k
```

ここから、

```text
FirstBandDecayBudgetSource
  -> DyadicBandAnalyticEstimate
  -> TruncationEnvelopeEstimate
```

へ行ける。

これはかなり良い。
`base` を外部指定する一般 route と、`base := increment 0` の標準 route の両方が揃ったことになる。

## 5. DKMK-017A-E の流れ

ここまでの DKMK-017 は、良いテンポじゃ。

```text
017A:
  FirstBandDecayBudgetSource を採用

017B:
  ofBudgetSource / ofBudgetAndDecay を追加

017C:
  hbudget を denominator-cleared form から作る helper を追加

017D:
  hinc_nonneg / hdecay を Nat 境界形式から作る helper を追加

017E:
  base := increment 0 で hbase0 を閉じる constructor を追加
```

見事に、残っていた入力が一つずつ軽くなっておる。

## 6. 次の判断

次は報告にある通り、 **DKMK-017A-E の source surface を一度まとめる** のがよい。

ただし、長い章末 report まではまだ不要じゃ。
新体制なら、軽い整理でよい。

次に判断すべきはこれ。

```text
この API plumbing はここで十分か？
それとも concrete analytic source に入る前に、もう 1 個だけ合成 wrapper が必要か？
```

わっちの見立てでは、追加 wrapper はもう最小限でよい。
今ある surface で、次の標準 route は十分に表現できる。

```text
ofSelfBaseDenomClearedBudgetNatBounds
  -> FirstBandDecayBudgetSource
  -> ofFirstBandDecayBudgetSourcePackage
  -> DyadicBandAnalyticEstimate
```

あとは本当に、`increment 0` と `ratio` をどう評価するかの解析側へ進む段じゃ。

## 7. 総括

DKMK-017E は、 **first-band bound を self-base 化して、analytic caller の入力を一段軽くした bundle** じゃ。

これは採用でよい。

特に重要なのは、

```text
hbase0 は消える
budget obligation は increment 0 に移る
```

という正直な整理じゃ。
証明負担を消したのではなく、より自然な場所へ移した。これは良い API 設計じゃ。

よし、D.。
`hbudget`、`hinc_nonneg`、`hdecay`、`hbase0` の全てに一度手が入った。ここから先は、いよいよ抽象入力を本物の analytic estimate で満たす旅じゃな。
