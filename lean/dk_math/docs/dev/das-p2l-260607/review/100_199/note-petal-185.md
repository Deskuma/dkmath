# Note: No. 185 cp

## 会計システム構築は収束へ向かっているか？

## 結論

うむ。**向かっている**。
ただし、まだ **Collatz 収束そのものへ直接到達している段階ではない**。

今の構築は、

```text
収束証明そのもの
```

ではなく、

```text
発散・破綻しそうな局所構造を、
回収可能な二項局所会計へ落とす装置
```

を作っている段階じゃ。

cp183 では、`failure + noAdjacentOverlap` から、ひとつの recovered adjacent pair に局所化し、その pair-local family が `budget ≤ -2`、`sum < 0`、`items.length = 2` を持つ diagnostic carrier へ束ねられた。これは「局所 failure が負の会計単位として回収できる」ことをかなり明確にしている。

## どの意味で収束へ向かっているか

いま見えている流れはこうじゃ。

```text
sorted-before failure
  -> adjacent diagnosis
  -> recovered pair or overlap obstruction
  -> no-overlap なら recovered pair
  -> pair-local accounted family
  -> negative two-item diagnostic
```

つまり、局所的には、

```text
破綻に見えるものを、
下降側の負 budget として回収する
```

ところまで来ている。

これは収束証明に必要な部品としてかなり重要じゃ。

なぜなら Collatz の発散シナリオは、どこかで「上がる局所構造」を長く維持しなければならない。
ところが、この構築では、その局所 failure が no-overlap 条件下で **負の回収会計** に落ちる。

これは発散側にとっては嫌な制約じゃ。

## まだ足りないもの

ただし、まだ決定的に足りないものがある。

```text
overlap obstruction の処理
```

じゃ。

今の theorem は、

```text
noAdjacentOverlap があるなら recovered diagnostic が出る
```

という形。

つまり、overlap がある場合はまだ Gap として残っている。

さらに、pair-local な負 budget は得ているが、まだ次は言っていない。

```text
全 failure が回収される
全 recovered family を合算できる
interval union accounting ができる
大域軌道全体で下降が勝つ
任意の開始値が 1 に到達する
```

ここは未到達じゃ。

## 現在地を DkMath 語彙で言うと

わっちなら、今の位置をこう見る。

```text
Core:
  failure を recovered adjacent diagnostic に落とす局所会計

Beam:
  その diagnostic が list / depth / orbit 方向へどう伝播するか

Gap:
  overlap obstruction と、まだ合算できない pair-local family 群

Big:
  すべての Gap を包んで、大域下降を保証する器
```

cp183 は **Core をかなり固めた** 段階じゃ。

収束へ向かってはいる。
だが、収束を言うには、Core だけでなく Beam と Gap の処理が必要になる。

## 次の山

次の本丸は、おそらくこの三つじゃ。

```text
1. diagnostic の list 構文 API を整える
2. overlap obstruction を分類・弱化・回収する
3. pair-local negative budget を安全に合算できる条件を探す
```

特に 3 は危険じゃ。
union accounting を不用意に入れると過大主張になる。

だから今は、まだ合算せず、

```text
短い list では diagnostic 不可能
tail から diagnostic を持ち上げられる
diagnostic は同じ pair-local family を保持する
```

のような構文補助を積むのが正しい。

## 端的に言うと

はい、収束へ向かっている。
ただし今は、

```text
Collatz が収束する証明
```

ではなく、

```text
発散に必要な局所 failure を、負の局所会計へ変換する証明基盤
```

を作っている。

これはかなり良い方向じゃ。
特に「破綻を消す」のではなく、「破綻を診断して負 budget として回収する」構築になっているのが強い。
