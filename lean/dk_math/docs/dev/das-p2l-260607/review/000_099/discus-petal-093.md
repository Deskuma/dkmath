# Discussion: No.093 cp

## Petal 構造の入れ子か？

## うむ、まさに Petal 系じゃ

ぬしの感覚はかなり正しい。

これは **Petal 構造そのもの** に見える。
しかも、単なる Petal ではなく、

```text
Petal の中に Petal があり、
その中にまた Petal がある
```

という **入れ子 Petal / 階層 Petal** じゃ。

## 何が Petal 的なのか

いま見えている Collatz の narrowing cylinder は、こういう構造を持っている。

```text
mod 8:
  3 -> recovery
  7 -> retention

mod 16:
  7  -> recovery
  15 -> retention

mod 32:
  15 -> recovery
  31 -> retention

mod 64:
  31 -> recovery
  63 -> retention
```

各階層で、ひとつの retention cell が、次の解像度で二つに割れる。

```text
親 cell:
  retention

子 cell A:
  recovery sibling

子 cell B:
  continuation sibling
```

これは完全に Petal 的じゃ。

## Petal として読むなら

Petal 語彙で読むと、こうなる。

```text
Petal cell:
  ある解像度で見える residue 区画

Recovery sibling:
  外へ戻る花弁

Continuation sibling:
  内側へ潜る花弁

Retention cylinder:
  入れ子に続く中心枝
```

つまり、`7 mod 8` は一つの花弁に見えるが、解像度を上げると、

```text
7 mod 16
15 mod 16
```

という二枚の花弁に割れる。

さらに `15 mod 16` も、

```text
15 mod 32
31 mod 32
```

に割れる。

これは、Petal の「外周に出る枝」と「中心へ潜る枝」が、階層的に繰り返されている状態じゃ。

## 入れ子構造としての本質

構造だけ抜き出すと、こう。

```text
RetentionCell r
  -> RecoverySibling r
  -> ContinuationSibling r
```

そして、

```text
ContinuationSibling r
  = RetentionCell (r + 1)
```

のように見える。

つまり、

```text
retention の継続先が、次階層の retention cell になる
```

これが入れ子じゃ。

だから、ただの分岐木ではない。
**自己相似的な分岐木** になっている。

## 数式で言えば

見えている中心枝は、

```text
7 mod 8
15 mod 16
31 mod 32
63 mod 64
127 mod 128
...
```

つまり、

```text
2^r - 1 mod 2^r
```

じゃ。

これは \(2\)-adic では \(-1\) に近づく列。

だから Petal 的には、

```text
各階層の中心核が -1 方向へ沈んでいく
```

と読める。

そしてその中心枝から、毎回 recovery sibling が外へ出る。

```text
7 mod 16   -> 3 mod 8
15 mod 32  -> 7 mod 16
31 mod 64  -> 15 mod 32
```

つまり、内側へ潜る枝と、外側へ戻る枝がある。

## これは「階層化された観測窓」

ぬしの言う通り、これは階層化されている。

`mod 2^n` は単なる分類解像度ではなく、

```text
第 n 階層の観測窓
```

になっている。

粗い窓では一つに見えるものが、細かい窓では二つに割れる。

```text
mod 8 では:
  7 mod 8 は retention

mod 16 では:
  7 mod 16 は recovery
  15 mod 16 は continuation

mod 32 では:
  15 mod 32 は recovery
  31 mod 32 は continuation
```

つまり、観測窓を深くすると、**以前の retention の内部構造が見える**。

これは Petal の「解像度上昇による花弁分解」そのものじゃ。

## DkMath 的に言えば

これはかなり綺麗にこう書ける。

```text
Core:
  retention cylinder

Beam:
  recovery sibling

Gap:
  continuation sibling

Big:
  次階層の Petal split
```

あるいは別の見方では、

```text
Core:
  低剥離を続ける条件

Beam:
  次に縮小へ戻る枝

Gap:
  さらに深く逃げる枝

Big:
  その階層での完全な二分
```

じゃ。

## 重要なのは「ただの木」ではないこと

これは単なる binary tree ではない。

なぜなら、continuation branch が次の階層で同じ構造を再生するからじゃ。

```text
retention
  -> recovery
  -> continuation = next retention
```

この形が繰り返される。

だから、これは

```text
recursive Petal
nested Petal
self-similar Petal
```

と呼べる。

## Collatz への意味

この見方を使うと、Collatz の低剥離問題はこう言い換えられる。

```text
軌道が低剥離を続けるには、
各 Petal 階層で continuation sibling を選び続けなければならない。
```

しかし各階層には recovery sibling がある。

```text
recovery を選ぶ:
  有限ステップで追加剥離が戻る

continuation を選ぶ:
  次のさらに細い Petal 階層へ潜る
```

つまり反例候補は、Petal の中心へ中心へと潜り続ける必要がある。

これはかなり強い構造認識じゃ。

## まとめ

ぬしの言う通り。

```text
この narrowing cylinder は Petal 系である。
しかも、入れ子化された階層 Petal である。
```

一番短くまとめるなら、

```text
Collatz の低剥離 path は、
2-adic Petal の中心枝を潜っていく運動として見える。
```

そして各階層では、

```text
外へ戻る recovery petal
内へ潜る continuation petal
```

が分岐する。

うむ。
これは DkMath.Petal と接続する価値がかなり高い。
次の設計では、`RetentionCylinder` をただの residue 定義にせず、**Petal address の階層セル**として扱うのがよさそうじゃ。
