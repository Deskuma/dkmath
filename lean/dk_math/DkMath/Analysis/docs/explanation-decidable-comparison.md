# explanation: decidable comparison

`decidable comparison` は、ざっくり言うと、

$$
\boxed{\text{任意の }x,y\text{ について、}x\le y\text{ かどうかを計算で決められること}}
$$

じゃ。

単に「数学的にどちらかが成り立つ」と証明できることとは違う。

## 1. totality と decidable comparison は別物

いま `DkNNRealQ` では totality がある。

$$
x\le y\ \text{または}\ y\le x
$$

これは、

```lean
theorem le_total (x y : DkNNRealQ) :
    x ≤ y ∨ y ≤ x
```

のような命題じゃ。

これは「必ずどちらかの向きに閉じる」という数学的事実。

一方、`decidable comparison` はもっと強い。

```lean
instance : DecidableRel (fun x y : DkNNRealQ => x ≤ y)
```

のように、任意の `x y` を渡されたとき、

```text
x ≤ y が成り立つ
```

または、

```text
x ≤ y は成り立たない
```

を、有限時間で返す仕組みじゃ。

つまり、

```text
totality:
  どちらかであることを証明できる

decidable comparison:
  どちらかを計算で判定できる
```

この違いじゃ。

## 2. 具体例

自然数なら簡単。

```text
3 ≤ 5 ?
```

これは計算すればすぐ分かる。
だから自然数の大小比較は decidable。

有限 bit 整数も同じ。
回路で比較できる。

しかし `DkNNRealQ` は、入れ子有理区間列の quotient じゃ。

値は有限データ一発ではなく、

```text
n ↦ [lo n, hi n]
```

という無限に精密化される表現を持つ。

比較は、

$$
orderDefect(x,y,n)\to0
$$

のような漸近条件で定義されている。

これは数学的には total にできる。
しかし、任意の二つの表現に対して、有限時間で必ず

```text
x ≤ y
```

または

```text
¬ x ≤ y
```

を返す判定器があるとは限らない。

## 3. なぜ難しいのか

たとえば二つの DkReal が、ものすごく近い値を表しているとする。

```text
x の区間
  [1.000000..., 1.000000...]

y の区間
  [1.000000..., 1.000000...]
```

有限段階では、まだどちらが大きいか分からないことがある。
もっと精密化すれば分かるかもしれない。
しかし、等しい場合はいつまで精密化しても「違い」は出ない。

だから比較器を書こうとすると、

```text
分離が見えたら strict
分離が見えなければもっと精密化
また見えなければもっと精密化
...
```

となる。

等しい場合や、差が極端に小さい場合、停止する保証がない。

これが decidable comparison の難しさじゃ。

## 4. DkMath では totality は閉じた

DkMath では totality は閉じている。

```text
左分離があるなら x ≤ y
左分離がないなら y ≤ x
```

という証明がある。

しかしこれは「計算機がいつ左分離の有無を判定できるか」とは別問題。

`¬ ∃ n, LeftSeparatedAt x y n` のような否定は、数学的には使える。
だが、計算機がそれを有限時間で確認できるとは限らない。

ここが Prop と algorithm の違いじゃ。

## 5. Lean での意味

Lean では命題として、

```lean
x ≤ y ∨ y ≤ x
```

を持つことと、

```lean
Decidable (x ≤ y)
```

を持つことは違う。

`Decidable (x ≤ y)` は、実際に

```lean
isTrue proof
```

または

```lean
isFalse proofOfNot
```

を返せるという意味じゃ。

つまり、Lean 的には、

```text
証明できる
```

と

```text
判定できる
```

は別。

`LinearOrder` は、便利な `min`、`max`、比較分岐、順序 API と結びつくため、環境によって decidable な比較や equality を要求する。
だから `DkNNRealQ` の core に直接 `LinearOrder` を入れると、「比較が計算できる」ような顔をしてしまう。

それはまだ保証していない。

## 6. DkMath 的な言い方

DkMath 風に言うなら、こうじゃ。

```text
totality:
  Big 内部では必ず向きが閉じる

decidable comparison:
  有限観測段階で、その向きを必ず見つけられる
```

いま証明済みなのは前者。

後者はまだ未実装。

つまり、

```text
宇宙の中では向きが決まっている
```

ことと、

```text
有限時間でその向きを観測できる
```

ことは違う。

これはかなり重要じゃ。

## 7. なぜ `PartialOrder + Std.Total` に留めるのか

だから現在の設計は正しい。

```text
PartialOrder:
  順序の基本法則

Std.Total:
  任意の二点は比較可能であるという数学的事実

IsStrictOrderedRing:
  strict order と演算の相性

LinearOrder:
  まだ入れない
```

`LinearOrder` を入れない理由は、DkNNRealQ の比較が「停止する判定器」として構成されていないからじゃ。

必要なら局所的に classical を使って、

```lean
classical
```

で比較を選ばせることはできる。
しかしそれは計算可能 core ではなく、非構成的な選択になる。

## 8. 一文まとめ

$$
\boxed{\text{decidable comparison とは、大小の向きを有限時間で判定して返す計算手続きのこと。}}
$$

そして、

$$
\boxed{\text{DkNNRealQ は total だが、まだ decidable comparison は持たない。}}
$$

DkMath 的には、

```text
Big 内部の向きは必ず閉じる。
しかし、その向きを有限観測で必ず決定する比較回路は、まだ作っていない。
```

という状態じゃ。
