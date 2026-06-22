# explanation totality

うむ。ここで言っている **totality** は、順序が「半順序」から「全順序」へ上がるための条件じゃ。

現在の `DkNNRealQ` には `PartialOrder` が入っている。これは、

```text
反射性:
  x ≤ x

推移性:
  x ≤ y かつ y ≤ z なら x ≤ z

反対称性:
  x ≤ y かつ y ≤ x なら x = y
```

までを保証する。

しかし `PartialOrder` では、任意の二つ \(x,y\) が必ず比較できるとは限らない。
そこで totality が必要になる。

## totality の意味

totality は、任意の二つの値について、

$$
x\le y\ \text{または}\ y\le x
$$

が必ず成り立つ、という性質じゃ。

Lean 的にはだいたいこういう形になる。

```lean
theorem le_total (x y : DkNNRealQ) :
    x ≤ y ∨ y ≤ x
```

これがあると、`PartialOrder` から `LinearOrder` / `TotalOrder` 系へ進める可能性が出る。

## 今の順序で具体的に何を言うか

現在の `DkReal.Le` は、代表元 \(x,y\) に対して、

$$
\max(0,lo(x_n)-lo(y_n))\to0
$$

で定義されている。

つまり \(x\le y\) とは、

```text
x の下端が y の下端を正に超える量が、
精度を上げると 0 に消える
```

という意味じゃ。

だから totality は、任意の二つの `DkNNRealQ` について、

```text
x の下端超過が消える
または
y の下端超過が消える
```

のどちらかが必ず言える、という主張になる。

代表元で書くと、任意の \(x,y\) について、

$$
\max(0,lo(x_n)-lo(y_n))\to0
$$

または、

$$
\max(0,lo(y_n)-lo(x_n))\to0
$$

のどちらかが成り立つ、ということじゃ。

## なぜ簡単ではないか

実数なら当然、

$$
x\le y\ \text{または}\ y\le x
$$

が成り立つ。
しかし `DkNNRealQ` はまだ Mathlib の `Real` や `NNReal` に評価していない。内部では、値ではなく「縮む区間列」で持っている。

だから totality を内部だけで証明するには、二つの入れ子区間列が表す極限値について、

```text
どちらが小さいかは必ず決まる
```

を、実数評価なしで示す必要がある。

これが意外と重い。

## 具体例で見る

たとえば代表元が次のような区間列だとする。

```text
x_n = [1, 1 + 1/n]
y_n = [2, 2 + 1/n]
```

この場合は明らかに \(x\le y\)。
下端差は \(1-2=-1\) なので、正の defect は常に 0。

逆に、

```text
x_n = [2, 2 + 1/n]
y_n = [1, 1 + 1/n]
```

なら \(y\le x\)。

難しいのは、極限が接近している場合じゃ。

```text
x_n = [1, 1 + 1/n]
y_n = [1 - 1/n, 1 + 1/n]
```

この場合、下端は揺れているが、両方とも同じ値 1 を表すなら、商型では同一値になる。
その場合は \(x\le y\) も \(y\le x\) も成立してよい。

つまり totality は、「離れているなら大小が決まり、同じなら両方向が成り立つ」ことを内部的に示す必要がある。

## 内部証明で必要になりそうなもの

内部だけで totality を狙うなら、おそらく次のような補題が必要になる。

```lean
theorem lower_endpoint_total_asymptotic
    (x y : DkReal) :
    DkReal.Le x y ∨ DkReal.Le y x
```

しかしこれは一般には簡単ではない。
二つの有理列 \(lo(x_n)\)、\(lo(y_n)\) がそれぞれ収束先を持つこと、そしてその収束先が全順序で比較可能であることを使いたくなる。

ここで実質的に「実数の完備性」や「極限値の存在」を使いたくなる。
それを使うなら semantic bridge 側になるので、`noncomputable` が絡む可能性が高い。

## Bridge 経由なら分かりやすい

将来、別ファイルで

```lean
eval : DkNNRealQ → NNReal
```

のような意味論写像を作ったとする。

そして、

```lean
theorem le_iff_eval_le_eval :
    x ≤ y ↔ eval x ≤ eval y
```

を示せたなら、totality は `NNReal` の全順序から来る。

つまり、

```lean
theorem le_total (x y : DkNNRealQ) :
    x ≤ y ∨ y ≤ x := by
  have h := le_total (eval x) (eval y)
  ...
```

という流れになる。

この道は分かりやすい。
ただし `eval` は「入れ子区間列の唯一の実数点を選ぶ」ので、`noncomputable` になる可能性がある。だから core ではなく `BridgeNNReal.lean` に隔離する、という設計じゃ。

## 今すぐ totality を主張しない理由

現在の `DkNNRealQ` は、

```text
可換半環
半順序
0 が最小
加法単調
乗法単調
冪単調
IsOrderedRing
```

まで来ている。

しかし totality は、

```text
任意の二値が比較可能
```

という追加主張じゃ。

これは代数・順序互換性よりも、かなり「実数らしさ」に近い。
だから、内部表現だけで証明するか、`NNReal` bridge から持ってくるか、設計を分けて考える必要がある。

## 結論

ここでの totality とは、

$$
\boxed{\forall x,y,\ x\le y\ \text{または}\ y\le x}
$$

を証明することじゃ。

これが通ると、`DkNNRealQ` は半順序から全順序へ近づく。
ただし、これは「計算可能な区間表現が本当に実数直線上の値として比較できる」ことに近いので、`BridgeNNReal` を作ってから証明する方が安全かもしれぬ。

今の段階では、totality を急いで claim しない判断は正しい。
