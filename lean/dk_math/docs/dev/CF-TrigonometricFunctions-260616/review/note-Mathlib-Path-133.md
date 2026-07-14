# Note: No.133 checkpoint

## Lean+Mathlib の `Path` とは何か

Lean+Mathlib における `Path x y` は、数学的には **点 \(x\) から点 \(y\) へ向かう連続経路** じゃ。

ただし Lean では、単なる関数ではなく、

```lean
Path x y
```

という **端点を型に持つ構造体** として定義されている。

Mathlib の説明では、`Path x y` は単位区間 \(I=[0,1]\) から位相空間 \(X\) への連続写像で、\(0\) を \(x\) に、\(1\) を \(y\) に送るもの、とされている。([fust.frourio.com][1])

## 定義の中身

概念的にはこうじゃ。

```lean
structure Path {X : Type _} [TopologicalSpace X] (x y : X)
    extends C(unitInterval, X) where
  source' : toFun 0 = x
  target' : toFun 1 = y
```

実際の Mathlib 定義でも、`Path` は `C(unitInterval, X)`、つまり単位区間から \(X\) への連続写像を拡張し、さらに `source'` と `target'` を持つ構造として定義されている。

つまり `Path x y` は三つを持つ。

```text
toFun:
  unitInterval → X

continuous_toFun:
  toFun が連続である証明

source' / target':
  始点と終点が指定点に一致する証明
```

ここが重要じゃ。
Lean の `Path` は「動く点列」ではなく、**連続写像と端点証明を束ねた dependent object** なのじゃ。

## `Path` は関数として使える

`Path x y` は `FunLike` instance を持つので、`γ : Path x y` があれば、

```lean
γ t
```

と書ける。

これは \(t\in[0,1]\) における経路上の点を意味する。

また `Path.ext` があり、二つの path は underlying function が等しければ path として等しい、と言える。Mathlib でも `Path.ext` は、関数として等しいことから path equality を得る定理として用意されている。

DkMath でよく使っている、

```lean
apply Path.ext
funext t
```

はこれじゃ。

意味は、

```text
path 構造体全体を比較するのではなく、
各 t で値が同じことを示して path equality にする
```

ということ。

## `source` と `target`

`γ : Path x y` に対して、

```lean
γ.source
γ.target
```

がある。

意味はそれぞれ、

```lean
γ 0 = x
γ 1 = y
```

じゃ。

Mathlib でも `Path.source` と `Path.target` は simp theorem として用意されている。

DkMath の文脈で言えば、closed path の source/target 比較をやっているときは、この `Path.source` / `Path.target` が効いている。

## `Path.trans` は経路の連結

`Path.trans` は、二つの path をつなぐ操作じゃ。

```lean
p : Path x y
q : Path y z
```

があれば、

```lean
p.trans q : Path x z
```

になる。

数学的には、前半 \(0\le t\le 1/2\) で \(p\) を歩き、後半 \(1/2\le t\le 1\) で \(q\) を歩く。Mathlib の定義説明でも、第一経路を \([0,1/2]\)、第二経路を \([1/2,1]\) に配置する concatenation と説明されている。

ここが DkMath の今の苦戦点でもある。

4 本をつなぐと、

```lean
(((p0.trans p1).trans p2).trans p3)
```

や、

```lean
p0.trans (p1.trans (p2.trans p3))
```

のように、入れ子構造が出る。

数学では同じ「四本を順に歩く path」に見えても、Lean では `Path.trans` の入れ子の形が違うと、定義上は別の項に見えることがある。

## `Path.map` は連続写像による押し出し

`Path.map` は、連続写像 \(f:X\to Y\) で path を送る操作じゃ。

```lean
γ : Path x y
hf : Continuous f
```

があれば、

```lean
γ.map hf : Path (f x) (f y)
```

になる。

Mathlib の定義でも、`Path.map γ hf` は連続写像 \(f\) による path の像として説明され、underlying function は \(f \circ γ\) になる。

DkMath の状況では、

```lean
shiftedCyclicChartEdgePath i
```

を

```lean
shiftedSemanticCyclicChartEval hcore z
```

で `map` している。

数学的には、

```text
quotient chart 上の edge path を
semantic boundary 上の edge path へ押し出す
```

という操作じゃ。

さらに Mathlib には、

```lean
Path.map_trans
```

があり、

```lean
(p.trans q).map hf = (p.map hf).trans (q.map hf)
```

を言える。Mathlib docs にも `Path.map_trans` は、連結してから map することと、map してから連結することが一致する theorem として載っている。

これが、いま欲しい「貼ってから写す」と「写してから貼る」の基本補題じゃ。

## `Path.cast` は端点ラベルの付け替え

`Path.cast` は、path の実際の値を変えずに、始点・終点の型だけを等式で付け替える操作じゃ。

```lean
γ : Path x y
hx : x' = x
hy : y' = y
```

があれば、

```lean
γ.cast hx hy : Path x' y'
```

になる。

Mathlib の説明でも、`Path.cast` は `x' = x` と `y' = y` があるとき、`Path x y` を `Path x' y'` として扱う操作で、underlying function は元の `γ` のままじゃ。

DkMath での使い方はまさにこれ。

```text
observed quotient endpoint
  と
finite level endpoint
  は値として同じ

しかし Lean 上の型表現が違う

だから Path.cast で endpoint label を付け替える
```

ここで起きる問題が、**証明項の違い** じゃ。

同じ等式 \(x'=x\) を表す証明が複数あると、`Path.cast` の中身としては別の proof term が入る。
数学的には同じ endpoint なのに、Lean の式としては違って見えることがある。

そこで DkMath 側で、

```lean
shiftedPath_cast_proof_irrel
```

を作っているわけじゃ。

これは、

```text
cast に使う等式証明が違っても、
path の値は変わらない
```

という補題じゃな。

## いま DkMath で詰まっている理由

DkMath の現在の状況を `Path` 用語で言うと、こうじゃ。

```text
1:
  quotient chart 上に 4 本の Path がある。

2:
  それらを seam equality で Path.trans して closed path にする。

3:
  semantic evaluation で Path.map する。

4:
  map した path の endpoint を Path.cast で finite endpoint API にそろえる。

5:
  それが observed semantic four-edge path と等しいことを示したい。
```

数学的には自然に、

$$
F(p_0 * p_1 * p_2 * p_3)
$$

と、

$$
F(p_0) * F(p_1) * F(p_2) * F(p_3)
$$

は一致するはずじゃ。

しかし Lean では、

```text
Path.trans の入れ子構造
Path.cast の endpoint equality
seam proof の証明項
```

が全部項として現れる。

だから、単に `simp` だけでは閉じない。

## なぜ edge-level は通ったのか

single edge では、構造が単純じゃ。

```lean
((edge.map hf).cast ... ...)
```

と、

```lean
observedEdge
```

は、どちらも underlying function が同じになる。

だから、

```lean
apply Path.ext
funext t
rfl
```

で閉じた。

これは、1 本の path なら `Path.trans` の入れ子も seam proof もないからじゃ。

## なぜ four-edge はまだ重いのか

four-edge では、

```lean
shiftedFourPathConcatWithSeams
```

の内部に、

```lean
Path.trans
Path.cast
Path.trans
Path.cast
Path.trans
Path.cast
```

のような構造が入る。

さらに map した後は、seam equality が

```text
quotient seam を semantic evaluation で写した証明
```

になる。

一方、canonical observed via-edge path では seam equality が

```text
finite endpoint API 側で用意した seam 証明
```

になる。

この二つは値として同じ端点一致を言っているが、proof term は違う。

したがって、次に必要なのは、

```lean
shiftedFourPathConcatWithSeams_congr_cast_irrel
```

のような補題じゃ。

意味は、

```text
四つの component path がそれぞれ等しいなら、
seam proof が違っていても、
四本連結 path 全体は等しい
```

というもの。

## DkMath 的な直感

ぬしの言葉で言えば、`Path` は **歩き方そのもの** じゃ。

`Path.trans` は、歩き方をつなぐこと。
`Path.map` は、歩いた軌跡を別の観測空間へ写すこと。
`Path.cast` は、同じ場所なのに名前が違う端点ラベルを貼り替えること。

いまやっているのは、

```text
先に四本を貼ってから観測する

各一本を観測してから四本を貼る
```

この二つが同じ歩き方であることの証明じゃ。

数学の紙では一行。
Lean では、端点と貼り合わせの証明項まで全部見える。
だから「接合部のラベル合わせ」が本当の作業になっている。

## まとめ

Lean+Mathlib の `Path x y` は、

```text
unitInterval から X への連続写像
始点が x である証明
終点が y である証明
```

を束ねた構造体じゃ。

主要操作はこう。

```text
Path.refl:
  定数 path

Path.symm:
  逆向き path

Path.trans:
  path の連結

Path.map:
  連続写像による path の押し出し

Path.cast:
  endpoint equality による始点・終点ラベルの付け替え

Path.ext:
  点ごとの値一致から path equality を得る
```

DkMath の現在の課題は、`Path.map`、`Path.trans`、`Path.cast` が絡む四本連結 path の正規化じゃ。
つまり、数学的には自然な「連続写像は経路の貼り合わせを保つ」を、Lean の dependent endpoint bookkeeping つきで証明している段階じゃな。

[1]: https://fust.frourio.com/docs/Mathlib/Topology/Path.html "Mathlib.Topology.Path"
