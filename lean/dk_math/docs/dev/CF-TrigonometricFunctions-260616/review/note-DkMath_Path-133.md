# Note: No.133 checkpoint

## DkMath.Path

## そうじゃな

かなり正確に言えば、今は **DkMath 側の数学内容を、Mathlib の `Path` 規格に正規化して載せている作業** じゃ。

数学的にはもう、

```text id="g4r9nz"
四本の辺を貼る
その貼ったものを評価写像で送る

各辺を評価写像で送る
それを四本貼る
```

この二つは同じ、というところまで見えている。

ただし Mathlib の `Path` は、

```text id="viy4i0"
連続写像
始点証明
終点証明
貼り合わせ証明
endpoint cast 証明
```

を全部きっちり型に持つ。
だから今は、その「規格」に合わせて、DkMath の経路構造を包装し直している。

## たとえるなら

DkMath 側では、もう橋は架かっている。

```text id="s59itp"
edge 0 は対応する
edge 1 は対応する
edge 2 は対応する
edge 3 は対応する
seam も値として合っている
```

しかし Mathlib の `Path` に提出するには、

```text id="x9hvdw"
どの証明で seam を貼ったか
どの順番で Path.trans したか
どの cast で endpoint を合わせたか
```

まで一致・正規化しなければならない。

だから、いまは数学を新しく発見しているというより、

**発見済みの構造を、Lean/Mathlib が検査できる標準形式へ変換している**

という段階じゃ。

## でも単なる事務作業ではない

ここが面白いところで、これはただの「Mathlib 都合」でもない。

この作業で得ている補題は、今後かなり使える。

```text id="hfc7t4"
Path.map と Path.cast の互換性
Path.cast の proof irrelevance
four-edge concatenator の標準包装
mapped edge と observed edge の一致
```

これらは、今後の DkMath の path / boundary / level-set / quotient chart 系で再利用できる。

つまり今は、

```text id="yi5hyi"
SemanticCF2D のためだけの修正
```

ではなく、

```text id="qrl2m4"
DkMath が Mathlib の Path 世界で自由に動くためのアダプタ層
```

を作っているとも言える。

## 現状の本質

いまの作業の本質はこれじゃ。

```text id="ynnhs0"
DkMath の pre-geometric な四相閉路
  を
Mathlib の dependent Path API
  に適合させる
```

そして、適合が終わると、

```text id="pl8mfs"
quotient chart 上の閉路
semantic boundary 上の閉路
finite four-level path
```

が、すべて同じ `Path` 言語で比較できるようになる。

ここまで行くと、次の上位層、たとえば refinement、normalization、limit、pre-geometric \(\pi\) への橋が非常に扱いやすくなる。

## 賢狼の一言

ぬしの言う通り、今は **Mathlib の都合に合わせている**。
ただし、それは屈服ではなく、**DkMath の構造を Mathlib の共通言語に翻訳している** ということじゃな。

言い換えると、

```text id="xqzf5u"
DkMath の森で見つけた道を、
Mathlib の測量図に正確に描き込んでいる
```

そんな段階じゃ。

---

## その通りじゃ

うむ。かなり正確に言えば、**Mathlib の `Path` を直接置き換える** というより、まずは DkMath 内部で

```text id="my9y5p"
Path の標準包装形式
Path の正規化規格
Path の構成 DSL
Path への bridge layer
```

を作れる、ということじゃな。

そして、それが十分に安定すれば、DkMath 内部では Mathlib の `Path.trans` / `Path.cast` を直接いじらず、DkMath 側の規格化された path 構造を主役にして、最後に Mathlib `Path` へ落とす、という設計が可能になる。

## いま見えている問題

Mathlib の `Path` は汎用性が高い。
しかし、今回のような構造では少し重い。

```text id="r32jae"
endpoint が型に入る

seam equality が必要になる

Path.trans の入れ子が項として残る

Path.cast の証明項差が邪魔になる

map / trans / cast の可換性を毎回整理する必要がある
```

これは Mathlib が悪いというより、Mathlib の `Path` が非常に一般的な位相空間上の経路を扱うための規格だからじゃ。

DkMath では、もっと構造が決まっている。

```text id="pyhdhz"
有限個の edge

明示的な seam

保存境界 level-set

semantic evaluation

canonical via-edge packaging
```

だから、DkMath 専用の正規形を持てる。

## 候補になるもの

将来的には、こういう DkMath 側の構造が考えられる。

```lean id="rruc80"
structure DkPathChain where
  vertices : ...
  edges : ...
  seams : ...
  closed : ...
```

あるいは、今回の four-edge に近い形なら、

```lean id="oyztm0"
structure FourEdgePathPackage where
  p0 : Path a0 b0
  p1 : Path a1 b1
  p2 : Path a2 b2
  p3 : Path a3 b3
  seam01 : b0 = a1
  seam12 : b1 = a2
  seam23 : b2 = a3
  seam30 : b3 = a0
```

そして、この構造に対して、

```text id="em5d1y"
map

concat

toPath

q2 preservation

endpoint theorem

congruence theorem
```

を整備する。

こうすれば、普段は `Path.trans` の入れ子や `Path.cast` の証明項を触らずに済む。
最後に必要なときだけ、

```lean id="zm0ife"
toPath : DkPathChain → Path source target
```

で Mathlib の `Path` に変換する。

## 置き換えるなら「内部表現」から

一番現実的なのは、Mathlib の `Path` そのものを置き換えるのではなく、DkMath 内部でこうすることじゃ。

```text id="y741my"
外部境界:
  Mathlib Path

DkMath 内部:
  DkPathPackage / DkPathChain / FourEdgePathPackage

bridge:
  toPath
  map_toPath
  concat_toPath
  q2_toPath
```

つまり、Mathlib と接続するときは `Path` を使う。
しかし、DkMath の構成や変換は DkMath 専用の正規化構造で行う。

これはかなり良い設計じゃ。

## なぜ強いか

今回の苦労から、すでに分かったことがある。

```text id="xqbd1p"
edge 単体の意味論は簡単に通る

問題は four-edge packaging

特に seam proof と cast proof の管理が重い
```

ならば、DkMath 側では seam proof を直接 `Path.cast` の中に埋め込むのではなく、構造体のフィールドとして保持する。

そして `toPath` の時だけ `Path.cast` に変換する。
こうすれば、普段の theorem は構造体レベルで書ける。

## 数学的には何か

数学用語で言えば、これは **path の合成構造を自由構成として先に持ち、あとで位相的経路へ実現する** という設計じゃ。

```text id="j06uvs"
combinatorial path data:
  edge と seam の有限データ

realized topological path:
  unitInterval から空間への連続写像
```

つまり、

```text id="oqhhr4"
経路の組合せ構造
  ↓ realization
Mathlib Path
```

という二層に分ける。

これは DkMath らしい。
見た目の path を先に置くのではなく、**edge・seam・保存境界という観測可能な構造** を先に置き、あとで `Path` として実現する。

## 今回の成果の意味

だから、今やっている `shiftedFourPathConcatWithSeams` 周辺の整備は、単なる場当たり補題ではない。

これは将来の

```text id="fc2q7g"
DkMath.PathPackage
DkMath.PathChain
DkMath.SemanticPath
DkMath.BoundaryPath
```

の原型になり得る。

いま作っている theorem 群は、その設計要件を洗い出している。

```text id="vyebku"
必要なもの:
  endpoint relabel
  seam alignment
  map compatibility
  trans compatibility
  cast proof irrelevance
  edge-level congruence
  chain-level congruence
```

これらが揃えば、DkMath 側の path calculus ができる。

## ただし注意点

Mathlib 本体の `Path` を置き換えるのは、かなり別問題じゃ。

Mathlib の `Path` は、一般の topology API、path connectedness、homotopy、fundamental group など、多くの定理と接続している。
だから上流の `Path` を置き換えるには、非常に広い互換性が必要になる。

現実的には、

```text id="i60ej7"
Mathlib Path:
  標準出力形式

DkMath PathPackage:
  内部構成形式

bridge:
  DkMath PathPackage → Mathlib Path
```

がよい。

## 賢狼の見立て

ぬしの言う通り、規格統一が進めば、DkMath 内部では `Path` の直接操作を置き換える候補になり得る。

ただし「Mathlib の `Path` を不要にする」のではない。
むしろ、

```text id="jiuk31"
Mathlib Path に提出する前の、
DkMath 標準中間表現
```

になる。

これはかなり強い。

今は Mathlib 規格に合わせるために苦労している。
だが、その苦労を抽象化すれば、次からは DkMath 規格で path を組み立て、最後に Mathlib 規格へ変換できる。

つまり今回の作業は、

```text id="jqnkb9"
Path を使う作業
```

から、

```text id="m1q8xi"
Path を生成する規格を作る作業
```

へ変わりつつある。

これは、DkMath.Analysis のかなり重要な基盤になり得るぞ。
