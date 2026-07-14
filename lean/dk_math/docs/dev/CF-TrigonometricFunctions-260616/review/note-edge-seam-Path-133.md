# Note: No.133 checkpoint

edge, seam
Path.trans, Path.cast

## 現状の数学的な言い換え

うむ。いまの状況を数学用語で言うなら、これは **貼り合わせ空間上の経路を、連続写像で押し出したとき、押し出しと貼り合わせが可換するかを証明している段階** じゃ。

もう少し短く言えば、

**「経路の貼り合わせ」と「意味論的評価写像」の自然性を証明している。**

## 登場している数学対象

いま扱っているものは、だいたい次の構図じゃ。

```text id="zx2rac"
quotient chart space:
  4 本の区間 edge を seam で貼り合わせた巡回チャート

semantic boundary space:
  Vec.q2 z が固定された level-set

semantic evaluation:
  quotient chart space から semantic boundary space への連続写像

path:
  quotient chart 上の closed four-edge traversal
```

数学用語では、

```text id="utwq58"
1. 位相空間
2. 商空間
3. 経路 Path
4. 経路の連結 Path.trans
5. 端点同一視 seam equality
6. 連続写像による経路の pushforward / map
7. level-set subtype
```

を同時に扱っている状態じゃ。

今回の報告では、quotient edge path を descended semantic evaluation で map し、endpoint を finite API へ relabel すると、対応する observed semantic edge path と一致する edge-level bridge が Lean で確立されている。

## いま証明できていること

数学的には、まず各 edge \(e_i\) について、次が証明された。

$$
\operatorname{Eval}_z \circ e_i \simeq \widetilde e_i
$$

ここで、

```text id="w2g0ez"
e_i:
  quotient chart 側の i 番目の edge path

Eval_z:
  semantic evaluation

\widetilde e_i:
  fixed-boundary 側の observed semantic edge path
```

じゃ。

つまり、単一の辺については、

```text id="iuo0kp"
先に quotient edge を歩いてから評価する
```

ことと、

```text id="i2cosz"
最初から semantic boundary 上の対応 edge を歩く
```

ことが一致している。

これは、数学的には **edge ごとの自然性** が成立した、ということじゃ。

## まだ残っていること

残っているのは、4 本を seam で貼った closed path 全体についての可換性じゃ。

欲しい主張は、概念的にはこれ。

$$
\operatorname{Eval}_z(e_0 * e_1 * e_2 * e_3) = \operatorname{Eval}_z(e_0) * \operatorname{Eval}_z(e_1) * \operatorname{Eval}_z(e_2) * \operatorname{Eval}_z(e_3)
$$

ここで \(*\) は経路の連結、つまり `Path.trans` に対応する。

数学的にはかなり自然な式じゃ。
連続写像は経路を経路に送り、経路の連結とも可換する。

ただし Lean では、これが単なる一行では終わらない。

理由は、4 本の edge を貼るときに、

```text id="apd9yq"
edge 0 の終点 = edge 1 の始点
edge 1 の終点 = edge 2 の始点
edge 2 の終点 = edge 3 の始点
edge 3 の終点 = edge 0 の始点
```

という seam equality が入るからじゃ。

そして `Path.cast` は、この equality proof を型の中で使う。

## 本質的な障害

数学的障害はもうほぼ無い。
残っているのは **証明項の整列** じゃ。

いま起きているのはこう。

```text id="f9gmee"
quotient seam を semantic evaluation で写した equality proof

finite boundary 側で既に持っている seam equality proof
```

この二つは、値としては同じ seam を言っている。

しかし Lean から見ると、証明の作り方が違うため、`Path.cast` の中で別物に見えることがある。

だから、現在の問題は数学的には、

**同じ端点同一視を表す異なる証明項による cast は、経路を変えない**

という補題を使って、貼り合わせの証明項差を吸収する段階じゃ。

このために、

```lean id="wa2zbo"
shiftedPath_cast_proof_irrel
```

が用意されている。

これは数学的には **証明無関係性**、または **同じ等式証明による transport の不変性** に近い役割じゃ。

## 圏論っぽく言うなら

かなり圏論的に言えば、いま証明したいのはこうじゃ。

```text id="vgathw"
Path construction:
  位相空間から path category 的な構造を作る

continuous map:
  path を pushforward する functor 的操作

claim:
  pushforward preserves composition of paths
```

つまり、

```text id="yml6tz"
F(p ⋅ q) = F(p) ⋅ F(q)
```

を 4 本連結に拡張したい。

ただし Lean の `Path` は端点を型に持つ dependent object なので、通常の関数合成よりも endpoint transport が重い。
その endpoint transport が、いまの `Path.cast` と seam proof alignment の正体じゃ。

## ホモトピー論っぽく言うなら

これはまだホモトピー同値を扱っているわけではない。
もっと手前の話で、**同じ parametrized path として等しいか** を証明している。

つまり、

```text id="mrawkq"
homotopic:
  連続変形で同じ

path equality:
  Lean の関数として同じ
```

いま狙っているのは後者じゃ。

だから難度が上がる。
数学の紙の上では「同じ貼り合わせ」と済ませるところを、Lean では `Path.trans` の入れ子構造、`Path.cast` の endpoint equality、proof term の違いまで処理する必要がある。

## DkMath 的な意味

DkMath 的に言えば、現状はこうじゃ。

```text id="v2du68"
pre-geometric chart:
  まだ円や角度を前提にしない 4 相チャート

semantic evaluation:
  chart 上の観測を fixed-q2 境界へ降ろす写像

edge-level:
  各辺は正しく fixed-q2 境界の observed edge になる

four-level:
  4 辺を貼り合わせた閉路全体でも同じことを示したい
```

ここで重要なのは、まだ Euclidean な円周や角度を使っていないことじゃ。
いまやっているのは、純粋に

```text id="n2gkhj"
4 相の貼り合わせ構造
保存境界 level-set
連続評価写像
経路連結の自然性
```

だけで閉路を作る作業じゃ。

## 現在の達成度

数学的に見れば、到達度はこうじゃ。

```text id="pi1n7x"
局所:
  各 edge の評価写像との可換性は証明済み

端点:
  seam の値レベル一致は証明済み

型補正:
  endpoint cast の proof irrelevance は準備済み

大域:
  4 本連結した closed path 全体の可換性が残っている
```

つまり、局所データは全部そろった。
残るのは、それを大域的な closed path equality へ昇格する補題じゃ。

## 次に必要な数学的補題

次に必要なのは、数学的には次の形じゃ。

**補題名の意味**

```text id="rwbrbe"
four-edge concatenator は、edge ごとの等式と seam proof の違いを吸収して、closed path 全体の等式を返す。
```

Lean 名で言えば、候補はこう。

```lean id="izyu1b"
shiftedFourPathConcatWithSeams_congr_cast_irrel
```

または、

```lean id="d6o5io"
shiftedFourPathConcatWithSeams_map
```

数学的意味は、

$$
F(p_0 * p_1 * p_2 * p_3) = F(p_0) * F(p_1) * F(p_2) * F(p_3)
$$

ただし seam の証明項差は無視してよい、というものじゃ。

## まとめ

現在の状況を一言で言うと、

**4 本の辺を持つ商チャート上の閉路を、保存境界の level-set へ連続写像で押し出すとき、辺ごとの押し出しは証明済み。残るのは、その押し出しが 4 本の貼り合わせ構造全体と可換することを、Lean の dependent endpoint bookkeeping 込みで証明する段階。**

これはかなり終盤じゃ。

数学的障害ではなく、形式化上の境界貼り合わせ補題の整備段階に入っている。
賢狼の言葉で言えば、もう「橋板」は全部そろった。今は、その橋板を一本の橋として固定する **接合金具の定理** を作っているところじゃ。
