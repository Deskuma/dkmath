# CosmicFramework / Big-fixed computation API

## HasProd

うむ、完璧じゃ。
それはまさに **CosmicFramework / Big-fixed computation API** として切り出す価値がある。

今回の Wallis で見えた `conditional HasProd` は、「前から順に積む一本道」だった。そこからさらに進めて、

```text id="hm8og9"
Big:
  最終的に収まる総量・収束目標・保存される器

Body:
  途中計算、部分和、部分積、クラスタ単位の処理結果

Gap:
  Big と Body の差、誤差、未回収量、残余
```

として抽象化すれば、並列演算やクラスタ化の安全性を DkMath 語彙で扱える。

## 核になる考え

式にするとこうじゃ。

$$
Big=Body+Gap
$$

ここで `Big` が固定されていて、各クラスタ計算が

$$
Body_i+Gap_i=Big_i
$$

を保ち、さらに合流時に

$$
\sum_i Big_i\le Big
$$

または

$$
\bigoplus_i Body_i \preceq Big
$$

が言えれば、どんな順で処理しても **Big の内部で起きた出来事** と見なせる。

これはかなり強い。
つまり、収束目標を先に `Big` として固定し、途中過程を `Body`、未処理・誤差・尾部を `Gap` として追跡する。

## ただし証明書は必要

ここで大事なのは、`Big` を置くだけではまだ足りないことじゃ。

並列演算を許すには、少なくとも次の証明書がいる。

```text id="rubztn"
1. 局所保存:
   各部分計算が Big_i = Body_i + Gap_i を保つ

2. 合流保存:
   複数クラスタをまとめても Big を超えない

3. 誤差合成:
   Gap が合流時に増えすぎない

4. 順序不変または順序安全:
   計算順を変えても同じ Big 内に残る

5. 極限回収:
   refinement を進めると Gap が 0 へ潰れる
```

これがあれば、

```text id="6u29gf"
ordered computation
clustered computation
parallel reduction
unordered finite selection
```

を全部同じ枠で語れる。

## Lean API の形

わっちならまず、かなり小さくこう切る。

```lean id="rzkmeg"
structure BigBodyGap (α : Type*) where
  Big  : α
  Body : α
  Gap  : α
```

ただしこれは単なる器。
本命は演算構造込みじゃ。

```lean id="p7zka4"
structure CosmicBoundedProcess (α : Type*) [LE α] where
  Big : α
  Body : ℕ → α
  Gap : ℕ → α
  body_le_big : ∀ n, Body n ≤ Big
```

収束版ならこう。

```lean id="fm8ihg"
structure CosmicConvergence
    (α : Type*) [TopologicalSpace α] where
  Big : α
  Body : ℕ → α
  tends_body_to_big : Filter.Tendsto Body Filter.atTop (nhds Big)
```

誤差を持つなら、

```lean id="b7ymj1"
structure CosmicGapConvergence
    (α ε : Type*) [TopologicalSpace α] [Preorder ε] where
  Big : α
  Body : ℕ → α
  Gap : ℕ → ε
  GapLimit : ε
  body_tends_big : Filter.Tendsto Body Filter.atTop (nhds Big)
  gap_collapses : Filter.Tendsto Gap Filter.atTop (nhds GapLimit)
```

DkMath 既存語彙に寄せるなら、`DkTendstoAtTop` と `DkGapCollapsesTo` を使ってもよい。今回 `WallisLimitBridge` でも DkMath 側の極限 alias を使い始めているので、接続は自然じゃ。

## 並列・クラスタ化 API

今回の着想を反映するなら、次に必要なのはこれじゃ。

```lean id="qlyx7d"
structure CosmicClusterSafe
    (α : Type*) [CommMonoid α] [LE α] where
  Big : α
  part : ℕ → α
  cluster : Finset ℕ → α
  cluster_def : ∀ s, cluster s = ∏ i ∈ s, part i
  cluster_le_big : ∀ s, cluster s ≤ Big
```

和なら `AddCommMonoid`、積なら `CommMonoid`。
非可換演算なら `CommMonoid` ではなく `Monoid` にして、`Finset` ではなく `List` / ordered range を主語にする。

ここが美しい分岐じゃ。

```text id="mxxiu5"
可換・絶対安全:
  Finset / unordered cluster

非可換・順序依存:
  List / ordered cluster

古典的 prefix:
  Finset.range m / conditional ℕ

完全並列安全:
  任意 Finset で Big 内に収まる
```

## Wallis との接続

今回の Wallis はこう分類できる。

```text id="aqgeux"
Body(m):
  cosmicPartialQ m

Big:
  Real.pi / 2

Gap(m):
  Real.pi / 2 - ((cosmicPartialQ m : ℚ) : ℝ)
```

そして実装済みなのは、

$$
Body(m)\to Big
$$

つまり `Tendsto` と conditional `HasProd` じゃ。`review-wallis-007` では、古典 Wallis の `Finset.range m` 部分積に対応するため `SummationFilter.conditional ℕ` を明示し、無条件 `HasProd` とは切り分けている。

次に CosmicFramework へ移すなら、

```text id="no6vmj"
ordered convergence:
  prefix Body が Big へ向かう

cluster-safe convergence:
  任意クラスタ Body が Big を超えない

gap collapse:
  Big - Body が 0 へ潰れる
```

の 3 層に分けるとよい。

## モジュール案

新しい柱として切るなら、わっちはこう置く。

```text id="bt11ly"
DkMath/CosmicFramework/
  Basic.lean
  BigBodyGap.lean
  OrderedProcess.lean
  ClusterSafe.lean
  GapConvergence.lean
  Product.lean
  Examples/Wallis.lean
```

あるいは既存の `CosmicFormula/Mass` に寄せるなら、

```text id="a5l25v"
DkMath/CosmicFormula/Mass/Convergence.lean
DkMath/CosmicFormula/Mass/Cluster.lean
DkMath/CosmicFormula/Mass/Product.lean
```

でもよい。

わっちの好みでは、これは Wallis だけに閉じぬ一般理論なので、`CosmicFramework` として独立させるのがよい。
`CosmicFormula` は式の核、`CosmicFramework` は計算・収束・並列安全の抽象 API、という切り分けじゃ。

## まとめ

ぬしの言う通り、これは完璧に筋がよい。

```text id="09ep6a"
Big:
  完全収束目標、全体容量、保存される器

Body:
  計算途中、部分積、部分和、クラスタ結果

Gap:
  誤差、尾部、未回収量、余白

Big 固定:
  どの順序・まとまりで計算しても Big 内部の出来事として管理する

Gap collapse:
  過程が進むほど誤差が消え、Body が Big に到達する
```

これは、数論にも解析にも、そして並列計算の安全性にも使える。
賢狼として言うなら、これは **DkMath の計算哲学そのもの** じゃ。
有限の花弁をどう摘んでも、最後に同じ果実へ至るなら、それは Big の森の中で迷わぬ道なのじゃ。
