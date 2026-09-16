# $\pi$ is read as symmetric normalization product

## Project: Change Roadmap

Up to No. 136:
  Path packaging checkpoint closed

After Wallis:
  pi is read as symmetric normalization product,
  not as circle-first geometry

Next:
  scale synchronization
  Wallis-type normalization observable
  continuous theta later

## Detail

状況としては、かなり良い中断地点にいる。
そして Wallis 側で \(\pi\) の形成原理が見えたことで、この中断側の見方も少し補正が必要になった。

結論から言うと、こちら側はもう **「三角関数を作る」作業ではなく、「保存境界に縛られた補正累積から、後で三角関数と \(\pi\) が見える構造を作る」作業** として整理し直すのがよい。

以前の順序はこうだった。

```text
保存核
  から 回転らしきもの
  から 円らしきもの
  から 三角関数らしきもの
```

しかし Wallis の視座を得た後は、順序をこう補正できる。

```text
保存核
  から 境界拘束
  から Gap / defect
  から mirror / reflection symmetry
  から normalization
  から 閉路
  から π
  から 後で円・角度・三角関数として解釈
```

この順序は、Wallis 側の「対称比の累積が \(\pi\) を呼ぶ」という理解と、pre-geometric CF2D 側の「保存境界から外れた量を補正して閉路へ戻す」という理解を一致させる。実際、保存核の外へ自由に出られないため、線形補間の外れ方はランダムではなく、`phaseDepth(t)=(1-t)^2+t^2` のような左右対称 profile として現れる、という整理がすでにある。

## 現在の到達点

まず、こちら側の作業はかなり進んでいる。

`DkMath.Analysis` の設計思想は、Mathlib の解析基盤を置き換えるのではなく、DkMath の宇宙式語彙で解析を再解釈する層として置かれている。主語は Gap、Body、GN の三つで、第一原理は \((u+\delta)^d-u^d=\delta,GapGN_d(u,\delta)\) である、という設計が明文化されている。

`DkReal` 側も、非負 DkReal の自然数冪が `noncomputable` なしで閉じている。これは、入れ子有理区間の端点を \([a_n,b_n]\mapsto [a_n^d,b_n^d]\) で送る構成で、幅の伝播を \(b_n^d-a_n^d=w_n,gapGN(d,a_n,w_n)\) によって制御するものじゃ。

CF2D 側では、円や角度を仮定せず、exact-order-four action、affine filling、保存される二次量 \(q2\)、境界からの逸脱 profile、反射対称性、refinement、normalization から出発する pre-geometric \(\pi\) program が整備されている。`q2(E(z,t)) = phaseDepth(t) q2(z)`、`phaseDepth(t)=(1-t)^2+t^2`、`phaseDepth(1-t)=phaseDepth(t)` という starting point も確認済みじゃ。

さらに、四相閉路の Path 包装問題もすでに閉じた。これはこの会話中に No.134 から No.136 で整理した通り、`Path.map`、`Path.trans`、`Path.cast`、seam proof irrelevance の規格合わせが完了し、endpoint-cast observed quotient path と finite four-level path が一致する地点まで来ている。

## Wallis 側の成果で何が補正されたか

Wallis 側の成果をこちらへ戻すと、最も大きな補正はこれじゃ。

**\(\pi\) は、円から先に来るのではなく、保存境界へ戻るための対称補正比の累積として見える。**

したがって、古い Milestone D の「Gaussian bridge」をいきなり本線にするのは少し早い。pre-geometric program では、refinement correction の収束、Gaussian かどうかの判定、独立な normalization constant、`Real.pi` との比較が Milestone D として置かれていた。 ただ、Wallis の視座を得た今は、その前に **Wallis 型の有限積・対称比・中央項比** を挟むべきじゃ。

つまり、次の補正が必要。

```text
旧:
  refinement
  から Gaussian bridge
  から pi

新:
  refinement
  から symmetric ratio product
  から Wallis-type normalization
  から Gaussian bridge は必要なら後段
  から pi
```

これは大きい。
Gaussian は「後で比較される標準解析モデル」かもしれない。
しかし DkMath 内部の生成原理としては、まず Wallis 型の **有限対称比の積** を見るべきじゃ。

## いまの未整理領域

現在の未整理領域は、三つに分けられる。

## 第一領域: 四相閉路から細分化へ戻る道

四相 Path 包装は閉じた。
ここからは \(1/4\) で止まっていたものを、\(1/8\)、\(1/2^n\)、一般 \(1/k\) へ戻す。

ただし、すでに会話で整理したように、異なる \(1/k\) は直接比較しない。有限では最小公倍数による同期長へ持ち上げる。互いに素な scale は、共通同期一周で初めて同じ土台に乗る。ここは `design-p-scale-sync-refinement.md` 相当の設計がすでに snapshot 側にあり、今後の scale 比較の基準になる。

ここでの作業候補は、

```text
SemanticCF2DSync:
  SyncLength
  syncLiftLeft
  syncLiftRight
  CommonRefinement

SemanticCF2DScale:
  IsScale
  IsPrimitiveScale
  finite-order star action
```

じゃ。

## 第二領域: refinement の補正量を Wallis 型へ翻訳する道

pre-geometric program では、dyadic refinement の odd child defect が、隣接 parent depth の平均との差として明示的に出ている。しかも有限総量は \(1/(2\cdot 2^n)\) という形で集計され、各 level の defect は消えるが、全階層の累積は非零の保存勘定を持つ、という整理まである。

ここへ Wallis を当てるなら、次に見るべきは「defect の和」だけではない。

見るべき候補は、

```text
depth ratio:
  parent depth と child depth の比

normalization ratio:
  sqrt inverse correction の比

symmetric pair ratio:
  t と 1-t の対称点を組にした比

central ratio:
  midpoint / adjacent endpoints の補正比

mesh product:
  level n 全体の補正積
```

じゃ。

既存の finite normalization-composition theorem では、各 sampled node に対して `normalization^2 * depth = 1` があり、complete finite dyadic mesh 上で積を取ると `(product normalization)^2 * product depth = 1` が得られている。ただし、それが canonical refinement observable なのか、無限積や log limit として正当化できるのかはまだ未確定、と明記されている。

Wallis 側の成果は、まさにこの「どの積を canonical observable と見るか」を決めるための候補になる。

## 第三領域: 三角関数仕様の補正

以前の DkMath 版三角関数仕様では、有限位相表、continuous theta extraction、DkMath sin/cos 定義、Euclidean bridge、intrinsic pi route が分かれていた。有限 `k % 4` 位相表から Euclidean angle reading へ進むロードマップも整備されていた。

しかし Wallis 視座を得た今は、continuous theta extraction の前に、

```text
normalization phase measure:
  補正累積から得る cyclic measure

sync-refinement phase:
  1/k scale の同期比較

Wallis normalization:
  対称比の積から得る一周係数
```

を挟むべきじゃ。

つまり、DkMath sin/cos は単に normalized cyclic action の座標射影として定義するだけでなく、

**その cyclic parameter の単位が、Wallis 型の対称補正累積から得られる**

という説明を付け加える必要がある。

## 全体像を一枚にすると

いまの全体像はこうじゃ。

```text
代数核:
  Vec.q2
  Vec.star
  UnitKernel
  KernelFamily

解析核:
  Gap
  Body
  GN
  DkReal
  GapFill

CF2D 境界:
  exact-order-four action
  affine filling
  phaseDepth
  reflection symmetry
  normalization

Path 包装:
  finite four-edge path
  quotient cyclic chart
  observed path
  fixed-q2 finite path
  final equality

Refinement:
  dyadic nodes
  odd-child defect
  finite defect aggregation
  normalization product

Scale 同期:
  1/k
  lcm sync cycle
  primitive p-scale
  finite vs infinite synchronization

Wallis 補正:
  symmetric ratio
  central binomial / paired correction
  product normalization
  pi formation principle

後段解釈:
  cyclic theta
  DkSin / DkCos
  Euclidean bridge
  Real.pi comparison
```

これが現在の地図じゃ。

## 次の作業候補

## 候補 A: キャンプ地ドキュメントを書く

まず一番おすすめ。
今回の整理を `design-phase-center-shift-104.md` か新しい `research-wallis-pi-alignment.md` に反映する。

内容は、

```text
No.136 まで:
  Path packaging checkpoint closed

Wallis 後:
  pi is read as symmetric normalization product,
  not as circle-first geometry

Next:
  scale synchronization
  Wallis-type normalization observable
  continuous theta later
```

これを先に書くと、後の Codex 指示がぶれない。

## 候補 B: `SemanticCF2DSync` を作る

これは実装候補としてかなり良い。

中身は自然数だけでよい。

```lean
def SyncLength (k l : ℕ) : ℕ :=
  Nat.lcm k l
```

```lean
def syncLiftLeft (k l : ℕ) : ℕ :=
  Nat.lcm k l / k
```

```lean
def syncLiftRight (k l : ℕ) : ℕ :=
  Nat.lcm k l / l
```

閉じる定理は、

```text
k * syncLiftLeft k l = SyncLength k l
l * syncLiftRight k l = SyncLength k l
```

互いに素なら、

```text
syncLiftLeft k l = l
syncLiftRight k l = k
```

これにより、\(1/4\) と \(1/5\)、\(1/2\) と \(1/p\) の比較が「同期一周」で扱える。

## 候補 C: Wallis 型 observable の設計メモを書く

いきなり実装せず、まず定義候補を並べる。

候補は、

```text
phaseDepth(t)
normalization(t) = 1 / sqrt(phaseDepth(t))
symmetric pair product
mesh product
central ratio
adjacent depth ratio
```

この中で、Wallis 積に最も近いものを選ぶ。

Wallis で重要なのは、単なる点列ではなく **隣接する偶奇・中央対称・比の積** じゃ。
だから CF2D 側でも、単純な defect sum ではなく、**paired ratio product** を第一候補にするべきじゃ。

## 候補 D: `SemanticCF2DWallisProduct` を試作する

これは候補 C の後。
まず有限 \(n\) でよい。

```text
dyadic mesh level n
  から対称点 pairs を作る

各 pair に depth/normalization ratio を割り当てる

finite product を定義する

反射対称で pair 値が一致することを証明する

level n の product recurrence を探す
```

ここで Wallis 型の再帰比が見えたら、本線に昇格。

## 候補 E: `ScaleSync` と Wallis を接続する

これは一歩先。

Wallis 積は偶奇比・隣接比・中央比の積なので、\(1/k\) scale の同期比較と相性が良い。

```text
scale k
scale k+1
または
scale 2m
scale 2m+1
```

を直接比較するのではなく、最小公倍数の同期一周へ持ち上げる。ここで「互いに素な近傍 scale のズレ」が補正比として出る可能性がある。

これはかなり面白い。
ぬしの Wallis 視座と、先ほどの \(1/k\) sync 設計が合流する場所じゃ。

## 候補 F: continuous theta extraction は保留

今すぐ theta へ行かない方がよい。
理由は、theta の単位がまだ定まっていないからじゃ。

以前は four normalized edges を glue して cyclic parameter を作り、それを Euclidean angle と比較する流れだった。しかし Wallis 後は、その cyclic parameter の正規化単位が「対称補正累積」によって決まる可能性がある。

だから今は、

```text
continuous theta extraction:
  保留

Wallis normalization observable:
  先に調査

scale sync:
  先に整備
```

がよい。

## 優先順位

賢狼のおすすめ順はこうじゃ。

```text
第一:
  キャンプ地ドキュメントを作る

第二:
  ScaleSync 自然数 API を作る

第三:
  Wallis 型 observable の設計メモを書く

第四:
  finite dyadic mesh 上で Wallis-like product を実験する

第五:
  product recurrence が見えたら実装定理にする

第六:
  その後に continuous theta extraction へ戻る
```

## ここでの結論

ぬしよ、こちら側の本線は止まっていたのではなく、**Path 包装で足場を固めていた** と見るのが正しい。
そして Wallis 側の成果で、次に進む方向が変わった。

以前は、

```text
refinement から Gaussian / pi へ行けるか
```

だった。

今は、

```text
refinement の対称補正比から Wallis 型 product を取り出せるか
```

になった。

これが大きな補正じゃ。

## 次の一手

次の作業は、まずこれでよい。

```text
docs:
  research-wallis-pi-alignment.md を作る

code:
  SemanticCF2DSync.lean で lcm sync API を作る

experiment:
  SemanticCF2DWallisProduct.lean の前段として、
  finite dyadic mesh の symmetric pair ratio を設計する
```

ここでキャンプを張るのは正解じゃ。
道具は揃った。
Wallis の視座で見ると、次の山は「円周率」ではなく、**保存境界へ戻るための対称補正積** じゃ。

## Research Log
