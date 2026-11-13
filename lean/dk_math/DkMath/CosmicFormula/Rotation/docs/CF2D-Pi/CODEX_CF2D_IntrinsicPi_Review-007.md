# CF2D Intrinsic π — 第6次レビュー 🐺🍎

ぬしよ、これは大きな進展じゃ！

今回は 正方形の幾何学的証明が閉じたこと と、πを使わずに正確な有限回転群を構成できたこと の二つが重要じゃ。

GitHub の [`dev/CF2D-pi-261112-v1`](https://github.com/Deskuma/dkmath/tree/dev/CF2D-pi-261112-v1?utm_source=chatgpt.com) を確認した。

対象 HEAD：[`1259fcf27787`](https://github.com/Deskuma/dkmath/commit/1259fcf277877a65d9252e6244b5c13e41fce2a8?utm_source=chatgpt.com)

`develop` から3コミット先行、遅れ0コミット。今回の追加分は独立した開発変更として整理されておる。

総合判定：今回の3モジュールは採用推奨。特に `HalfKernelOrder.lean` は、CF2D の代数構造を幾何学へ接続するための重要な基盤になった。

| 審査対象                           | 判定   | 所見                     |
| ---------------------------------- | ------ | ------------------------ |
| 正方形の凸包と原点ファンの一致     | 合格   | 集合の等式として証明     |
| 正方形の測度が2                    | 合格   | 無条件定理               |
| 正方形の支持半平面表示             | 合格   | 4辺の不等式と一致        |
| 正方形の外接領域による円盤包含     | 合格   | 初期段階で無条件         |
| 二分核の正確な位数                 | 合格   | π-free の群論的証明      |
| 直接軌道の頂点数と相異性           | 合格   | 位数定理から導出         |
| 直接軌道の保存量・巡回・半周対称性 | 合格   | 代数的に構成             |
| 既存のユークリッド軌道との一致     | 合格   | bridge 内で証明          |
| 一般の凸包面積・円盤包含           | 未完成 | 幾何学的な追加証明が必要 |

## 1. `HalfKernelOrder.lean` — 今回最大の成果

[実装を見る](https://github.com/Deskuma/dkmath/blob/dev/CF2D-pi-261112-v1/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/HalfKernelOrder.lean?utm_source=chatgpt.com)

まず、二分核の反復から、

\[ g_{n+1}^{\,2}=g_n \]

を得る。

これを帰納的に展開すれば、

\[ \boxed{g_n^{\,2^n}=g_0} \]

じゃ。

初期核 \(g_0=(0,1)\) は、

\[ g_0^2=(-1,0),\qquad g_0^4=(1,0) \]

を満たす。

したがって、

\[ \boxed{ \begin{aligned} g_n^{\,2^{n+1}}&=(-1,0)\\ g_n^{\,2^{n+2}}&=(1,0) \end{aligned} } \]

となる。

ここで Codex は `orderOf_eq_prime_pow` を使用して、

```
theorem sequence_kernel_orderOf (n : ℕ) :
    orderOf (sequence n).kernel = 4 * 2 ^ n
```

を証明している。

この証明方法がよい。

単に \(g_n^{4\cdot2^n}=1\) と示すだけでは、位数がその真の約数である可能性を排除できない。

しかし、今回の実装では、

\[ g_n^{2^{n+1}}\ne1 \]

も独立に証明している。

そして、位数が2の冪の約数であることを利用して、正確な位数を確定しておる。

有限巡回群の位数まで、三角関数も `Real.pi` も使わずに決定できた。

これは CF2D の研究目的に非常によく合っている。

### 直接軌道への接続

さらに、

```
def directVertex
    (n : ℕ) (j : Fin (4 * 2 ^ n)) : Vec ℝ
```

によって、核の冪を直接作用させた頂点を構成している。

次の定理も確認した。

```
directVertex_q2
directVertex_injective
directVertex_ncard
directVertex_next
directVertex_opposite
```

これらによって、π-free な代数層だけで、

\[ \boxed{ \#\{g_n^j\mid 0\le j<4\cdot2^n\} =4\cdot2^n } \]

という軌道の大きさを確定できる。

しかも、各頂点で保存量が1であり、半周先の頂点が元の頂点の負になる。

この成果を、わっちは高く評価する。

## 2. `IntrinsicPolygonSquare.lean` — 正方形の幾何学が完成

[実装を見る](https://github.com/Deskuma/dkmath/blob/dev/CF2D-pi-261112-v1/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/IntrinsicPolygonSquare.lean?utm_source=chatgpt.com)

今回の正方形は、単位円に内接する45°回転した正方形じゃ。

4頂点は、

\[ (1,0),\quad(0,1),\quad(-1,0),\quad(0,-1) \]

そして、その凸包は、

\[ \boxed{ K_0=\{(x,y)\in\mathbb R^2\mid |x|+|y|\le1\} } \]

と証明されておる。

この集合について、Codex は4象限ごとに座標を場合分けし、原点ファンの三角形へ所属することを示している。

したがって、

\[ K_0=\bigcup_{j=0}^{3}T_{0,j} \]

が無条件で成立する。

さらに、以前証明済みだった三角形同士の測度零の交わりを利用して、

\[ \boxed{\operatorname{vol}(K_0)=2} \]

が成立する。

この2という値は、半径1の円に内接する正方形の面積じゃ。最初の作図で用いた一辺1の正方形とは、スケールが異なることに注意するのじゃ。

### 支持半平面も完成

今回、

```
intrinsicPolygonRegion_zero_eq_edgeHalfSpaces
```

によって、

\[ K_0=H_0 \]

まで証明している。

さらに、

```
closedBall_subset_intrinsicPolygonOuterRegion_zero
```

も成立。

つまり、初期段階では既に、

\[ \boxed{ K_0\subseteq B(0,1)\subseteq K_0^{\mathrm{out}} } \]

という幾何学的挟み込みが完成しておる。

これは一般の \(n\) に対する証明の 基底ケース として有用じゃ。

## 3. 次の核心：二分核から頂点の細分化を直接証明する

ここで、わっちから新しい提案がある。

これまでのレビューでは、一般の正多角形について巡回順序・凸包被覆・測度零の重なりを証明する必要があると述べてきた。

しかし今回、`HalfKernelOrder.lean` が完成したことで、別の強力な道具が使えるようになった。

二分核による新しい頂点は、古い多角形の隣接頂点の和から直接構成できる。

これは今回のコードから導ける、新たな補題の候補じゃ。

### 偶数番目の頂点

第 \(n\) 段階の頂点を、

\[ v_{n,j}=g_n^j \]

と書く。

二分核の平方関係から、

\[ g_{n+1}^2=g_n \]

なので、

\[ \boxed{ v_{n+1,2j}=v_{n,j} } \]

が成立する。

つまり、細分化後の多角形には、前段階の頂点がそのまま残る。

### 奇数番目の頂点

こちらが本題じゃ。

二分核の定義から、次の代数恒等式が成立する。

\[ \boxed{ 1+g_n=2c_{n+1}g_{n+1} } \]

ここで \(1=(1,0)\) は回転核の単位元を表す。

実際、第一成分は半角公式から、

\[ 1+c_n=2c_{n+1}^{\,2} \]

第二成分は倍角公式から、

\[ s_n=2c_{n+1}s_{n+1} \]

となる。

したがって、古い隣接頂点の和は、

\[ \begin{aligned} v_{n,j}+v_{n,j+1} &=g_n^j+g_n^{j+1}\\ &=g_n^j(1+g_n)\\ &=2c_{n+1}g_n^jg_{n+1}\\ &=2c_{n+1}v_{n+1,2j+1} \end{aligned} \]

ゆえに、

\[ \boxed{ v_{n+1,2j+1} =\frac{v_{n,j}+v_{n,j+1}}{2c_{n+1}} } \]

が成立する！

これはπ-free の恒等式じゃ。

しかも、単なる抽象的な位数の定理とは違って、細分化後の頂点が、以前の隣接頂点に対してどこへ配置されるかを直接表しておる。

新しい頂点は、古い辺の中点から原点を通る半直線上にあり、単位円上まで正規化された点になる。

この関係が得られれば、次の幾何学的性質を証明するための足場になる。

\[ \boxed{K_n\subseteq K_{n+1}} \]

そして、新しい頂点が古い各辺の外側へ追加されることを示せれば、凸多角形の細分化を帰納法で解析できる のじゃ。

これが、次段階で最も優先したい補題じゃな。

なお、現状の位数定理だけでは、頂点列が自己交差せず反時計回りに並ぶことまでは保証されない。例えば、同じ位数の巡回群でも、異なる生成元を選ぶと星形の巡回順序になり得るからじゃ。

今回の二分核には、第一象限の非負平方根を選ぶという追加情報がある。この情報と上記の細分化恒等式を組み合わせることが、巡回順序の証明に役立つはずじゃ。

## 4. `IntrinsicDirectOrbitBridge.lean` の設計評価

[実装を見る](https://github.com/Deskuma/dkmath/blob/dev/CF2D-pi-261112-v1/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/IntrinsicDirectOrbitBridge.lean?utm_source=chatgpt.com)

このファイルは、わずか28行ほどじゃが、設計上の役割は明確じゃ。

```
theorem directVertex_eq_regularVertex
    (n : ℕ) (j : Fin (dyadicSides n)) :
    QuadrantUnitKernel.directVertex n j =
      regularVertex (dyadicSides n) j
```

これによって、二つの構成を同一視している。

| π-free の直接構成 | 既存の幾何学的構成        |
| ----------------- | ------------------------- |
| `HalfKernelOrder` | `IntrinsicRegularPolygon` |
| `sequence n`      | `regularKernel`           |
| `directVertex`    | `regularVertex`           |
| 代数的な位数      | 標準角度による等角回転    |

この bridge の分離は妥当じゃ。

ただし、既存の `IntrinsicRegularPolygon` を参照する `IntrinsicPolygonSquare` は、依然として解析的 bridge への依存を持つ。

したがって、現段階の成果は、π-free の有限巡回軌道が構成できたこと であり、幾何学的測度までの全依存グラフがπ-freeになったことではない。

将来的には、`directVertex` を `EuclideanPlane` に変換して直接 `Polygon` を構成することで、幾何学的定義自体も解析的 bridge から分離できる。

## 5. 次回 Codex に推奨する作業

わっちなら、一般の三角形対を一つずつ場合分けする前に、二分化による帰納構造を形式化する。

1. `directVertex_even`：新しい偶数番目の頂点が前段階の頂点と一致すること。
2. `directVertex_odd_normalized_midpoint`：奇数番目の頂点について、上記の正規化された中点の等式。
3. `intrinsicPolygonRegion_mono`：\(K_n\subseteq K_{n+1}\)。
4. `intrinsicPolygon_dyadic_refinement`：前段階の各辺が二つの新しい辺に分割され、巡回順序が保存されること。
5. その帰納構造を使った、一般のファン被覆、全三角形対の `AEDisjoint`、および支持半平面表示の証明。

目標は単に多数の幾何学的補題を増やすことではない。

正方形で成立する構造が、回転の二分割によって次の正多角形にも保存されることを証明する。

これができれば、今回完成した \(n=0\) の定理を、一般の \(n\) へ拡張する明確な経路になる。

ただし、凸包・支持半平面の帰納的な保存には、辺の向きや新頂点の位置に関する追加の証明が必要じゃ。

## 6. 最終判定

今回の3ファイルについて、ソース上の定理の型と証明を確認した範囲では、重大な数学的問題は見つからなかった。

公理依存と focused build の成功については Codex の報告に基づく。わっち自身は Lean コンパイラによる再検証を行っていない。

研究としての進捗を整理すると、次のようになる。

\[ \boxed{ \begin{gathered} \text{π-free の代数的回転核} \quad\checkmark\\ \Downarrow\\ \text{正確な位数を持つ有限巡回群} \quad\checkmark\\ \Downarrow\\ \text{正方形の凸包と測度} \quad\checkmark\\ \Downarrow\\ \text{二分割による凸多角形の一般的細分化} \quad\text{未完}\\ \Downarrow\\ \text{一般の正多角形の測度} \quad\text{未完}\\ \Downarrow\\ \text{円盤の内外挟み込み} \quad\text{未完} \end{gathered} } \]

ぬしよ、ここに来て、わっちは数学的な設計方針を少し変えたいと思う。

これまでは、正多角形の幾何学を一度に証明しようとしていた。

しかし、今回の位数定理と直接軌道があれば、正方形を出発点として、二分化そのものが幾何学的構造を保存することを帰納的に証明する という経路が考えられる。

これは、ぬしが最初から考えていた、

「対称的な構造を半分にしていき、その軌跡として円が現れる」

という発想に、さらに近い証明構造じゃ。

次の鍵は、回転核の代数的二分割と、正多角形の幾何学的細分化が同じ操作であることの証明。

ふふっ……CF2D が目指していた本来の数学的構造が、ますますはっきりしてきたのう！🐺🍎
