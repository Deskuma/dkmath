# CF2D Intrinsic π — 第5次レビュー 🐺🍎

ぬしよ！ また一つ、重要な証明上の障壁を越えたのう。

最新の [`dev/CF2D-pi-261112-v0`](https://github.com/Deskuma/dkmath/tree/dev/CF2D-pi-261112-v0) を確認したぞ。対象コミットは [`a3c992465f42`](https://github.com/Deskuma/dkmath/commit/a3c992465f42c3bd43e3780e4c7dc67456404bdf) じゃ。

今回の実装は採用してよい。特に、三角形の面積公式を行列式と測度変換則まで還元したことは、非常に大きな進展じゃ。

現在の状況をまとめよう。

| 項目                                 | 状態     | 評価         |
| ------------------------------------ | -------- | ------------ |
| 原点が凸包に属する                   | 証明済み | 合格         |
| 原点ファンの各三角形が凸包に含まれる | 証明済み | 合格         |
| 隣接頂点の外積が正                   | 証明済み | 合格         |
| 各三角形と標準三角形の線形対応       | 証明済み | 合格         |
| 線形変換の行列式が \(s_n\)           | 証明済み | 合格         |
| 線形変換による測度の倍率             | 証明済み | 合格         |
| 標準三角形の面積が \(1/2\)           | 未証明   | 次の最優先   |
| 原点ファンによる凸包の被覆           | 未証明   | 幾何学的課題 |
| 三角形同士の重なりが測度ゼロ         | 未証明   | 幾何学的課題 |
| 内接円盤が凸包に含まれる             | 未証明   | 幾何学的課題 |

GitHub 上では `develop` より12コミット先行、遅れ0コミット。ブランチ運用も正常じゃ。

## 1. 今回の中心的な成果

[IntrinsicOriginTriangleLinear.lean](https://github.com/Deskuma/dkmath/blob/dev/CF2D-pi-261112-v0/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/IntrinsicOriginTriangleLinear.lean)

ここに、次の定理が完成している。

```
theorem intrinsicOriginTriangle_volume_eq_beam_mul_standard
    (n : ℕ) (j : Fin (dyadicSides n)) :
    MeasureTheory.volume (intrinsicOriginTriangle n j) =
      ENNReal.ofReal ((sequence n).beam) *
        MeasureTheory.volume standardTriangle
```

つまり、

\[ \boxed{ \operatorname{Area}(T_{n,j}) =s_n\operatorname{Area}(\Delta) } \]

が既に無条件で証明されておる。

そして、

\[ \operatorname{Area}(\Delta)=\frac12 \]

さえ証明すれば、

\[ \boxed{ \operatorname{Area}(T_{n,j})=\frac{s_n}{2} } \]

となる。

しかも、この証明では既存の `intrinsicPi_eq_real_pi` も、標準三角関数も利用していない。

二次元の線形代数と測度論だけで成立する面積公式 になっているのじゃ。

この分離は非常によい。

## 2. 標準三角形の面積は、正方形の対称性で証明できる

ここで、わっちは今回の研究にふさわしい証明方法を提案したい。

標準三角形の面積 \(1/2\) は、積分や三角関数を直接使わず、単位正方形の対称性から求められる。

単位正方形を、

\[ S=[0,1]\times[0,1] \]

標準三角形を、

\[ \Delta=\{(x,y)\in S\mid x+y\le1\} \]

とする。

ここで、写像

\[ R(x,y)=(1-x,1-y) \]

を考える。

これは正方形の中心を基準とした180°回転じゃ。

\[ R(R(x,y))=(x,y) \]

しかも、

\[ |\det DR|=1 \]

なので、ルベーグ測度を保存する。

この操作で \(\Delta\) を写すと、正方形の残り半分になる。

したがって、

\[ S=\Delta\cup R(\Delta) \]

かつ、その共通部分は対角線 \(x+y=1\) だけじゃ。

対角線の二次元測度はゼロ。

ゆえに、

\[ \operatorname{Area}(S) =2\operatorname{Area}(\Delta) \]

単位正方形の面積は1だから、

\[ \boxed{ \operatorname{Area}(\Delta)=\frac12 } \]

となる。

この証明に必要なのは、積測度、平行移動・反転による測度保存、直線の二次元測度がゼロであることじゃ。

Lean では `standardTriangle` を座標不等式で特徴付ける補題を先に作り、対称変換による二分割を示すのがよい。

これは今回の 「半分の構造を対称性から復元する」 という研究思想にも一致しておる。

## 3. 内接円盤の包含には、もう一つの補題が必要じゃ

[IntrinsicPolygonCircumscribed.lean](https://github.com/Deskuma/dkmath/blob/dev/CF2D-pi-261112-v0/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/IntrinsicPolygonCircumscribed.lean)

今回の、

```
theorem intrinsicPolygon_edge_midpoint_norm ...
```

は、各辺の中点の原点からの距離が \(c_{n+1}\) であることを示している。

ただし、ここから直ちに内接円盤の包含が成立するわけではない。

次に必要なのは、各辺が多角形の支持直線を形成していること じゃ。

隣接頂点を \(v_j,v_{j+1}\)、その中点を \(m_j\) とすると、両頂点は単位円上なので、

\[ \|v_j\|^2=\|v_{j+1}\|^2=1 \]

したがって、

\[ \begin{aligned} \langle m_j,v_{j+1}-v_j\rangle &=\frac12\langle v_j+v_{j+1},v_{j+1}-v_j\rangle\\ &=\frac12(\|v_{j+1}\|^2-\|v_j\|^2)\\ &=0 \end{aligned} \]

となる。

つまり、辺の中点へ向かうベクトルは、その辺と直交する。

すでに、

\[ \|m_j\|=c_{n+1} \]

が証明されているので、各辺の支持直線と原点の距離は \(c_{n+1}\) じゃ。

さらに、正多角形の凸包が各支持半平面の共通部分であることを証明すれば、

\[ \boxed{ B(0,c_{n+1})\subseteq K_n } \]

へ到達できる。

ただし、すべての辺の距離が等しいという事実だけでは不十分じゃ。頂点の巡回順序と、それぞれの直線が凸包を支持することも保証する必要がある。

この点は形式化で慎重に扱いたい。

## 4. 次に Codex へ渡すべき優先課題

わっちなら、まず比較的独立性の高い標準三角形の測度を片付ける。

その後、原点ファンの幾何学へ進むのがよい。

| 優先 | 新しい証明目標                                    | 目的                     |
| ---- | ------------------------------------------------- | ------------------------ |
| 1    | `standardTriangle_volume`                         | 面積 \(1/2\) を無条件化  |
| 2    | `intrinsicOriginTriangle_volume`                  | 全原点三角形の面積を確定 |
| 3    | `intrinsicPolygonRegion_eq_iUnion_originTriangle` | 凸包の被覆               |
| 4    | `intrinsicOriginTriangle_pairwise_aeDisjoint`     | 面積の加法性             |
| 5    | `intrinsicPolygonRegion_volume_eq_areaApprox`     | 凸包の面積公式           |
| 6    | `intrinsicPolygonRegion_innerBall_subset`         | 内接円盤の包含           |
| 7    | `disk_measureReal_eq_intrinsicPi`                 | 最終定理の無条件化       |

一つだけ設計上の補足がある。

現在の幾何学モジュールは標準の `Real.pi` を使う `IntrinsicPiBridge` に依存している。したがって、将来の `disk_measureReal_eq_intrinsicPi` がそのファイルを経由して証明された場合、証明本体が `Real.pi` を参照していなくても、依存グラフまでπ-free とは限らない。

完全な独立性を目指すなら、二分核から多角形の頂点を直接生成する構成へ移行し、標準角度との照合を別の bridge に残すのが次の課題じゃ。

とはいえ、いまは測度の補題を完成させる方が先決じゃろう。

## 5. 最終評価

現在の数学的な進捗を、一つの図式にまとめるなら、

\[ \boxed{ \begin{gathered} \text{CF2D の回転不変量}\\ \Downarrow\\ \text{π-free な二分核}\\ \Downarrow\\ \text{内接・外接面積候補}\\ \Downarrow\\ \text{π-free な収束・誤差保証}\quad\checkmark\\ \Downarrow\\ \text{正多角形の辺長・靴紐和}\quad\checkmark\\ \Downarrow\\ \text{三角形の線形変換と測度倍率}\quad\checkmark\\ \Downarrow\\ \text{三角形分割・凸包の面積}\quad\text{未完}\\ \Downarrow\\ \text{円盤面積との同一性}\quad\text{未完} \end{gathered} } \]

ぬしよ。

今回、わっちが特に感慨深いのは、最後まで残った標準三角形の面積 \(1/2\) も、正方形の鏡映対称性で導ける ということじゃ。

正方形から始まり、対称性で半分に分け、それを繰り返して円へ近づく。

最初の GeoGebra の着想が、Lean の証明構造にここまで反映されてきた。

ただし、これは古典的な幾何学を DkMath の体系で再構成している段階であり、新しい円周率の値や未知られた数学的法則の発見を意味するものではない。

それでも、代数的不変量から円盤の測度までの依存関係を、一つずつ証明でつなぐ という目標は十分に価値がある。

そして、残る未証明の条件は、もう抽象的な問題ではない。

具体的な集合の等式と測度の等式にまで分解されておる。

ここから先は、一つずつ仕留めていくのじゃ。🐺🍎
