## 第4次レビュー：CF2D の幾何学的 π 構成 🐺🍎

ぬしよ、最新コミット [`adc64768b265`](https://github.com/Deskuma/dkmath/commit/adc64768b265daa01b62157beeb7902083ac9d7d) を確認したぞ。

今回の実装は合格じゃ。しかも、証明すべきことと、まだ証明できていないことの境界が非常に明確になった。

`develop` との差分は10コミット先行、遅れ0コミット。ブランチ運用にも問題はない。

### 1. 今回の実装で成立したこと

| 定理・構造                                            | 評価                          |
| ----------------------------------------------------- | ----------------------------- |
| `outerApprox_eq_areaApprox_div_core_sq`               | π-free の代数恒等式として成立 |
| `core_lt_one`, `beam_pos`                             | 有限段階の非退化性を保証      |
| `intrinsicOriginTriangle_vertexCross_pos`             | 三角形の向きを保証            |
| `intrinsicPolygonOuterRegion_volume`                  | 拡大による面積倍率を証明      |
| `intrinsicPolygonRegion_volume_of_origin_fan`         | 明示的な3条件の下で成立       |
| `disk_measureReal_eq_intrinsicPi_of_polygon_sandwich` | 明示的な2条件の下で成立       |
| 円盤面積と `intrinsicPi` の無条件の一致               | 未証明                        |

特に [IntrinsicPolygonCircumscribed.lean](https://github.com/Deskuma/dkmath/blob/dev/CF2D-pi-261112-v0/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/IntrinsicPolygonCircumscribed.lean) の最後にある定理が、今回の成果の中心じゃ。

```
theorem disk_measureReal_eq_intrinsicPi_of_polygon_sandwich
    (harea : ∀ n,
      MeasureTheory.volume (intrinsicPolygonRegion n) =
        ENNReal.ofReal (areaApprox n))
    (hcover : ∀ n,
      Metric.closedBall (0 : EuclideanPlane) 1 ⊆
        intrinsicPolygonOuterRegion n) :
    MeasureTheory.volume.real
      (Metric.closedBall (0 : EuclideanPlane) 1) =
        intrinsicPi
```

これは、われわれが目指している幾何学的な証明を、二つの補題へ還元することに成功している。

数学的には、

\[ \operatorname{Area}(K_n)=A_n \]

および、

\[ B(0,1)\subseteq K_n^{\mathrm{out}} \]

が証明できれば、

\[ A_n\le\operatorname{Area}(B(0,1))\le U_n \]

となる。

ここから既証明の収束性を使って、

\[ \boxed{ \operatorname{Area}(B(0,1)) =\Pi_{\mathrm{CF2D}} } \]

が従う。

しかも、この条件付き定理の証明本体では `intrinsicPi_eq_real_pi` を利用しておらぬ。

これはよい設計じゃ！

## 2. 三角形の測度公式は、線形変換として証明できる

現在の `intrinsicOriginTriangle` は、

\[ T_j=\operatorname{conv}\{0,v_j,v_{j+1}\} \]

と定義されている。

ここで、標準三角形を、

\[ \Delta=\{(a,b)\in\mathbb R^2\mid a\ge0,\ b\ge0,\ a+b\le1\} \]

としよう。

その面積は、

\[ \operatorname{Area}(\Delta)=\frac12 \]

じゃ。

そして線形写像、

\[ F_j(a,b)=av_j+bv_{j+1} \]

を考える。

この線形写像の行列式は、

\[ \det F_j=\det(v_j,v_{j+1}) \]

じゃな。

既に Lean では、

\[ \boxed{\det(v_j,v_{j+1})=s_n>0} \]

が証明済み。

したがって、線形変換による測度の倍率から、

\[ \operatorname{Area}(T_j) =|\det F_j|\operatorname{Area}(\Delta) \]

となる。

よって、

\[ \boxed{\operatorname{Area}(T_j)=\frac{s_n}{2}} \]

じゃ。

ここには三角関数もπも要らぬ。

既存の外積定理と、線形変換による測度の変換公式を結ぶだけでよい。

固定版 Mathlib に目的の単体面積定理が存在しないなら、この経路を Codex に検討させるのがよいと思う。

## 3. 凸包の分割では、原点の所属を先に証明しよう

現在の `intrinsicOriginTriangle_subset_region` は、

```
(hzero : (0 : EuclideanPlane) ∈ intrinsicPolygonRegion n)
```

を仮定している。

これは正しいが、ここは無条件に証明できるはずじゃ。

なぜなら、正 \(4\cdot2^n\) 角形の頂点には、必ず反対側の頂点がある。

\[ v_{j+N_n/2}=-v_j \]

したがって、

\[ 0=\frac12v_j+\frac12(-v_j) \]

となる。

凸包の定義から、

\[ \boxed{0\in K_n} \]

が従う。

これを最初に証明すれば、原点ファンの各三角形が凸包に含まれることを無条件化できる。

続いて、頂点が反時計回りの凸多角形を構成することを使い、

\[ \boxed{ K_n=\bigcup_{j=0}^{N_n-1}T_j } \]

を証明する。

異なる三角形の共通部分は境界の線分や原点に限られるため、その交わりは二次元測度ゼロになる。

これで条件付き定理の三つの仮定を取り除ける見込みじゃ。

## 4. 外接多角形の包含は、別の形にすると簡単になる

現在、外側領域は、

\[ K_n^{\mathrm{out}} =\frac1{c_{n+1}}K_n \]

として実装されている。

ここで直接、

\[ B(0,1)\subseteq K_n^{\mathrm{out}} \]

を証明するより、次の等価な命題を先に証明することを勧める。

\[ \boxed{ B(0,c_{n+1})\subseteq K_n } \]

なぜなら、\(c_{n+1}>0\) だからじゃ。

これは内接正多角形の 内接円半径 が \(c_{n+1}\) であることを表している。

その証明には、多角形を各辺が定める内側の半平面の共通部分として表せばよい。

隣接頂点を \(v_j,v_{j+1}\) とすると、その辺の中点方向は、

\[ m_j=\frac{v_j+v_{j+1}}2 \]

じゃ。

保存量から、

\[ \|m_j\|=c_{n+1} \]

となる。

したがって、原点から各辺までの距離はすべて \(c_{n+1}\)。

これが全辺について成立するので、半径 \(c_{n+1}\) の閉円盤は多角形の内部に収まる。

この包含を証明すれば、スカラー拡大によって目標の円盤包含が得られる。

## 5. 設計上の注意点

一点だけ、今後の依存関係について明確にしておきたい。

現在の `IntrinsicRegularPolygon.lean` は `IntrinsicPiBridge` と `EuclideanRegularOrbit` を import している。

また、生成核の一致証明では `sequence_trig` を利用している。

したがって、幾何学的モジュールには既知のπを使った実数角度との対応が含まれる。

これは証明の正しさを損なわない。しかし、将来的に、

「CF2D の代数だけで頂点軌道を構成し、面積の測度を経由してπへ到達した」

という、より強い依存関係上の独立性を実現するなら、`sequence n` の核を直接反復して頂点を生成するモジュールも必要になるじゃろう。

また `#print axioms` が標準公理のみであることは、条件付き定理の証明が公理を追加していないことを確認するものじゃ。定理の引数にある `harea` や `hcover` が証明済みであることを意味するわけではない。

Codex はその点を適切に区別しておる。

## 6. 次段階の優先順位

わっちなら、次は次の順序で実装させる。

1. `intrinsicPolygonRegion_origin_mem` — 原点の凸包所属。
2. `intrinsicOriginTriangle_volume` — 標準三角形と線形変換による面積公式。
3. `intrinsicOriginTriangle_pairwise_aeDisjoint` — 異なる三角形の重複部分の測度ゼロ。
4. `intrinsicPolygonRegion_eq_iUnion_originTriangle` — 凸包の原点ファンによる被覆。
5. `intrinsicPolygonRegion_volume_eq_areaApprox` — 面積の無条件の同一性。
6. `closedBall_subset_intrinsicPolygonOuterRegion` — 外接多角形の包含。
7. `disk_measureReal_eq_intrinsicPi` — 条件付き定理の無条件化。

なお、`lake build` と専用テストの成功は報告として確認したが、わっち自身がこの環境で Lean の型検査を再実行したわけではないぞ。

### 賢狼の最終評価

ぬしよ、今回の進展を過小評価してはならぬ。

最初は、

「正方形の対称性を繰り返すと、円が現れるのではないか」

という考察だった。

それが今や、

\[ \boxed{ \begin{gathered} \text{代数的な回転と保存量}\\ \Downarrow\\ \text{角度の二分割}\\ \Downarrow\\ \text{内接・外接正多角形}\\ \Downarrow\\ \text{面積を挟む二つの数列}\\ \Downarrow\\ \text{π-free な極限}\\ \Downarrow\\ \text{円盤のルベーグ測度} \end{gathered} } \]

という、一つの形式的証明計画になった。

現時点では最後の測度接続は条件付きじゃが、残された仮定は具体的で、個々の幾何学的補題へ分解できている。

わっちが今回最も高く評価するのは、この点じゃ。

すでに「何を証明すればよいかわからない」段階ではない。

何を証明すれば完成するかが、Lean の定理の型として明示された。

そして、その型に必要な仮定を一つずつ取り除いている。

これは、形式数学の研究として非常に健全な進み方じゃよ。🐺🍎
