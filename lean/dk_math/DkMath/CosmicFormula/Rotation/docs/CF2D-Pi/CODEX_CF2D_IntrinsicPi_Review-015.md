# CF2D Intrinsic π — 015 実装レビュー 🐺🍎

D.よ、これは非常によい進展じゃ！ 🐺🍎

## **レビュー014：非負錐による全平面の被覆**

**判定：目標達成。π-free な幾何学的巡回順序の証明に向けて、重要な基盤が完成した。**

以下の実装を確認した。

- [DyadicCone.lean](https://github.com/Deskuma/dkmath/blob/dev/CF2D-pi-261112-v1/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/DyadicCone.lean)
- [IntrinsicPolygonSupport.lean](https://github.com/Deskuma/dkmath/blob/dev/CF2D-pi-261112-v1/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/IntrinsicPolygonSupport.lean)

### **1. 非負錐の二分**

まず、`nonnegativeCone_split` が一般の実ベクトル空間に対して証明されている点がよい。

\[ p+q=cw,\qquad c>0 \]

という条件から、

\[ \boxed{ \operatorname{Cone}(p,q) = \operatorname{Cone}(p,w) \cup \operatorname{Cone}(w,q) } \]

を得ている。

この補題は CF2D 固有の構造に依存しないため、今後も再利用できる。

さらに `dyadicCone_refinement` で直接軌道の正規化中点公式を適用し、`dyadicCones_cover_plane` では初期四象限から帰納法を完成させておる。

ここまでの証明に `Real.pi`、`Real.sin`、`Real.cos` の直接参照はなく、`sorry`、`admit`、追加の `axiom` 宣言も見当たらなかった。

### **2. 偏角による頂点選択の置換**

こちらも確認できた。

以前の `intrinsicEdgeHalfSpaces_subset_intrinsicPolygonRegion` は、`Complex.arg` と三角関数を用いて隣接頂点を選んでいた。

現在は、

```
have hxcover :
    euclideanPlaneToPair x ∈ ⋃ j, DyadicCone n j := by
  rw [dyadicCones_cover_plane]
  exact Set.mem_univ _
```

から、隣接頂点の非負線形結合

\[ x=ap+bq,\qquad a,b\ge0 \]

を取り出している。

続いて、対応する支持半平面の不等式から

\[ a+b\le1 \]

を得て凸包への所属を証明する。

**偏角を使っていた部分は、確かに非負錐の被覆によって置換されておる。**

ただし、`directVertex_eq_regularVertex` を使って既存のユークリッド軌道に接続しているため、この支持半平面定理全体が π-free になったわけではない。ぬしの報告は、その点も正確じゃ。

## **3. 次の証明には、もう一つ強力な補題がある**

ここからが、わっちの提案じゃ。

今回の錐の二分公式を、もう少し強化できる。

**二つの子錐の共通部分が、分割点&#x20;**\(w\)**&#x20;の半直線だけになることを証明しよう。**

\(p,q\) が一次独立で、

\[ p+q=cw,\qquad c>0 \]

とする。

すると、

\[ \boxed{ \operatorname{Cone}(p,w) \cap \operatorname{Cone}(w,q) = \{tw\mid t\ge0\} } \]

が成立する。

証明は、二つの表示

\[ x=ap+bw \]

\[ x=sw+dq \]

を比較すればよい。

\(w=(p+q)/c\) を代入すると、\(p,q\) の係数比較から

\[ a+d=0 \]

が得られる。

非負性より \(a=d=0\) じゃ。

したがって、共通部分は \(w\) の半直線に限られる。

これは三角関数なしの線形代数で証明できる。

### **この補題が意味するもの**

今回証明したのは、

\[ \text{親錐}=\text{子錐}_1\cup\text{子錐}_2 \]

だった。

次に、

\[ \operatorname{interior}(\text{子錐}_1) \cap \operatorname{interior}(\text{子錐}_2) =\varnothing \]

まで得られる。

初期四象限でも内部が互いに交わらないことは明らかじゃから、この性質を細分化に沿って帰納的に維持できる見込みがある。

つまり、

\[ \boxed{ i\ne j \Longrightarrow \operatorname{interior}(C_{n,i}) \cap \operatorname{interior}(C_{n,j}) =\varnothing } \]

を全段階で目指せるのじゃ。

これが成立すれば、単なる全平面被覆から、 **内部が重ならない巡回扇形分割** へ進める。

## **4. 残る三角関数依存**

現在の `IntrinsicPolygonSupport.lean` で、標準角度に依存する主要部分は次の二つじゃ。

| 定理                                         | 役割                                     |
| -------------------------------------------- | ---------------------------------------- |
| `intrinsicPolygon_vertex_mem_edge_halfspace` | 全旧頂点に対する支持不等式               |
| `other_odd_mem_halfspace`                    | 他の増分三角形の新頂点に対する支持不等式 |

この二つが、次の置換対象になる。

新しく得た錐の被覆と、これから証明する内部非交差・巡回順序を利用すれば、外積と内積による証明へ移行できる可能性がある。

ただし、内部非交差だけで支持不等式が自動的に出るわけではない。頂点が定める弦に対して、他の頂点が一貫して内側に位置することを別途接続する必要がある。

## **レビュー015への提案**

優先順位は次のとおりじゃ。

1. `nonnegativeCone_children_inter`：二つの子錐の交わりが共通半直線に等しい。
2. `dyadicCones_pairwise_interior_disjoint`：任意の異なる錐の内部が交わらない。
3. `dyadicCones_cyclic_order`：被覆と内部非交差から、全周の巡回順序を確立する。
4. その順序を使い、残る支持半平面不等式の π-free 化を進める。

公開 import と専用回帰例も確認できた。ビルド成功についてはぬしの報告に基づくもので、わっち自身は Lean を再実行していない。

**今回の成果は、幾何学的な「一周」を、標準角度を使わずに扱うための決定的な土台じゃ。**

正方形の四象限から始め、それぞれを二分し、さらに二分する。

その操作だけで、どの方向にも必ず対応する領域が存在することを証明した。

ふふっ。円周率を知らなくても、平面の全方向を覆えるわけじゃな。

これは実に面白い！
