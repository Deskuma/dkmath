# CF2D Intrinsic π — 016 実装レビュー 🐺🍎

D.よ、これは大きな進展じゃ！ 🐺🍎

**角度依存を解消するための次の道筋が、かなり明確になった。**

[DyadicCone.lean](https://github.com/Deskuma/dkmath/blob/dev/CF2D-pi-261112-v1/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/DyadicCone.lean) を確認した。`nonnegativeCone_children_inter`、`dyadicCones_pairwise_interior_disjoint`、`dyadicCones_cyclic_order` は、いずれも追加の幾何仮定を持たない定理として実装されておる。

ただし、`dyadicCones_cyclic_order` の型が保証するのは、被覆・内部非交差・隣接錐が共有半直線を含むことじゃ。任意の二錐の交わりを完全に特徴付ける定理までは含まれておらぬ。

それでも、次の支持不等式を証明するには十分有力な材料じゃ。

## **1. 次の核心：支持直線を越えた点は錐の内部に入る**

旧辺の両端を \(p,q\)、中点を \(m\) とする。

\[ m=\frac{p+q}{2} \]

両端は単位円上にあり、

\[ \langle p,q\rangle=c_n \]

なので、

\[ \langle m,p\rangle = \langle m,q\rangle = \frac{1+c_n}{2} = c_{n+1}^{\,2} \]

となる。

ここで、単位円盤内の点 \(x\) が支持直線より外側にあると仮定しよう。

\[ \langle m,x\rangle>c_{n+1}^{\,2} \]

わっちが次に証明することを勧める補題は、次の主張じゃ。

\[ \boxed{ \begin{gathered} \|x\|\le1\\ \langle m,x\rangle>c_{n+1}^{\,2} \end{gathered} \quad\Longrightarrow\quad x\in\operatorname{interior}(\operatorname{Cone}(p,q)) } \]

これが成立すれば、支持不等式と錐の内部非交差を結び付けられる。

### **どう証明するか**

既に

\[ \det(p,q)=s_n>0 \]

が証明済みじゃ。

したがって \(p,q\) は一次独立なので、任意の点 \(x\) は一意に

\[ x=ap+bq \]

と表せる。

外積から係数を具体的に定めればよい。

\[ a=\frac{\det(x,q)}{\det(p,q)}, \qquad b=\frac{\det(p,x)}{\det(p,q)} \]

このとき、

\[ \langle m,x\rangle = c_{n+1}^{\,2}(a+b) \]

だから、支持直線より外側という仮定から

\[ a+b>1 \]

が得られる。

一方、二乗和を展開すると、

\[ \begin{aligned} \|x\|^2 &=a^2+b^2+2c_nab\\ &=(a+b)^2-2(1-c_n)ab \end{aligned} \]

じゃ。

ここで \(ab\le0\) と仮定すると、\(c_n<1\) より

\[ \|x\|^2\ge(a+b)^2>1 \]

となり、\(\|x\|\le1\) に矛盾する。

したがって、

\[ ab>0 \]

さらに \(a+b>1\) なので、

\[ a>0,\qquad b>0 \]

が従う。

すなわち \(x\) は錐の内部に位置する。

**この議論は、三角関数も角度も使わない。**

## **2. 全旧頂点の支持不等式を導く**

次に、旧辺 \(j\) に対して、その両端以外の頂点 \(v_k\) を考える。

仮に、

\[ \langle m_j,v_k\rangle>c_{n+1}^{\,2} \]

なら、先ほどの補題から

\[ v_k\in\operatorname{interior}(C_{n,j}) \]

となる。

しかし \(v_k\) は、自身を始点とする錐 \(C_{n,k}\) の境界半直線上にある。

非退化な錐では、境界上の頂点はその錐の内部点の極限として近似できる。

したがって、もし \(v_k\) が別の錐 \(C_{n,j}\) の内部にあれば、その開近傍に \(C_{n,k}\) の内部点が存在してしまう。

これは、今回証明された

```
dyadicCones_pairwise_interior_disjoint
```

に矛盾する。

ゆえに、

\[ \boxed{ \langle m_j,v_k\rangle \le c_{n+1}^{\,2} } \]

となる。

これが、現在三角関数に依存している

`intrinsicPolygon_vertex_mem_edge_halfspace`

の π-free な証明候補じゃ。

## **3. 他の奇数頂点に対する不等式は、さらに直接的**

`other_odd_mem_halfspace` も同じ方法で置換できる可能性が高い。

新しい奇数頂点 \(w_k\) は、既存の正規化中点公式から

\[ w_k = \frac{v_k+v_{k+1}}{2c_{n+1}} \]

と表される。

分母は正じゃ。

したがって \(w_k\) は、親錐 \(C_{n,k}\) の内部にある。

ここで \(j\ne k\) とする。

もし \(w_k\) が旧辺 \(j\) の支持直線を越えれば、

\[ w_k\in\operatorname{interior}(C_{n,j}) \]

となる。

しかし既に

\[ w_k\in\operatorname{interior}(C_{n,k}) \]

なのだから、内部非交差に矛盾する。

つまり、 **奇数頂点の支持不等式は、錐の内部非交差をほぼ直接利用できる** 。

## **4. 推奨する実装順序**

わっちは次の順序を勧める。

| 優先 | 補題候補                                   | 目的                                           |
| ---- | ------------------------------------------ | ---------------------------------------------- |
| 1    | `strictCone_mem_interior`                  | 正の係数を持つ点が錐の内部にあること           |
| 2    | `outside_chord_mem_cone_interior`          | 支持直線を越えた単位円盤内の点を錐の内部へ移す |
| 3    | `orbit_vertex_not_mem_other_cone_interior` | 別の頂点が錐の内部に入らないこと               |
| 4    | `directVertex_mem_edge_halfspace`          | 全旧頂点の支持不等式を π-free に証明           |
| 5    | `other_odd_mem_halfspace_pi_free`          | 異なる増分三角形の新頂点に対する支持不等式     |
| 6    | 既存の支持半平面証明を置換                 | 三角関数依存の除去                             |

実装上は、`DyadicCone` が `ℝ × ℝ` を使っているので、ノルムの扱いには注意が必要じゃ。

この型の一般のノルムをユークリッドノルムと同一視せず、

\[ Q(x)=x_1^2+x_2^2 \]

という保存量を直接使うのが安全じゃろう。

さらに、正の係数表示から錐の内部所属を得る際には、一次独立性を利用して「正係数の点全体が開集合である」ことを示すとよい。

## **5. π-free 化の最終的な境界**

現在の [IntrinsicPolygonSupport.lean](https://github.com/Deskuma/dkmath/blob/dev/CF2D-pi-261112-v1/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/IntrinsicPolygonSupport.lean) には、主に二種類の橋がある。

1. 頂点の配置を `Real.cos`・`Real.sin` で比較する橋。
2. `directVertex_eq_regularVertex` によって、直接軌道と既存の正多角形軌道を同一視する橋。

今回提案した補題群は、まず 1 を解消するものじゃ。

完全な π-free 幾何モジュールを目指すなら、その後に直接軌道から凸包を定義し、2 の bridge を最終的な比較定理へ隔離するとよい。

この順序なら、既存の完成済み定理を維持しながら依存を減らせる。

### **レビュー015：総評**

今回の `DyadicCone.lean` については、**全平面被覆と全対の内部非交差を、二分核から構成できたことを確認した** 。

公開 import と専用テストの登録も確認できた。ビルド成功はぬしの報告に基づくもので、わっち自身は Lean を再実行しておらぬ。

そして、次に進むべき数学的な核心は明確じゃ。

\[ \boxed{ \text{支持直線の外側} \Longrightarrow \text{錐の内部} \Longrightarrow \text{内部非交差との矛盾} } \]

この三段階が成立すれば、現在の標準角度に依存した支持不等式を、外積・内積・保存量だけの証明へ置き換える道が開ける。

D.よ、わっちはこの方向を最優先に推す。

**今度は円周率を使わずに、正多角形の辺が本当に支持辺であることを証明するのじゃ。**
