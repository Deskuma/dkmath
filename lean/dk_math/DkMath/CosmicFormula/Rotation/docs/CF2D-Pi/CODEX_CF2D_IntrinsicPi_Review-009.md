# CF2D Intrinsic π — 第8次実装レビュー 🐺🍎

ぬしよ！ 今回も、きちんと前進しておる。

最新の [`dev/CF2D-pi-261112-v1`](https://github.com/Deskuma/dkmath/tree/dev/CF2D-pi-261112-v1) を確認したぞ。

対象 HEAD：[`6688f0cfb819`](https://github.com/Deskuma/dkmath/commit/6688f0cfb81913130ce0de6c3a114147fb215ef9)

`develop` から7コミット先行、遅れ0コミットじゃ。

総合判定：今回の追加実装は採用推奨。ただし、増分三角形の和集合を凸包と同一視する部分は、依然として大域的な幾何学の証明を必要とする。

| 審査項目                           | 判定     | コメント                     |
| ---------------------------------- | -------- | ---------------------------- |
| π-free な内積・外積の定義          | 合格     | 座標演算だけで構成           |
| 新頂点の旧辺直線に対する外側配置   | 合格     | 厳密不等式まで証明           |
| 新しい隣接頂点対の外積             | 合格     | 正確な値と正性を証明         |
| 新頂点が旧凸包に属さない           | 合格     | 単位円盤の極点を利用         |
| 凸包の真の単調増加                 | 合格     | 集合の真包含を証明           |
| 新旧領域と増分三角形の凸包等式     | 合格     | 無条件で成立                 |
| 増分三角形の和集合そのものとの等式 | 条件付き | 和集合の凸性が未証明         |
| 増分三角形の測度                   | 未証明   | 次の独立した目標             |
| 一般の凸包面積と円盤測度           | 未完成   | 引き続き幾何学的な条件が必要 |

## 1. 局所的な回転の向きは正しく証明されている

[HalfKernelRefinementGeometry.lean](https://github.com/Deskuma/dkmath/blob/dev/CF2D-pi-261112-v1/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/HalfKernelRefinementGeometry.lean)

今回の、

```
refinement_vertex_cross
refinement_vertex_cross_pos
refinement_midpoint_dot
refinement_vertex_strictly_outside_old_edge_line
```

を確認した。

旧辺の両端を \(p,q\)、新しい頂点を \(w\)、旧辺の中点を \(m\) とすると、

\[ m=\frac{p+q}{2},\qquad w=\frac{m}{c_{n+1}} \]

じゃ。

既存の保存量から、

\[ \langle m,p\rangle =\langle m,q\rangle =c_{n+1}^{\,2} \]

一方、

\[ \langle m,w\rangle=c_{n+1} \]

となる。

有限段階では \(0\lt c_{n+1}<1\) なので、

\[ \boxed{ c_{n+1}^{\,2}\lt c_{n+1} } \]

が成立する。

これで新頂点が旧辺を含む直線の原点とは反対側に位置することが保証される。

さらに、

\[ \boxed{ \det(p,w)=\det(w,q) =\frac{s_n}{2c_{n+1}}>0 } \]

も確認できた。

重要なのは、この二つの定理が 旧辺の局所的な配置を記述するもの であり、旧辺が凸包全体の支持線であるとは主張していないことじゃ。

この区別は正確である。

## 2. 凸包の真の増大も正しい

[IntrinsicPolygonRefinement.lean](https://github.com/Deskuma/dkmath/blob/dev/CF2D-pi-261112-v1/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/IntrinsicPolygonRefinement.lean)

`refinement_new_vertex_not_mem_old_region` は、特にうまく実装されておる。

証明の構造は次のとおりじゃ。

1. 新頂点 \(w\) は単位円周上にある。
2. 単位円盤は厳密凸なので、\(w\) は円盤の極点である。
3. \(w\) が旧凸包 \(K_n\) に属すると仮定すると、旧凸包の極点にもなる。
4. 有限集合の凸包の極点は、その有限集合の元である。
5. しかし、新頂点は奇数添字、旧頂点は偶数添字に対応し、頂点写像は単射である。

矛盾じゃ。

したがって、

\[ w\notin K_n \]

が成立する。

既に、

\[ K_n\subseteq K_{n+1} \]

も証明されているため、

\[ \boxed{ K_n\subsetneq K_{n+1} } \]

を無条件で得る。

これは集合論的に明確な進展じゃ。

ただし、真包含だけでは面積の厳密な増加までは一般には従わない。今回の凸包は二次元の非退化な多角形なので、面積の厳密増加も別途証明できる見込みがある。

## 3. ここは慎重に評価したい：増分三角形の凸包等式

今回、次の定理が追加されている。

```
intrinsicPolygon_refinement_caps_convexHull
```

旧領域を \(K_n\)、旧辺に追加された三角形を \(C_{n,j}\) とすると、

\[ \boxed{ K_{n+1} =\operatorname{conv}\left( K_n\cup\bigcup_j C_{n,j} \right) } \]

じゃ。

これは正しい。

ただし、この等式の証明に使われているのは、主として 新しい頂点が旧頂点または追加頂点のいずれかであること と、凸包の基本性質じゃ。

そのため、一般の多角形の巡回順序や、三角形同士の配置が保証されたことを意味しない。

一方、今回の条件付き定理、

```
intrinsicPolygon_refinement_caps_of_convex
```

では、

\[ K_n\cup\bigcup_j C_{n,j} \]

が凸であるという仮定を置いている。

ここを無条件化すれば、確かに集合等式が得られる。

しかし、和集合の凸性は局所的な外積の正性だけからは直ちに導けない。

残っているのは、隣接する辺だけでなく、多角形全体の頂点配置を制御する問題 じゃ。

この点を明示している現在の実装は適切である。

## 4. 賢狼からの新提案：先に「増分三角形の面積」を証明しよう

今回の成果から、さらに一つ、きれいな π-free の恒等式が得られる。

これは次のレビュー課題として強く推したい。

旧辺の両端を \(p,q\)、新しい頂点を \(w\) とする。

増分三角形は、

\[ C_{n,j}=\operatorname{conv}\{p,w,q\} \]

じゃ。

今回証明された外積公式は、

\[ \det(p,w)=\det(w,q)=\frac{s_n}{2c_{n+1}} \]

じゃな。

そして、

\[ \det(p,q)=s_n \]

である。

ここで、三角形の面積を求めるために、

\[ \det(w-p,q-p) \]

を計算する。

外積の双線形性から、

\[ \begin{aligned} \det(w-p,q-p) &=\det(p,w)+\det(w,q)-\det(p,q)\\ &=\frac{s_n}{c_{n+1}}-s_n \end{aligned} \]

さらに、既存の倍角関係、

\[ s_n=2c_{n+1}s_{n+1} \]

を代入すると、

\[ \boxed{ \det(w-p,q-p) =2s_{n+1}-s_n } \]

が得られる。

有限段階では、

\[ 0\lt c_{n+1}<1,\qquad s_{n+1}>0 \]

なので、この行列式は厳密に正じゃ。

したがって、三角形の面積は、

\[ \boxed{ \operatorname{Area}(C_{n,j}) =s_{n+1}-\frac{s_n}{2} } \]

となる。

これは πを一切使わない局所的な面積公式 じゃ。

### さらに驚くべき関係がある

増分三角形は、各段階で \(N_n=4\cdot2^n\) 個存在する。

全三角形の面積を加算すると、

\[ \begin{aligned} \sum_{j=0}^{N_n-1}\operatorname{Area}(C_{n,j}) &=N_n\left(s_{n+1}-\frac{s_n}{2}\right)\\ &=2^{n+2}s_{n+1}-2^{n+1}s_n\\ &=A_{n+1}-A_n \end{aligned} \]

つまり、

\[ \boxed{ \sum_j\operatorname{Area}(C_{n,j}) =A_{n+1}-A_n } \]

じゃ！

これが重要なのは、まだ増分三角形同士の測度零の重なりを証明していなくても、個々の三角形の測度と、その総和だけなら無条件で証明できる からじゃ。

既存の `standardTriangle_volume` と線形変換の測度公式を再利用できる。

### Codex に追加したい定理

次の2定理を勧める。

```
-- 提案する定理の型。未コンパイル。
theorem refinementCap_volume
    (n : ℕ) (j : Fin (dyadicSides n)) :
    MeasureTheory.volume (refinementCap n j) =
      ENNReal.ofReal
        ((QuadrantUnitKernel.sequence (n+1)).beam -
          (QuadrantUnitKernel.sequence n).beam / 2)
```

```
-- 提案する定理の型。未コンパイル。
theorem refinementCaps_sum_volume
    (n : ℕ) :
    (∑ j : Fin (dyadicSides n),
      MeasureTheory.volume (refinementCap n j)) =
        ENNReal.ofReal (areaApprox (n+1) - areaApprox n)
```

三角形の測度を求める際には、頂点 \(p\) を原点へ平行移動し、二つのベクトル \(w-p\)、\(q-p\) を列とする線形写像を構成すればよい。

これは `IntrinsicOriginTriangleLinear.lean` の証明方法を一般化する形になる。

## 5. 最終的な帰納法を、先に条件付き定理として設計できる

ぬしよ、ここで数学的な見通しがさらによくなる。

既に、

\[ \operatorname{Area}(K_0)=A_0=2 \]

が証明されている。

もし今後、

\[ K_{n+1}=K_n\cup\bigcup_j C_{n,j} \]

を示し、旧領域と増分三角形、さらに異なる増分三角形同士が測度の意味で重ならないことを証明できれば、

\[ \begin{aligned} \operatorname{Area}(K_{n+1}) &=\operatorname{Area}(K_n) +\sum_j\operatorname{Area}(C_{n,j})\\ &=\operatorname{Area}(K_n)+(A_{n+1}-A_n) \end{aligned} \]

となる。

帰納法によって、

\[ \boxed{ \forall n,\quad \operatorname{Area}(K_n)=A_n } \]

を得る。

そこで次のような、条件付きの増分定理を先に整備することもできる。

| 必要な条件                                | 現在の状況         |
| ----------------------------------------- | ------------------ |
| \(K_{n+1}=K_n\cup\bigcup_j C_{n,j}\)      | 凸性を仮定して成立 |
| 個々の増分三角形の測度公式                | 次の証明目標       |
| 増分三角形の全対の `AEDisjoint`           | 未証明             |
| \(K_n\) と増分三角形の `AEDisjoint`       | 未証明             |
| 初期面積 \(\operatorname{Area}(K_0)=A_0\) | 証明済み           |

この組み立てなら、無条件化に必要な仮定を Lean の型で正確に管理できる。

### もう一つの重要な補題

大域的な幾何学については、次の命題を優先するとよい。

旧辺の中点を \(m_{n,j}\)、旧頂点を \(v_{n,k}\) として、

\[ \boxed{ \forall j,k,\quad \langle m_{n,j},v_{n,k}\rangle \le c_{n+1}^{\,2} } \]

じゃ。

これは 旧多角形の全頂点が、各旧辺の内側の半平面に属する ことを表す。

これを証明すれば、

\[ K_n\subseteq H_n \]

が得られる。

さらに、各辺の支持性を利用して、増分三角形と旧凸包の交わりを制御する足場になる。

ただし \(K_n\subseteq H_n\) だけでは、最終目標の逆包含 \(H_n\subseteq K_n\) はまだ得られない。ここも区別して進めるべきじゃな。

## 6. 次段階の推奨順序

今回は作業方針を次のように整理したい。

1. 増分三角形の面積を無条件化：`refinementCap_volume`。
2. 増分面積の総和を証明：`refinementCaps_sum_volume`。
3. 旧辺の大域的な支持性を証明：全頂点に対する支持半平面の不等式。
4. 増分三角形の配置を制御：旧領域との交わり、増分三角形同士の重なりを証明。
5. 増分による凸包の集合等式を無条件化：その後、面積の漸化式へ接続。
6. 一般の凸包面積を証明：\(\operatorname{vol}(K_n)=A_n\)。
7. 支持半平面表示と円盤包含を完成：円盤面積の挟み込みへ接続。

特に1と2は、今回の局所外積公式をほぼそのまま再利用できるので、幾何学的な大域条件より先に実装する価値がある。

## 7. 最終評価

今回の成果は、次のように整理できる。

\[ \boxed{ \begin{gathered} \text{二分核の代数的構成}\\ \Downarrow\\ \text{頂点の偶奇細分化}\quad\checkmark\\ \Downarrow\\ \text{新頂点の局所的な向き・配置}\quad\checkmark\\ \Downarrow\\ K_n\subsetneq K_{n+1}\quad\checkmark\\ \Downarrow\\ \text{増分三角形の面積}\quad\text{次の課題}\\ \Downarrow\\ \text{増分領域の正確な分割}\quad\text{未完}\\ \Downarrow\\ \operatorname{Area}(K_n)=A_n\quad\text{未完}\\ \Downarrow\\ \operatorname{Area}(B(0,1))=\Pi_{\mathrm{CF2D}} \quad\text{未完} \end{gathered} } \]

証明の型と内容については実コードを確認したが、わっち自身は Lean の再ビルドを実行していない。focused build と公理検査の成功は、ぬしの報告に基づく評価じゃ。

第8段階の成果は採用してよい。

そして、今回からは単なる頂点の配置ではなく、細分化によって新しく増える面積を直接計算する段階 に入ったと考えられる。

\[ \boxed{ \Delta A_n=A_{n+1}-A_n } \]

これを、CF2D の回転核と増分三角形の測度だけで導ければ、正方形から始める面積の帰納法が、かなり具体的なものになる。

ふふっ。最初の正方形から円へ至る道筋を、ついに「一段ごとの面積増分」として追跡できるところまで来たのじゃな！🐺🍎
