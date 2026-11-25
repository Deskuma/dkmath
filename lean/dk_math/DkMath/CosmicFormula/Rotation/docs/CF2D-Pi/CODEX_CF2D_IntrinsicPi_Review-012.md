D.よ……ついに到達したのぅ！ 🐺🍎

# **レビュー012：CF2D Intrinsic π 幾何学的証明の完成**



主要目標達成

無条件定理を確認



**判定：レビュー011で残っていた最後の幾何条件は解消された。円盤の測度と&#x20;**`intrinsicPi`**&#x20;の一致が、既知の&#x20;**`intrinsicPi = Real.pi`**&#x20;を用いずに証明されている。**

GitHub 上の実装を確認した。今回は特に、支持半平面の逆包含と、最終定理の依存関係を調べたぞ。

## **1. 支持半平面表示の証明**

[IntrinsicPolygonSupport.lean](https://github.com/Deskuma/dkmath/blob/dev/CF2D-pi-261112-v1/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/IntrinsicPolygonSupport.lean?utm_source=chatgpt.com)

新しい核心は次の定理じゃ。

```
theorem intrinsicEdgeHalfSpaces_subset_intrinsicPolygonRegion (n : ℕ) :
    intrinsicEdgeHalfSpaces n ⊆ intrinsicPolygonRegion n
```

証明方法を確認したところ、次の構成になっておる。

1. `ray_angle` で、原点以外の点を極座標表示する。
2. `ray_between_vertices` で、その方向を挟む隣接頂点 \(p,q\) を選ぶ。
3. 外積から非負係数 \(a,b\) を構成し、\(x=ap+bq\) を示す。
4. 支持半平面の不等式から \(a+b\le1\) を導く。
5. 原点と \(p,q\) の凸性から、\(x\) が多角形の凸包に属することを示す。

この方法は数学的に明快じゃ。

とりわけ、係数を外積から構成している点がよい。

\[ a=\frac{\det(x,q)}{\det(p,q)}, \qquad b=\frac{\det(p,x)}{\det(p,q)} \]

であり、方向の選択から \(a,b\ge0\)、半平面条件から \(a+b\le1\) が得られる。

これにより、

\[ \boxed{K_n=H_n} \]

が完成している。

## **2. 円盤包含と最終定理**

同じファイルで、次の二つも無条件になっている。

```
intrinsicInnerBall_subset_region
closedBall_subset_intrinsicPolygonOuterRegion
```

したがって、全ての \(n\) について

\[ B(0,c_{n+1})\subseteq K_n \]

および

\[ B(0,1)\subseteq K_n^{\mathrm{out}} \]

が成立する。

さらに [IntrinsicRefinementCapMeasure.lean](https://github.com/Deskuma/dkmath/blob/dev/CF2D-pi-261112-v1/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/IntrinsicRefinementCapMeasure.lean?utm_source=chatgpt.com) の最終定理は、実際に次の形じゃ。

```
theorem disk_measureReal_eq_intrinsicPi :
    volume.real (Metric.closedBall (0 : EuclideanPlane) 1) =
      intrinsicPi :=
  disk_measureReal_eq_intrinsicPi_of_polygon_sandwich
    intrinsicPolygonRegion_volume_eq_areaApprox
    closedBall_subset_intrinsicPolygonOuterRegion
```

この定理には追加仮定がない。

証明は以前から用意していた条件付きの挟み込み定理に、今回までに完成した二つの無条件定理を渡す構成になっている。

これが美しいのぅ。

## **3. π-free 性についての厳密な判定**

ここは区別して記録しておこう。

| 項目                           | 判定                                  |
| ------------------------------ | ------------------------------------- |
| `intrinsicPi` の定義           | π-free                                |
| 数列の内外評価と誤差上界       | π-free                                |
| 凸包面積公式の最終的な数値関係 | \(A_n\) に一致                        |
| 支持半平面表示の証明           | `Real.pi`・三角関数を使用             |
| 円盤面積への最終的な挟み込み   | `intrinsicPi_eq_real_pi` を使用しない |

最後の定理は `intrinsicPi_eq_real_pi` を参照しておらず、挟み込みの既存証明にもその参照は見当たらなかった。

ゆえに、これは **解析的な同一性定理を前提としない、幾何学的な導出経路** と評価できる。

ただし、支持半平面の幾何証明そのものまで π-free になったわけではない。その点をぬしが明記しているのは正確じゃ。

## **4. 今回の監査結果**

ソースから確認した事項は次のとおり。

- 新しい最終定理に未解消の幾何仮定はない。
- 対象の追加証明に `sorry`、`admit`、公理宣言は見当たらない。
- 専用回帰テストに、半平面表示・外接領域への円盤包含・円盤測度の各 `example` がある。
- 主要二定理の `#print axioms` が回帰テストに登録されている。

ビルド成功と公理依存の実際の出力については、ぬしの報告に基づく。わっち自身は今回、Lean を再実行しておらぬ。

## **5. 次の研究課題**

今回の目的に関しては、もはや未証明の幾何条件は残っておらぬ。

そのうえで、次に進める価値があるのは次の二つじゃ。

**1. 一般の原点ファン被覆の無条件化**

実は、今回の `intrinsicEdgeHalfSpaces_subset_intrinsicPolygonRegion` の証明には、その材料がほとんど揃っている。

点 \(x\) に対し、隣接頂点 \(p,q\) と非負係数 \(a,b\) を構成し、\(a+b\le1\) を示しておるからじゃ。

これはそのまま

\[ x\in\operatorname{conv}\{0,p,q\} \]

を意味する。

したがって、証明を少し整理すれば

\[ K_n=\bigcup_j T_{n,j} \]

という、かつて未完成だった原点ファン被覆を一般の \(n\) で証明できる見込みが高い。

**2. 幾何学的証明から標準角度への依存を減らす**

今回の証明は正しい構造を持つが、角度の選択に三角関数を利用している。

将来的には、既に証明済みの二分核の正確な位数、直接軌道、外積の正性を使って、巡回順序そのものを π-free に構成できるか検討する価値がある。

これは現在の完成を妨げる課題ではなく、証明の独立性をさらに強くする研究じゃ。

## **総評**

D.よ、今回の成果は明確じゃ。

\[ \boxed{ \operatorname{volume}_{\mathbb R} \bigl(B(0,1)\bigr) = \mathrm{intrinsicPi} } \]

ここに至るまでに、

- 二分核
- 正多角形の軌道
- 面積候補と収束
- 厳密な誤差上界
- 凸包と靴紐和の対応
- 増分三角形による測度の加法性
- 支持半平面表示
- 円盤の内外挟み込み

を接続できた。

**CF2D Intrinsic π の当初の幾何学的目標は達成された、と判定する。**

わっちからのレビュー012は、ここで一区切りじゃ。

長く残っていた条件付き定理が、最後には無条件の定理へと閉じた。こういう仕事こそ、形式化の醍醐味じゃな。🍎
