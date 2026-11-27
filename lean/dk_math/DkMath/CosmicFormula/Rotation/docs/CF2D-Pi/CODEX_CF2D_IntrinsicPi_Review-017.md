# CF2D Intrinsic π — 017 実装レビュー 🐺🍎

D.よ、ついに支持不等式まで到達したのぅ！ 🐺🍎

## **レビュー016：保存量による支持不等式**

π-free な支持不等式を確認

[DyadicConeSupport.lean](https://github.com/Deskuma/dkmath/blob/dev/CF2D-pi-261112-v1/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/DyadicConeSupport.lean) と [IntrinsicPolygonSupport.lean](https://github.com/Deskuma/dkmath/blob/dev/CF2D-pi-261112-v1/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/IntrinsicPolygonSupport.lean) を確認した。

**判定：レビュー015で提案した、保存量と錐の内部非交差による二つの支持不等式は実装されている。**

今回の証明構造は非常によい。

### **1. 証明の完成範囲**

| 定理                                       | 役割                                           | 判定 |
| ------------------------------------------ | ---------------------------------------------- | ---- |
| `strictCone_mem_interior`                  | 正の係数表示から錐の内部所属を導く             | 完成 |
| `outside_chord_mem_cone_interior`          | 支持直線の外側を錐の内部へ対応させる           | 完成 |
| `orbit_vertex_mem_closure_cone_interior`   | 頂点を自身の錐の内部点で近似する               | 完成 |
| `orbit_vertex_not_mem_other_cone_interior` | 別の頂点が指定した錐の内部に入らないことを示す | 完成 |
| `directVertex_mem_edge_halfspace`          | 全旧頂点の支持不等式                           | 完成 |
| `other_odd_mem_halfspace_pi_free`          | 他の辺の奇数頂点の支持不等式                   | 完成 |

特に評価したいのは、`outside_chord_mem_cone_interior` の証明じゃ。

\[ q_2(x) = (a+b)^2-2(1-c_n)ab \]

という恒等式から、

\[ q_2(x)\le1,\qquad a+b>1 \]

を使い、\(ab>0\) を導いている。

これは三角関数による角度比較を、保存量の不等式に置き換えたことを意味する。

しかも、旧頂点と奇数頂点の両方を同じ原理で処理しておる。

**単なるコードの置換ではなく、証明原理そのものが変わった** わけじゃな。

## **2. 依存関係の変化**

以前は支持不等式の証明に、

\[ \cos(\theta_1)\le\cos(\theta_2) \]

という角度比較を使っていた。

現在は、

\[ \boxed{ \begin{aligned} q_2(x)\le1 &\Longrightarrow \text{保存量による制約}\\ &\Longrightarrow \text{錐の内部所属}\\ &\Longrightarrow \text{内部非交差との矛盾}\\ &\Longrightarrow \text{支持不等式} \end{aligned} } \]

という構成になっている。

新規ファイルには `Real.pi`、`Real.sin`、`Real.cos` の直接参照がなく、`sorry`、`admit`、追加の `axiom` 宣言も見当たらない。

公開 import と主要定理の `#print axioms` 登録も確認できた。

## **3. 残る標準角度依存はどこか**

現在の `IntrinsicPolygonSupport.lean` では、既存のユークリッド多角形への移送に次の補題を使っている。

```
directVertex_eq_regularVertex
```

具体的には、次の等式じゃ。

```
private theorem directVertex_plane (n : ℕ)
    (j : Fin (dyadicSides n)) :
    pairToEuclideanPlane (directVertex n j).toProd =
      (intrinsicRegularPolygon n).vertices j
```

つまり、 **直接軌道についての支持不等式は π-free になったが、既存の多角形との同一視には bridge が残っている** 。

これはぬしの報告どおりじゃ。

ここから先は、証明内容よりもモジュールの依存関係を整理する仕事になる。

## **4. 次の優先課題：直接軌道から多角形を定義する**

わっちの提案は、既存の `intrinsicRegularPolygon` をすぐ変更することではない。

新しく、二分核だけからユークリッド平面の頂点集合を定義することじゃ。

例えば、概念的には次の形になる。

```
noncomputable def intrinsicDirectVertex
    (n : ℕ) (j : Fin (4 * 2 ^ n)) : EuclideanPlane :=
  pairToEuclideanPlane (directVertex n j).toProd
```

そして、この頂点集合の凸包を定義する。

そうすれば、

1. `DyadicConeSupport` の支持不等式を直接利用する。
2. 直接軌道の凸包について支持半平面表示を証明する。
3. 直接軌道の増分三角形とその面積を計算する。
4. 既存のユークリッド多角形との一致は、最後に bridge として証明する。

という分離が可能になる。

| 層                  | 内容                            | 標準角度への依存 |
| ------------------- | ------------------------------- | ---------------- |
| 二分核              | `HalfKernel`、`HalfKernelOrder` | 不要             |
| 位相と錐            | `DyadicPhase`、`DyadicCone`     | 不要             |
| 支持性              | `DyadicConeSupport`             | 不要             |
| 直接多角形          | 新しい幾何層                    | 不要を目指す     |
| 既存軌道との bridge | `directVertex_eq_regularVertex` | 必要             |

ただし、円盤測度まで完全に π-free な import 依存で再構成するには、三角形の測度公式や凸包面積の帰納法も直接軌道側へ接続する必要がある。

今回の支持不等式の無条件化だけで、その全工程が完了したわけではない点は区別しておこう。

### **総評**

**レビュー016の支持不等式は、数学的にも実装構造としても良好じゃ。**

わっちが特に評価するのは、以前から存在していた `Vec.q2` が、今回の幾何学的な支持性の証明に直接使われたことじゃ。

保存量は単に「回転しても長さが変わらない」という性質にとどまらなかった。

それが、

- 頂点の配置
- 非負錐の内部所属
- 全周の扇形分割
- 凸多角形の支持性

を結び付ける中心的な道具になった。

これは、ぬしが研究してきた保存核構造の一つの具体的な成果と言える。

**次のレビュー017では、直接軌道から定義する凸多角形の π-free 幾何層を独立させること** を推すぞ。

D.よ、ここまで来ると、最初に使っていた標準角度が「定義の土台」から「最後に比較する対象」へ移りつつある。

それこそ、今回の発展編が目指していた方向じゃな！
