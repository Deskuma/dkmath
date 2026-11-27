# CF2D Intrinsic π — 010 実装レビュー 🐺🍎

D.よ、今回の追加はかなり重要な前進じゃ。🐺

GitHub 上の [IntrinsicRefinementCapMeasure.lean](https://github.com/Deskuma/dkmath/blob/dev/CF2D-pi-261112-v1/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/IntrinsicRefinementCapMeasure.lean) と関連モジュールを確認した。

## **レビュー010：判定**



証明構造は妥当

一般の幾何学的分割は未完了



**増分三角形の面積計算と、その総和の恒等式は、幾何学的な未証明条件から独立して完成しておる。**

今回の意義は、一般の凸包面積公式に必要な仕事を、ほぼ純粋な幾何学的配置の問題へ分離できたことじゃ。

### **1. 確認できた成果**

| 定理                                                 | レビュー結果                                            |
| ---------------------------------------------------- | ------------------------------------------------------- |
| `triangle_volume_eq_abs_cross`                       | 任意の3頂点について、凸包の測度を行列式の絶対値から計算 |
| `refinementCap_cross`                                | 増分三角形の行列式を \(2s_{n+1}-s_n\) と計算            |
| `refinementCap_volume`                               | 各増分三角形の測度公式を無条件で証明                    |
| `refinementCaps_sum_volume`                          | 全増分三角形の測度の総和を \(A_{n+1}-A_n\) と同一視     |
| `intrinsicPolygonRegion_volume_succ_of_caps`         | 被覆・測度零の交わりを仮定した一段の面積増分            |
| `intrinsicPolygonRegion_volume_of_cap_decomposition` | 正方形の既知の面積を基底とする条件付き帰納法            |

特に、重要な式は

\[ \operatorname{volume}(C_{n,j}) = \operatorname{ENNReal.ofReal} \left(s_{n+1}-\frac{s_n}{2}\right) \]

および

\[ \sum_{j=0}^{4\cdot 2^n-1} \operatorname{volume}(C_{n,j}) = \operatorname{ENNReal.ofReal}(A_{n+1}-A_n) \]

じゃ。

ここで気に入ったのは、最初に一般三角形の測度公式を独立させた設計じゃな。後続の幾何定理にも再利用できる。

### **2. 帰納法の仮定は適切か**

適切じゃ。

追加された条件付き定理は、次の3条件を明確に要求しておる。

1. 次段階の凸包が旧領域と増分三角形で覆われる。
2. 異なる増分三角形どうしが、測度の意味でほとんど交わらない。
3. 旧領域と増分三角形の和集合が、測度の意味でほとんど交わらない。

これらから測度の加法性を適用し、

\[ \begin{aligned} \operatorname{volume}(K_{n+1}) &=\operatorname{volume}(K_n)   +\sum_j\operatorname{volume}(C_{n,j})\\ &=A_n+(A_{n+1}-A_n)\\ &=A_{n+1} \end{aligned} \]

と進める。

基底 \(n=0\) についても、既に無条件で証明した正方形の測度 \(2=A_0\) を利用している。

**循環論法になっていない** ことを確認できたのは大きい。

## **3. 次の最優先課題**

わっちは、次の順序を勧める。

### **優先1：旧辺の大域的支持性**

任意の旧辺 \(j\) について、その辺が定める内側半平面を \(H_{n,j}\) とすれば、

\[ K_n\subseteq H_{n,j} \]

を証明する。

既に `refinement_vertex_strictly_outside_old_edge_line` があるため、支持性が得られれば、新頂点が旧領域の外側にあることを半平面で説明できる。

そこから、旧領域と当該増分三角形の交わりが旧辺上に限られることを示せるはずじゃ。

これは `hold` を解消する直接的な経路になる。

### **優先2：増分三角形どうしの交わり**

次に必要なのは

\[ i\ne j \Longrightarrow \operatorname{AEDisjoint} \bigl(\operatorname{volume},C_{n,i},C_{n,j}\bigr) \]

じゃ。

ここでは単なる隣接添字の分類だけでなく、巡回順序と支持半平面の関係が重要になる。

旧辺の支持性を先に確立しておけば、この段階で使える分離条件も増える。

### **優先3：被覆**

既に

\[ K_{n+1} = \operatorname{conv}\left( K_n\cup\bigcup_j C_{n,j} \right) \]

は証明済みじゃ。

したがって、残るのは凸包を取り除ける条件を確立すること。

ただし、ここには一つ別案がある。

**面積公式だけを目的とするなら、集合としての完全一致は必須ではない。**

既知の包含

\[ K_n\cup\bigcup_j C_{n,j}\subseteq K_{n+1} \]

を利用し、差集合について

\[ \operatorname{volume}\left( K_{n+1}\setminus \left(K_n\cup\bigcup_j C_{n,j}\right) \right)=0 \]

を証明する経路もある。

これは集合等式より弱い主張じゃ。一般の凸包分割を完全に形式化するのが難航する場合、検討する価値があるのぅ。

## **4. 改善提案**

小さな提案が二つある。

- 専用回帰テストに `refinementCap_volume`、`refinementCaps_sum_volume`、条件付き帰納法の型を直接確認する `example` を追加する。現在のテストは集約 import を通じて新ファイルを型検査するが、新しい定理を直接呼ぶ例は確認できなかった。
- 新規定理についても `#print axioms` を取得する。ソースには `sorry` や新しい公理宣言は見当たらないが、公理依存の監査結果は別に記録しておくとよい。

なお、新規ファイルに `Real.pi` の直接参照がないことと、幾何モジュール全体が π-free であることは別じゃ。既存の標準角度との bridge を import 経由で利用している点は、これまでどおり区別しておくべきじゃな。

今回、わっちが直接確認したのは GitHub 上の証明ソースと公開 import・回帰テストの構成じゃ。Lean のビルドは手元で再実行しておらず、ビルド成功はぬしの報告に基づく。

### **総評**

**レビュー010は、証明範囲を明確にしたうえで受理相当と判断する。**

今回の成果により、一般段階の面積公式に向けた計算部分は、かなり整理された。

残る中心課題は

\[ \boxed{ \text{大域的支持性} \;\Longrightarrow\; \text{測度零の交わり・被覆} \;\Longrightarrow\; \operatorname{volume}(K_n)=A_n } \]

じゃ。

わっちとしては、次の実装対象を **旧辺の支持半平面に対する全旧頂点の包含** に絞るのがよいと思う。

これが確立すれば、局所的な外積計算から大域的な凸多角形の幾何へ橋を架けられる。いよいよ面白いところまで来たのぅ、D.よ。🍎
