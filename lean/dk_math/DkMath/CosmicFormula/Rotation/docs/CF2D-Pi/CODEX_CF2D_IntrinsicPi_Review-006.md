# CF2D Intrinsic π — v1 実装レビュー 🐺🍎

ぬしよ、今回のレポートは慎重でよい。特に 「型検査に成功した定理」と「まだ仮定として残っている幾何条件」を明確に区別している 点を評価するぞ。

報告された HEAD [`842845e5bf62d569e0ca352c96c4f3cc5db0b4fe`](https://github.com/Deskuma/dkmath/commit/842845e5bf62d569e0ca352c96c4f3cc5db0b4fe) の実コードを取得して確認した。

## 総合判定

証明済みの成果は採用可能。幾何学的な最終定理は未完成。研究の進行方向は適切じゃ。

| 領域                                   | 現在の状態               | 判定 |
| -------------------------------------- | ------------------------ | ---- |
| π-free な回転核・二分割                | 証明済み                 | 合格 |
| π-free な `intrinsicPi` の定義         | 証明済み                 | 合格 |
| 単調収束と \(8\cdot4^{-n}\) の誤差保証 | 証明済み                 | 合格 |
| `intrinsicPi = Real.pi`                | 解析的 bridge で証明済み | 合格 |
| 標準三角形の測度 \(1/2\)               | 無条件で証明済み         | 合格 |
| 一般の原点三角形の測度                 | 無条件で証明済み         | 合格 |
| 隣接・対向三角形の測度零の交わり       | 証明済み                 | 合格 |
| 正方形 \(n=0\) の全三角形対            | 証明済み                 | 合格 |
| 一般の \(n\) の凸包被覆                | 未証明                   | 継続 |
| 一般の \(n\) の全三角形対              | 未証明                   | 継続 |
| 内接円盤の凸包包含                     | 未証明                   | 継続 |
| 円盤測度と `intrinsicPi` の無条件一致  | 未証明                   | 継続 |

## 1. 今回の特筆すべき成果：正方形から三角形の面積を証明

[IntrinsicStandardTriangleMeasure.lean](https://github.com/Deskuma/dkmath/blob/842845e5bf62d569e0ca352c96c4f3cc5db0b4fe/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/IntrinsicStandardTriangleMeasure.lean)

`standardTriangle_volume` の実装を確認した。

証明は、単位正方形を対角線で二つに分け、中心反転によって双方の測度が等しいことを示す構成じゃ。

\[ \operatorname{vol}([0,1]^2)=1 \]

\[ \operatorname{vol}(\Delta) =\operatorname{vol}(R(\Delta)) \]

\[ \operatorname{vol}(\Delta\cap R(\Delta))=0 \]

したがって、

\[ \boxed{\operatorname{vol}(\Delta)=\frac12} \]

となる。

これはわれわれが前回提案した 正方形の対称性から半分の面積を復元する方法 そのものじゃ。

しかも、Codex は対角線を適切なアフィン部分空間として構成し、その二次元測度がゼロであることまで証明している。

`standardTriangle_volume` から、任意の段階 \(n\) と頂点番号 \(j\) について、

\[ \boxed{ \operatorname{vol}(T_{n,j})=\frac{s_n}{2} } \]

も無条件で証明済みじゃ。

これは重要な進歩じゃよ。一般の三角形の面積公式について、未解決の仮定はもう残っておらぬ。

## 2. 半周対称性と隣接三角形の証明

[IntrinsicPolygonAntipodal.lean](https://github.com/Deskuma/dkmath/blob/842845e5bf62d569e0ca352c96c4f3cc5db0b4fe/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/IntrinsicPolygonAntipodal.lean)

この実装もよい。

半周先の頂点について、

\[ v_{j+N_n/2}=-v_j \]

を証明し、さらに対応する三角形について、

\[ T_{j+N_n/2}=-T_j \]

を得ている。

そこから、

\[ \boxed{ T_j\cap T_{j+N_n/2}=\{0\} } \]

を証明している。

これは単なる面積ゼロの主張よりも強い、集合としての厳密な等式じゃ。

一方、[IntrinsicPolygonAdjacent.lean](https://github.com/Deskuma/dkmath/blob/842845e5bf62d569e0ca352c96c4f3cc5db0b4fe/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/IntrinsicPolygonAdjacent.lean) では、隣接する二つの三角形の共通部分が共有頂点方向の直線上にあることを証明している。

両者の共通部分が測度ゼロになることも正しい。

ただし、一般の \(N_n\) 角形では、隣接でも対向でもない組が存在する。

例えば正八角形では、\(T_0\) と \(T_2\) はどちらでもない。

今回のレポートは、ここを未証明として正しく残しておる。

## 3. 正方形の面積が2であることと、その凸包の面積が2であることは別

[IntrinsicPolygonFan.lean](https://github.com/Deskuma/dkmath/blob/842845e5bf62d569e0ca352c96c4f3cc5db0b4fe/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/IntrinsicPolygonFan.lean)

ここには、次の定理がある。

```
theorem intrinsicOriginFan_zero_volume :
    volume (intrinsicOriginFan 0) = ENNReal.ofReal 2
```

これは無条件の定理じゃ。

しかし、凸包の面積として証明されているのは、

```
theorem intrinsicPolygonRegion_zero_volume_ge_two :
    ENNReal.ofReal 2 ≤ volume (intrinsicPolygonRegion 0)
```

までじゃな。

この区別は非常に重要。

原点ファンの測度が2であることは、まだ凸包全体の測度が2であることを意味しない。

次に比較的短く証明できそうなのは、

\[ \boxed{ K_0=\operatorname{intrinsicOriginFan}(0) } \]

じゃ。

正方形では、4頂点が、

\[ (1,0),(0,1),(-1,0),(0,-1) \]

となり、その凸包は、

\[ K_0=\{(x,y)\mid |x|+|y|\le1\} \]

で表せる。

これと4枚の原点三角形の和集合を一致させれば、

\[ \boxed{ \operatorname{vol}(K_0)=2 } \]

が無条件で成立する。

一般の \(n\) に進む前に、正方形の凸包面積を完全に閉じる のは有効な小目標じゃろう。

## 4. 辺の半平面についても、正しい境界に到達している

[IntrinsicPolygonCircumscribed.lean](https://github.com/Deskuma/dkmath/blob/842845e5bf62d569e0ca352c96c4f3cc5db0b4fe/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/IntrinsicPolygonCircumscribed.lean)

今回は各辺の中点 \(m_j\) を使って、

\[ H_n= \bigcap_j \left\{ x\;\middle|\; \langle m_j,x\rangle\le c_{n+1}^2 \right\} \]

を定義している。

そして、

\[ \boxed{ B(0,c_{n+1})\subseteq H_n } \]

が証明済みじゃ。

この証明はコーシー・シュワルツの不等式と、

\[ \|m_j\|=c_{n+1} \]

だけで成立している。

次に必要なのは、

\[ \boxed{H_n\subseteq K_n} \]

じゃな。

ただし、わっちはここで少し設計を変えることを提案したい。

目標をさらに強めて、

\[ \boxed{ K_n=H_n } \]

という 凸包の支持半平面表示 を証明してはどうか。

これは有限個の頂点で定めた正多角形と、その各辺が定める半平面の共通部分とが一致するという定理じゃ。

これが成立すれば、内接円盤の包含は直ちに従う。

さらに、正多角形の凸性を示す基礎定理として、今後の三角形分割にも再利用できる。

ただし、この等式を証明するには、頂点が適切な巡回順序で並ぶことを利用する必要がある。

単に辺の中点の距離が等しいというだけでは、等式は成立せぬ。

## 5. 賢狼から、今回の最も重要な追加提案

ぬしよ。

最新コードを読みながら、わっちはもう一つ重要なことに気づいた。

CF2D の二分核から、πを使用せずに、正 \(4\cdot2^n\) 角形の巡回群そのものを構成できる可能性がある。

これは以前からの「幾何モジュールは解析 bridge に依存している」という課題を解消する方法じゃ。

現在の単位核を、

\[ g_n=(c_n,s_n) \]

と書こう。

すでに証明済みの `sequence_star` から、

\[ g_{n+1}^{\,2}=g_n \]

が成立する。

そこで、この式を繰り返せば、

\[ \boxed{ g_n^{\,2^n}=g_0 } \]

が得られる。

初期核は、

\[ g_0=(0,1) \]

であるから、

\[ g_0^2=(-1,0) \]

\[ g_0^4=(1,0) \]

じゃな。

したがって、

\[ \boxed{ \begin{aligned} g_n^{\,2^{n+1}}&=(-1,0)\\ g_n^{\,2^{n+2}}&=(1,0) \end{aligned} } \]

が成立する。

ここで重要なのは、\(2^{n+2}\) が2の冪であることじゃ。

\(g_n\) の位数は \(2^{n+2}\) を割り切る。一方、その半分の冪では単位元にならない。

したがって、

\[ \boxed{ \operatorname{orderOf}(g_n)=2^{n+2} =4\cdot2^n } \]

となる！

これは、三角関数もπも使わずに証明できる群論的な命題 じゃ。

そして、この核の冪を使って、

\[ v_{n,j}=g_n^j\star(1,0) \]

と定めれば、ちょうど \(4\cdot2^n\) 個の相異なる頂点を作れる。

しかも、すべての頂点は、

\[ Q(v_{n,j})=1 \]

を満たす。

### なぜ、これが重要か

現在の `IntrinsicRegularPolygon.lean` は、既存の `EuclideanRegularOrbit` に接続するため、`Real.pi` や `Real.sin`、`Real.cos` を利用している。

しかし、上記の位数の証明ができれば、頂点の個数・巡回・単位円上への配置を、CF2D の代数だけで保証できる。

もちろん、頂点が幾何学的に反時計回りの凸多角形を形成することや、凸包の面積を求めることには追加証明が必要じゃ。

それでも、依存関係は大幅に改善する。

わっちは、これを独立した研究課題として強く推したい。

## 6. Codex に対する次のレビュー指示

残る作業は、次の順序で進めるのがよいじゃろう。

1. 正方形 \(n=0\) の凸包を閉じる。 `intrinsicPolygonRegion 0 = intrinsicOriginFan 0` と、凸包測度が2であることを無条件で証明する。
2. 二分核の正確な位数を証明する。 \(g_n^{2^n}=g_0\)、`orderOf g_n = 4 * 2^n` をπ-free で形式化する。
3. 一般の巡回順序を定式化する。 非隣接頂点の相対位置を、添字の巡回順序から制御する。
4. 一般の原点ファンを完成させる。 被覆と全ての異なる三角形対の `AEDisjoint` を証明し、凸包の面積公式を無条件化する。
5. 支持半平面と凸包を接続する。 \(H_n=K_n\) を目標に、内接円盤の包含を導く。
6. 最終定理を無条件化する。 既存の条件付き挟み込み定理に証明済みの補題を渡し、円盤測度が `intrinsicPi` に一致することを示す。

このうち位数の証明は、最終的な測度の同一性に直接必須というわけではない。しかし CF2D 固有の代数から幾何学までを一貫させる という意味で、重要な設計改善じゃ。

## 7. コード品質・検証について

今回の実装を読む限り、重大な数学的矛盾や、仮定を隠した無条件定理は見つからなかった。

ただし、いくつかの注意点はある。

`Polygon` 型の意味：固定 Mathlib v4.34.1 の `Mathlib.Geometry.Polygon.Basic` も確認した。この `Polygon` は基本的に `Fin n → P` という頂点列を持つ構造であり、凸性や自己交差の不在を型だけで保証するものではない。したがって、今回残っている巡回順序・凸性・領域分割の証明は必要じゃ。

公理検査の意味：`#print axioms` の結果が標準公理だけでも、条件付き定理の引数 `hcover` などは解消されない。今回のレポートはその点を正しく認識している。

回帰テスト：`IntrinsicPiReview.lean` には、原点所属や中点距離など同じ内容の `example` が複数箇所にある。動作上の問題ではないが、今後は整理してもよい。

ビルド：focused build の成功はユーザー報告として扱う。今回わっちは GitHub のソースを検証したが、同一環境で Lean のコンパイラを実行したわけではない。8983 jobs という表示も、クリーンビルドを意味するものとしては扱わぬ。

## 8. 最終評価

現在、二つの道が見えておる。

解析的な道は完成している。

\[ \boxed{ \text{CF2D} \longrightarrow A_n \longrightarrow\Pi_{\mathrm{CF2D}} \longrightarrow\mathrm{Real.pi} } \]

一方、幾何学的な道は、残る定理が明確になった段階じゃ。

\[ \boxed{ \begin{gathered} \text{CF2D の二分回転}\\ \Downarrow\\ \text{有限巡回軌道}\\ \Downarrow\\ \text{正多角形の凸包}\\ \Downarrow\\ \text{三角形分割による面積}\\ \Downarrow\\ \text{円盤の内外挟み込み}\\ \Downarrow\\ \Pi_{\mathrm{CF2D}} \end{gathered} } \]

現時点では、後者が独立した証明として完成したとは言えぬ。しかし、標準三角形の面積、各原点三角形の面積、半周対称性、局所的な重なりの測度零までが証明されたことは確かな前進じゃ。

そして、今回わっちが特に注目するのは、二分核の位数から直接、

\[ \boxed{\operatorname{orderOf}(g_n)=4\cdot2^n} \]

を導けるという点じゃ。

これはぬしが最初に考えていた 「半分にしていく対称性から、全体の構造が復元される」 という発想を、群論の定理として表現するものになる。

第5段階の成果を維持しつつ、v1 は継続開発を推奨。次の最重要課題は一般の凸包被覆と内接円盤の包含じゃ。

ふふっ。CF2D の π 研究が、単なる定数の構成から、代数・群論・幾何・測度論をつなぐ体系へ育ってきたのう。🐺🍎
