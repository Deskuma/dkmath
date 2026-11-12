おおおっ！！ぬしよ、また一段進んだのう！🐺🍎

指定ブランチの最新コードを確認したぞ。

今回の更新で、CF2D は「πを使わずに定数を構成する」段階から、「πを使わずに収束速度まで保証し、実際の正多角形の幾何学へ接続する」段階へ進んだ。

しかも、レビューの結果、もう一つ重要な発見があった。

誤差上界は、今回証明された \(8(1/2)^n\) よりも、さらに強くできる！

## 1. レビュー結果

対象コミット：[`10d3ec3592`](https://github.com/Deskuma/dkmath/commit/10d3ec359270971be8b88d3b20c3f03a7e7b7e4b)

まず Git の件は訂正しておこう。`develop` と比較したところ、対象ブランチは6コミット先行、遅れ0コミットだった。開発ブランチとして問題ない のじゃ。

| レビュー項目               | 判定               |
| -------------------------- | ------------------ |
| π-free な二分核            | 合格               |
| 内外からの上界・下界       | 合格               |
| 第一成分の収束             | 合格               |
| 内外誤差の0への収束        | 合格               |
| 明示的な誤差上界           | 合格・改善余地あり |
| 正多角形の頂点構成         | 合格               |
| 頂点の単位円上への配置     | 合格               |
| 頂点の相異性・等角回転     | 合格               |
| ユークリッド周長との一致   | 合格               |
| 靴紐公式による符号付き面積 | 合格               |
| 凸包の測度としての面積     | 未証明             |
| 稠密性                     | 未証明             |

コードを読む限り、主要定理の論理構成に明白な問題は見当たらなかった。Lean の再ビルドと公理検査については Codex の実行報告に基づく評価じゃ。

## 2. `IntrinsicBounds.lean` の成果

[ソースを見る](https://github.com/Deskuma/dkmath/blob/dev/CF2D-pi-261112-v0/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/IntrinsicBounds.lean)

今回の実装は、非常に重要な関係を完成させている。

\[ \boxed{ A_n\le\Pi_{\mathrm{CF2D}}\le U_n } \]

しかも、

\[ \lim_{n\to\infty}A_n =\lim_{n\to\infty}U_n =\Pi_{\mathrm{CF2D}} \]

が証明されている。

これは 内側と外側の両方から同じ定数へ収束する ことを意味する。

そして、

\[ 0\le U_n-A_n\le8\left(\frac12\right)^n \]

という、π-free な誤差評価も得られた。

ここまでは Codex の成果じゃ。

### ところが、さらに強い評価を導ける！

既存の定理から、

\[ A_{n+1}=2^{n+2}s_{n+1}\le4 \]

が成立している。

したがって、

\[ s_{n+1}\le\frac1{2^n} \]

となる。

一方、単位核の保存量は、

\[ c_{n+1}^2+s_{n+1}^2=1 \]

じゃな。

ここで内外の差を計算してみよう。

\[ \begin{aligned} U_n-A_n &=\frac{A_{n+1}}{c_{n+1}}-c_{n+1}A_{n+1}\\ &=\frac{A_{n+1}(1-c_{n+1}^2)}{c_{n+1}}\\ &=\frac{A_{n+1}s_{n+1}^2}{c_{n+1}} \end{aligned} \]

すでに、

\[ A_{n+1}\le4,\qquad c_{n+1}\ge\frac12 \]

も証明済み。

ゆえに、

\[ U_n-A_n \le\frac{4}{1/2}\left(\frac1{2^n}\right)^2 \]

すなわち、

\[ \boxed{ 0\le U_n-A_n\le8\left(\frac14\right)^n } \]

なんと、誤差の減少率を \(2^{-n}\) から \(4^{-n}\) へ強化できるのじゃ！

これもπ-freeじゃ。

しかも、新しい数学的仮定は必要ない。既存定理を組み合わせるだけで証明できる。

この評価を使えば、

\[ \boxed{ \begin{aligned} 0&\le\Pi_{\mathrm{CF2D}}-A_n \le8\cdot4^{-n}\\ 0&\le U_n-\Pi_{\mathrm{CF2D}} \le8\cdot4^{-n} \end{aligned} } \]

まで導ける。

これを次の小さな改善として Codex に依頼する価値があるぞ。

## 3. 幾何学との接続は大きな前進

[IntrinsicRegularPolygon.lean](https://github.com/Deskuma/dkmath/blob/dev/CF2D-pi-261112-v0/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/IntrinsicRegularPolygon.lean)

今回はこちらの成果も大きい。

特に、

```
theorem regularKernel_dyadic (n : ℕ) :
    regularKernel (dyadicSides n) = (sequence n).kernel
```

によって、二分核が既存の正多角形の生成核と一致することを示している。

さらに、

```
theorem intrinsicPolygonSignedArea_eq_areaApprox (n : ℕ) :
    intrinsicPolygonSignedArea n = areaApprox n
```

および、

```
theorem intrinsicPolygonPerimeter_div_two (n : ℕ) :
    intrinsicPolygonPerimeter n / 2 =
      halfPerimeterApprox n
```

が証明されている。

これによって、以前は単なる代数列だった \(A_n\)、\(P_n\) が、実際の頂点座標を使った幾何学的な計算と結び付いた。

しかも、それらの証明の核心は、

\[ \det(v_j,v_{j+1})=s_n \]

という、回転核の第二成分がそのまま隣接頂点の外積になる関係じゃ。

これは美しいのう。

回転核の代数的不変量から、面積の構成要素が直接得られている。

ただし一点、依存関係を確認しておこう。

`IntrinsicRegularPolygon.lean` は `IntrinsicPiBridge` と `EuclideanRegularOrbit` を import し、`regularKernel_dyadic` では `sequence_trig` を使っている。

したがって、この幾何学モジュール自体は π-free な依存構造ではない。これは設計上の誤りではなく、内在的な核を既存のユークリッド幾何へ接続する bridge 側の役割だからじゃ。

## 4. 次の重要目標は「測度としての面積」

現在証明されているのは、

\[ A_n=\frac12\sum_{j=0}^{N_n-1} \det(v_j,v_{j+1}) \]

じゃ。

次に必要なのは、

\[ \boxed{ \operatorname{volume} \left( \operatorname{conv}\{v_0,\ldots,v_{N_n-1}\} \right) =A_n } \]

という命題じゃな。

そのためには、多角形の頂点が反時計回りに並び、単純かつ凸であることを確認し、原点と隣接頂点で作る三角形による分割を測度の加法性へ結び付ければよい。

ここが完成すれば、単に靴紐和を計算しただけではなく、実際の領域の面積がCF2Dの代数列に一致する ことになる。

さらに、正多角形の面積が円盤の面積に収束することを示せれば、

\[ \lim_{n\to\infty}\operatorname{Area}(P_n) =\operatorname{Area}(\text{単位円盤}) \]

となる。

これを既存の、

\[ \lim_{n\to\infty}A_n=\Pi_{\mathrm{CF2D}} \]

と接続できる。

そうなれば、πとの一致に対して、三角関数の `sinc` を利用した解析的経路に加え、幾何学的な測度からの独立した経路 を構築できるのじゃ。

## 5. 賢狼の評価

ぬしよ、今回の進展で重要なのは、数学的な依存の向きが明確になったことじゃ。

\[ \boxed{ \begin{gathered} \text{CF2D 代数}\\ \downarrow\\ \text{平方根による二分核}\\ \downarrow\\ \text{面積・周長の代数列}\\ \downarrow\\ \text{π-free な内外評価と収束}\\ \downarrow\\ \Pi_{\mathrm{CF2D}}\\ \downarrow\\ \text{ユークリッド幾何への接続}\\ \downarrow\\ \text{実際の正多角形の面積・周長} \end{gathered} } \]

すでに、かなりの部分が Lean で証明されている。

しかも、単調収束と誤差評価は π-free なまま完成している。

これは、πを使ってπを近似したという循環的な話とは明確に異なる。

最後に残るのは、この代数構造が生み出す面積が、ユークリッド平面で実際に測定される面積と一致することの完全な形式化 じゃ。

そして、わっちは今回の追加成果として、

\[ \boxed{ U_n-A_n\le8\cdot4^{-n} } \]

を強く推したい。

これは既存のCF2D定理だけで導ける、より高精度な誤差保証じゃ。

次は、誤差の \(4^{-n}\) 評価を取り込みつつ、凸包の測度と靴紐和を接続する。

ここまで進めば、DkMath の `IntrinsicPi` は、数学的にもソフトウェア的にも一層完成度の高いモジュールになるぞ。🐺🍎

---

誤差上界を **π-free の `8(1/4)ⁿ` に強化**しました。凸包の測度との接続は、可測な領域と三角形分割の候補まで実装しましたが、面積の等式はまだ未証明です。

[IntrinsicBounds.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/IntrinsicBounds.lean) に、保存量から得る厳密な差の式と、次の評価を追加しました。

\[
\begin{aligned}
0 &\le U_n-A_n \le 8(1/4)^n,\\
0 &\le \mathrm{intrinsicPi}-A_n \le 8(1/4)^n,\\
0 &\le U_n-\mathrm{intrinsicPi} \le 8(1/4)^n.
\end{aligned}
\]

[IntrinsicPolygonMeasure.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/IntrinsicPolygonMeasure.lean) では、頂点の凸包を実際のユークリッド平面の集合として定義し、コンパクト性、可測性、単位閉円盤への包含を証明しました。共通頂点を持つ三角形の候補についても、それぞれがコンパクトで凸包に含まれることを示しました。

**未達成の箇所**は、凸包の測度が `Aₙ` に等しいという定理と、そこから円盤面積への収束を得る独立した幾何学的経路です。三角形候補が凸包全体を覆うこと、重なりが測度ゼロであること、各三角形の測度と行列式の関係が必要です。追加した凸包の測度上界は、既存の `intrinsicPi = Real.pi` と円盤面積公式に依存しています。

[回帰テスト](/lean/dk_math/DkMathTest/CosmicFormula/Rotation/CF2D/IntrinsicPiReview.lean) と CF2D 集約モジュールのビルド、`git diff --check` は成功しました。主要追加定理の公理依存は `[propext, Classical.choice, Quot.sound]` のみです。
