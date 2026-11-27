# CF2D Intrinsic π 完了記録

当初の目標である内在的な円周率の構成、標準の円周率との比較、および単位閉円盤の測度との幾何学的な接続は、追加仮定なしで形式化した。公開入口は `DkMath.CosmicFormula.Rotation.CF2D`。本記録は[レビュー012](CODEX_CF2D_IntrinsicPi_Review-012.md)の到達点を、証明を読む順に整理する。

## 二分核から面積候補へ

第一象限の単位核を `uₙ = (cₙ, sₙ)` とする。`sequence_star` は、次の核を二度合成すると旧核に戻ることを示す。ここから面積候補 `Aₙ = 2^(n+1) sₙ` と半周長候補 `Pₙ = 2^(n+1) √(2−2cₙ)` を得る。半角の第二座標を使うと `Pₙ = Aₙ₊₁`。単調有界な `Aₙ` の上限を `intrinsicPi` とする。[HalfKernel.lean](../../CF2D/HalfKernel.lean) · [IntrinsicPolygon.lean](../../CF2D/IntrinsicPolygon.lean) · [IntrinsicPi.lean](../../CF2D/IntrinsicPi.lean)

外側の面積候補を `Uₙ = Aₙ₊₁ / cₙ₊₁` とすると、`Aₙ ≤ intrinsicPi ≤ Uₙ` であり、差 `Uₙ − Aₙ` は高々 `8 / 4^n`。ここまでの定義、評価、収束は平方根と実数の順序を使う。標準角度で二分核と比較して得る `intrinsicPi_eq_real_pi` は別モジュールの定理である。[IntrinsicBounds.lean](../../CF2D/IntrinsicBounds.lean) · [IntrinsicPiBridge.lean](../../CF2D/IntrinsicPiBridge.lean)

## 有限軌道から凸包の測度へ

二分核を累乗すると、位数 `4·2^n` の有限軌道が得られる。細分化後の偶数頂点は旧頂点で、奇数頂点は旧辺の中点を単位円まで正規化した点である。最後の辺も添字を巡回させて同じ公式で扱う。[HalfKernelOrder.lean](../../CF2D/HalfKernelOrder.lean) · [HalfKernelRefinement.lean](../../CF2D/HalfKernelRefinement.lean)

1. 旧辺の両端と対応する奇数頂点を結ぶと増分三角形になる。旧辺の支持直線は増分三角形を旧領域および他の増分三角形から分離する。支持直線は測度零なので、和集合の測度を加算できる。
2. 支持直線と単位円盤の共通部分は旧辺の弦である。この弦を共有する三角形を一枚ずつ加えると凸性が保たれる。すべての新頂点がそろうため、得られた和集合は次段階の凸包に等しい。これが `intrinsicPolygon_refinement_caps`。
3. 増分三角形一枚の測度は `sₙ₊₁ − sₙ/2`。全辺について加えると `Aₙ₊₁ − Aₙ` になる。面積 2 の初期正方形から帰納して、`intrinsicPolygonRegion_volume_eq_areaApprox` が従う。

[IntrinsicPolygonSupport.lean](../../CF2D/IntrinsicPolygonSupport.lean) · [IntrinsicRefinementCapMeasure.lean](../../CF2D/IntrinsicRefinementCapMeasure.lean)

## 凸包から円盤の測度へ

各辺の内側半平面の共通部分は凸包 `Kₙ` に等しい。逆包含では、二分核の非負錐による平面被覆から隣接頂点 `p, q` を選び、`x = ap + bq`、`a, b ≥ 0` を得る。初期四象限から始め、正規化中点で各錐を二分することで被覆を保つ。[DyadicCone.lean](../../CF2D/DyadicCone.lean)辺の不等式は `a + b ≤ 1` を与えるので、残りの係数を原点に割り当てれば凸結合になる。

この表示により半径 `cₙ₊₁` の閉円盤は `Kₙ` に含まれる。拡大すると、単位閉円盤が外接領域に含まれる。内接・外接領域の測度 `Aₙ, Uₙ` が同じ極限を持つため、`disk_measureReal_eq_intrinsicPi` が成立する。[支持半平面の証明](../../CF2D/IntrinsicPolygonSupport.lean) · [円盤測度の最終定理](../../CF2D/IntrinsicRefinementCapMeasure.lean)

円盤測度の挟み込みは `intrinsicPi_eq_real_pi` を使わない。辺の支持不等式は直接軌道で証明する。支持直線の外側にある点の係数を `a, b` とすると、`a+b>1` と `Vec.q2 ≤ 1` から両係数の正性が従う。すると、別の頂点がこの条件を満たすことは錐の内部非交差と矛盾する。[DyadicConeSupport.lean](../../CF2D/DyadicConeSupport.lean)

直接軌道側でも同じ経路が閉じている。`intrinsicDirectPolygon_refinement_caps` が被覆を与え、支持直線の零測度から面積の加法性が従う。初期正方形は対角線で二分して測度 2 を得る。これを基底として `intrinsicDirectPolygonRegion_volume_eq_areaApprox` を証明し、内外の測度を挟んで `direct_disk_measureReal_eq_intrinsicPi` を得る。この経路の CF2D import 依存には標準角度との比較層が入らない。[DirectPolygonMeasure.lean](../../CF2D/DirectPolygonMeasure.lean)

既存のユークリッド多角形との一致には、比較層の `directVertex_eq_regularVertex` を使う。

## 検証

`lean/dk_math` で `lake build DkMathTest.CosmicFormula.Rotation.CF2D.IntrinsicPiReview` を実行する。回帰例は凸包の分割、凸包測度、支持半平面表示、外接領域への包含、円盤測度の各定理を公開入口から確認する。主要定理の `#print axioms` で報告される依存は `propext`、`Classical.choice`、`Quot.sound`。
