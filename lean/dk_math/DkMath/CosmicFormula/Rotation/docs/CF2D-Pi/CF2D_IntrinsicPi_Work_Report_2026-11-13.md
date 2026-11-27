# CF2D Intrinsic π 作業状況・検証レポート

作成日: 2026-11-13  
対象ブランチ: `dev/CF2D-pi-261112-v1`  
確認した HEAD: `842845e5bf62d569e0ca352c96c4f3cc5db0b4fe`

## 判定

**π-free な定数構成と既知の `Real.pi` への解析的 bridge は証明済み。幾何学的な円盤面積への独立した経路は未完了。**

中断前の追加分は現ブランチに存在し、CF2D 集約モジュールと専用テストの focused build は成功した。以下のビルドは既存キャッシュの再利用を含む。一般の正多角形に対する原点ファンの被覆・全対の測度零・内接円盤の包含を、成功済みとは扱わない。

## 1. ブランチとマージ後の状態

- `HEAD` とローカル `develop` はともに `842845e5bf62d569e0ca352c96c4f3cc5db0b4fe`。
- 中断時の `2d30550543a9aca23c20ac03318b3ad48271d823` は HEAD の祖先であり、マージコミット `72cc6ad36` を経由している。
- `2d305505...` と HEAD の間で、`CF2D.lean`、その `CF2D/` 配下、および `IntrinsicPiReview.lean` に差分はなかった。
- マージ後の `lakefile.toml` には `DkMathHeavyTest` があり、`DkMathTest.lean` は専用テスト `DkMathTest.CosmicFormula.Rotation.CF2D.IntrinsicPiReview` を import する。
- 今回は focused build のキャッシュ利用時の成功を確認した。クリーンビルド時間の比較は行っていないため、以前の長時間化の原因や改善量はこの検証からは判定できない。

## 2. 証明済みの構成

以下の定理名は `DkMath.CosmicFormula.Rotation.CF2D` 名前空間内。`u_n = (c_n,s_n)`、`A_n = areaApprox n`、`P_n = halfPerimeterApprox n`、`U_n = outerApprox n` と書く。

### π-free の核・数列・上限

- `QuadrantUnitKernel.half_star`、`QuadrantUnitKernel.sequence_star`: 第一象限の非負平方根による二分核と `u_(n+1) ⋆ u_(n+1) = u_n`。符号確定には beam の非負性を使う。
- `halfPerimeterApprox_eq_areaApprox_succ`: `P_n = A_(n+1)`。
- `areaApprox_eq_core_mul_succ`、`areaApprox_monotone`、`areaApprox_le_four`: `A_n = c_(n+1) A_(n+1)`、単調非減少、上界 4。
- `intrinsicPi := sSup (Set.range areaApprox)` と `tendsto_areaApprox_intrinsicPi`: 上限による定義と収束。
- `tendsto_core_one`、`intrinsicPi_bounds`、`tendsto_outer_sub_area_zero`: `c_n → 1`、`A_n ≤ intrinsicPi ≤ U_n`、`U_n - A_n → 0`。
- `outerApprox_sub_areaApprox_le_quarter_pow`、`intrinsicPi_sub_areaApprox_le_quarter_pow`、`outerApprox_sub_intrinsicPi_le_quarter_pow`: 誤差の上界 `8(1/4)^n`。これは段階数に関する等比的上界である。
- `intrinsicPi_eq_real_pi`: 別の `IntrinsicPiBridge` で三角関数の半角公式と `sinc` の連続性を用いて `intrinsicPi = Real.pi` を証明。

### 幾何側で成立した範囲

- `regularKernel_dyadic` は二分核を既存の等角有限軌道に接続する。頂点は単位円上で相異なり、等角に進む。
- `intrinsicPolygonPerimeter_div_two` は実際の頂点間距離の和から半周長を計算し、`P_n` と同一視する。
- `intrinsicPolygonSignedArea_eq_areaApprox` は頂点の靴紐和が `A_n` に等しいことを示す。この結果だけでは凸包の測度と `A_n` の一致を意味しない。
- `standardTriangle_volume` と `intrinsicOriginTriangle_volume` は標準三角形の測度 `1/2` と各原点三角形の測度 `ENNReal.ofReal (s_n / 2)` を無条件に証明。
- `intrinsicPolygonRegion_origin_mem` は原点の凸包所属、`intrinsicPolygonRegion_neg` は凸包の原点対称性を示す。
- `intrinsicOriginTriangle_aedisjoint_next` と `intrinsicOriginTriangle_aedisjoint_opposite` は、それぞれ隣接対と半周離れた対の共通部分が測度零であることを示す。
- `intrinsicOriginTriangle_zero_pairwise_aedisjoint` は **`n = 0` の４三角形**の全ての異なる対について成立する。
- `intrinsicOriginFan_subset_region`、`intrinsicOriginFan_volume_le_areaApprox`、`intrinsicPolygonRegion_volume_pos` は、ファンの凸包への包含、ファン測度の上界、凸包測度の正性を示す。
- `intrinsicOriginFan_zero_volume` は **`n = 0` のファン**の測度が `ENNReal.ofReal 2` であることを示す。凸包について現時点で確認した定理は `intrinsicPolygonRegion_zero_volume_ge_two`（測度が少なくとも 2）である。
- `intrinsicPolygon_edge_midpoint_norm`、`intrinsicPolygon_edge_midpoint_orthogonal` と `intrinsicInnerBall_subset_edgeHalfSpaces` は、辺の中点の距離・直交性、および内接円盤が辺の半平面の共通部分に入ることを示す。

幾何側の `IntrinsicRegularPolygon` は `IntrinsicPiBridge` と `EuclideanRegularOrbit` を import し、`sequence_trig` を使用する。したがって幾何側全体の import 依存を π-free とは呼ばない。

## 3. 未完了の課題と条件付き定理

一般の `n` について次は未証明である。

1. `intrinsicPolygonRegion n = intrinsicOriginFan n`、すなわち原点ファンによる凸包全体の被覆。
2. 隣接・対向に限らない、全ての異なる原点三角形対の `AEDisjoint`。
3. 辺の半平面の共通部分が凸包に含まれること、およびそこから導く半径 `c_(n+1)` の閉円盤の凸包への包含。
4. 以上に基づく、凸包の測度 `= ENNReal.ofReal (areaApprox n)` と、測度の挟み込みによる円盤面積 `= intrinsicPi` の無条件定理。

`intrinsicPolygonRegion_volume_of_origin_fan_geometry` は 1 と 2 を仮定する。`disk_measureReal_eq_intrinsicPi_of_polygon_sandwich` は各段階の凸包の面積公式と単位円盤の外側領域への包含を仮定する。これらの定理が型検査されていることは、仮定が解消されたことを意味しない。

次の実装は、頂点の巡回順序を用いて一般の三角形対の交わりとファン被覆を証明し、支持半平面の共通部分から凸包への逆包含を示すこと。その後、既存の条件付き定理に無条件の補題を渡し、幾何学的な円盤測度の挟み込みを完成させる。

## 4. 今回の検証結果

作業ディレクトリ: `lean/dk_math`。

| 検証                                                                                                     | 結果                                                                           |
| -------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------ |
| `lake build DkMath.CosmicFormula.Rotation.CF2D DkMathTest.CosmicFormula.Rotation.CF2D.IntrinsicPiReview` | 成功。集約モジュールと専用テストを再生し、8983 jobs と表示。キャッシュ利用あり |
| `lake env lean /tmp/cf2d_v1_report_audit.lean`                                                           | 成功。集約 import、主要10定理の公理依存、条件付き定理の型を確認                |
| intrinsic ４ファイルに対する `Real.pi/sin/cos/arcsin/arccos` と禁止 bridge の直接 import の検索          | 該当なし                                                                       |
| 対象13ファイルの `sorry` / `admit` / `axiom` の文字列検索                                                | 該当なし                                                                       |
| `git diff --check`                                                                                       | 成功（レポート作成前）                                                         |

`#print axioms` を実行した `QuadrantUnitKernel.half_star`、`halfPerimeterApprox_eq_areaApprox_succ`、`outerApprox_sub_areaApprox_le_quarter_pow`、`intrinsicPi_eq_real_pi`、`intrinsicOriginTriangle_volume`、隣接・対向の `AEDisjoint`、`intrinsicOriginTriangle_zero_pairwise_aedisjoint`、`intrinsicOriginFan_zero_volume`、`disk_measureReal_eq_intrinsicPi_of_polygon_sandwich` は、いずれも `[propext, Classical.choice, Quot.sound]` のみ。最後の定理は上記の仮定を持つ。

本レポートでは、focused build の結果をリポジトリ全体のクリーンビルドや全テストの結果に拡大しない。
