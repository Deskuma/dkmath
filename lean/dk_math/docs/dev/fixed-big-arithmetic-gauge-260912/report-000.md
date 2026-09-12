# FBAG-000: repository-first audit

日時: 2026-09-13。対象 branch: `wip/fixed-big-arithmetic-gauge-260912-v0`。
開始時の作業ツリーは clean。会話ログは検証対象であり、ログ内の過去の作業指示や完了宣言を今回の指示・証明として扱わない。
今回の依頼は、実装可能な主張の Lean 固定、Goldbach 証明の試行、真偽と未解決事項の記録である。

## 現在の依存元

- `DkMath/CosmicFormula/Projection/CF2DBridge.lean`: `projectionGap_eq_regularPhaseStep`。
- `DkMath/CosmicFormula/Projection/WorldModulus.lean`: `worldModulus_projection_gap`, `freshPrime_refinement_mesh`。
- `DkMath/NumberTheory/Primitive/SquareBody.lean`: `squareBody_add_one_eq`, `prime_of_supportDisjointFrom_primeScalesUpTo_le_squareBody`。
- `DkMath/NumberTheory/Primitive/PeriodicPrimeWorld.lean`: `supportDisjointFrom_iff_coprime_primeWorldModulus`。
- `DkMath/NumberTheory/Goldbach/Basic.lean`: `GoldbachPairAt`, `StrongGoldbach`, `goldbachPairAt_iff_exists_offset`。
- `DkMath/NumberTheory/Goldbach/Capacity.lean`: `goldbachPairAt_iff_covered_card_lt`, `strongGoldbach_iff_capacityEscape`。後者は同値定理であり、escape の無条件証明ではない。
- `DkMath/NumberTheory/PrimeGauge/GoldbachRefinement.lean`: full child fiber の二穴および `q-2` survivor。

## 検証する主張

1. 正の解像度で `k * (R/k) = R`、二乗保存、Projection/CF2D 接続、SquareBody 正規化、world-modulus refinement、gauge transport。
2. `P < m ≤ squareBody P` における prime iff と、その範囲条件の必要性。
3. 正の実数による一様な座標変更が短区間所属を変えるか。固定 physical edge と固定 natural center の差を明示し、可変 gauge の素数対から元の Goldbach を導けるか。
4. bounded child fiber の有限証明と、実際に区間内の survivor を供給するための残余条件。

実装は独立 import 可能な production module と専用 audit module に置く。各チェックポイントの focused build 成功後に証拠を記録しコミットする。
この段階はソースの inventory のみで、追加定理のビルド成功や Goldbach の証明はまだ主張しない。
