# NOTE-032 安定直線判別式接続ステータス

## 実装済み

新規モジュール `DkMath.FLT.FreyStableLineDiscriminantCriterion` を追加した。

- `residual_irreducible_iff_zeroComponent_not_stable_at_two`
  - 既約性と、2上の `residualZeroComponent` が大域ガロア安定でないことを同値化。
  - `residual_isIrreducible_iff_no_stable_line`、零成分の一次元性、
    `residual_stable_line_eq_zeroComponent_at_two` を合成。
- `residual_hno_iff_zeroComponent_not_stable_at_two`
  - `Even S.b` の向き付き大域二択を使い、Cofixed安定直線の不存在を
    零成分直線の非安定性へ縮約。
- `residual_hno_iff_exists_zeroComponent_line_escape`
  - `hno` を、`P ∈ E₀[p]` かつ `ρ σ P ∉ E₀[p]` となる大域ガロア元の存在へ変換。
- `residual_hno_iff_exists_zeroComponent_line_escape_outside_decomposition_of_seven`
  - `a ≡ 7 mod 8` の既存分解群固定定理を合成し、脱出元を
    `σ ∉ A.decompositionSubgroup ℚ` に限定。
- `residual_cofixed_implies_rational_two_p_torsion`
  - `Even S.b` と Cofixed な一次元核から、同じ整数係数商モデル上の有理点
    `Q` を構成し、`addOrderOf Q = 2 * p` を無条件に証明。
  - 源の有理二捩れ点を商準同型の Galois 同変性で有理二捩れ点へ降下し、
    Cofixed から得た有理 `p` 捩れ点との和に
    `addOrderOf_eq_of_nsmul_and_div_prime_nsmul` を適用した。
- `residual_cofixed_implies_rational_two_p_torsion_of_seven`
  - `a ≡ 7 mod 8` から `b` の偶数性を自動供給する薄い公開ラッパー。
- `card_weierstrass_points_le_two_mul_card_add_one`
  - 有限体上の Weierstrass 方程式を固定 `x` ファイバーへ分解し、各ファイバーの
    `y` 根が高々二つであることから `#E(K) ≤ 2 * #K + 1` を証明。
  - Hasse の評価、Frobenius、群構造を使わず、`Point.X_eq_iff` による初等的な
    二次根数え上げだけを使う。
- `addOrderOf_le_natCard_of_injective_addMonoidHom`
  - 有限標的群への単射加法準同型が、元の点の加法位数を標的の `Nat.card` 以下に
    抑える一般群論補題。
- `addOrderOf_le_two_mul_card_add_one_of_weierstrass`
  - 有限体 Weierstrass 点群へ恒等写像を適用し、捩れ位数へ初等点数上界を輸送。
- `no_two_mul_order_of_weierstrass_of_card_lt`
  - `2 * #K + 1 < 2 * p` のとき、有限体 Weierstrass 点群に厳密位数 `2 * p` の
    点が存在しないことを証明。
- `no_two_mul_order_of_weierstrass_of_card_le`
  - `#K ≤ q < p` という形で、後段の `𝔽_q` 特殊化へ渡す算術ラッパー。
- `finite_smooth_torsion_ncard_le_two_mul_residue_card_add_one`
  - 良還元を持つ付値環モデルについて、`reduce_injOn_torsion` と有限剰余体上の
    点数上界を合成し、一般ファイバーの滑らかな `n` 捩れ集合を
    `2 * #ResidueField + 1` 以下に抑える。
  - これは有限剰余体を明示的に要求する抽象局所定理であり、`ℤ_(q)` の剰余体が
    `𝔽_q` であることや Frey 標的との同定までは含めない。

## 数学的境界

今回証明したのは、探索対象を任意の安定直線から 2上の零成分直線一本へ縮約することと、
Cofixed 枝から有理 `2 * p` 捩れを構成する構造的帰結までである。
脱出元 `σ` の実在性、`E₀[p]` の大域非安定性、`hno` 自体、Mazur の分類を使った
`p ≥ 7` の排除、`q = p` の局所理論、FLT の閉鎖はこのモジュールでは証明していない。
有限体上の点数評価と、有限体上での `2 * p` 位数排除は無条件に証明したが、
有理商曲線の良還元から `𝔽_q` の点群へ実際の還元準同型を構成する接続は未完成である。
従って、現段階では `residual_cofixed_implies_rational_two_p_torsion` と
`residual_integer_target_good_at_prime` を組み合わせた `hno` 排除までは到達していない。

## 検証

- `lake build DkMath.FLT.FreyStableLineDiscriminantCriterion`
- `lake build DkMathTest.FLT.FreyStableLineDiscriminantCriterion`
- `lake build DkMath.FLT.FreyRationalTwoPTorsion`
- `lake build DkMathTest.FLT.FreyRationalTwoPTorsion`
- `lake build DkMath.Lib.NumberTheory.FiniteFieldWeierstrassCard`
- `lake build DkMathTest.Lib.NumberTheory.FiniteFieldWeierstrassCard`
- `lake build DkMath.FLT`
- `git diff --check`

回帰テストで既存の四定理と新しい `2 * p` 捩れ定理を直接使用した。
新定理の `#print axioms` は標準の
`[propext, Classical.choice, Quot.sound]` の範囲であり、新しい `sorry` や独自 `axiom` は導入していない。

## 次の具体的課題

`residual_hno_iff_exists_zeroComponent_line_escape` の右辺に現れる脱出元を、
既存の `a ≡ 7 mod 8` 側の分解群固定定理と比較する。局所分解群の外にある大域元の構成が、
次の算術的な核心課題である。並行して、今回の有理 `2 * p` 捩れを良還元素数で
排除する有限体点数評価は完了した。次は `FreyLocalReduction.LocalRing q` の剰余体を
有限体モデルへ同定し、`reduce_injOn_torsion` をこの点数評価へ接続する。
その後、必要なら Mazur 分類のうち依存部分だけを形式化する。

今回の追加定理は、この比較を論理的に完了したものであり、分解群外の元を構成したものではない。
