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

## 数学的境界

今回証明したのは、探索対象を任意の安定直線から 2上の零成分直線一本へ縮約することと、
Cofixed 枝から有理 `2 * p` 捩れを構成する構造的帰結までである。
脱出元 `σ` の実在性、`E₀[p]` の大域非安定性、`hno` 自体、Mazur の分類を使った
`p ≥ 7` の排除、`q = p` の局所理論、FLT の閉鎖はこのモジュールでは証明していない。

## 検証

- `lake build DkMath.FLT.FreyStableLineDiscriminantCriterion`
- `lake build DkMathTest.FLT.FreyStableLineDiscriminantCriterion`
- `lake build DkMath.FLT.FreyRationalTwoPTorsion`
- `lake build DkMathTest.FLT.FreyRationalTwoPTorsion`
- `lake build DkMath.FLT`
- `git diff --check`

回帰テストで既存の四定理と新しい `2 * p` 捩れ定理を直接使用した。
新定理の `#print axioms` は標準の
`[propext, Classical.choice, Quot.sound]` の範囲であり、新しい `sorry` や独自 `axiom` は導入していない。

## 次の具体的課題

`residual_hno_iff_exists_zeroComponent_line_escape` の右辺に現れる脱出元を、
既存の `a ≡ 7 mod 8` 側の分解群固定定理と比較する。局所分解群の外にある大域元の構成が、
次の算術的な核心課題である。並行して、今回の有理 `2 * p` 捩れを良還元素数で
排除する有限体点数評価と、必要なら Mazur 分類のうち依存部分だけを形式化する。

今回の追加定理は、この比較を論理的に完了したものであり、分解群外の元を構成したものではない。
