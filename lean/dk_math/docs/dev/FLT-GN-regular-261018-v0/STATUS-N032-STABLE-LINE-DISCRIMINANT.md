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
- `localResidueFieldEquiv`
  - `FreyLocalReduction.LocalRing q` の剰余体を `ZMod q` へ環同値で固定。
  - `ℤ ⧸ (q)` と `ZMod q` の標準同値、および極大イデアルでの商から剰余体への
    全単射性を組み合わせたもので、代数閉包の剰余体を誤って有限体とみなさない。
- `localResidueField_natCard` / `localResidueField_card`
  - 上の同値から剰余体の `Nat.card` および `Fintype.card` が正確に `q` であることを
    証明。
- `localResidueFieldEquiv_comp_algebraMap`
  - 整数から局所環を経て剰余体へ送る写像が、`ZMod q` の通常の整数剰余と可換する
    ことを証明。
- `localResidue_weierstrass_points_card_le_two_mul_prime_add_one`
  - 実際の `LocalRing q` 上の Weierstrass モデルを剰余体へ還元した点群について、
    良還元（剰余判別式非零）を仮定すれば `#E(𝔽_q) ≤ 2*q+1` を直接供給。
- `no_two_mul_order_of_localResidue_weierstrass_of_prime`
  - `q < p` と剰余モデルの `IsElliptic` を仮定し、`ZMod q` 上の点群に厳密位数
    `2*p` の点が存在しないことを、上の点数評価から導出。
  - これは「有限剰余ファイバー上の排除」であり、有理 `2*p` 捩れ点の局所モデルへの
    輸送をまだ含まない。
- `finite_smooth_torsion_ncard_le_two_mul_prime_add_one_of_residueEquiv`
  - 任意の付値部分環について、剰余体との明示的な環同値
    `ResidueField A ≃+* ZMod q` があれば、抽象的な滑らか捩れ集合の上界を
    `2*q+1` へ特殊化。
  - `LocalRing q` そのものと付値部分環の輸送が完成した後に、還元単射性の定理を
    直接消費するための再利用可能な橋である。
- `addOrderOf_le_two_mul_residue_card_add_one_of_good`
  - 一点 `Q` の `n • Q = 0` から `AddSubgroup.zmultiples Q` 全体を滑らかな
    `n` 捩れ集合へ包含し、その部分群の濃度 `addOrderOf Q` を集合の `ncard` と
    比較する一般定理を追加。
  - これにより「一点だけを数えた」状態から、巡回部分群全体を数える正しい位数比較へ
    進んだ。局所化と `ValuationSubring ℚ` の型輸送はまだ要求しない。
- `localValuationSubring` / `localRingValuationSubringEquiv`
  - `LocalRing q` を、その DVR の有理数体上の付値部分環へ環同値で輸送。
  - `localRingValuationSubringEquiv_coe` により、輸送後の係数の有理数値が元の
    `LocalRing q → ℚ` と一致することを確認。
- `mapModelToValuationSubring_map_subtype`
  - `LocalRing q` 上の Weierstrass モデルを付値部分環へ移した後の `ℚ` 基底変換が、
    元の局所化モデルの基底変換と一致することを証明。
- `localResidueFieldValuationSubringEquiv`
  - 上の環同値から、`ResidueField (LocalRing q)` と
    `ResidueField (localValuationSubring q)` の環同値を構成。
  - `localResidueFieldValuationSubringEquiv_residue` により、局所環の係数を
    先に剰余へ送る場合と、付値部分環へ輸送してから剰余へ送る場合の可換性を固定。
- `localValuationSubringResidueFieldEquiv` / `localValuationSubringResidueField_card`
  - 付値部分環側の剰余体を `ZMod q` と同定し、その `Fintype.card` が厳密に `q` であることを証明。
  - これで、局所化表現と `ValuationSubring ℚ` 表現の双方で、有限体のサイズを同じ
    算術値として参照できる。
- `mapModelToValuationSubring_residue_discriminant_map`
  - 局所化モデルと付値部分環へ輸送したモデルの判別式が、上の剰余体環同値で
    正確に対応することを証明。
  - 従って、局所化表示での良還元判定を付値部分環表示へ移す際に、判別式非零性を
    別の公理や同型の選択に依存せずに再利用できる。

## 数学的境界

今回証明したのは、探索対象を任意の安定直線から 2上の零成分直線一本へ縮約することと、
Cofixed 枝から有理 `2 * p` 捩れを構成する構造的帰結までである。
脱出元 `σ` の実在性、`E₀[p]` の大域非安定性、`hno` 自体、Mazur の分類を使った
`p ≥ 7` の排除、`q = p` の局所理論、FLT の閉鎖はこのモジュールでは証明していない。
有限体上の点数評価と、有限体上での `2 * p` 位数排除は無条件に証明した。さらに、
`FreyLocalReduction.LocalRing q` の剰余体については `ZMod q` との明示的な環同値と
その整数写像との可換性を証明し、局所化された還元モデルの点数上界まで接続した。
さらに、整数モデルの判別式非可除性から有理 `2 * p` 捩れ点の局所次数上界を直接得る
橋を追加した。`q = 3`、`p ≥ 5`、`Even S.b`、`3 ∤ a*b*c` の条件では、
`residual_hno_of_three_good` が Cofixed 一次元核の存在を排除するところまで到達した。
これは局所還元写像を別途構成せず、整数モデルの付値輸送と巡回部分群の濃度比較を
使う経路である。一般の `q`、`q = p`、分解群外元の構成、FLT の閉鎖は依然として未完成である。

## 検証

- `lake build DkMath.FLT.FreyStableLineDiscriminantCriterion`
- `lake build DkMathTest.FLT.FreyStableLineDiscriminantCriterion`
- `lake build DkMath.FLT.FreyRationalTwoPTorsion`
- `lake build DkMathTest.FLT.FreyRationalTwoPTorsion`
- `lake build DkMath.Lib.NumberTheory.FiniteFieldWeierstrassCard`
- `lake build DkMathTest.Lib.NumberTheory.FiniteFieldWeierstrassCard`
- `lake build DkMath.Lib.NumberTheory.FreyLocalResidueField`
- `lake build DkMathTest.Lib.NumberTheory.FreyLocalResidueField`
- `lake build DkMath.Lib.NumberTheory.EllipticSmoothTorsionOrderBound`
- `lake build DkMathTest.Lib.NumberTheory.EllipticSmoothTorsionOrderBound`
- `lake build DkMath.Lib.NumberTheory.FreyLocalValuationSubring`
- `lake build DkMathTest.Lib.NumberTheory.FreyLocalValuationSubring`
- `lake build DkMath.Lib.NumberTheory.FreyLocalTorsionOrderBound`
- `lake build DkMathTest.Lib.NumberTheory.FreyLocalTorsionOrderBound`
- `lake build DkMath.FLT.FreyFiniteKernelGoodReduction`
- `lake build DkMathTest.FLT.FreyFiniteKernelGoodReduction`
- `lake build DkMath.FLT.FreyHnoThreeGood`
- `lake build DkMathTest.FLT.FreyHnoThreeGood`
- `lake build DkMath.Lib`
- `lake build DkMath.FLT`
- `lake build DkMathTest`
- `git diff --check`

回帰テストで既存の四定理と新しい `2 * p` 捩れ定理を直接使用した。
新定理の `#print axioms` は標準の
`[propext, Classical.choice, Quot.sound]` の範囲であり、新しい `sorry` や独自 `axiom` は導入していない。

## 次の具体的課題

## 追加実装: 整数モデルからの局所トーション上界

`FreyLocalTorsionOrderBound.lean` に、レビューで指定された一般接続を追加した。
`addOrderOf_le_two_mul_prime_add_one_of_integral_good` は、整数 Weierstrass モデル
`W` の判別式が素数 `q` で割れず、`q ∤ n` かつ `n • Q = 0` である有理点 `Q` に対し、

\[
  \operatorname{addOrderOf}(Q) \le 2q+1
\]

を無条件に証明する。証明は、`LocalRing q` への基底変換、同じ付値を表す
`localValuationSubring q` への環同値、剰余判別式の同値、付値単元性、そして
`addOrderOf_le_two_mul_residue_card_add_one_of_good` の合成である。点そのものは
`pointEquivOfModelEq` で輸送し、加法位数は `AddEquiv.addOrderOf_eq` で戻している。

この結果単体は `hno` を主張しないが、Source 側の薄い判別式 provider と
`residual_cofixed_implies_rational_two_p_torsion` を組み合わせることで、下記の
`q=3` 条件付き排除へ接続済みである。

この Source 側の第一段として、`residual_integer_target_discriminant_not_dvd_at_good_prime`
を `FreyFiniteKernelGoodReduction.lean` に追加した。これは `q` 上の付値環を一つ選び、
既存の `residual_integer_target_good_value_one` と
`valuation_intCast_lt_one_of_dvd` を背理法で組み合わせるだけの薄い公開入口である。
従って、局所良還元の構成を重複実装せず、次の `hno` 接続が必要とする整数判別式の
非可除性をそのまま取り出せる。

`residual_hno_of_three_good` によって `q = 3` の条件付き排除まで閉じ、さらに
`residual_hno_of_small_good_prime` によって `q < p` の小さい良い住所へ一般化した。
次は `q ∣ a*b*c` の住所と `q = p` の局所理論を別の入口として整理する。並行して、
`residual_hno_iff_exists_zeroComponent_line_escape` の右辺に現れる脱出元を、
既存の `a ≡ 7 mod 8` 側の分解群固定定理と比較する。局所分解群の外にある大域元の構成が、
次の算術的な核心課題である。並行して、今回の有理 `2 * p` 捩れを良還元素数で
排除する有限体点数評価は完了した。次は `FreyLocalReduction.LocalRing q` の剰余体を
有限体モデルへ同定し、`reduce_injOn_torsion` をこの点数評価へ接続する。
その後、必要なら Mazur 分類のうち依存部分だけを形式化する。

今回の局所剰余体同定は、`EllipticSmoothTorsionReduction` の抽象定理を
`LocalRing q` の具体的モデルへ適用するための係数体側の準備を完了したものだが、
同定だけではまだ有理点の還元写像は得られない。巡回部分群の位数比較と、局所化環から
有理数体の付値部分環への係数輸送は今回完了した。次はこの環同値に沿って剰余体同値、
滑らかな点の述語、そして `reduce_injOn_torsion` を輸送するか、局所化版の還元単射補題を
直接供給する必要がある。

今回、剰余体同値そのものとその `ZMod q` カード計算まで完了した。残る未解決義務は、
この同値を点の座標・`HasSmoothReduction`・`reducePointSmooth` に持ち上げ、
有理 `2*p` 捩れ点の巡回部分群を実際に有限剰余点群へ単射に送ることである。
加えて、判別式非零性の係数輸送は完了したので、次はこの条件から付値部分環側の
`HasSmoothReduction` を供給し、点の加法位数比較へ接続する。

今回の追加定理は、`q = 3` の範囲でこの比較を論理的に完了したものであり、分解群外の元を
構成したものではない。

## 今回の追加実装: 小さい良素数の一般化

`DkMath.FLT.FreyHnoSmallGoodPrime` を追加し、`q = 3` に固有だった排除を、次の
明示的な有限住所へ一般化した。

- `residual_hno_of_small_good_prime`
  - `5 ≤ p`、`Even S.b`、`q` 素数、`q ≠ 2`、`q < p`、`q ∤ a*b*c` のもとで、
    Cofixed な一次元 Galois 安定直線の存在を排除。
  - `2*p` 位数の有理点、整数商モデルの判別式非可除性、局所上界 `2*q+1` を合成し、
    `2*p ≤ 2*q+1` と `q < p` の矛盾を得る。
- `residual_cofixed_forces_small_prime_support`
  - Cofixed な安定直線が実際に存在すると仮定し、`q < p` の全ての奇素数について
    `q ∣ a*b*c` を導く。
  - これは小さい良素数版 `hno` の対偶であり、プリモリアル型の可除性条件へ渡すための
    算術的な必要条件である。これ自体は矛盾や FLT の結論を主張しない。
- `residual_cofixed_forces_prime_support`
  - 既存の `2 ∣ a*b*c` と奇素数版を一つの点wise な入口へ統合し、素数 `q < p` 全体に
    対して `(q : ℤ) ∣ a*b*c` を得る。
  - `q = 2` は偶奇補題へ、`q ≠ 2` は小さい良素数の局所位数矛盾へ分岐する。
- `residual_cofixed_forces_odd_prime_product_support`
  - 上の点wise な可除性を、`p` 未満の奇素数の有限積が `a*b*c` を割るという一つの
    整数係数定理へ束ねた。
  - `Finset.prod_dvd_of_coprime` と相異なる素数の互いに素性だけを使い、primorial の
    名前や正値性を仮定しない。従って後段で標準 `primorial (p - 1)` へ輸送できる。
- `residual_cofixed_forces_primorial_support`
  - `2` に対する既存の `two_dvd_product` と上記の奇素数支持を同じ有限積へ組み込み、
    標準 primorial の形 `(primorial (p - 1) : ℤ) ∣ a*b*c` を得た。
  - `primorial (p - 1)` を `p` 未満の素数積へ展開し、素数間の互いに素性で整数係数の
    可除性を閉じている。これは依然として Cofixed 枝の必要条件であり、数値矛盾や FLT
    の結論を意味しない。
- `residual_hno_of_not_primorial_dvd`
  - primorial が `a*b*c` を割らないという一つの仮定から、Cofixed 安定直線の不存在を
    対偶で直接得る。利用側で個別の良素数 `q` を選ぶ必要がない。
- `residual_cofixed_forces_multiplicative_below_p`
  - `q < p` の各素数住所について、点wise 支持条件を既存の
    `residual_integer_target_multiplicative_at_bad_place` へ渡し、整数商標的の乗法的還元を
    得る。`q = 2` は dyadic 分岐、奇素数は primorial 支持へ分け、`q = p` は意図的に除外する。
- `residual_irreducible_of_three_good`
  - 上の一般定理を `q = 3` へ特殊化し、既存の oriented cofixed obstruction から
    `S.ResidualIsIrreducible` を直接供給。
- `residual_escape_outside_decomposition_of_three_good_seven`
  - `a ≡ 7 mod 8` のもとで、`q = 3` の排除を既存の分解群外逃避同値へ渡し、
    `σ ∉ A.decompositionSubgroup ℚ` と零成分からの脱出点の存在を供給。

従って、今回新しく証明したのは `q` を一般化した局所位数矛盾と、そこから得られる
全素数の点wise 支持・有限積・primorial 支持、primorial 非可除性からの `hno`、および
小素数住所での乗法的還元であり、既約性と分解群外元の定理は既存の大域同値との合成である。
`q ∣ a*b*c` の住所そのものを除く場合、`q = p`、全ての Frey 住所を覆う無条件 `hno`、
および FLT の閉鎖は未解決のままである。

### 今回の検証

- `lake build DkMath.FLT.FreyHnoSmallGoodPrime`
- `lake build DkMath.FLT.FreyHnoThreeGood`
- `lake build DkMathTest.FLT.FreyHnoSmallGoodPrime`
- `git diff --check`

回帰テスト `DkMathTest.FLT.FreyHnoSmallGoodPrime` は一般 `q` の排除、Cofixed 枝の
小素数支持条件、全素数の点wise 支持条件とその有限積版、標準 primorial への輸送、
primorial 非可除性からの `hno`、`q < p` の乗法的還元、`q = 3` の既約性、`a ≡ 7 mod 8`
の分解群外逃避を `example` から使用する。九公開定理の
`#print axioms` はいずれも `[propext, Classical.choice, Quot.sound]` であり、今回の
追加ファイルには新しい `sorry` や独自 `axiom` はない。
