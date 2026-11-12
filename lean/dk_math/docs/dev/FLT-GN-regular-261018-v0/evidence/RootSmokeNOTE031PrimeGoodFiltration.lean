import DkMath

#print "file: RootSmokeNOTE031PrimeGoodFiltration"

/-!
# NOTE-031-004部分実装の通常入口と、残る標数の境界

良還元終点・整点存在・付値環共役・節点p捩れ排除を通常ルートから参照する。
最後の型表示は現行の除法多項式と倍写像の同値がCharZeroを保持することの確認であり、
それを標数pの剰余体へ適用した証明ではない。
-/
#check DkMath.Lib.RepresentationTheory.AbsorbingSubspace.fixed_or_cofixed
#check DkMath.Lib.NumberTheory.EllipticReductionKernel.reductionKernel
#check DkMath.FLT.Frey.Source.exists_integral_torsion_of_stable_line
#check DkMath.FLT.Frey.Source.residual_fixed_or_cofixed_at_p_of_good
#check DkMath.FLT.Frey.Source.residual_common_side_at_p_of_good
#check DkMath.Lib.NumberTheory.AbsoluteInertiaConjugacy.common_side_on_places
#check DkMath.Lib.NumberTheory.EllipticNodalTorsion.eq_zero_of_residue_characteristic_torsion
#check DkMath.Lib.NumberTheory.EllipticDivision.WeierstrassCurve.smul_eq_zero_iff_evalEval_ψ
#print axioms DkMath.FLT.Frey.Source.residual_common_side_at_p_of_good
