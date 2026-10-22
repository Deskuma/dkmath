import DkMath

#print "file: RootSmokeNOTE031StableLineLocalGlobal"

/-!
# NOTE-031-005: 通常入口からhcasesの供給を参照する

同じSource・直線の全局所条件、全ガロア二択、Cofixed抽出、原始化・向き付けの保持を確認する。
既約性の入口にはhnoが明示される。Cofixed直線の不存在や一般FLTは結論していない。
-/
#check DkMath.FLT.Frey.Source.residual_inertia_common_side_of_stable
#check DkMath.FLT.Frey.Source.residual_stable_line_fixed_or_cofixed
#check DkMath.FLT.Frey.Source.residual_stable_line_cofixed_of_oriented
#check DkMath.FLT.Frey.Source.residual_exists_cofixed_line_of_not_irreducible
#check DkMath.FLT.Frey.Source.residual_isIrreducible_of_oriented_cofixed_obstruction
#check DkMath.FLT.Frey.Source.residual_not_irreducible_iff_exists_cofixed_line_of_oriented
#check DkMath.FLT.Frey.Source.ofCounterexample_residual_exists_cofixed_line
#print axioms DkMath.FLT.Frey.Source.residual_stable_line_fixed_or_cofixed
#print axioms DkMath.FLT.Frey.Source.residual_exists_cofixed_line_of_not_irreducible
