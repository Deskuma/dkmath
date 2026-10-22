import DkMath

#print "file: RootSmokeNOTE031BranchComparison"

/-! NOTE-031-002C5: 通常ルートから実際の和差比較と同じSourceの輸送へ到達する。 -/
#check DkMath.Lib.NumberTheory.EllipticBranchComparison.branch_distance_dichotomy
#check DkMath.Lib.NumberTheory.EllipticBranchComparison.sub_of_same_branch
#check DkMath.Lib.NumberTheory.EllipticBranchComparison.add_of_opposite_branch
#check DkMath.Lib.NumberTheory.EllipticBranchComparison.sub_of_same_branch_of_model
#check DkMath.Lib.NumberTheory.EllipticBranchComparison.add_of_opposite_branch_of_model
#check @DkMath.FLT.Frey.Source.shallow_sub_of_same_branch 37
#check @DkMath.FLT.Frey.Source.shallow_add_of_opposite_branch 37
#print axioms DkMath.FLT.Frey.Source.shallow_sub_of_same_branch
#print axioms DkMath.FLT.Frey.Source.shallow_add_of_opposite_branch
