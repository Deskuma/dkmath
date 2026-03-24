import DkMath.FLT.Basic

/-! # DkMathTest.FLT

`DkMath.FLT.Basic` に置いていた `#print axioms` 群の退避先。

必要時のみ実行して、axioms 依存の回帰確認を行う。
-/

#print "file: DkMathTest.FLT"

namespace DkMathTest.FLT

#print axioms DkMath.GN3_one_not_cube_use_FLT3  -- OK: 2026/02/22 06:59
#print axioms DkMath.GN3_cube_not_cube_of_gt_one_use_FLT3  -- OK: 2026/02/22 07:03
#print axioms DkMath.pick_primitive_q_data_GN3  -- OK: no Research link 2026/03/06 01:24
-- OK: no Research link 2026/03/05
#print axioms DkMath.GN3_cube_not_cube_of_gt_one_of_provider_core
#print axioms DkMath.GN3_cube_not_cube_of_gt_one_of_provider  -- OK: no Research link 2026/03/05
#print axioms DkMath.GN3_cube_not_cube_of_gt_one_of_squarefree  -- OK: no Research link 2026/03/05
#print axioms DkMath.FLT_case_3  -- OK: no Research link 2026/03/17 00:35
-- `DkMath.FLT_case_3` は `GN3_one_not_cube_use_FLT3` を通じて Mathlib FLT(3) を参照する。
#print axioms DkMath.gcd_three_case_contra_template  -- OK: no Research link 2026/03/17 00:35
#print axioms DkMath.gcd_u_GN3  -- OK: no Research link 2026/03/17
#print axioms DkMath.u_eq_one_of_coprime_gcd  -- OK: no Research link 2026/03/17 00:35
#print axioms DkMath.FLT  -- NG: 2026/02/22 07:39 so#rryAx

end DkMathTest.FLT
