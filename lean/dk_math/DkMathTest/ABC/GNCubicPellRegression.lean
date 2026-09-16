/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessCubicIncidenceObstruction

namespace DkMathTest.ABC.GNCubicPellRegression

open DkMath.ABC

example : GNCubicComplementPell 0 = (0, 1) := by
  rfl

example : GNCubicComplementPell 1 = (21, 13) := by
  norm_num [GNCubicComplementPell]

example : GNCubicComplementPell 2 = (312, 181) := by
  norm_num [GNCubicComplementPell]

example : GNCubicComplementPell 3 = (4365, 2521) := by
  norm_num [GNCubicComplementPell]

example : GNExcessCubicComplement (GNCubicComplementPell 3).1 = 3 := by
  exact GNCubicComplementPell_complement_eq_three 3

end DkMathTest.ABC.GNCubicPellRegression
