/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.MiddleBlockScaffoldTail

#print "file: DkMath.ABC.MiddleBlockTail"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※ ABC010 relay entry.
  実体は named owner 群へ移設済み。
  現在は downstream 互換のため `MiddleBlockScaffoldTail` を re-export する。
-/

namespace DkMath.ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

namespace Prob

end Prob

end DkMath.ABC
