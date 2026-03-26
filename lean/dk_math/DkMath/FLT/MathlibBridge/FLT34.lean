/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.NumberTheory.FLT.Three
import Mathlib.NumberTheory.FLT.Four

#print "file: DkMath.FLT.FLT34"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Mathlib FLT(3,4) Bridge

Mathlib 依存の `n=3,4` 補題を 1 箇所へ集約する暫定ブリッジ。

方針:
- ここだけが `Mathlib.NumberTheory.FLT.Three/Four` を直接 import する。
- 他ファイルは `FLT3_core` / `FLT4_core` の名前だけを参照する。
- 将来、Triomino/Cosmic 側の独立証明が完成したら、このファイルだけ差し替える。
-/

namespace DkMath.FLT

/-- 暫定: Mathlib からの FLT(3)。将来は独立証明で置換する。 -/
theorem FLT3_core : FermatLastTheoremFor 3 :=
  fermatLastTheoremThree

/-- 暫定: Mathlib からの FLT(4)。将来は独立証明で置換する。 -/
theorem FLT4_core : FermatLastTheoremFor 4 :=
  fermatLastTheoremFour

end DkMath.FLT
