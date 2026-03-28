/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmicBranchA

#print "file: DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

/-!
# Triomino/Cosmic Branch A Exceptional Existence

`PrimeGe5BranchACFBRCExceptionalExistenceOnWieferichTarget` の concrete 証明を
育てるための隔離モジュール。

[CFBRC] 現段階では theorem 本体はまだ Branch A 局所 target のまま保持し、
このファイルを concrete proof の canonical 置き場とする。
`CFBRC/Bridge` への昇格は、statement が十分薄いと確認できてから後回しにする。
-/

/--
Branch A exceptional existence proof file の canonical mainline target。

[CFBRC] 現段階の concrete 証明探索は、この local theorem を埋めることを意味する。
-/
abbrev PrimeGe5BranchAExceptionalExistenceMainlineTarget : Prop :=
  PrimeGe5BranchACFBRCExceptionalExistenceOnWieferichTarget

/--
proof file mainline target があれば、
primitive packet descent へは既存 wrapper でそのまま流せる。

[CFBRC] concrete proof はこのファイルに集め、packet descent への配線は
Branch A 本体の bridge を再利用する。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_exceptionalMainline_and_restore
    (hMain : PrimeGe5BranchAExceptionalExistenceMainlineTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_localExceptionalExistence_and_restore
    hMain hRestore

end DkMath.FLT
