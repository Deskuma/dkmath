/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmicBranchA

#print "file: DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestore"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

/--
restore 前半の arithmetic core を表す canonical alias。

付録:
- `RestoreFromArithmetic`
  のうち、
  arithmetic witness から smaller counterexample の bare existence を作る段を
  今後この module で育てる。
-/
abbrev PrimeGe5BranchAPrimitiveRestoreArithmeticCoreTarget : Prop :=
  PrimeGe5BranchAPrimitiveSmallerCounterexampleFromArithmeticTarget

/--
restore 後半の packet packaging core を表す canonical alias。

付録:
- smaller counterexample を
  Branch A normal-form packet に包装する purely structural な段である。
-/
abbrev PrimeGe5BranchAPrimitiveRestorePacketPackagingTarget : Prop :=
  PrimeGe5BranchAPrimitivePacketOfSmallerCounterexampleTarget

/--
restore sub-target 2 本が揃えば、
元の `RestoreFromArithmetic` target は橋だけで閉じる。

付録:
- 以後の restore 作業は、
  この theorem を canonical recompose bridge として参照すればよい。
-/
theorem primeGe5BranchAPrimitivePacketRestoreFromArithmetic_of_restoreSubtargets
    (hArithCore : PrimeGe5BranchAPrimitiveRestoreArithmeticCoreTarget)
    (hPackCore : PrimeGe5BranchAPrimitiveRestorePacketPackagingTarget) :
    PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget :=
  primeGe5BranchAPrimitivePacketRestoreFromArithmetic_of_smallerCounterexample_and_packet
    hArithCore hPackCore

end DkMath.FLT
