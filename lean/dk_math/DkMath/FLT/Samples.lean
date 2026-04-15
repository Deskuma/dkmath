/- 
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.RegularPrimeRoute

#print "file: DkMath.FLT.Samples"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# FLT Samples

`DkMath.FLT.Samples` は、`DkMath.FLT` import 後に
「どの theorem を入口として使うべきか」を見失わないための discovery 用モジュール。

目的:
- `d = 3` の公開面と、regular-prime / prime-ge5 の公開面を混同しない
- `RegularPrimeRoute` の abstract route と provider concrete route の住み分けを固定する
- `TriominoSquarefreeGNBridgeProvider` を持つ場合の canonical route を
  example でそのまま示す

このファイルの example は、新しい数学内容を足すためではなく、
推奨導線を IDE / grep / theorem search で見つけやすくするためのもの。
-/

namespace DkMath.FLT.Samples

section RegularPrimeRoute

variable
  (hPeq : PrimeGe5BranchAPrimitiveQAdicGapReductionPEqualsBranchTarget)
  (hRegBranch : PrimeGe5BranchAPrimitiveQAdicGapReductionRegularBranchTarget)
  (hRegClass : ∀ {p : ℕ}, Nat.Prime p → 5 ≤ p → IsRegularPrimeReceiver.{0} p)
  (hCl : CyclotomicClassGroupPTorsionFreeTarget.{0})
  (hUnit0 : CyclotomicUnitNormalizationTarget.{0})
  (hNorm : CyclotomicNormDescentTarget)
  (hSqProv : TriominoSquarefreeGNBridgeProvider)
  (hPFE : PrimeGe5BranchAValuationPeelPacketFromErrorTarget)
  (hNoLift : TriominoCosmicNonLiftableGNBridge)

/--
Sample 1:
squarefree provider をまだ持たず、
Stage 3 を abstract theorem parameter として渡す branch では、
`FLTPrimeGe5Target_of_refinedRegularPrimeRoute` を使う。
-/
example : FLTPrimeGe5Target := by
  exact FLTPrimeGe5Target_of_refinedRegularPrimeRoute
    hPeq hRegBranch hRegClass hCl hUnit0 hNorm hPFE hNoLift

/--
Sample 2:
`TriominoSquarefreeGNBridgeProvider` を concrete に持てる branch では、
まず `FLTPrimeGe5Target_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
で regular-prime concrete mainline を作る。
-/
example : FLTPrimeGe5Target := by
  exact FLTPrimeGe5Target_of_refinedRegularPrimeRoute_and_squarefreeGNProvider
    hPeq hRegBranch hRegClass hCl hUnit0 hSqProv hPFE hNoLift

/--
Sample 3:
provider-facing な公開面へ直結したいときは、
`triominoCosmic_globalProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
を使って `GlobalPrimeExponentFLTProvider` へ上げる。
-/
example : GlobalPrimeExponentFLTProvider := by
  exact triominoCosmic_globalProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider
    hPeq hRegBranch hRegClass hCl hUnit0 hSqProv hPFE hNoLift

/--
Sample 4:
Triomino 側の公開 API へ渡したいときは、
`triominoPrimeProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
を使って `TriominoPrimeProvider` にする。
-/
example : TriominoPrimeProvider := by
  exact triominoPrimeProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider
    hPeq hRegBranch hRegClass hCl hUnit0 hSqProv hPFE hNoLift

end RegularPrimeRoute

end DkMath.FLT.Samples
