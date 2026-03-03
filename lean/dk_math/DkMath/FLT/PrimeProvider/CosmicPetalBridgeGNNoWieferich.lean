/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNCore

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

/--
Branch B の lift 抽出と下降仕様が揃えば、NoWieferich bridge は直ちに従う。

このファイルは phase-15 の研究室として作られたが、現時点では
`CosmicPetalBridgeGNCore` にある no-`sorry` の合成だけで閉じる。
-/
theorem triominoNoWieferichBridge_of_descent
    (hDesc : WieferichDescentB) :
    TriominoNoWieferichBridge := by
  exact
    triominoNoWieferichBridge_of_wieferichLiftExclusion <|
      wieferichLiftExclusion_of_liftExists_and_descent
        counterexampleHasWieferichLiftB_impl
        hDesc

/--
Branch B 文脈で使う NoWieferich bridge の最終供給点。

`DescentB` 内の no-arg 利用箇所がこのファイルより前で評価されるため、
現段階では phase-15 用の stub として保持する。
-/
theorem triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core :
    TriominoNoWieferichBridge := by
  sorry

end DkMath.FLT
