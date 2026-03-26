/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNCore
import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichResearch

#print "file: DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichDefault"

namespace DkMath.FLT

/--
No-Wieferich bridge の固定注入点（default）。

`DescentB` 本体側から research core の直参照を外すため、
固定注入の 1 点だけを専用モジュールへ隔離する。
-/
def triominoWieferichNoWieferichBridge_default :
    TriominoNoWieferichBridge :=
  triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core

end DkMath.FLT
