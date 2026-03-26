/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferich

#print "file: DkMath.FLT.PrimeProvider.TriominoSquarefreeGNBridgeProvider"

namespace DkMath.FLT

/--
PrimeProvider 層で `Squarefree (GN ...)` を供給するための最小 provider。

phase-15 では、この provider が供給する honest bridge 仕様から
`TriominoNoWieferichBridge` を閉じる。
-/
structure TriominoSquarefreeGNBridgeProvider where
  hSq : TriominoSquarefreeGNBridge

/--
PrimeProvider 層で `¬ q^2 ∣ GN ...` を直接供給するための最小 provider。

これは `Squarefree (GN ...)` より弱い honest bridge で、phase-15 が本質的に欲しい条件に一致する。
-/
structure TriominoNoLiftGNBridgeProvider where
  hNoLift : TriominoNoLiftGNBridge

/--
`Squarefree (GN ...)` を供給する provider があれば、NoWieferich bridge は直ちに従う。
-/
theorem triominoNoWieferichBridge_of_provider
    (P : TriominoSquarefreeGNBridgeProvider) :
    TriominoNoWieferichBridge := by
  exact triominoNoWieferichBridge_of_squarefree_GN P.hSq

/--
`¬ q^2 ∣ GN ...` を直接供給する provider があれば、NoWieferich bridge は直ちに従う。
-/
theorem triominoNoWieferichBridge_of_noLift_provider
    (P : TriominoNoLiftGNBridgeProvider) :
    TriominoNoWieferichBridge := by
  exact triominoNoWieferichBridge_of_not_sq_GN P.hNoLift

end DkMath.FLT
