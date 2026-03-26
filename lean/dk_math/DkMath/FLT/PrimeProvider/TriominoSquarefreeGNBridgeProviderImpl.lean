/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoSquarefreeGNBridgeProvider

#print "file: DkMath.FLT.TriominoSquarefreeGNBridgeProviderImpl"

namespace DkMath.FLT

/--
phase-15 の実装室。

`TriominoSquarefreeGNBridge` の実体供給は PrimeProvider 層で行うが、
本流配線からはまだ参照しない。ここでは、将来の実装が満たすべき型だけを
固定しておく。
-/
abbrev TriominoSquarefreeGNBridgeProviderImplTarget : Prop :=
  TriominoSquarefreeGNBridgeProvider

/--
`¬ q^2 ∣ GN ...` を直接供給する provider の phase-15 実装室 target。
-/
abbrev TriominoNoLiftGNBridgeProviderImplTarget : Prop :=
  TriominoNoLiftGNBridgeProvider

/--
squarefree provider 実装が与えられれば、honest no-lift bridge は既存の薄い橋で回収できる。
-/
theorem triominoNoLiftGNBridge_of_provider_impl
    (P : TriominoSquarefreeGNBridgeProviderImplTarget) :
    TriominoNoLiftGNBridge := by
  exact triominoNoLiftGNBridge_of_squarefree_GN P.hSq

/--
Provider 実装が与えられれば、本流の NoWieferich bridge へは既存の注入で到達する。
-/
theorem triominoNoWieferichBridge_of_provider_impl
    (P : TriominoSquarefreeGNBridgeProviderImplTarget) :
    TriominoNoWieferichBridge := by
  exact triominoNoWieferichBridge_of_provider P

/--
より弱い honest bridge (`¬ q^2 ∣ GN ...`) を供給する provider 実装が与えられれば、
本流の NoWieferich bridge へ到達する。
-/
theorem triominoNoWieferichBridge_of_noLift_provider_impl
    (P : TriominoNoLiftGNBridgeProviderImplTarget) :
    TriominoNoWieferichBridge := by
  exact triominoNoWieferichBridge_of_noLift_provider P

/--
phase-15 の正規入口。

実装室は concrete な `NoLift` provider を仮定せず、
squarefree provider から honest bridge を派生させる構成だけを保持する。
-/
theorem triominoNoWieferichBridge_impl
    (P : TriominoSquarefreeGNBridgeProviderImplTarget) :
    TriominoNoWieferichBridge := by
  exact triominoNoWieferichBridge_of_provider_impl P

end DkMath.FLT
