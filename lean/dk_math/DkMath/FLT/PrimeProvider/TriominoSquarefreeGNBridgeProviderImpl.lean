/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoSquarefreeGNBridgeProvider

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
phase-15 の本命実装室。

ここで `¬ q^2 ∣ GN ...` を直接供給する provider を育てる。
現時点では研究 stub として保持し、本流配線にはまだ差し込まない。
-/
def triominoNoLiftGNBridgeProvider_impl :
    TriominoNoLiftGNBridgeProvider := by
  refine ⟨?_⟩
  intro p x y z q hpack hp_not_dvd_gap hqP hq_dvd_diff hq_not_dvd_gap
  -- phase-15 の研究核:
  -- primitive-prime 文脈で `¬ q^2 ∣ GN p (z - y) y` を供給する。
  sorry

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

実装室では `¬ q^2 ∣ GN ...` を直接供給する provider を本命とし、
そこから本流の `TriominoNoWieferichBridge` へ直に注入する。
-/
def triominoNoWieferichBridge_impl : TriominoNoWieferichBridge := by
  exact triominoNoWieferichBridge_of_noLift_provider
    triominoNoLiftGNBridgeProvider_impl

end DkMath.FLT
