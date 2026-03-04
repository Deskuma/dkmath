/- 
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNCore
import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

/--
phase-15 の分岐契約。

非-Wieferich 側の `NoLift` を受け取れば、Wieferich 側の Branch B 下降は
`CosmicPetalBridgeGNDescentB` で組み立てる。
-/
abbrev TriominoWieferichLiftBridge : Prop :=
  WieferichDescentB

/--
NoLift / Lift の二分岐をまとめて受け取る最小インターフェイス。
-/
structure TriominoWieferichBranchBridge where
  hNoLift : TriominoNoLiftGNBridge

/--
一般 `GN` nonlift bridge の本丸インターフェイス。

`lift` 供給は core 側で no-`sorry` 化済み。残る `descent` のみを
`CosmicPetalBridgeGNDescentB` に隔離し、このファイルは配線専用に保つ。
-/
theorem triominoWieferichLiftKernel_impl
    : TriominoWieferichLiftKernel := by
  exact ⟨counterexampleHasWieferichLiftB_impl, triominoWieferichDescent_impl⟩

/-- 現段階の `TriominoWieferichLiftExclusion` は、最小反例選択と下降のカーネルへ委譲する。 -/
theorem triominoWieferichLiftExclusion_impl
    : TriominoWieferichLiftExclusion := by
  exact wieferichLiftExclusion_of_liftExists_and_descent
    triominoWieferichLiftKernel_impl.1
    triominoWieferichLiftKernel_impl.2

/-- 現段階の `TriominoNoWieferichBridge` 実装は、Wieferich lift 排除ブリッジへ委譲する。 -/
theorem triominoNoWieferichBridge_impl
    (hBranch : TriominoWieferichBranchBridge) :
    TriominoNoWieferichBridge := by
  exact triominoNoWieferichBridge_of_not_sq_GN hBranch.hNoLift

end DkMath.FLT
