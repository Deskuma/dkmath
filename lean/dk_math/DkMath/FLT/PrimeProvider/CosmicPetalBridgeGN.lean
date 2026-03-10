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

Wieferich 側の Branch B 下降仕様を受ける最小契約。
-/
abbrev TriominoWieferichLiftBridge : Prop :=
  WieferichDescentB

/--
方針B（最小反例 + 下降）で使う最小インターフェイス。

`NoLift` は global bridge として要求せず、
`WieferichDescentB` のみを受け取る。
-/
structure TriominoWieferichBranchBridge where
  hDescent : TriominoWieferichLiftBridge

/--
一般 `GN` nonlift bridge の本丸インターフェイス。

`lift` 供給は core 側で no-`so#rry` 化済み。残る `descent` を
`CosmicPetalBridgeGNDescentB` に隔離し、このファイルは配線専用に保つ。
-/
theorem triominoWieferichLiftKernel_impl
    (hBranch : TriominoWieferichBranchBridge)
    : TriominoWieferichLiftKernel := by
  exact ⟨counterexampleHasWieferichLiftB_impl, hBranch.hDescent⟩

/-- 現段階の `TriominoWieferichLiftExclusion` は、最小反例選択と下降のカーネルへ委譲する。 -/
theorem triominoWieferichLiftExclusion_impl
    (hBranch : TriominoWieferichBranchBridge)
    : TriominoWieferichLiftExclusion := by
  exact wieferichLiftExclusion_of_liftExists_and_descent
    (triominoWieferichLiftKernel_impl hBranch).1
    (triominoWieferichLiftKernel_impl hBranch).2

/-- 現段階の `TriominoNoWieferichBridge` 実装は、Wieferich lift 排除ブリッジへ委譲する。 -/
theorem triominoNoWieferichBridge_impl
    (hBranch : TriominoWieferichBranchBridge) :
    TriominoNoWieferichBridge := by
  exact triominoNoWieferichBridge_of_wieferichLiftExclusion
    (triominoWieferichLiftExclusion_impl hBranch)

end DkMath.FLT
