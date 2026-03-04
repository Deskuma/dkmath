/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoSquarefreeGNBridgeProvider
import DkMath.NumberTheory.ZsigmondyCyclotomicNoLift

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
実装本体は `NumberTheory` 側の常設 spine へ委譲し、ここは組み立てだけを担う。
-/
def triominoNoLiftGNBridgeProvider_impl :
    TriominoNoLiftGNBridgeProvider := by
  refine ⟨?_⟩
  intro p x y z q hpack hp_not_dvd_gap hqP hq_dvd_diff hq_not_dvd_gap
  have hzy_coprime : Nat.Coprime z y := by
    exact (coprime_right_of_add_pow_eq_pow hpack.hp hpack.hxy hpack.hEq).symm
  exact
    DkMath.NumberTheory.GcdNext.noLift_GN_of_primitive_prime_factor
      (a := z) (b := y) (d := p) (q := q)
      hpack.hp
      (le_trans (by decide : 3 ≤ 5) hpack.hp5)
      hpack.hyz_lt
      (Nat.pos_of_ne_zero hpack.hy0)
      hzy_coprime
      hp_not_dvd_gap
      hqP
      hq_dvd_diff
      hq_not_dvd_gap

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
  exact triominoNoWieferichBridge_of_not_sq_GN
    triominoNoLiftGNBridgeProvider_impl.hNoLift

end DkMath.FLT
