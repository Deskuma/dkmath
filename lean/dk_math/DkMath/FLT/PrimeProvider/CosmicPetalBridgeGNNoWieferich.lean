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
`padicValNat q (z^p - y^p) ≤ 1` が一様に供給できれば、NoWieferich bridge は直ちに従う。

phase-15 では、最後の研究核をこの valuation 上界へ押し込める。
-/
theorem triominoNoWieferichBridge_of_padicValNat_le_one
    (hVal :
      ∀ {p x y z q : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ¬ p ∣ (z - y) →
        Nat.Prime q → q ∣ (z ^ p - y ^ p) → ¬ q ∣ (z - y) →
        padicValNat q (z ^ p - y ^ p) ≤ 1) :
    TriominoNoWieferichBridge := by
  intro p x y z q hpack hp_not_dvd_gap hqP hq_dvd_diff hq_not_dvd_gap
  have hpow_pos : 0 < p := hpack.hp.pos
  have hdiff_ne0 : z ^ p - y ^ p ≠ 0 := by
    have hyz_pow_lt : y ^ p < z ^ p := by
      exact Nat.pow_lt_pow_left hpack.hyz_lt hpack.hp.ne_zero
    exact Nat.sub_ne_zero_of_lt hyz_pow_lt
  intro hq2_dvd_diff
  have h2_le : 2 ≤ padicValNat q (z ^ p - y ^ p) := by
    exact (@padicValNat_dvd_iff_le q (Fact.mk hqP) (z ^ p - y ^ p) 2 hdiff_ne0).1 hq2_dvd_diff
  exact (not_le_of_gt h2_le) <|
    hVal hpack hp_not_dvd_gap hqP hq_dvd_diff hq_not_dvd_gap

/--
phase-15 の最小研究核:
反例文脈で primitive prime divisor の `padicValNat` が高々 1 であることを示す。
-/
theorem triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_le_one_core :
    ∀ {p x y z q : ℕ}, PrimeGe5CounterexamplePack p x y z →
      ¬ p ∣ (z - y) →
      Nat.Prime q → q ∣ (z ^ p - y ^ p) → ¬ q ∣ (z - y) →
      padicValNat q (z ^ p - y ^ p) ≤ 1 := by
  sorry

/--
Branch B 文脈で使う NoWieferich bridge の最終供給点。

`DescentB` 内の no-arg 利用箇所がこのファイルより前で評価されるため、
現段階では phase-15 用の stub として保持する。
-/
theorem triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core :
    TriominoNoWieferichBridge := by
  exact
    triominoNoWieferichBridge_of_padicValNat_le_one
      triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_le_one_core

end DkMath.FLT
