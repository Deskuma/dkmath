/- 
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB
import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichResearch

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

open DkMath.CosmicFormulaBinom

section NoLiftKernel

/--
`candidateZ_data` の固定注入 wrapper（quarantine）。

research 側 no-Wieferich core の固定注入をこのファイルへ隔離する。
-/
def triominoWieferichShrinkKernelEqSeedTracePackB_kernel_candidateZ_data_of_noWieferich_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkKernelCandidateZDataB p x y z q := by
  exact
    triominoWieferichShrinkKernelEqSeedTracePackB_kernel_candidateZ_data
      (p := p) (x := x) (y := y) (z := z) (q := q)
      triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/--
`candidateZ` の固定注入 wrapper（quarantine）。
-/
def triominoWieferichShrinkKernelEqSeedTracePackB_kernel_candidateZ_of_noWieferich_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    { z' : ℕ //
      z' < z
        ∧ ¬ p ∣ (z' - y)
        ∧ (x / q) ^ p + y ^ p = z' ^ p } := by
  exact
    triominoWieferichShrinkKernelEqSeedTracePackB_kernel_candidateZ
      (p := p) (x := x) (y := y) (z := z) (q := q)
      triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/--
`z_core` の固定注入 wrapper（quarantine）。
-/
def triominoWieferichShrinkKernelEqSeedTracePackB_kernel_z_core_of_noWieferich_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkKernelZEqB p x y z q := by
  exact
    triominoWieferichShrinkKernelEqSeedTracePackB_kernel_z_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/--
Branch B の下降法本体（固定注入 wrapper）。
-/
theorem triominoWieferichDescent_impl_of_noWieferich_core : WieferichDescentB := by
  exact triominoWieferichDescent_impl_clean triominoWieferichDescentStepB_impl

/--
Branch B の下降法本体（公開 wrapper）。
-/
theorem triominoWieferichDescent_impl : WieferichDescentB := by
  exact triominoWieferichDescent_impl_of_noWieferich_core

end NoLiftKernel

end DkMath.FLT
