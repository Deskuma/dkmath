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
`kernel` の固定注入 wrapper（quarantine）。
-/
def triominoWieferichShrinkKernelEqSeedTracePackB_kernel_of_noWieferich_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkKernelSeedLinkB p x y z q := by
  exact
    triominoWieferichShrinkKernelEqSeedTracePackB_kernel_clean
      triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/--
Triomino/Cosmic 固有の等式側 trace 生成 pack（固定注入 wrapper）。
-/
def triominoWieferichShrinkKernelEqSeedTracePackB_kernel
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkKernelSeedLinkB p x y z q := by
  exact
    triominoWieferichShrinkKernelEqSeedTracePackB_kernel_clean
      triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- canonical eq-side trace pack から `Inv` witness を回収する投影版（固定注入 wrapper）。 -/
theorem triominoWieferichShrinkKernelInv_of_nums_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkWitnessInvB
      p x y z q
      (triominoWieferichShrinkKernelNums_of_pack
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x'
      (triominoWieferichShrinkKernelNums_of_pack
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y'
      (triominoWieferichShrinkKernelNums_of_pack
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' := by
  exact
    triominoWieferichShrinkKernelInv_of_nums_of_pack_clean
      triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- canonical eq-side trace pack から `x = q * x'` を回収する投影版（固定注入 wrapper）。 -/
theorem triominoWieferichShrinkKernel_hxmul_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    x =
      q *
        (triominoWieferichShrinkKernelNums_of_pack
          (p := p) (x := x) (y := y) (z := z) (q := q)
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' := by
  exact
    triominoWieferichShrinkKernel_hxmul_of_pack_clean
      triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- canonical eq-side trace pack から `y' = y` を回収する投影版（固定注入 wrapper）。 -/
theorem triominoWieferichShrinkKernel_hy_eq_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    (triominoWieferichShrinkKernelNums_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' = y := by
  exact
    triominoWieferichShrinkKernel_hy_eq_of_pack_clean
      triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- `KernelData` 固定注入 wrapper（quarantine）。 -/
def triominoWieferichShrinkKernelDataB_kernel
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkKernelDataB p x y z q := by
  exact
    triominoWieferichShrinkKernelDataB_kernel_clean
      triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- `XYZ_kernel` 固定注入 wrapper（quarantine）。 -/
def triominoWieferichShrinkXYZ_kernel
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkXYZB p x y z q := by
  exact
    triominoWieferichShrinkXYZ_kernel_clean
      triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- `XYZ_core` 固定注入 wrapper（quarantine）。 -/
def triominoWieferichShrinkXYZ_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkXYZB p x y z q := by
  exact
    triominoWieferichShrinkXYZ_core_clean
      triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- `Trace_core` 固定注入 wrapper（quarantine）。 -/
theorem triominoWieferichShrinkTrace_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkTraceB p x y z q
      (triominoWieferichShrinkXYZ_core
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN) := by
  exact
    triominoWieferichShrinkTrace_core_clean
      triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- `XYZTraceB_core` 固定注入 wrapper（quarantine）。 -/
def triominoWieferichShrinkXYZTraceB_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    { t : TriominoWieferichShrinkXYZB p x y z q //
      TriominoWieferichShrinkTraceB p x y z q t } := by
  exact
    triominoWieferichShrinkXYZTraceB_core_clean
      triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- `XYZTraceB_impl` 固定注入 wrapper（quarantine）。 -/
def triominoWieferichShrinkXYZTraceB_impl
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    { t : TriominoWieferichShrinkXYZB p x y z q //
      TriominoWieferichShrinkTraceB p x y z q t } := by
  exact
    triominoWieferichShrinkXYZTraceB_impl_clean
      triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- `XYZCertB_impl` 固定注入 wrapper（quarantine）。 -/
def triominoWieferichShrinkXYZCertB_impl
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkXYZCertB p x y z q := by
  exact
    triominoWieferichShrinkXYZCertB_impl_clean
      triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- `XYZB_impl` 固定注入 wrapper（quarantine）。 -/
def triominoWieferichShrinkXYZB_impl
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkXYZB p x y z q := by
  exact
    triominoWieferichShrinkXYZB_impl_clean
      triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- strict 減少の固定注入 wrapper（quarantine）。 -/
theorem triominoWieferichShrink_hzlt
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    (triominoWieferichShrinkXYZB_impl
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' < z := by
  exact
    triominoWieferichShrink_hzlt_clean
      triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- Branch B 保存の固定注入 wrapper（quarantine）。 -/
theorem triominoWieferichShrink_hpB'
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    ¬ p ∣
      ((triominoWieferichShrinkXYZB_impl
          (p := p) (x := x) (y := y) (z := z) (q := q)
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z'
        -
        (triominoWieferichShrinkXYZB_impl
          (p := p) (x := x) (y := y) (z := z) (q := q)
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y') := by
  exact
    triominoWieferichShrink_hpB'_clean
      triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- witness 回収の固定注入 wrapper（quarantine）。 -/
theorem triominoWieferichShrink_witness
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkWitnessB
      p x y z q
      (triominoWieferichShrinkXYZB_impl
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x'
      (triominoWieferichShrinkXYZB_impl
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y'
      (triominoWieferichShrinkXYZB_impl
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' := by
  exact
    triominoWieferichShrink_witness_clean
      triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- `NumsB_impl` 固定注入 wrapper（quarantine）。 -/
def triominoWieferichShrinkNumsB_impl
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkNumsB p x y z q := by
  exact
    triominoWieferichShrinkNumsB_impl_clean
      triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- `CandB_impl` 固定注入 wrapper（quarantine）。 -/
def triominoWieferichShrinkCandB_impl
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkCandB p z := by
  exact
    triominoWieferichShrinkCandB_impl_clean
      triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- `ShrinkB` 固定注入 wrapper（quarantine）。 -/
def triominoWieferichShrinkB
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichDescentResultB p z := by
  exact
    triominoWieferichShrinkB_clean
      triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- `DescentStep` 固定注入 wrapper（quarantine）。 -/
def triominoWieferichDescentStepB_impl : TriominoWieferichDescentStepB := by
  exact
    triominoWieferichDescentStepB_impl_clean
      triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core

/-- `DescentCore` 固定注入 wrapper（quarantine）。 -/
theorem triominoWieferichDescentCoreB_impl : TriominoWieferichDescentCoreB := by
  exact triominoWieferichDescentCoreB_of_step triominoWieferichDescentStepB_impl

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
