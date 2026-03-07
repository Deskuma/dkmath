/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferich
import DkMath.NumberTheory.ZsigmondyCyclotomicResearch

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

open DkMath.CosmicFormulaBinom

/--
phase-15 の研究核（diff 版）:
primitive prime divisor 文脈で `z^p - y^p` の `q`-進付値が高々 1 であることを示す。

この供給源は依然として research placeholder に依存するため、
permanent な NoWieferich glue からは分離して保持する。
-/
theorem triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_diff_le_one_of_primitivePrime_core :
    ∀ {p x y z q : ℕ}, PrimeGe5CounterexamplePack p x y z →
      ¬ p ∣ (z - y) →
      Nat.Prime q → q ∣ (z ^ p - y ^ p) → ¬ q ∣ (z - y) →
      padicValNat q (z ^ p - y ^ p) ≤ 1 := by
  intro p x y z q hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
  have hzy_coprime : Nat.Coprime z y := by
    exact (coprime_right_of_add_pow_eq_pow hpack.hp hpack.hxy hpack.hEq).symm
  exact
    DkMath.NumberTheory.GcdNext.padicValNat_primitive_prime_factor_le_one
      (a := z) (b := y) (d := p) (q := q)
      hpack.hp
      (le_trans (by decide : 3 ≤ 5) hpack.hp5)
      hpack.hyz_lt
      hpack.y_pos
      hzy_coprime
      hpB
      hqP
      hq_dvd_diff
      hq_not_dvd_gap

/--
`padicValNat q (GN p (z - y) y) ≤ 1` が供給できれば、
`padicValNat q (z^p - y^p) ≤ 1` は no-`sorry` で従う。
-/
theorem triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_GN_le_one_core :
    ∀ {p x y z q : ℕ}, PrimeGe5CounterexamplePack p x y z →
      ¬ p ∣ (z - y) →
      Nat.Prime q → q ∣ (z ^ p - y ^ p) → ¬ q ∣ (z - y) →
      padicValNat q (GN p (z - y) y) ≤ 1 := by
  intro p x y z q hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
  have hdiff_le :
      padicValNat q (z ^ p - y ^ p) ≤ 1 :=
    triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_diff_le_one_of_primitivePrime_core
      hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
  have hEq :
      padicValNat q (z ^ p - y ^ p) = padicValNat q (GN p (z - y) y) :=
    triominoWieferichShrink_padicValNat_diff_eq_GN_core
      hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
  rw [← hEq]
  exact hdiff_le

/--
phase-15 の研究核:
反例文脈で primitive prime divisor の `padicValNat` が高々 1 であることを示す。
-/
theorem triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_le_one_core :
    ∀ {p x y z q : ℕ}, PrimeGe5CounterexamplePack p x y z →
      ¬ p ∣ (z - y) →
      Nat.Prime q → q ∣ (z ^ p - y ^ p) → ¬ q ∣ (z - y) →
      padicValNat q (z ^ p - y ^ p) ≤ 1 := by
  intro p x y z q hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
  exact
    (triominoWieferichShrink_padicValNat_diff_eq_GN_core
      hpack hpB hqP hq_dvd_diff hq_not_dvd_gap).trans_le <|
      triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_GN_le_one_core
        hpack hpB hqP hq_dvd_diff hq_not_dvd_gap

/--
Branch B 文脈で使う research-side の NoWieferich bridge 供給点。

この定理は research placeholder に依存するため、permanent glue から切り離して保持する。
-/
theorem triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core :
    TriominoNoWieferichBridge := by
  exact
    triominoNoWieferichBridge_of_padicValNat_le_one
      triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_le_one_core

end DkMath.FLT
