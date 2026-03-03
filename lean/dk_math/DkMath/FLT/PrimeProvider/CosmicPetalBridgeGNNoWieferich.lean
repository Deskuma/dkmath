/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNCore
import DkMath.NumberTheory.ZsigmondyCyclotomicResearch

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

open DkMath.CosmicFormulaBinom

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
ただし現時点では、この上界は
`DkMath.NumberTheory.GcdNext.squarefree_implies_padic_val_le_one`
という research placeholder に委譲しており、実際の未解決は local bridge ではなく
その statement repair 側にある。
-/
theorem triominoNoWieferichBridge_of_padicValNat_le_one
    (hVal :
      ∀ {p x y z q : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ¬ p ∣ (z - y) →
        Nat.Prime q → q ∣ (z ^ p - y ^ p) → ¬ q ∣ (z - y) →
        padicValNat q (z ^ p - y ^ p) ≤ 1) :
    TriominoNoWieferichBridge := by
  intro p x y z q hpack hp_not_dvd_gap hqP hq_dvd_diff hq_not_dvd_gap
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
Branch B の primitive prime 文脈では、`z^p - y^p` の `q`-進付値は
`GN p (z - y) y` の `q`-進付値と一致する。

`q ∤ (z - y)` により、差の因数分解の左因子の付値が 0 になるため。
-/
theorem triominoWieferichShrink_padicValNat_diff_eq_GN_core
    {p x y z q : ℕ} (hpack : PrimeGe5CounterexamplePack p x y z)
    (_hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (_hq_dvd_diff : q ∣ (z ^ p - y ^ p))
    (hq_not_dvd_gap : ¬ q ∣ (z - y)) :
    padicValNat q (z ^ p - y ^ p) = padicValNat q (GN p (z - y) y) := by
  have hdiff_ne0 : z ^ p - y ^ p ≠ 0 := by
    have hyz_pow_lt : y ^ p < z ^ p := by
      exact Nat.pow_lt_pow_left hpack.hyz_lt hpack.hp.ne_zero
    exact Nat.sub_ne_zero_of_lt hyz_pow_lt
  have hfactor : z ^ p - y ^ p = (z - y) * GN p (z - y) y := by
    simpa using
      DkMath.NumberTheory.GcdNext.pow_sub_pow_factor_cosmic_N
        hpack.hp.pos hpack.hyz_lt
  have hGN_ne : GN p (z - y) y ≠ 0 := by
    intro hGN0
    rw [hfactor, hGN0, mul_zero] at hdiff_ne0
    exact hdiff_ne0 rfl
  have hpadic :=
    DkMath.NumberTheory.GcdNext.padicValNat_factorization
      hpack.hp.pos hpack.hyz_lt hqP hfactor hGN_ne
  have hzero : padicValNat q (z - y) = 0 := by
    exact padicValNat.eq_zero_of_not_dvd hq_not_dvd_gap
  simpa [hzero] using hpadic

/--
phase-15 の最小研究核（diff 版）:
primitive prime divisor 文脈で `z^p - y^p` の `q`-進付値が高々 1 であることを示す。

この形は既存の primitive-prime valuation 補題と最も直接に一致する。
ただし現行の供給源は research file の placeholder なので、ここで新しい深い数学を
足すのではなく、上流の statement repair を待つのが正しい。
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
phase-15 の最小研究核:
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
