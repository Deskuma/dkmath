/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferich
import DkMath.NumberTheory.PrimitiveBeam
import DkMath.NumberTheory.ZsigmondyCyclotomicResearch

#print "file: DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichResearch"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

open DkMath.CosmicFormulaBinom

/--
phase-15 で current research debt として残っている最小入力仕様。

primitive-prime branch で
`padicValNat q (z^p - y^p) ≤ 1`
が一様に供給できれば、PrimeProvider / Kummer 側の glue は clean に閉じる。
-/
abbrev TriominoPrimitivePrimeFactorPadicValNatLeOneTarget : Prop :=
  ∀ {p x y z q : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ¬ p ∣ (z - y) →
    Nat.Prime q → q ∣ (z ^ p - y ^ p) → ¬ q ∣ (z - y) →
    padicValNat q (z ^ p - y ^ p) ≤ 1

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
    DkMath.NumberTheory.GcdNext.padicValNat_primitive_prime_factor_le_one_research
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
current research debt を abstract target として受け取る薄い wrapper。

これにより、`so#rryAx` root は
`TriominoPrimitivePrimeFactorPadicValNatLeOneTarget`
1 本だけだと theorem 境界で固定できる。
-/
theorem triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_diff_le_one_of_target
    (hVal : TriominoPrimitivePrimeFactorPadicValNatLeOneTarget) :
    ∀ {p x y z q : ℕ}, PrimeGe5CounterexamplePack p x y z →
      ¬ p ∣ (z - y) →
      Nat.Prime q → q ∣ (z ^ p - y ^ p) → ¬ q ∣ (z - y) →
      padicValNat q (z ^ p - y ^ p) ≤ 1 := by
  intro p x y z q hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
  exact hVal hpack hpB hqP hq_dvd_diff hq_not_dvd_gap

/--
Translate the FLT Branch-B primitive-prime inputs into the shared
`PrimitiveBeam` primitive-factor predicate.

This is the main handshake between the FLT NoWieferich branch and the newer
`PrimitiveBeam` valuation route.
-/
theorem primitivePrimeFactorOfDiffPow_of_FLT_branch
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (_hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_dvd_diff : q ∣ (z ^ p - y ^ p))
    (hq_not_dvd_gap : ¬ q ∣ (z - y)) :
    DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q z y p := by
  refine ⟨hqP, hq_dvd_diff, ?_⟩
  have hzy_coprime : Nat.Coprime z y := by
    exact (coprime_right_of_add_pow_eq_pow hpack.hp hpack.hxy hpack.hEq).symm
  intro k hk_pos hk_lt
  exact
    DkMath.NumberTheory.GcdNext.prime_exp_not_dvd_diff_imp_primitive
      (a := z) (b := y) (d := p) (q := q)
      hpack.hp
      hpack.hp.one_lt
      hqP
      hzy_coprime
      hpack.hyz_lt
      hpack.y_pos
      hq_dvd_diff
      hq_not_dvd_gap
      hk_pos
      hk_lt

/--
`padicValNat q (GN p (z - y) y) ≤ 1` が供給できれば、
`padicValNat q (z^p - y^p) ≤ 1` は no-`so#rry` で従う。
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
research target が供給されれば、`GN` 側 valuation 上界は clean に回収できる。
-/
theorem triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_GN_le_one_of_target
    (hVal : TriominoPrimitivePrimeFactorPadicValNatLeOneTarget) :
    ∀ {p x y z q : ℕ}, PrimeGe5CounterexamplePack p x y z →
      ¬ p ∣ (z - y) →
      Nat.Prime q → q ∣ (z ^ p - y ^ p) → ¬ q ∣ (z - y) →
      padicValNat q (GN p (z - y) y) ≤ 1 := by
  intro p x y z q hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
  have hdiff_le :
      padicValNat q (z ^ p - y ^ p) ≤ 1 :=
    triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_diff_le_one_of_target hVal
      hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
  have hEq :
      padicValNat q (z ^ p - y ^ p) = padicValNat q (GN p (z - y) y) :=
    triominoWieferichShrink_padicValNat_diff_eq_GN_core
      hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
  rw [← hEq]
  exact hdiff_le

/--
direct no-lift bridge (`¬ q^2 ∣ GN`) が供給されれば、
primitive-prime branch の valuation target は no-`so#rry` で閉じる。
-/
theorem triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge
    (hNoLift : TriominoNoLiftGNBridge) :
    TriominoPrimitivePrimeFactorPadicValNatLeOneTarget := by
  intro p x y z q hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
  have hPrim :
      DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q z y p :=
    primitivePrimeFactorOfDiffPow_of_FLT_branch
      hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
  have hGN_not_sq : ¬ q ^ 2 ∣ GN p (z - y) y :=
    hNoLift hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
  exact
    DkMath.NumberTheory.PrimitiveBeam.primitive_prime_padic_bound_diff_of_noLift_GN
      hPrim
      hpack.hp.pos
      hpack.hp.one_lt
      hpack.hyz_lt
      hGN_not_sq

/--
squarefree bridge が供給されれば、primitive-prime branch の valuation target は
NoLift bridge 経由で従う。

This keeps the FLT-side hierarchy aligned with the ABC-side hierarchy:
local NoLift is the main route, and full `GN` squarefreeness is a sufficient
condition.
-/
theorem triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_squarefreeGNBridge
    (hSq : TriominoSquarefreeGNBridge) :
    TriominoPrimitivePrimeFactorPadicValNatLeOneTarget := by
  exact
    triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge
      (triominoNoLiftGNBridge_of_squarefree_GN hSq)

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

/--
current research debt を explicit に受け取る no-Wieferich bridge。

これ以降の PrimeProvider glue は no-`so#rry` で閉じるので、
upstream root の最小入力は
`TriominoPrimitivePrimeFactorPadicValNatLeOneTarget`
だけである。
-/
theorem triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core_of_target
    (hVal : TriominoPrimitivePrimeFactorPadicValNatLeOneTarget) :
    TriominoNoWieferichBridge := by
  exact
    triominoNoWieferichBridge_of_padicValNat_le_one
      (triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_diff_le_one_of_target hVal)

end DkMath.FLT
