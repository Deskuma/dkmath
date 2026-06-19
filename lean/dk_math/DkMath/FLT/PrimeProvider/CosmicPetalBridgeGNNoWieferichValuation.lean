/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferich
import DkMath.NumberTheory.PrimitiveBeam

#print "file: DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichValuation"

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
direct no-lift bridge (`¬ q^2 ∣ GN`) が供給されれば、
primitive-prime branch の valuation target は no-`so#rry` で閉じる.
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
NoLift bridge 経由で従う.

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

end DkMath.FLT
