/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.IrregularPrime37
import DkMath.FLT.Kummer.ElevenRegularTransport
import DkMath.FLT.Kummer.ThirteenRegularTransport

#print "file: DkMathTest.FLT.Kummer.IrregularObstruction"

/-! IRR の境界：正則例の実消滅、単元障害の反例、積保存だけでは消えない群モデル。 -/

namespace IrregularObstructionTest

open DkMath.Lib.NumberTheory DkMath.FLT.Kummer
open DkMath.Lib.Cosmic
open scoped NumberField

local instance prime37 : Fact (Nat.Prime 37) := ⟨by decide⟩

example {R : Type*} [CommRing R] (x u : R) :
    (x + u) ^ 37 - u ^ 37 = x * DkMath.CosmicFormula.GN 37 x u :=
  thirtySeven_difference_left x u

example {R : Type*} [CommRing R] (x u : R) :
    (x + u) ^ 37 - x ^ 37 = u * DkMath.CosmicFormula.GN 37 u x :=
  thirtySeven_difference_right x u

example {R : Type*} [Monoid R] (x : R) :
    x ^ 37 = (((x ^ 2) ^ 2) ^ 3) ^ 3 * x := pow_thirtySeven_small x

example {k : ℕ} (hk : 0 < k) (hkp : k < 37) :
    37 ∣ Nat.choose 37 k ∧ ¬ 1369 ∣ Nat.choose 37 k := thirtySeven_choose_exact_layer hk hkp

example (x u : ZMod 37) : DkMath.CosmicFormula.GN 37 x u = x ^ 36 := prime_GN_zmod x u

example : BernoulliPrime37.BernoulliIrregularPair 37 32 :=
  (BernoulliPrime37.irregular_pair_thirtySeven_iff 32).mpr rfl

example {R : Type*} [CommRing R] [IsDedekindDomain R] {p : ℕ} {Q : R}
    (E : IdealPowerObstruction R p Q) (hp : p ≠ 0) (hn : E.obstruction ≠ 1) :
    ¬ ∃ (u : Rˣ) (b : R), Q = u * b ^ p :=
  fun ⟨u, b, h⟩ => hn (E.trivial_of_unit_power hp u b h)

-- These are actual proved regular arithmetic providers, rather than assumed regularity labels.
example {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {11} ℚ K]
    {Q : 𝓞 K} (E : IdealPowerObstruction (𝓞 K) 11 Q) : E.obstruction = 1 :=
  E.trivial_of_torsionFree RegularDescent.eleven_classGroup_torsion_free

example {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {13} ℚ K]
    {Q : 𝓞 K} (E : IdealPowerObstruction (𝓞 K) 13 Q) : E.obstruction = 1 :=
  E.trivial_of_torsionFree RegularDescent.thirteen_classGroup_torsion_free

-- Principal ideal extraction does not absorb units. The exponent 2 is deliberate here.
example : ∃ U : UnitObstructionPacket ℤ 2 (-1), U.obstruction ≠ 1 := by
  let U : UnitObstructionPacket ℤ 2 (-1) := ⟨-1, 1, by norm_num⟩
  refine ⟨U, ?_⟩
  intro h
  obtain ⟨b, hb⟩ := U.exists_power_of_trivial h
  nlinarith [sq_nonneg b]

-- Countermodel for group constraints only: this does not construct a cyclotomic ideal class.
example : ∃ w : Multiplicative (ZMod 37), w ≠ 1 ∧ w ^ 37 = 1 ∧ w * w⁻¹ = 1 := by
  refine ⟨Multiplicative.ofAdd 1, by decide, by decide, mul_inv_cancel _⟩

example {m : ℕ} (E : RegularDescent.State IrregularPrime37.phase37 (m + 1)) :
    (IrregularPrime37.observe E).source = E := IrregularDescent.ofState_source (by decide) E

example {m : ℕ} (E : RegularDescent.State IrregularPrime37.phase37 (m + 1)) :
    (∏ i, (IrregularPrime37.observe E).phases.obstruction i) = 1 :=
  IrregularPrime37.product_obstruction_one E

-- Arbitrary degree: local class vanishing suffices for the weighted step; no global free input.
example {R : Type*} [CommRing R] [IsDedekindDomain R] {p : ℕ} [Fact p.Prime]
    {P : RamifiedPhasePacket R p} {m : ℕ} (O : IrregularDescent.ObstructedState P m)
    (ho : Odd p) (hp3 : 3 ≤ p) (hlocal : ∀ i, O.phases.obstruction i = 1) :
    Nonempty (IrregularDescent.WeightedObstructedState P m) := O.exists_weighted ho hp3 hlocal

example {R : Type*} [CommRing R] [IsDedekindDomain R] {p : ℕ} [Fact p.Prime]
    {P : RamifiedPhasePacket R p} {m : ℕ} (W : IrregularDescent.WeightedObstructedState P m)
    (hlocal : W.unitObstruction = 1) : ∃ E : RegularDescent.State P m, E.y = W.y ∧ E.z = W.z :=
  W.normalize hlocal

end IrregularObstructionTest
