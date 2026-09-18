/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicOrbitSplit
import DkMath.Lib.NumberTheory.HomogeneousPowerQuotient
import DkMath.Lib.NumberTheory.PowerFactor

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicOrbitPowerSplit"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open DkMath.Lib.NumberTheory

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000

/-! ## Exact stripped product and generic seventh-power extraction -/

theorem directOrbit_stripped_cores_product_eq
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r)
    (s : DirectOrbitGapSplit source r)
    (gapCore quotientCore : SevenRealCubicInt)
    (hgap : directOrbitGap p =
      eisensteinAxis ^ (32 + 42 * s.k) * gapCore)
    (hquot : directOrbitQuotient p = eisensteinAxis ^ 3 * quotientCore) :
    gapCore * quotientCore =
      orbitUnit01 *
        (thetaSevenUnit ^ (1 + 2 * s.k) * (s.a : SevenRealCubicInt) ^ 2) ^ 7 := by
  have hA : (r.summit.gapRoot : SevenRealCubicInt) =
      (7 : SevenRealCubicInt) ^ s.k * (s.a : SevenRealCubicInt) := by
    rw [s.gap_eq]
    norm_num [Nat.cast_pow]
  have hprod :
      eisensteinAxis ^ (35 + 42 * s.k) * (gapCore * quotientCore) =
        orbitUnit01 *
          (eisensteinAxis ^ 5 * thetaSevenUnit *
            (r.summit.gapRoot : SevenRealCubicInt) ^ 2) ^ 7 := by
    have hfac :
        directOrbitGap p * directOrbitQuotient p =
          orbitUnit01 *
            (eisensteinAxis ^ 5 * thetaSevenUnit *
              (r.summit.gapRoot : SevenRealCubicInt) ^ 2) ^ 7 := by
      exact directOrbit_gap_mul_quotient (p := p)
    calc
      eisensteinAxis ^ (35 + 42 * s.k) * (gapCore * quotientCore) =
          (eisensteinAxis ^ (32 + 42 * s.k) * gapCore) *
            (eisensteinAxis ^ 3 * quotientCore) := by ring
      _ = directOrbitGap p * directOrbitQuotient p := by rw [hgap, hquot]
      _ = orbitUnit01 *
          (eisensteinAxis ^ 5 * thetaSevenUnit *
            (r.summit.gapRoot : SevenRealCubicInt) ^ 2) ^ 7 :=
        hfac
  have hseven : (7 : SevenRealCubicInt) =
      eisensteinAxis ^ 3 * thetaSevenUnit :=
    seven_eq_eisensteinAxis_cube_mul_unit
  have hrewrite :
      orbitUnit01 *
          (eisensteinAxis ^ 5 * thetaSevenUnit *
            (r.summit.gapRoot : SevenRealCubicInt) ^ 2) ^ 7 =
        eisensteinAxis ^ (35 + 42 * s.k) *
          (orbitUnit01 *
            (thetaSevenUnit ^ (1 + 2 * s.k) *
              (s.a : SevenRealCubicInt) ^ 2) ^ 7) := by
    rw [hA, hseven]
    ring
  have hcancel :
      eisensteinAxis ^ (35 + 42 * s.k) * (gapCore * quotientCore) =
        eisensteinAxis ^ (35 + 42 * s.k) *
          (orbitUnit01 *
            (thetaSevenUnit ^ (1 + 2 * s.k) *
              (s.a : SevenRealCubicInt) ^ 2) ^ 7) :=
    hprod.trans hrewrite
  exact (mul_left_cancel₀
    (pow_ne_zero _ eisensteinAxis_prime.ne_zero) hcancel)

theorem directOrbit_gapCore_associated_pow_seven
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (s : DirectOrbitGapSplit source r)
    (gapCore quotientCore : SevenRealCubicInt)
    (hcop : IsCoprime gapCore quotientCore)
    (hproduct : gapCore * quotientCore =
      orbitUnit01 *
        (thetaSevenUnit ^ (1 + 2 * s.k) *
          (s.a : SevenRealCubicInt) ^ 2) ^ 7) :
    ∃ g : SevenRealCubicInt, Associated (g ^ 7) gapCore := by
  let w : SevenRealCubicInt :=
    thetaSevenUnit ^ (1 + 2 * s.k) *
      (s.a : SevenRealCubicInt) ^ 2
  have hassoc : Associated
      (w ^ 7)
      (gapCore * quotientCore) := by
    rw [show gapCore * quotientCore = orbitUnit01 * w ^ 7 by simpa [w] using hproduct]
    exact (associated_unit_mul_left (w ^ 7) orbitUnit01
      orbitUnit01_isUnit
      ).symm
  exact exists_associated_pow_of_associated_pow_mul
    (R := SevenRealCubicInt) (a := gapCore) (b := quotientCore)
    (c := w) (k := 7) hcop hassoc

theorem directOrbit_quotientCore_associated_pow_seven
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (s : DirectOrbitGapSplit source r)
    (gapCore quotientCore : SevenRealCubicInt)
    (hcop : IsCoprime gapCore quotientCore)
    (hproduct : gapCore * quotientCore =
      orbitUnit01 *
        (thetaSevenUnit ^ (1 + 2 * s.k) *
          (s.a : SevenRealCubicInt) ^ 2) ^ 7) :
    ∃ h : SevenRealCubicInt, Associated (h ^ 7) quotientCore := by
  let w : SevenRealCubicInt :=
    thetaSevenUnit ^ (1 + 2 * s.k) *
      (s.a : SevenRealCubicInt) ^ 2
  have hassoc : Associated
      (w ^ 7)
      (quotientCore * gapCore) := by
    rw [mul_comm quotientCore gapCore,
      show gapCore * quotientCore = orbitUnit01 * w ^ 7 by simpa [w] using hproduct]
    exact (associated_unit_mul_left (w ^ 7) orbitUnit01
      orbitUnit01_isUnit
      ).symm
  exact exists_associated_pow_of_associated_pow_mul
    (R := SevenRealCubicInt) (a := quotientCore) (b := gapCore)
    (c := w) (k := 7) hcop.symm hassoc

private theorem associated_pow_seven_eq_unit_mul
    {a g : SevenRealCubicInt}
    (h : Associated (g ^ 7) a) :
    ∃ u : SevenRealCubicIntˣ, a = (u : SevenRealCubicInt) * g ^ 7 := by
  rcases h with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  simpa [mul_comm] using hu.symm

/-! ## Stable current-provenance packet -/

structure DirectOrbitPowerSplitPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (base : DirectRealCubicRootPacket source r) where
  gapSplit : DirectOrbitGapSplit source r
  gapCore : SevenRealCubicInt
  quotientCore : SevenRealCubicInt
  gap_eq : directOrbitGap base =
    eisensteinAxis ^ (32 + 42 * gapSplit.k) * gapCore
  quotient_eq : directOrbitQuotient base =
    eisensteinAxis ^ 3 * quotientCore
  gapCore_not_axis_dvd : ¬eisensteinAxis ∣ gapCore
  quotientCore_not_axis_dvd : ¬eisensteinAxis ∣ quotientCore
  cores_isCoprime : IsCoprime gapCore quotientCore
  cores_product_eq : gapCore * quotientCore =
    orbitUnit01 *
      (thetaSevenUnit ^ (1 + 2 * gapSplit.k) *
        (gapSplit.a : SevenRealCubicInt) ^ 2) ^ 7
  gapRoot : SevenRealCubicInt
  quotientRoot : SevenRealCubicInt
  gapUnit : SevenRealCubicIntˣ
  quotientUnit : SevenRealCubicIntˣ
  gapCore_eq : gapCore = (gapUnit : SevenRealCubicInt) * gapRoot ^ 7
  quotientCore_eq :
    quotientCore = (quotientUnit : SevenRealCubicInt) * quotientRoot ^ 7

theorem directOrbitPowerSplit_nonempty
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    Nonempty (DirectOrbitPowerSplitPacket p) := by
  obtain ⟨s, gapCore, quotientCore, hgap, hquotient,
    hgapnot, hquotientnot, hcop⟩ := directOrbit_stripped_cores_isCoprime p
  have hproduct := directOrbit_stripped_cores_product_eq
    p s gapCore quotientCore hgap hquotient
  obtain ⟨gapRoot, hgapAssoc⟩ :=
    directOrbit_gapCore_associated_pow_seven
      s gapCore quotientCore hcop hproduct
  obtain ⟨quotientRoot, hquotAssoc⟩ :=
    directOrbit_quotientCore_associated_pow_seven
      s gapCore quotientCore hcop hproduct
  obtain ⟨gapUnit, hgapCoreEq⟩ := associated_pow_seven_eq_unit_mul hgapAssoc
  obtain ⟨quotientUnit, hquotCoreEq⟩ :=
    associated_pow_seven_eq_unit_mul hquotAssoc
  exact ⟨{
    gapSplit := s
    gapCore := gapCore
    quotientCore := quotientCore
    gap_eq := hgap
    quotient_eq := hquotient
    gapCore_not_axis_dvd := hgapnot
    quotientCore_not_axis_dvd := hquotientnot
    cores_isCoprime := hcop
    cores_product_eq := hproduct
    gapRoot := gapRoot
    quotientRoot := quotientRoot
    gapUnit := gapUnit
    quotientUnit := quotientUnit
    gapCore_eq := hgapCoreEq
    quotientCore_eq := hquotCoreEq }⟩

noncomputable def directOrbitPowerSplit
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    DirectOrbitPowerSplitPacket p :=
  Classical.choice (directOrbitPowerSplit_nonempty p)

end
end DkMath.FLT.Seven
