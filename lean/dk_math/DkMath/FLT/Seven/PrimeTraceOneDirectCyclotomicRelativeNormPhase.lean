/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicUnitCongruence

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicRelativeNormPhase"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

open SevenRealCubicInt
open SevenCyclotomicDegreeSixInt

namespace SevenCyclotomicDegreeSixInt

/-- Quadratic conjugation on the unit group of the concrete carrier. -/
def starUnit : Ringˣ →* Ringˣ where
  toFun u := star u
  map_one' := by
    apply Units.ext
    simp
  map_mul' u v := by
    apply Units.ext
    simp

/-- The relative quadratic norm on units. -/
def quadraticNormUnit : Ringˣ →* SevenRealCubicIntˣ :=
  Units.map QuadraticAlgebra.norm

@[simp] theorem quadraticNormUnit_apply (u : Ringˣ) :
    (quadraticNormUnit u : SevenRealCubicInt) =
      QuadraticAlgebra.norm (u : Ring) :=
  rfl

theorem quadraticNormUnit_star (u : Ringˣ) :
    quadraticNormUnit (starUnit u) = quadraticNormUnit u := by
  apply Units.ext
  simp [quadraticNormUnit, starUnit, QuadraticAlgebra.norm_star]

end SevenCyclotomicDegreeSixInt

/-- The unit-level relative norm-one phase attached to an R12 unit. -/
def directRelativeNormOnePhase
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectCyclotomicChosenQuotientPowerPacket source r) :
    SevenCyclotomicDegreeSixInt.Ringˣ :=
  p.unit_isUnit.unit /
    SevenCyclotomicDegreeSixInt.starUnit p.unit_isUnit.unit

structure DirectRelativeNormOnePhasePacket
    {x y z : ℕ} (source : CounterexamplePack x y z)
    (r : PrimitiveCounterexampleRamifiedProvenance source)
    (p : DirectCyclotomicChosenQuotientPowerPacket source r) where
  sourceUnit : SevenCyclotomicDegreeSixInt.Ringˣ
  sourceUnit_eq : (sourceUnit : SevenCyclotomicDegreeSixInt.Ring) = p.unit
  phase : SevenCyclotomicDegreeSixInt.Ringˣ
  phase_def : phase = directRelativeNormOnePhase p
  phase_norm_one :
    SevenCyclotomicDegreeSixInt.quadraticNormUnit phase = 1
  phase_sub_one_mem_sevenIdeal :
    ((phase : SevenCyclotomicDegreeSixInt.Ring) - 1) ∈ sevenIdeal

private theorem star_sub_int_mem_sevenIdeal
    (a : SevenCyclotomicDegreeSixInt.Ring) (m : ℤ)
    (h : a - (m : SevenCyclotomicDegreeSixInt.Ring) ∈ sevenIdeal) :
    star a - (m : SevenCyclotomicDegreeSixInt.Ring) ∈ sevenIdeal := by
  rw [sevenIdeal, Ideal.mem_span_singleton] at h ⊢
  rcases h with ⟨k, hk⟩
  refine ⟨star k, ?_⟩
  have hs := congrArg star hk
  change starRingEnd SevenCyclotomicDegreeSixInt.Ring
      (a - (m : SevenCyclotomicDegreeSixInt.Ring)) =
    starRingEnd SevenCyclotomicDegreeSixInt.Ring (7 * k) at hs
  rw [map_sub, map_mul, map_intCast] at hs
  have hseven :
      starRingEnd SevenCyclotomicDegreeSixInt.Ring (7 :
        SevenCyclotomicDegreeSixInt.Ring) = 7 := by
    simp [starRingEnd_apply]
  simpa only [starRingEnd_apply, hseven] using hs

private theorem sourceUnit_eq_packet_unit
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectCyclotomicChosenQuotientPowerPacket source r) :
    ((p.unit_isUnit.unit : SevenCyclotomicDegreeSixInt.Ringˣ) :
      SevenCyclotomicDegreeSixInt.Ring) = p.unit :=
  p.unit_isUnit.unit_spec

theorem directRelativeNormOnePhase_norm_one
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectCyclotomicChosenQuotientPowerPacket source r) :
    SevenCyclotomicDegreeSixInt.quadraticNormUnit
        (directRelativeNormOnePhase p) = 1 := by
  unfold directRelativeNormOnePhase
  rw [map_div, SevenCyclotomicDegreeSixInt.quadraticNormUnit_star]
  simp

theorem directRelativeNormOnePhase_sub_one_mem_sevenIdeal
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectCyclotomicChosenQuotientPowerPacket source r) :
    ((directRelativeNormOnePhase p : SevenCyclotomicDegreeSixInt.Ring) - 1) ∈
      sevenIdeal := by
  obtain ⟨m, hm, hcong⟩ := p.unit_congruentToRationalModSeven
  have hstar := star_sub_int_mem_sevenIdeal p.unit m hcong
  have hdiff :
      p.unit - star p.unit ∈ sevenIdeal := by
    have hdiff' := sevenIdeal.sub_mem hcong hstar
    convert hdiff' using 1
    ring
  have hmul := sevenIdeal.mul_mem_right
    (↑((SevenCyclotomicDegreeSixInt.starUnit p.unit_isUnit.unit)⁻¹) :
      SevenCyclotomicDegreeSixInt.Ring) hdiff
  unfold directRelativeNormOnePhase
  have hsource := sourceUnit_eq_packet_unit p
  have hstarunit :
      ((SevenCyclotomicDegreeSixInt.starUnit p.unit_isUnit.unit :
        SevenCyclotomicDegreeSixInt.Ringˣ) :
        SevenCyclotomicDegreeSixInt.Ring) = star p.unit := by
    simp [SevenCyclotomicDegreeSixInt.starUnit]
  change ((p.unit_isUnit.unit : SevenCyclotomicDegreeSixInt.Ring) *
      (↑((SevenCyclotomicDegreeSixInt.starUnit p.unit_isUnit.unit)⁻¹) :
        SevenCyclotomicDegreeSixInt.Ring) - 1) ∈ sevenIdeal
  have hsinv :
      (↑(SevenCyclotomicDegreeSixInt.starUnit p.unit_isUnit.unit) :
        SevenCyclotomicDegreeSixInt.Ring) *
          (↑((SevenCyclotomicDegreeSixInt.starUnit p.unit_isUnit.unit)⁻¹) :
            SevenCyclotomicDegreeSixInt.Ring) = 1 := by
    change (↑(SevenCyclotomicDegreeSixInt.starUnit p.unit_isUnit.unit *
      (SevenCyclotomicDegreeSixInt.starUnit p.unit_isUnit.unit)⁻¹) :
        SevenCyclotomicDegreeSixInt.Ring) = 1
    simp
  convert hmul using 1
  calc
    (p.unit_isUnit.unit : SevenCyclotomicDegreeSixInt.Ring) *
          (↑((SevenCyclotomicDegreeSixInt.starUnit p.unit_isUnit.unit)⁻¹) :
            SevenCyclotomicDegreeSixInt.Ring) - 1 =
        ((p.unit_isUnit.unit : SevenCyclotomicDegreeSixInt.Ring) -
          (↑(SevenCyclotomicDegreeSixInt.starUnit p.unit_isUnit.unit) :
            SevenCyclotomicDegreeSixInt.Ring)) *
          (↑((SevenCyclotomicDegreeSixInt.starUnit p.unit_isUnit.unit)⁻¹) :
            SevenCyclotomicDegreeSixInt.Ring) := by
      rw [sub_mul, hsinv]
    _ = (p.unit - star p.unit) *
          (↑((SevenCyclotomicDegreeSixInt.starUnit p.unit_isUnit.unit)⁻¹) :
            SevenCyclotomicDegreeSixInt.Ring) := by
      rw [hsource, hstarunit]

def RelativeNormOneScalarUnitAtSeven : Prop :=
  ∀ delta : SevenCyclotomicDegreeSixInt.Ringˣ,
    SevenCyclotomicDegreeSixInt.quadraticNormUnit delta = 1 →
    ((delta : SevenCyclotomicDegreeSixInt.Ring) - 1) ∈ sevenIdeal →
    delta = 1

theorem directRelativeNormOnePhase_eq_one_of_target
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectCyclotomicChosenQuotientPowerPacket source r)
    (htarget : RelativeNormOneScalarUnitAtSeven) :
    directRelativeNormOnePhase p = 1 := by
  apply htarget
  · exact directRelativeNormOnePhase_norm_one p
  · exact directRelativeNormOnePhase_sub_one_mem_sevenIdeal p

def ofRealUnit : SevenRealCubicIntˣ →* SevenCyclotomicDegreeSixInt.Ringˣ :=
  Units.map SevenCyclotomicDegreeSixInt.ofReal

private theorem unit_sq_eq_ofReal_normUnit_pow
    (u : SevenCyclotomicDegreeSixInt.Ringˣ)
    (v : SevenRealCubicIntˣ)
    (hstar : u = SevenCyclotomicDegreeSixInt.starUnit u)
    (hnorm : SevenCyclotomicDegreeSixInt.quadraticNormUnit u = v ^ 7) :
    u ^ 2 = ofRealUnit v ^ 7 := by
  have hstar' :
      star (u : SevenCyclotomicDegreeSixInt.Ring) = (u :
        SevenCyclotomicDegreeSixInt.Ring) := by
    have h := congrArg
      (fun w : SevenCyclotomicDegreeSixInt.Ringˣ =>
        (w : SevenCyclotomicDegreeSixInt.Ring)) hstar
    simpa [SevenCyclotomicDegreeSixInt.starUnit] using h.symm
  apply Units.ext
  have hnorm' := congrArg
    (fun w : SevenRealCubicIntˣ => (w : SevenRealCubicInt)) hnorm
  change (u : SevenCyclotomicDegreeSixInt.Ring) ^ 2 =
    ((ofRealUnit v : SevenCyclotomicDegreeSixInt.Ringˣ) :
      SevenCyclotomicDegreeSixInt.Ring) ^ 7
  calc
    (u : SevenCyclotomicDegreeSixInt.Ring) ^ 2 =
        (u : SevenCyclotomicDegreeSixInt.Ring) *
          star (u : SevenCyclotomicDegreeSixInt.Ring) := by
      rw [hstar']
      ring
    _ = SevenCyclotomicDegreeSixInt.ofReal
        (SevenCyclotomicDegreeSixInt.quadraticNormUnit u :
          SevenRealCubicInt) := by
      rw [SevenCyclotomicDegreeSixInt.quadraticNormUnit_apply]
      symm
      exact QuadraticAlgebra.algebraMap_norm_eq_mul_star (u :
        SevenCyclotomicDegreeSixInt.Ring)
    _ = SevenCyclotomicDegreeSixInt.ofReal ((v : SevenRealCubicInt) ^ 7) := by
      rw [hnorm']
      simp
    _ = ((ofRealUnit v : SevenCyclotomicDegreeSixInt.Ringˣ) :
        SevenCyclotomicDegreeSixInt.Ring) ^ 7 := by
      simp [ofRealUnit]

private theorem unit_is_seventh_power_of_sq_eq_pow_seven
    (u : SevenCyclotomicDegreeSixInt.Ringˣ)
    (t : SevenCyclotomicDegreeSixInt.Ringˣ)
    (h : u ^ 2 = t ^ 7) :
    ∃ w : SevenCyclotomicDegreeSixInt.Ringˣ, u = w ^ 7 := by
  refine ⟨t ^ 4 * u⁻¹, ?_⟩
  have hcalc : (t ^ 4 * u⁻¹) ^ 7 = u := by
    calc
      (t ^ 4 * u⁻¹) ^ 7 = (t ^ 7) ^ 4 * (u ^ 7)⁻¹ := by
        rw [mul_pow]
        group
      _ = (u ^ 2) ^ 4 * (u ^ 7)⁻¹ := by rw [h]
      _ = u := by group
  exact hcalc.symm

theorem DirectCyclotomicChosenQuotientPowerPacket.unit_isSeventhPower_of_phase_target
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectCyclotomicChosenQuotientPowerPacket source r)
    (htarget : RelativeNormOneScalarUnitAtSeven) :
    ∃ w : SevenCyclotomicDegreeSixInt.Ringˣ,
      p.unit_isUnit.unit = w ^ 7 := by
  let u : SevenCyclotomicDegreeSixInt.Ringˣ := p.unit_isUnit.unit
  have hphase : directRelativeNormOnePhase p = 1 :=
    directRelativeNormOnePhase_eq_one_of_target p htarget
  have hstar : u = SevenCyclotomicDegreeSixInt.starUnit u := by
    apply div_eq_one.mp
    simpa [u, directRelativeNormOnePhase] using hphase
  have hnorm_eq :
      SevenCyclotomicDegreeSixInt.quadraticNormUnit u =
        directChosenQuotientNormUnit p := by
    apply Units.ext
    simp [u, SevenCyclotomicDegreeSixInt.quadraticNormUnit,
      directChosenQuotientNormUnit]
  obtain ⟨v, hv⟩ := p.exists_realNormUnit_seventhPower
  have hsq : u ^ 2 = ofRealUnit v ^ 7 := by
    apply unit_sq_eq_ofReal_normUnit_pow u v hstar
    rw [hnorm_eq, hv]
  obtain ⟨w, hw⟩ := unit_is_seventh_power_of_sq_eq_pow_seven u
    (ofRealUnit v) hsq
  exact ⟨w, hw⟩

theorem DirectCyclotomicChosenQuotientPowerPacket.exists_quotient_seventhPower_of_phase_target
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectCyclotomicChosenQuotientPowerPacket source r)
    (htarget : RelativeNormOneScalarUnitAtSeven) :
    ∃ gamma : SevenCyclotomicDegreeSixInt.Ring,
      directCyclotomicPhaseQuotient r 1 = gamma ^ 7 := by
  obtain ⟨w, hw⟩ := p.unit_isSeventhPower_of_phase_target htarget
  refine ⟨(w : SevenCyclotomicDegreeSixInt.Ring) * p.beta, ?_⟩
  rw [p.quotient_eq, ← p.unit_isUnit.unit_spec, hw, mul_pow]
  simp

theorem DirectCyclotomicChosenQuotientPowerPacket.exists_directLinearFactor_seventhPower_of_phase_target
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectCyclotomicChosenQuotientPowerPacket source r)
    (htarget : RelativeNormOneScalarUnitAtSeven) :
    ∃ gamma : SevenCyclotomicDegreeSixInt.Ring,
      directLinearFactor r =
        ramifiedUniformizer * gamma ^ 7 := by
  obtain ⟨gamma, hgamma⟩ :=
    p.exists_quotient_seventhPower_of_phase_target htarget
  refine ⟨gamma, ?_⟩
  rw [directLinearFactor_eq_uniformizer_mul_quotient,
    ← directCyclotomicPhaseQuotient_one r, hgamma]

theorem exists_directRelativeNormOnePhasePacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectCyclotomicChosenQuotientPowerPacket source r) :
    Nonempty (DirectRelativeNormOnePhasePacket source r p) := by
  let u : SevenCyclotomicDegreeSixInt.Ringˣ := p.unit_isUnit.unit
  refine ⟨{
    sourceUnit := u
    sourceUnit_eq := by exact p.unit_isUnit.unit_spec
    phase := directRelativeNormOnePhase p
    phase_def := rfl
    phase_norm_one := directRelativeNormOnePhase_norm_one p
    phase_sub_one_mem_sevenIdeal :=
      directRelativeNormOnePhase_sub_one_mem_sevenIdeal p }⟩

end
end DkMath.FLT.Seven
