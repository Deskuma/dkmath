/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Data.ZMod.Basic

#print "file: DkMath.NumberTheory.GapFocusing.UnitGauge"

/-!
The geometric-sum unit rewrites the coefficient of a focused phase factor.
Its presence does not make different monic phase factors associates.
After a unit-times-power extraction is given, changing the ramifier by a
unit changes the residual unit by an explicitly controlled power.
-/

namespace DkMath.NumberTheory.GapFocusing

open scoped BigOperators
open Polynomial

/-- The geometric sum changes the background coefficient, retaining the Gap term. -/
theorem phase_geometric_sum_rewrite
    {R : Type*} [CommRing R] (x u zeta : R) (j : ℕ) :
    x + (1 - zeta ^ j) * u =
      x + (1 - zeta) * (∑ i ∈ Finset.range j, zeta ^ i) * u := by
  rw [mul_neg_geom_sum]

/-- For a coprime phase, the coefficient rewrite uses an explicit cyclotomic unit. -/
theorem phase_geometric_sum_unit
    {R : Type*} [CommRing R] [IsDomain R] {zeta : R} {n j : ℕ}
    (hzeta : IsPrimitiveRoot zeta n) (hn : 2 ≤ n) (hj : j.Coprime n)
    (x u : R) :
    ∃ eta : Rˣ, (eta : R) = (∑ i ∈ Finset.range j, zeta ^ i) ∧
      x + (1 - zeta ^ j) * u = x + (1 - zeta) * (eta : R) * u := by
  let heta := hzeta.geom_sum_isUnit hn hj
  exact ⟨heta.unit, heta.unit_spec, by
    rw [heta.unit_spec]
    exact phase_geometric_sum_rewrite x u zeta j⟩

/-- Monic phase factors with a nonzero background are associated precisely when
their phases agree. Association of the ramifier coefficients does not identify
these linear polynomial carriers. -/
theorem phase_polynomial_associated_iff
    {R : Type*} [CommRing R] [IsDomain R] {u zeta eta : R}
    (hu : u ≠ 0) :
    Associated (X + C ((1 - zeta) * u)) (X + C ((1 - eta) * u)) ↔
      zeta = eta := by
  constructor
  · intro h
    have heq := eq_of_monic_of_associated (monic_X_add_C _) (monic_X_add_C _) h
    have hc := congrArg (fun p : R[X] => p.coeff 0) heq
    simp only [coeff_add, coeff_X_zero, coeff_C_zero, zero_add] at hc
    have hsub := mul_right_cancel₀ hu hc
    exact (sub_right_inj).mp hsub
  · intro h
    subst eta
    exact Associated.refl _

/-- Equality modulo n-th powers in the unit group, without choosing a quotient
or assuming any finite or complete system of representatives. -/
def SameUnitPowerClass
    {R : Type*} [CommMonoid R] (n : ℕ) (u v : Rˣ) : Prop :=
  ∃ t : Rˣ, u = v * t ^ n

/-- The residual unit class is independent of the power root in an integrally
closed domain, for a fixed nonzero normalized element and positive exponent.
This promotes the merged FLT3/5/7 audit's neutral algebraic statement. -/
theorem unitPowerClass_independent
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {alpha beta gamma u v : R} {n : ℕ}
    (hn : n ≠ 0) (halpha : alpha ≠ 0)
    (hu : IsUnit u) (hv : IsUnit v)
    (hleft : alpha = u * beta ^ n)
    (hright : alpha = v * gamma ^ n) :
    ∃ t : R, IsUnit t ∧ u = v * t ^ n := by
  have hpowers : Associated (beta ^ n) (gamma ^ n) :=
    (associated_unit_mul_right (beta ^ n) u hu).trans
      ((Associated.of_eq (hleft.symm.trans hright)).trans
        (associated_unit_mul_left (gamma ^ n) v hv))
  obtain ⟨t, hroot⟩ := (Associated.pow_iff hn).mp hpowers
  have hbeta : beta ^ n ≠ 0 := by
    intro hzero
    apply halpha
    rw [hleft, hzero, mul_zero]
  refine ⟨(t : R), t.isUnit, ?_⟩
  have heq : u * beta ^ n = v * gamma ^ n := hleft.symm.trans hright
  rw [← hroot, mul_pow] at heq
  apply mul_right_cancel₀ hbeta
  simpa only [mul_assoc, mul_comm, mul_left_comm] using heq

/-- Root-choice independence after cancelling a fixed nonzero ramifier.
Different ramifier representatives are governed by `ramifier_rescaling`. -/
theorem fixedRamifier_unitPowerClass_independent
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {A lambda beta gamma u v : R} {n : ℕ}
    (hn : n ≠ 0) (hA : A ≠ 0) (hlambda : lambda ≠ 0)
    (hu : IsUnit u) (hv : IsUnit v)
    (hleft : A = lambda * (u * beta ^ n))
    (hright : A = lambda * (v * gamma ^ n)) :
    ∃ t : R, IsUnit t ∧ u = v * t ^ n := by
  have hnormalized : u * beta ^ n = v * gamma ^ n :=
    mul_left_cancel₀ hlambda (hleft.symm.trans hright)
  have hnonzero : u * beta ^ n ≠ 0 := by
    intro hzero
    apply hA
    rw [hleft, hzero, mul_zero]
  exact unitPowerClass_independent hn hnonzero hu hv rfl hnormalized

/-- The same fixed-extraction result expressed in the actual unit group. -/
theorem sameUnitPowerClass_of_fixed_extraction
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {A lambda beta gamma : R} {n : ℕ} (u v : Rˣ)
    (hn : n ≠ 0) (hA : A ≠ 0) (hlambda : lambda ≠ 0)
    (hleft : A = lambda * ((u : R) * beta ^ n))
    (hright : A = lambda * ((v : R) * gamma ^ n)) :
    SameUnitPowerClass n u v := by
  obtain ⟨t, ht, heq⟩ := fixedRamifier_unitPowerClass_independent
    hn hA hlambda u.isUnit v.isUnit hleft hright
  refine ⟨ht.unit, ?_⟩
  apply Units.ext
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val, ht.unit_spec] using heq

/-- Rescaling a ramifier by `w` at load `r` changes the residual unit by `w⁻ʳ`.
The extraction equality is an input; the phase decomposition does not supply it. -/
theorem ramifier_rescaling
    {R : Type*} [CommMonoid R] (lambda beta : R) (w u : Rˣ) (r n : ℕ) :
    lambda ^ r * (u : R) * beta ^ n =
      ((w : R) * lambda) ^ r * ((w⁻¹ ^ r * u : Rˣ) : R) * beta ^ n := by
  simp only [mul_pow, Units.val_mul, Units.val_pow_eq_pow_val]
  simp [mul_assoc, mul_comm, mul_left_comm, ← mul_pow]

/-- A ramifier rescaling preserves the residual unit class exactly when its
load-weighted unit is an n-th power in the actual unit group. -/
theorem ramifier_rescaling_same_class_iff
    {R : Type*} [CommMonoid R] (w u : Rˣ) (r n : ℕ) :
    SameUnitPowerClass n (w⁻¹ ^ r * u) u ↔
      ∃ t : Rˣ, w ^ r = t ^ n := by
  constructor
  · rintro ⟨t, ht⟩
    have ht' : w⁻¹ ^ r = t ^ n := by
      apply mul_right_cancel (b := u)
      simpa only [mul_comm] using ht
    refine ⟨t⁻¹, ?_⟩
    simpa only [inv_pow, inv_inv] using congrArg Inv.inv ht'
  · rintro ⟨t, ht⟩
    refine ⟨t⁻¹, ?_⟩
    have ht' : w⁻¹ ^ r = (t⁻¹) ^ n := by
      simpa only [inv_pow] using congrArg Inv.inv ht
    rw [ht', mul_comm]

/-- A finite prime-exponent regression: rescaling by the unit `2` in `ZMod 7`
changes the cube class. This is a calibration of the neutral theorem, not an
identification with any FLT integral carrier. -/
theorem ramifier_rescaling_can_change_cube_class :
    let w : (ZMod 7)ˣ := ⟨2, 4, by decide, by decide⟩
    ¬ SameUnitPowerClass 3 (w⁻¹ ^ 1 * 1) 1 := by
  intro w
  rw [ramifier_rescaling_same_class_iff]
  decide +kernel

end DkMath.NumberTheory.GapFocusing
