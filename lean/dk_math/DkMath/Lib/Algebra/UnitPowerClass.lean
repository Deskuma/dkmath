/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.PowerSubgroup
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

#print "file: DkMath.Lib.Algebra.UnitPowerClass"

/-!
# 固定した非零因子の、単元冪剰余類

二つの単元倍冪分解を比較し、根の選択を変えても単元の冪剰余類が変わらないことを示す。
必要なのは整閉整域であり、Dedekind 性や類群条件は要求しない。
既存 GapFocusing.UnitGauge の中立な比較補題を Lib に移し、実際の商群へ接続する。
-/

namespace DkMath.Lib.Algebra

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

/-- 単元の具体的な冪補正と、単元冪部分群による商の等式は同値。 -/
theorem sameUnitPowerClass_iff_quotient_eq
    {R : Type*} [CommMonoid R] {n : ℕ} {u v : Rˣ} :
    SameUnitPowerClass n u v ↔
      (u : Rˣ ⧸ unitPowerSubgroup R n) = (v : Rˣ ⧸ unitPowerSubgroup R n) := by
  constructor
  · rintro ⟨t, rfl⟩
    rw [QuotientGroup.mk_mul]
    have ht : ((t ^ n : Rˣ) : Rˣ ⧸ unitPowerSubgroup R n) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨t, rfl⟩
    rw [ht, mul_one]
  · intro h
    obtain ⟨t, ht⟩ := (QuotientGroup.eq_iff_div_mem.mp h)
    refine ⟨t, ?_⟩
    change t ^ n = u / v at ht
    rw [ht]
    simp [div_eq_mul_inv, mul_left_comm]

/-- 同じ剰余類にある単元の一方が冪なら、もう一方にも明示的な冪根を与える。 -/
theorem exists_unit_pow_of_same_class
    {R : Type*} [CommMonoid R] {n : ℕ} {u v : Rˣ}
    (h : SameUnitPowerClass n u v) (hv : ∃ k : Rˣ, v = k ^ n) :
    ∃ k : Rˣ, u = k ^ n := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨k, hk⟩ := hv
  exact ⟨k * t, by rw [ht, hk, mul_pow]⟩

/-- 固定した非零分岐因子の二つの分解は、実際の単元冪商で同じ元を与える。 -/
theorem quotient_eq_of_fixed_extraction
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {A lambda beta gamma : R} {n : ℕ} (u v : Rˣ)
    (hn : n ≠ 0) (hA : A ≠ 0) (hlambda : lambda ≠ 0)
    (hleft : A = lambda * ((u : R) * beta ^ n))
    (hright : A = lambda * ((v : R) * gamma ^ n)) :
    (u : Rˣ ⧸ unitPowerSubgroup R n) = (v : Rˣ ⧸ unitPowerSubgroup R n) :=
  sameUnitPowerClass_iff_quotient_eq.mp
    (sameUnitPowerClass_of_fixed_extraction u v hn hA hlambda hleft hright)

/-- 分解の根自体の対応と、単元の補正を同じ証人 t で返す。
`beta=t*gamma` なら `v=u*t^n` となる。逆数の向きを隠さない。 -/
theorem exists_root_and_unit_correction
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {A lambda beta gamma : R} {n : ℕ} (u v : Rˣ)
    (hn : n ≠ 0) (hA : A ≠ 0) (hlambda : lambda ≠ 0)
    (hleft : A = lambda * ((u : R) * beta ^ n))
    (hright : A = lambda * ((v : R) * gamma ^ n)) :
    ∃ t : Rˣ, beta = (t : R) * gamma ∧ v = u * t ^ n := by
  have heq : (u : R) * beta ^ n = (v : R) * gamma ^ n :=
    mul_left_cancel₀ hlambda (hleft.symm.trans hright)
  have hpowers : Associated (beta ^ n) (gamma ^ n) :=
    (associated_unit_mul_right (beta ^ n) (u : R) u.isUnit).trans
      ((Associated.of_eq heq).trans
        (associated_unit_mul_left (gamma ^ n) (v : R) v.isUnit))
  obtain ⟨t, ht⟩ := (Associated.pow_iff hn).mp hpowers.symm
  have hb : beta = (t : R) * gamma := by simpa only [mul_comm] using ht.symm
  have hg : gamma ^ n ≠ 0 := by
    intro hz
    exact hA (by rw [hright, hz, mul_zero, mul_zero])
  refine ⟨t, hb, ?_⟩
  apply Units.ext
  apply mul_right_cancel₀ hg
  rw [hb, mul_pow] at heq
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val, mul_assoc, mul_comm, mul_left_comm]
    using heq.symm

/-- 同じ非零分解を介して、片側の単元の冪性を他方へ移す。 -/
theorem exists_unit_pow_of_fixed_extraction
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {A lambda beta gamma : R} {n : ℕ} (u v : Rˣ)
    (hn : n ≠ 0) (hA : A ≠ 0) (hlambda : lambda ≠ 0)
    (hleft : A = lambda * ((u : R) * beta ^ n))
    (hright : A = lambda * ((v : R) * gamma ^ n))
    (hv : ∃ k : Rˣ, v = k ^ n) : ∃ k : Rˣ, u = k ^ n :=
  exists_unit_pow_of_same_class
    (sameUnitPowerClass_of_fixed_extraction u v hn hA hlambda hleft hright) hv

/-- 分岐因子が単元 w だけ異なる場合、比較先は v ではなく w*v。
この補正を忘れると、単元の冪剰余類を誤って同一視してしまう。 -/
theorem sameUnitPowerClass_of_rescaled_extraction
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {A lambda beta gamma : R} {n : ℕ} (u v w : Rˣ)
    (hn : n ≠ 0) (hA : A ≠ 0) (hlambda : lambda ≠ 0)
    (hleft : A = lambda * ((u : R) * beta ^ n))
    (hright : A = ((w : R) * lambda) * ((v : R) * gamma ^ n)) :
    SameUnitPowerClass n u (w * v) := by
  apply sameUnitPowerClass_of_fixed_extraction u (w * v) hn hA hlambda hleft
  simpa only [Units.val_mul, mul_assoc, mul_comm, mul_left_comm] using hright

end DkMath.Lib.Algebra
