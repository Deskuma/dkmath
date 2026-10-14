/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicOrbit
import DkMath.FLT.Seven.SevenRealCubicCoprimeExtraction
import DkMath.Lib.NumberTheory.HomogeneousPowerQuotient

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicOrbitSplit"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open DkMath.Lib.NumberTheory

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

set_option linter.style.longLine false

/-! ## The direct orbit factorization -/

def directOrbitGap
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) : SevenRealCubicInt :=
  rotateEquiv p.rho - p.rho

def directOrbitQuotient
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) : SevenRealCubicInt :=
  seventhQuotient (rotateEquiv p.rho) p.rho

theorem directOrbit_gap_mul_quotient
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    directOrbitGap p * directOrbitQuotient p =
      orbitUnit01 *
        (eisensteinAxis ^ 5 * thetaSevenUnit *
          (r.summit.gapRoot : SevenRealCubicInt) ^ 2) ^ 7 := by
  rw [directOrbitGap, directOrbitQuotient,
    ← pow_seven_sub_pow_seven_factorization]
  have h := directRealCubicOrbit_source_difference_factorization (r := r)
  simp only [directRealCubicOrbitSource, ite_true, one_ne_zero, ite_false] at h
  rw [p.source_eq_pow, map_pow] at h
  simpa [directRealCubicOrbitSource, directOrbitGap] using h

/-! ## The seven-adic unit part of the gap root -/

structure DirectOrbitGapSplit
    {x y z : ℕ} (source : CounterexamplePack x y z)
    (r : PrimitiveCounterexampleRamifiedProvenance source) where
  k : ℕ
  a : ℕ
  gap_eq : r.summit.gapRoot = 7 ^ k * a
  a_pos : 0 < a
  a_not_seven_dvd : ¬7 ∣ a

def directOrbitGapSplit
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    DirectOrbitGapSplit source r := by
  let A := r.summit.gapRoot
  have hA : A ≠ 0 := r.summit.gapRoot_pos.ne'
  let k := padicValNat 7 A
  let a := Nat.divMaxPow A 7
  have hfactor : a * 7 ^ k = A := by
    exact Nat.divMaxPow_mul_pow_padicValNat 7 A
  have hnot : ¬7 ∣ a := by
    exact Nat.not_dvd_divMaxPow (by norm_num) hA
  have hpos : 0 < a := by
    exact Nat.pos_of_ne_zero (by
      intro ha
      rw [ha, zero_mul] at hfactor
      exact hA hfactor.symm)
  exact {
    k := k
    a := a
    gap_eq := by simp [A, a, k]
    a_pos := hpos
    a_not_seven_dvd := hnot }

/-! ## Local exact-depth calculus -/

private theorem exactDepth_mul
    {x y : SevenRealCubicInt} {m n : ℕ}
    (hx : HasExactThetaDepth x m)
    (hy : HasExactThetaDepth y n) :
    HasExactThetaDepth (x * y) (m + n) := by
  rcases hx.1 with ⟨x0, hx0⟩
  rcases hy.1 with ⟨y0, hy0⟩
  have hx0_not : ¬eisensteinAxis ∣ x0 := by
    intro h
    apply hx.2
    rcases h with ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    rw [hx0]
    simp [pow_succ, mul_assoc, mul_comm]
  have hy0_not : ¬eisensteinAxis ∣ y0 := by
    intro h
    apply hy.2
    rcases h with ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    rw [hy0]
    simp [pow_succ, mul_assoc, mul_comm]
  constructor
  · refine ⟨x0 * y0, ?_⟩
    rw [hx0, hy0, pow_add]
    ring
  · rintro ⟨z, hz⟩
    have hcancel : eisensteinAxis ∣ x0 * y0 := by
      have hz' :
          eisensteinAxis ^ (m + n + 1) ∣
            eisensteinAxis ^ (m + n) * (x0 * y0) := by
        refine ⟨z, ?_⟩
        calc
          eisensteinAxis ^ (m + n) * (x0 * y0) = x * y := by
            rw [hx0, hy0, pow_add]
            ring
          _ = eisensteinAxis ^ (m + n + 1) * z := hz
      rw [show m + n + 1 = (m + n) + 1 by omega,
        pow_add, pow_one,
        mul_dvd_mul_iff_left
          (pow_ne_zero (m + n) eisensteinAxis_prime.ne_zero)] at hz'
      exact hz'
    exact
      (eisensteinAxis_prime.dvd_or_dvd hcancel).elim
        hx0_not hy0_not

private theorem exactDepth_pow
    {x : SevenRealCubicInt} {m : ℕ}
    (hx : HasExactThetaDepth x m) (n : ℕ) :
    HasExactThetaDepth (x ^ n) (m * n) := by
  induction n with
  | zero =>
      constructor
      · simp
      · intro h
        exact eisensteinAxis_prime.not_isUnit
          (isUnit_of_dvd_one (by simpa using h))
  | succ n ih =>
      rw [pow_succ, Nat.mul_succ]
      exact exactDepth_mul ih hx

private theorem exactDepth_left_of_mul
    {x y : SevenRealCubicInt} {m n : ℕ}
    (hxy : HasExactThetaDepth (x * y) (m + n))
    (hy : HasExactThetaDepth y n) :
    HasExactThetaDepth x m := by
  rcases hy.1 with ⟨y0, hy0⟩
  have hy0_not : ¬eisensteinAxis ∣ y0 := by
    intro h
    apply hy.2
    rcases h with ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    rw [hy0]
    simp [pow_succ, mul_assoc, mul_comm]
  have hxmuly0 : eisensteinAxis ^ m ∣ x * y0 := by
    have hprod :
        eisensteinAxis ^ (m + n) ∣
          eisensteinAxis ^ n * (x * y0) := by
      rcases hxy.1 with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      calc
        eisensteinAxis ^ n * (x * y0) = x * y := by rw [hy0]; ring
        _ = eisensteinAxis ^ (m + n) * z := hz
    rw [pow_add] at hprod
    rw [mul_comm (eisensteinAxis ^ m) (eisensteinAxis ^ n)] at hprod
    rw [mul_dvd_mul_iff_left
      (pow_ne_zero n eisensteinAxis_prime.ne_zero)] at hprod
    exact hprod
  refine ⟨eisensteinAxis_prime.pow_dvd_of_dvd_mul_right
      m hy0_not hxmuly0, ?_⟩
  intro hxnext
  apply hxy.2
  rcases hxnext with ⟨x1, hx1⟩
  refine ⟨x1 * y0, ?_⟩
  rw [hx1, hy0,
    show m + n + 1 = (m + 1) + n by omega,
    pow_add]
  ring

private theorem exactDepth_intCast_of_not_seven_dvd
    (m : ℤ) (hm : ¬(7 : ℤ) ∣ m) :
    HasExactThetaDepth (m : SevenRealCubicInt) 0 := by
  constructor
  · simp
  · simpa [HasExactThetaDepth,
      eisensteinAxis_dvd_iff_thetaConstModSeven_eq_zero,
      thetaConstModSeven,
      ZMod.intCast_zmod_eq_zero_iff_dvd] using hm

private theorem exactDepth_unit (u : SevenRealCubicIntˣ) :
    HasExactThetaDepth (u : SevenRealCubicInt) 0 := by
  constructor
  · simp
  · intro h
    exact eisensteinAxis_prime.not_isUnit
      (isUnit_of_dvd_unit h u.isUnit)

private theorem exactDepth_eisensteinAxis :
    HasExactThetaDepth eisensteinAxis 1 := by
  refine ⟨by simp, ?_⟩
  rintro ⟨z, hz⟩
  have hmul : eisensteinAxis * z = 1 := by
    apply mul_left_cancel₀ eisensteinAxis_prime.ne_zero
    simpa [pow_two, mul_assoc] using hz.symm
  exact eisensteinAxis_prime.not_isUnit (IsUnit.of_mul_eq_one z hmul)

private theorem exactDepth_seven :
    HasExactThetaDepth (7 : SevenRealCubicInt) 3 := by
  rw [seven_eq_eisensteinAxis_cube_mul_unit]
  simpa [Nat.mul_comm] using
    exactDepth_mul (exactDepth_pow exactDepth_eisensteinAxis 3)
      (exactDepth_unit thetaSevenUnit_isUnit.unit)

private theorem exactDepth_natCast_seven_pow (k : ℕ) :
    HasExactThetaDepth ((7 ^ k : ℕ) : SevenRealCubicInt) (3 * k) := by
  have hpow := exactDepth_pow exactDepth_seven k
  simpa [Nat.mul_comm, Nat.cast_pow] using hpow

private theorem theta_dvd_directOrbit_gap
    (rho : SevenRealCubicInt) :
    eisensteinAxis ∣ rotateEquiv rho - rho := by
  rw [eisensteinAxis_dvd_iff_thetaConstModSeven_eq_zero]
  change thetaResidue (rotateEquiv rho - rho) = 0
  rw [map_sub, thetaResidue_rotateEquiv, sub_self]

private theorem directRoot_dvd_residual
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    p.rho ∣ (r.summit.residualRoot : SevenRealCubicInt) := by
  refine ⟨rotateEquiv p.rho * rotateEquiv (rotateEquiv p.rho), ?_⟩
  change ((r.summit.residualRoot : ℤ) : SevenRealCubicInt) = _
  rw [← p.norm_eq_residualRoot, ← mul_rotateEquiv_mul_rotateEquiv_sq_eq_norm]
  ring

private theorem exactDepth_gapRoot_pow
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source)
    (s : DirectOrbitGapSplit source r) :
    HasExactThetaDepth
      ((r.summit.gapRoot : SevenRealCubicInt) ^ 14) (42 * s.k) := by
  rw [s.gap_eq, Nat.cast_mul, Nat.cast_pow]
  have ha := exactDepth_intCast_of_not_seven_dvd
    (s.a : ℤ) (by exact_mod_cast s.a_not_seven_dvd)
  have h7 := exactDepth_natCast_seven_pow s.k
  have h := exactDepth_mul h7 ha
  have hp := exactDepth_pow h 14
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hp

private theorem exactDepth_orbitW_pow
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source)
    (s : DirectOrbitGapSplit source r) :
    HasExactThetaDepth
      ((eisensteinAxis ^ 5 * thetaSevenUnit *
        (r.summit.gapRoot : SevenRealCubicInt) ^ 2) ^ 7)
      (35 + 42 * s.k) := by
  have htheta := exactDepth_pow exactDepth_eisensteinAxis 5
  have hu := exactDepth_unit thetaSevenUnit_isUnit.unit
  have ha := exactDepth_gapRoot_pow r s
  have ha2 :
      HasExactThetaDepth
        ((r.summit.gapRoot : SevenRealCubicInt) ^ 2) (6 * s.k) := by
    rw [s.gap_eq, Nat.cast_mul, Nat.cast_pow]
    have h7 := exactDepth_natCast_seven_pow s.k
    have hcore := exactDepth_intCast_of_not_seven_dvd
      (s.a : ℤ) (by exact_mod_cast s.a_not_seven_dvd)
    have h := exactDepth_mul h7 hcore
    have hp := exactDepth_pow h 2
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hp
  have hw := exactDepth_mul (exactDepth_mul htheta hu) ha2
  have hp := exactDepth_pow hw 7
  simpa [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm,
    Nat.mul_comm] using hp

/-! ## Exact quotient depth and the stable gap divisibility -/

theorem directOrbit_quotient_exactDepth_three
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    HasExactThetaDepth (directOrbitQuotient p) 3 := by
  obtain ⟨core, hcore, hnot⟩ :=
    exists_seventhQuotient_core_exactDepth_three
      (rotateEquiv p.rho) p.rho p.not_eisensteinAxis_dvd
      (theta_dvd_directOrbit_gap p.rho)
  rw [directOrbitQuotient, hcore]
  have htheta := exactDepth_pow exactDepth_eisensteinAxis 3
  have hcore0 : HasExactThetaDepth core 0 := by
    exact ⟨by simp, by simpa using hnot⟩
  simpa using exactDepth_mul htheta hcore0

theorem directOrbit_gap_exactDepth
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) (s : DirectOrbitGapSplit source r) :
    HasExactThetaDepth (directOrbitGap p) (32 + 42 * s.k) := by
  have hprod := exactDepth_orbitW_pow r s
  have hunit := exactDepth_unit orbitUnit01Unit
  have hrhs := exactDepth_mul hunit hprod
  have hrhs' : HasExactThetaDepth
      (orbitUnit01 *
        (eisensteinAxis ^ 5 * thetaSevenUnit *
          (r.summit.gapRoot : SevenRealCubicInt) ^ 2) ^ 7)
      (35 + 42 * s.k) := by
    simpa [orbitUnit01Unit_val] using hrhs
  have hfac :
      HasExactThetaDepth
        (directOrbitGap p * directOrbitQuotient p)
        ((32 + 42 * s.k) + 3) := by
    rw [directOrbit_gap_mul_quotient p]
    convert hrhs' using 1; omega
  have hq := directOrbit_quotient_exactDepth_three p
  have hleft := exactDepth_left_of_mul
    (m := 32 + 42 * s.k) (n := 3) hfac hq
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hleft

theorem directOrbit_gap_axis_pow32_dvd
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    eisensteinAxis ^ 32 ∣ directOrbitGap p := by
  let s := directOrbitGapSplit r
  rcases (directOrbit_gap_exactDepth p s).1 with ⟨c, hc⟩
  refine ⟨eisensteinAxis ^ (42 * s.k) * c, ?_⟩
  simpa [pow_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
    mul_assoc] using hc

/-! ## Current-provenance coprimality and common-prime localization -/

theorem directOrbit_roots_isCoprime
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    IsCoprime p.rho (rotateEquiv p.rho) := by
  have hcop : IsCoprime (r.summit.gapRoot : SevenRealCubicInt)
      (r.summit.residualRoot : SevenRealCubicInt) := by
    have h : IsCoprime (r.summit.gapRoot : ℤ) (r.summit.residualRoot : ℤ) :=
      Int.isCoprime_iff_nat_coprime.mpr (by simpa using r.gap_residual_coprime)
    simpa using h.map (Int.castRingHom SevenRealCubicInt)
  apply isCoprime_of_prime_dvd
  · rintro ⟨h, _⟩
    exact p.not_eisensteinAxis_dvd (h ▸ dvd_zero _)
  · intro q hq hq0 hq1
    have hqB := hq0.trans (directRoot_dvd_residual p)
    have hqW : q ∣
        eisensteinAxis ^ 5 * thetaSevenUnit *
          (r.summit.gapRoot : SevenRealCubicInt) ^ 2 := by
      have hqD := dvd_sub (dvd_pow hq1 (by decide : 7 ≠ 0))
        (dvd_pow hq0 (by decide : 7 ≠ 0))
      rw [pow_seven_sub_pow_seven_factorization] at hqD
      change q ∣ directOrbitGap p * directOrbitQuotient p at hqD
      rw [directOrbit_gap_mul_quotient p] at hqD
      have hqpow := (hq.dvd_mul.mp hqD).resolve_left
        (fun h => hq.not_isUnit (isUnit_of_dvd_unit h orbitUnit01_isUnit))
      exact hq.dvd_of_dvd_pow hqpow
    have hqA : q ∣ (r.summit.gapRoot : SevenRealCubicInt) := by
      rcases hq.dvd_mul.mp hqW with ht | ha
      · rcases hq.dvd_mul.mp ht with ht | hu
        · have hassoc := hq.associated_of_dvd eisensteinAxis_prime
            (hq.dvd_of_dvd_pow ht)
          exact (p.not_eisensteinAxis_dvd
            (hassoc.dvd_iff_dvd_left.mp hq0)).elim
        · exact (hq.not_isUnit
            (isUnit_of_dvd_unit hu thetaSevenUnit_isUnit)).elim
      · exact hq.dvd_of_dvd_pow ha
    exact hq.not_isUnit (hcop.isUnit_of_dvd' hqA hqB)

theorem directOrbit_commonPrime_associated_theta
    {x y : SevenRealCubicInt} (hxy : IsCoprime x y) (q : SevenRealCubicInt)
    (hq : Prime q) (hgap : q ∣ x - y) (hh : q ∣ seventhQuotient x y) :
    Associated q eisensteinAxis := by
  have hseven : q ∣ (7 : SevenRealCubicInt) := by
    apply prime_dvd_exponent_cast_of_coprime_gap_and_homogeneous
      q x y 7 hq hxy hgap
    simpa [homogeneousPowerQuotient, DkMath.Algebra.DiffPow.diffPowSum,
      seventhQuotient, Finset.sum_range_succ] using hh
  rw [seven_eq_eisensteinAxis_cube_mul_unit] at hseven
  have htheta := (hq.dvd_mul.mp hseven).resolve_right
    (fun h => hq.not_isUnit
      (isUnit_of_dvd_unit h thetaSevenUnit_isUnit))
  exact hq.associated_of_dvd eisensteinAxis_prime
    (hq.dvd_of_dvd_pow htheta)

/-! ## The production checkpoint stops at stripped core coprimality.

The PID extraction is deliberately kept as the next bounded checkpoint: the
current theorem exposes the exact cores and their support control without
introducing a historical receiver or an unproved Archimedean successor. -/

set_option maxHeartbeats 800000 in
-- The dependent core witness proof needs the larger elaboration budget.
theorem directOrbit_stripped_cores_isCoprime
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    ∃ s : DirectOrbitGapSplit source r,
      ∃ gapCore quotientCore : SevenRealCubicInt,
        directOrbitGap p =
          eisensteinAxis ^ (32 + 42 * s.k) * gapCore ∧
        directOrbitQuotient p = eisensteinAxis ^ 3 * quotientCore ∧
        ¬eisensteinAxis ∣ gapCore ∧
        ¬eisensteinAxis ∣ quotientCore ∧
        IsCoprime gapCore quotientCore := by
  let s := directOrbitGapSplit r
  have hd := directOrbit_gap_exactDepth p s
  have hq := directOrbit_quotient_exactDepth_three p
  rcases hd.1 with ⟨gapCore, hgap⟩
  rcases hq.1 with ⟨quotientCore, hquotient⟩
  have hgapnot : ¬eisensteinAxis ∣ gapCore := by
    intro h
    apply hd.2
    rcases h with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [hgap, hc, pow_succ]
    ring
  have hquotientnot : ¬eisensteinAxis ∣ quotientCore := by
    intro h
    apply hq.2
    rcases h with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [hquotient, hc, pow_succ]
    ring
  have hcop : IsCoprime gapCore quotientCore := by
    apply isCoprime_of_prime_dvd
    · rintro ⟨h, _⟩
      exact hgapnot (h ▸ dvd_zero _)
    · intro q hqprime hgd hqh
      have hqgap : q ∣ directOrbitGap p := by
        have htemp : q ∣
            eisensteinAxis ^ (32 + 42 * s.k) * gapCore :=
          dvd_mul_of_dvd_right hgd _
        simpa only [hgap] using htemp
      have hqquot : q ∣ directOrbitQuotient p := by
        have htemp : q ∣ eisensteinAxis ^ 3 * quotientCore :=
          dvd_mul_of_dvd_right hqh _
        simpa only [hquotient] using htemp
      have hassoc := directOrbit_commonPrime_associated_theta
        (directOrbit_roots_isCoprime p).symm q hqprime
        hqgap hqquot
      exact hgapnot (hassoc.dvd_iff_dvd_left.mp hgd)
  exact ⟨s, gapCore, quotientCore, hgap, hquotient,
    hgapnot, hquotientnot, hcop⟩

end
end DkMath.FLT.Seven
