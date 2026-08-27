/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimitiveCoordinateCoprime

#print "file: DkMath.FLT.Seven.QuadraticConjugateCoprime"

namespace DkMath.FLT.Seven

open DkMath.CosmicFormulaBinom
open DkMath.NumberTheory.TraceOneQuadratic

local notation "tqNorm" => DkMath.NumberTheory.TraceOneQuadratic.norm

theorem irreducible_sevenAxis :
    Irreducible (sevenAxis : TraceOneInt (-2)) := by
  refine ⟨?_, ?_⟩
  · rw [isUnit_iff_norm_eq_one, sevenAxis_norm]
    norm_num
  · intro a b hab
    have haxis0 : (sevenAxis : TraceOneInt (-2)) ≠ 0 := by
      intro h
      have hnorm0 : tqNorm (sevenAxis : TraceOneInt (-2)) = 0 :=
        (norm_eq_zero_iff_of_negTwo sevenAxis).2 h
      rw [sevenAxis_norm] at hnorm0
      norm_num at hnorm0
    have ha0 : a ≠ 0 := by
      intro ha
      rw [ha, zero_mul] at hab
      exact haxis0 hab
    have hb0 : b ≠ 0 := by
      intro hb
      rw [hb, mul_zero] at hab
      exact haxis0 hab
    have haPos := one_le_traceOneNorm_negTwo_of_ne_zero a ha0
    have hbPos := one_le_traceOneNorm_negTwo_of_ne_zero b hb0
    have hnorm : tqNorm a * tqNorm b = 7 := by
      rw [← traceOne_norm_mul, ← hab, sevenAxis_norm]
    have hdiv : tqNorm a ∣ (7 : ℤ) := ⟨tqNorm b, hnorm.symm⟩
    have hdivNat : (tqNorm a).natAbs ∣ 7 := by
      simpa using (Int.natAbs_dvd_natAbs.mpr hdiv)
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hdivNat with haOne | haSeven
    · left
      rw [isUnit_iff_norm_eq_one]
      have := Int.natAbs_of_nonneg (le_trans (by norm_num) haPos)
      omega
    · right
      rw [isUnit_iff_norm_eq_one]
      have haNonneg : 0 ≤ tqNorm a := le_trans (by norm_num) haPos
      have haCast := Int.natAbs_of_nonneg haNonneg
      have haNorm : tqNorm a = 7 := by omega
      nlinarith

theorem prime_sevenAxis : Prime (sevenAxis : TraceOneInt (-2)) :=
  irreducible_iff_prime.mp irreducible_sevenAxis

theorem isUnit_of_dvd_sevenAxis_of_dvd_terminal
    {d r : TraceOneInt (-2)} (hdAxis : d ∣ sevenAxis) (hdr : d ∣ r)
    (hterminal : ¬ sevenAxis ∣ r) : IsUnit d := by
  rcases hdAxis with ⟨k, hk⟩
  rcases irreducible_sevenAxis.isUnit_or_isUnit hk with hd | hkUnit
  · exact hd
  · exfalso
    apply hterminal
    rcases isUnit_iff_exists_inv.mp hkUnit with ⟨kinv, hkinv⟩
    have hAxisD : sevenAxis ∣ d := by
      refine ⟨kinv, ?_⟩
      calc
        d = d * (k * kinv) := by rw [hkinv, mul_one]
        _ = (d * k) * kinv := by ring
        _ = sevenAxis * kinv := by rw [← hk]
    exact hAxisD.trans hdr

theorem cyclotomicSeven_gcd_conj_isUnit_of_not_seven_dvd_gap
    {z y : ℕ} (hcop : Nat.Coprime z y) (hgap : ¬ 7 ∣ z - y) :
    IsUnit (gcd (cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ))
      (conj (cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ)))) := by
  let C := cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ)
  let d := gcd C (conj C)
  have hdC : d ∣ C := gcd_dvd_left C (conj C)
  have hdConj : d ∣ conj C := gcd_dvd_right C (conj C)
  have hdAxis : d ∣ sevenAxis :=
    common_divisor_cyclotomic_conj_dvd_sevenAxis hcop hdC hdConj
  by_contra hdUnit
  rcases hdAxis with ⟨k, hk⟩
  rcases irreducible_sevenAxis.isUnit_or_isUnit hk with hd | hkUnit
  · exact hdUnit hd
  · have hAxisD : sevenAxis ∣ d := by
      rcases isUnit_iff_exists_inv.mp hkUnit with ⟨kinv, hkinv⟩
      refine ⟨kinv, ?_⟩
      calc
        d = d * (k * kinv) := by rw [hkinv, mul_one]
        _ = (d * k) * kinv := by ring
        _ = sevenAxis * kinv := by rw [← hk]
    have hAxisC : sevenAxis ∣ C := hAxisD.trans hdC
    have hgapInt : (7 : ℤ) ∣ (z : ℤ) - (y : ℤ) :=
      (sevenAxis_dvd_cyclotomicSevenToTraceOne_iff (z : ℤ) (y : ℤ)).mp hAxisC
    have hyz : y ≤ z := by
      by_contra hnot
      have hzero : z - y = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hnot)
      exact hgap (by simp [hzero])
    apply hgap
    apply Int.ofNat_dvd.mp
    simpa [Int.ofNat_sub hyz] using hgapInt

private theorem cyclotomic_mul_conj_eq_GN_intCast
    {z y : ℕ} (hyz : y ≤ z) :
    cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ) *
        conj (cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ)) =
      ((GN 7 (z - y) y : ℕ) : TraceOneInt (-2)) := by
  rw [traceOne_mul_conj]
  have hnorm := GN_seven_sub_eq_traceOneNorm_negTwo z y hyz
  change ofInt (-2) (tqNorm (cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ))) =
    ofInt (-2) ((GN 7 (z - y) y : ℕ) : ℤ)
  rw [hnorm]

theorem exists_cyclotomicSeven_eq_seventh_power_of_away
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hgap : ¬ 7 ∣ z - y) :
    ∃ gamma : TraceOneInt (-2),
      cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ) = gamma ^ 7 := by
  rcases (branchAway_seventh_power_factor_split hPack hgap).2 with ⟨v, hv⟩
  let C := cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ)
  have hyz := (right_lt_of_fermat7Equation hPack.hx hPack.hEq).le
  have hmul : C * conj C = (v : TraceOneInt (-2)) ^ 7 := by
    rw [show C * conj C = ((GN 7 (z - y) y : ℕ) : TraceOneInt (-2)) by
      exact cyclotomic_mul_conj_eq_GN_intCast hyz]
    rw [hv]
    norm_num
  exact exists_eq_seventh_power_of_coprime_mul_eq_pow
    (cyclotomicSeven_gcd_conj_isUnit_of_not_seven_dvd_gap
      (coprime_y_z_of_counterexamplePack hPack).symm hgap) hmul

theorem SevenQuadraticResidualPacket.gcd_residual_conj_isUnit
    {x y z : ℕ} (q : SevenQuadraticResidualPacket x y z) :
    IsUnit (gcd q.residualCore (conj q.residualCore)) := by
  let d := gcd q.residualCore (conj q.residualCore)
  have hdr : d ∣ q.residualCore := gcd_dvd_left _ _
  have hdrc : d ∣ conj q.residualCore := gcd_dvd_right _ _
  have hdC : d ∣ cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ) := by
    rw [q.coordinate_eq]
    exact dvd_mul_of_dvd_right hdr sevenAxis
  have hdConjC : d ∣ conj (cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ)) := by
    rw [q.coordinate_eq, traceOne_conj_mul, conj_sevenAxis]
    exact dvd_mul_of_dvd_right hdrc (-sevenAxis)
  have hcop : Nat.Coprime z y :=
    (coprime_y_z_of_counterexamplePack
      q.powerSplit.sevenAdic.counterexample).symm
  have hdAxis : d ∣ sevenAxis :=
    common_divisor_cyclotomic_conj_dvd_sevenAxis hcop hdC hdConjC
  exact isUnit_of_dvd_sevenAxis_of_dvd_terminal hdAxis hdr q.residual_terminal

theorem SevenQuadraticResidualPacket.exists_residualCore_eq_seventh_power
    {x y z : ℕ} (q : SevenQuadraticResidualPacket x y z) :
    ∃ gamma : TraceOneInt (-2), q.residualCore = gamma ^ 7 := by
  have hmul : q.residualCore * conj q.residualCore =
      (q.powerSplit.b : TraceOneInt (-2)) ^ 7 := by
    rw [traceOne_mul_conj]
    rw [q.residual_norm_eq]
    change (((q.powerSplit.b : ℤ) ^ 7 : ℤ) : TraceOneInt (-2)) =
      ((q.powerSplit.b : ℤ) : TraceOneInt (-2)) ^ 7
    exact Int.cast_pow q.powerSplit.b 7
  exact exists_eq_seventh_power_of_coprime_mul_eq_pow
    q.gcd_residual_conj_isUnit hmul

end DkMath.FLT.Seven
