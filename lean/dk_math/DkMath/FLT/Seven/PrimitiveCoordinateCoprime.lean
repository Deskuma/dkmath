/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.QuadraticCoprimeFactor

#print "file: DkMath.FLT.Seven.PrimitiveCoordinateCoprime"

namespace DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic

private theorem intCast_traceOneNegTwo (a : ℤ) :
    (a : TraceOneInt (-2)) = ⟨a, 0⟩ := rfl

theorem prime_dvd_both_cyclotomicSeven_coordinates
    {z y q : ℕ} (hq : Nat.Prime q)
    (hA : (q : ℤ) ∣ cyclotomicSevenFst (z : ℤ) (y : ℤ))
    (hB : (q : ℤ) ∣ cyclotomicSevenSnd (z : ℤ) (y : ℤ)) :
    q ∣ z ∧ q ∣ y := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  have hAZ : (cyclotomicSevenFst (z : ℤ) (y : ℤ) : ZMod q) = 0 :=
    (CharP.intCast_eq_zero_iff (ZMod q) q _).2 hA
  have hBZ : (cyclotomicSevenSnd (z : ℤ) (y : ℤ) : ZMod q) = 0 :=
    (CharP.intCast_eq_zero_iff (ZMod q) q _).2 hB
  have hApoly : (z : ZMod q) ^ 3 + (z : ZMod q) ^ 2 * (y : ZMod q) -
      (y : ZMod q) ^ 3 = 0 := by
    simpa [cyclotomicSevenFst] using hAZ
  have hBpoly : (z : ZMod q) * (y : ZMod q) * ((z : ZMod q) + y) = 0 := by
    have hneg : -((z : ZMod q) * (y : ZMod q) * ((z : ZMod q) + y)) = 0 := by
      calc
        -((z : ZMod q) * (y : ZMod q) * ((z : ZMod q) + y)) =
            (cyclotomicSevenSnd (z : ℤ) (y : ℤ) : ZMod q) := by
              simp [cyclotomicSevenSnd]
              ring
        _ = 0 := hBZ
    exact neg_eq_zero.mp hneg
  have hZY : (z : ZMod q) = 0 ∧ (y : ZMod q) = 0 := by
    rcases mul_eq_zero.mp hBpoly with hzy | hsum
    · rcases mul_eq_zero.mp hzy with hz | hy
      · rw [hz] at hApoly
        have hy3 : (y : ZMod q) ^ 3 = 0 := by simpa using hApoly
        exact ⟨hz, eq_zero_of_pow_eq_zero hy3⟩
      · rw [hy] at hApoly
        have hz3 : (z : ZMod q) ^ 3 = 0 := by simpa using hApoly
        exact ⟨eq_zero_of_pow_eq_zero hz3, hy⟩
    · have hz : (z : ZMod q) = -(y : ZMod q) := eq_neg_of_add_eq_zero_left hsum
      rw [hz] at hApoly
      have hy3 : (y : ZMod q) ^ 3 = 0 := by
        ring_nf at hApoly
        simpa using neg_eq_zero.mp hApoly
      have hy : (y : ZMod q) = 0 := eq_zero_of_pow_eq_zero hy3
      exact ⟨by simp [hz, hy], hy⟩
  constructor
  · exact (ZMod.natCast_eq_zero_iff z q).1 hZY.1
  · exact (ZMod.natCast_eq_zero_iff y q).1 hZY.2

theorem cyclotomicSeven_coordinates_isCoprime
    {z y : ℕ} (hcop : Nat.Coprime z y) :
    IsCoprime (cyclotomicSevenFst (z : ℤ) (y : ℤ))
      (cyclotomicSevenSnd (z : ℤ) (y : ℤ)) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hg
  rcases Nat.exists_prime_and_dvd hg with ⟨q, hq, hqgcd⟩
  have hqgcdInt : (q : ℤ) ∣
      (Int.gcd (cyclotomicSevenFst (z : ℤ) (y : ℤ))
        (cyclotomicSevenSnd (z : ℤ) (y : ℤ)) : ℤ) :=
    Int.natCast_dvd_natCast.mpr hqgcd
  have hqA : (q : ℤ) ∣ cyclotomicSevenFst (z : ℤ) (y : ℤ) :=
    hqgcdInt.trans (Int.gcd_dvd_left _ _)
  have hqB : (q : ℤ) ∣ cyclotomicSevenSnd (z : ℤ) (y : ℤ) :=
    hqgcdInt.trans (Int.gcd_dvd_right _ _)
  rcases prime_dvd_both_cyclotomicSeven_coordinates hq hqA hqB with ⟨hqz, hqy⟩
  exact (Nat.not_coprime_of_dvd_of_dvd hq.one_lt hqz hqy) hcop

theorem counterexample_cyclotomicSeven_coordinates_isCoprime
    {x y z : ℕ} (hPack : CounterexamplePack x y z) :
    IsCoprime (cyclotomicSevenFst (z : ℤ) (y : ℤ))
      (cyclotomicSevenSnd (z : ℤ) (y : ℤ)) :=
  cyclotomicSeven_coordinates_isCoprime
    (coprime_y_z_of_counterexamplePack hPack).symm

theorem sub_conj_eq_snd_mul_sevenAxis (w : TraceOneInt (-2)) :
    w - conj w = (w.snd : TraceOneInt (-2)) * sevenAxis := by
  rcases w with ⟨a, b⟩
  rw [sevenAxis_eq]
  apply traceOne_ext
  · norm_num [conj, intCast_traceOneNegTwo]
  · norm_num [conj, intCast_traceOneNegTwo]
    ring

theorem sevenAxis_mul_sub_tau_mul_sub_conj (w : TraceOneInt (-2)) :
    sevenAxis * w - tau (-2) * (w - conj w) =
      (w.fst : TraceOneInt (-2)) * sevenAxis := by
  rcases w with ⟨a, b⟩
  rw [sevenAxis_eq]
  ext <;> norm_num [tau, conj, intCast_traceOneNegTwo] <;> ring

theorem common_divisor_dvd_sevenAxis_of_coordinate_coprime
    {w d : TraceOneInt (-2)} (hcoords : IsCoprime w.fst w.snd)
    (hdw : d ∣ w) (hdconj : d ∣ conj w) : d ∣ sevenAxis := by
  have hdsnd : d ∣ (w.snd : TraceOneInt (-2)) * sevenAxis := by
    rw [← sub_conj_eq_snd_mul_sevenAxis]
    exact dvd_sub hdw hdconj
  have hdfst : d ∣ (w.fst : TraceOneInt (-2)) * sevenAxis := by
    rw [← sevenAxis_mul_sub_tau_mul_sub_conj]
    exact dvd_sub (dvd_mul_of_dvd_right hdw sevenAxis)
      (dvd_mul_of_dvd_right (dvd_sub hdw hdconj) (tau (-2)))
  rcases hcoords with ⟨m, n, hbezout⟩
  rcases hdfst with ⟨a, ha⟩
  rcases hdsnd with ⟨b, hb⟩
  refine ⟨(m : TraceOneInt (-2)) * a + (n : TraceOneInt (-2)) * b, ?_⟩
  have hcast : ((m * w.fst + n * w.snd : ℤ) : TraceOneInt (-2)) = 1 := by
    rw [hbezout]
    norm_num
  calc
    sevenAxis = ((m * w.fst + n * w.snd : ℤ) : TraceOneInt (-2)) * sevenAxis := by
      rw [hcast, one_mul]
    _ = (m : TraceOneInt (-2)) * ((w.fst : TraceOneInt (-2)) * sevenAxis) +
        (n : TraceOneInt (-2)) * ((w.snd : TraceOneInt (-2)) * sevenAxis) := by
      push_cast
      ring
    _ = d * ((m : TraceOneInt (-2)) * a + (n : TraceOneInt (-2)) * b) := by
      rw [ha, hb]
      ring

theorem common_divisor_cyclotomic_conj_dvd_sevenAxis
    {z y : ℕ} {d : TraceOneInt (-2)} (hcop : Nat.Coprime z y)
    (hd : d ∣ cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ))
    (hdc : d ∣ conj (cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ))) :
    d ∣ sevenAxis := by
  apply common_divisor_dvd_sevenAxis_of_coordinate_coprime
    (w := cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ))
  · simpa [cyclotomicSevenToTraceOne] using
      (cyclotomicSeven_coordinates_isCoprime hcop)
  · exact hd
  · exact hdc

end DkMath.FLT.Seven
