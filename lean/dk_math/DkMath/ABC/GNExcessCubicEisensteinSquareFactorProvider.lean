/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Three.EisensteinEuclidean
import DkMath.ABC.GNExcessCubicEisensteinCoordinates
import DkMath.ABC.GNExcessCubicSquarefulPell
import DkMath.Lib.NumberTheory.SquarefreePowerFactor
import DkMath.Lib.NumberTheory.EisensteinLatticeLanding

#print "file: DkMath.ABC.GNExcessCubicEisensteinSquareFactorProvider"

/-!
# Cubic Eisenstein square-factor provider

The coefficient-one cubic coordinate makes the squarefree residual's integer
norm squarefree.  This module supplies the resulting factorization and then
matches its norm factors with the shell's canonical odd/even allocation.
It does not prove any ABC counting or asymptotic statement.
-/

namespace DkMath.ABC

noncomputable section

open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.Lib.NumberTheory

local notation "tqNorm" => DkMath.NumberTheory.TraceOneQuadratic.norm

theorem squarefree_conj {x : TraceOneInt (-1)} (hx : Squarefree x) :
    Squarefree (conj x) := by
  intro d hd
  obtain ⟨k, hk⟩ := hd
  have hdd : conj d * conj d ∣ x := by
    refine ⟨conj k, ?_⟩
    have h := congrArg conj hk
    simpa only [traceOne_conj_invol, traceOne_conj_mul] using h
  obtain ⟨u, hu⟩ := hx (conj d) hdd
  rw [isUnit_iff_dvd_one]
  refine ⟨conj (↑(u⁻¹) : TraceOneInt (-1)), ?_⟩
  have hmul : conj d * (↑(u⁻¹) : TraceOneInt (-1)) = 1 := by
    rw [← hu]
    exact Units.mul_inv u
  have h := congrArg conj hmul
  simpa only [traceOne_conj_mul, traceOne_conj_invol,
    show conj (1 : TraceOneInt (-1)) = 1 from rfl] using h.symm

theorem scalar_dvd_of_square_dvd_norm
    {b : TraceOneInt (-1)} (hb : Squarefree b) {d : ℤ}
    (hd : d * d ∣ tqNorm b) : (d : TraceOneInt (-1)) ∣ b := by
  have hsq : (d : TraceOneInt (-1)) * (d : TraceOneInt (-1)) ∣ conj b * b := by
    obtain ⟨k, hk⟩ := hd
    refine ⟨(k : TraceOneInt (-1)), ?_⟩
    rw [mul_comm (conj b) b, traceOne_mul_conj]
    change ((tqNorm b : ℤ) : TraceOneInt (-1)) = _
    simpa only [Int.cast_mul] using
      congrArg (fun z : ℤ => (z : TraceOneInt (-1))) hk
  exact (squarefree_conj hb).dvd_of_squarefree_of_mul_dvd_mul_right hsq

theorem squarefree_norm_of_dvd_cubicCoord
    {a : ℤ} {b : TraceOneInt (-1)} (hb : Squarefree b)
    (hba : b ∣ eisensteinCoord (a + 2) 1) :
    Squarefree (tqNorm b) := by
  intro d hd
  obtain ⟨k, hk⟩ := (scalar_dvd_of_square_dvd_norm hb hd).trans hba
  have hs := congrArg TraceOneInt.snd hk
  change -(1 : ℤ) = d * k.snd + 0 * k.fst + 0 * k.snd at hs
  have hd1 : d ∣ (-1 : ℤ) := ⟨k.snd, by simpa using hs⟩
  exact isUnit_of_dvd_unit hd1 (isUnit_one.neg)

theorem exists_cubicCoord_squarefree_norm_mul_sq (a : ℤ) :
    ∃ b c : TraceOneInt (-1),
      Squarefree b ∧ Squarefree (tqNorm b) ∧
      eisensteinCoord (a + 2) 1 = b * c ^ 2 := by
  have ha : eisensteinCoord (a + 2) 1 ≠ 0 := by
    intro h
    have hs := congrArg TraceOneInt.snd h
    norm_num at hs
  obtain ⟨b, c, hb, hbc⟩ := exists_squarefree_mul_sq
    (eisensteinCoord (a + 2) 1) ha
  exact ⟨b, c, hb, squarefree_norm_of_dvd_cubicCoord hb ⟨c ^ 2, hbc⟩, hbc⟩

theorem exists_cubicCoord_nat_squarefree_norm_mul_sq (a : ℕ) :
    ∃ b c : TraceOneInt (-1),
      Squarefree (tqNorm b).natAbs ∧
      a ^ 2 + 3 * a + 3 = (tqNorm b).natAbs * (tqNorm c).natAbs ^ 2 ∧
      eisensteinCoord ((a : ℤ) + 2) 1 = b * c ^ 2 := by
  obtain ⟨b, c, _, hb, hbc⟩ := exists_cubicCoord_squarefree_norm_mul_sq (a : ℤ)
  refine ⟨b, c, Int.squarefree_natAbs.mpr hb, ?_, hbc⟩
  have hn : ((a ^ 2 + 3 * a + 3 : ℕ) : ℤ) = tqNorm b * tqNorm c ^ 2 := by
    calc
      ((a ^ 2 + 3 * a + 3 : ℕ) : ℤ) =
          tqNorm (eisensteinCoord ((a : ℤ) + 2) 1) := by
        rw [norm_eisensteinCoord]
        push_cast
        ring
      _ = tqNorm b * tqNorm c ^ 2 := by
        rw [hbc, pow_two, traceOne_norm_mul, traceOne_norm_mul]
        ring
  simpa only [Int.natAbs_natCast, Int.natAbs_mul, Int.natAbs_pow] using
    congrArg Int.natAbs hn

theorem nat_squarefree_square_decomposition_unique
    {T d B G : ℕ} (hT : Squarefree T) (hB : Squarefree B)
    (hd : d ≠ 0) (hG : G ≠ 0)
    (heq : T * d ^ 2 = B * G ^ 2) :
    B = T ∧ G = d := by
  have hT0 : T ≠ 0 := hT.ne_zero
  have hB0 : B ≠ 0 := hB.ne_zero
  have hv (q : ℕ) : B.factorization q = T.factorization q ∧
      G.factorization q = d.factorization q := by
    have ht := hT.natFactorization_le_one q
    have hb := hB.natFactorization_le_one q
    have he := congrArg (fun n : ℕ => n.factorization q) heq
    simp only [Nat.factorization_mul hT0 (pow_ne_zero _ hd),
      Nat.factorization_mul hB0 (pow_ne_zero _ hG),
      Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply,
      smul_eq_mul] at he
    omega
  exact ⟨Nat.eq_of_factorization_eq hB0 hT0 (fun q => (hv q).1),
    Nat.eq_of_factorization_eq hG hd (fun q => (hv q).2)⟩

theorem shell_squarefree_norm_allocation
    {X D a B G : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D)
    (hB : Squarefree B) (hG : G ≠ 0)
    (hNorm : a ^ 2 + 3 * a + 3 = B * G ^ 2) :
    B = oddPart (GNExcessCubicFullRepeatedModulus a) *
        GNExcessCubicComplement a ∧
    G = evenPart (GNExcessCubicFullRepeatedModulus a) := by
  let M := GNExcessCubicFullRepeatedModulus a
  let S := GNExcessCubicComplement a
  have hMS : (M, S) ∈
      GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D :=
    Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hT :=
    GNExcessCubicRealizedLargeModulusShellIncidencePair_squarefree_pellParameter hMS
  have hdecomp :=
    (GNExcessCubicRealizedLargeModulusShellIncidencePair_squareful_packet hMS).1
  have hprod : M * S = a ^ 2 + 3 * a + 3 :=
    (GNExcessCubicRealizedLargeModulusShellWitness_complement_packet ha).2.2.2.2.2.1
  have hd : evenPart M ≠ 0 := by
    intro hz
    rw [hz] at hdecomp
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero] at hdecomp
    rw [hdecomp, zero_mul] at hprod
    omega
  apply nat_squarefree_square_decomposition_unique hT hB hd hG
  calc
    (oddPart M * S) * (evenPart M) ^ 2 =
        (oddPart M * (evenPart M) ^ 2) * S := by ring
    _ = M * S := congrArg (fun z : ℕ => z * S) hdecomp.symm
    _ = a ^ 2 + 3 * a + 3 := hprod
    _ = B * G ^ 2 := hNorm

theorem GNExcessCubicRealizedLargeModulusShellWitness_exists_eisenstein_square_factor
    {X D a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D) :
    ∃ beta gamma : TraceOneInt (-1),
      (tqNorm beta).natAbs =
        oddPart (GNExcessCubicFullRepeatedModulus a) *
          GNExcessCubicComplement a ∧
      (tqNorm gamma).natAbs =
        evenPart (GNExcessCubicFullRepeatedModulus a) ∧
      eisensteinCoord ((a : ℤ) + 2) 1 = beta * gamma ^ 2 := by
  obtain ⟨beta, gamma, hsf, hnorm, hfac⟩ :=
    exists_cubicCoord_nat_squarefree_norm_mul_sq a
  have hG : (tqNorm gamma).natAbs ≠ 0 := by
    intro hg
    have hg0 : tqNorm gamma = 0 := Int.natAbs_eq_zero.mp hg
    have hgamma : gamma = 0 := (traceOne_neg_one_norm_eq_zero_iff gamma).mp hg0
    subst gamma
    norm_num [DkMath.NumberTheory.TraceOneQuadratic.norm] at hnorm
  have halloc := shell_squarefree_norm_allocation
    (X := X) (D := D) (a := a) (B := (tqNorm beta).natAbs)
    (G := (tqNorm gamma).natAbs) ha hsf hG hnorm
  exact ⟨beta, gamma, halloc.1, halloc.2, hfac⟩

end

#print axioms squarefree_norm_of_dvd_cubicCoord
#print axioms exists_cubicCoord_nat_squarefree_norm_mul_sq
#print axioms shell_squarefree_norm_allocation
#print axioms GNExcessCubicRealizedLargeModulusShellWitness_exists_eisenstein_square_factor

end DkMath.ABC
