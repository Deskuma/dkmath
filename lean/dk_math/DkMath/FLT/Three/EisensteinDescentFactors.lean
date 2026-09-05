/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Three.EisensteinSectorExclusion

#print "file: DkMath.FLT.Three.EisensteinDescentFactors"

namespace DkMath.FLT.Three

open DkMath.NumberTheory.TraceOneQuadratic

/-!
# Origin-preserving Eisenstein descent factors

This module carries the same routed packet through exact-cube extraction and
then splits the three signed factors into pairwise-coprime natural cubes.  It
stops before sign routing into a new positive FLT3 triple.
-/

/-- The flattened exact-cube source used by the descent-factor API. -/
structure EisensteinDescentFactorSource
    (a b c : ℕ) : Type where
  origin : SignedThreeAdicOriginPacket a b c
  exactCube : EisensteinExactCubePacket a b c
  A : ℕ
  B : ℕ
  r : ℤ
  s : ℤ
  A_pos : 0 < A
  B_pos : 0 < B
  coprime_A_B : Nat.Coprime A B
  three_not_dvd_B : ¬ 3 ∣ B
  distinguished_eq :
    origin.packet.distinguished = 3 * A * B
  product_eq :
    r * s * (r + s) = (A : ℤ) ^ 3
  norm_eq :
    r ^ 2 + r * s + s ^ 2 = (B : ℤ)

/-- Build the flattened source through one and the same origin packet. -/
noncomputable def eisensteinDescentFactorSource_of_primitive_solution
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hEq : a ^ 3 + b ^ 3 = c ^ 3) :
    EisensteinDescentFactorSource a b c := by
  let origin := signedThreeAdicOriginPacket_of_primitive_solution ha hb hc hab hEq
  let splitWithPacket := signedThreeAdicPowerSplit_with_packet origin.packet
  let split := splitWithPacket.1
  let stripped := eisensteinRamifierStrippedPacket_of_powerSplit split
  let conjugateCoprime := eisensteinConjugateCoprimePacket_of_stripped stripped
  let cubeUpToUnit :=
    eisensteinCubeUpToUnitPacket_of_conjugateCoprime conjugateCoprime
  let sector := eisensteinCubeSectorPacket_of_cubeUpToUnit cubeUpToUnit
  let exactCube := eisensteinExactCubePacket_of_sectorPacket sector
  let r := exactCube.sectorPacket.gamma.fst
  let s := exactCube.sectorPacket.gamma.snd
  have hA :
      exactCube.sectorPacket.cubeUpToUnit.conjugateCoprime.stripped.powerSplit.A =
        split.A := by
    rfl
  have hB :
      exactCube.sectorPacket.cubeUpToUnit.conjugateCoprime.stripped.powerSplit.B =
        split.B := by
    rfl
  refine {
    origin := origin
    exactCube := exactCube
    A := split.A
    B := split.B
    r := r
    s := s
    A_pos := split.A_pos
    B_pos := split.B_pos
    coprime_A_B := split.coprime_A_B
    three_not_dvd_B := split.three_not_dvd_B
    distinguished_eq := ?_
    product_eq := ?_
    norm_eq := ?_ }
  · rw [← splitWithPacket.2]
    exact split.distinguished_eq
  · simpa [r, s, hA] using
      gamma_coordinate_product_eq_A_cube exactCube.sectorPacket
  · simpa [r, s, hB] using
      gamma_coordinate_norm_eq_B exactCube.sectorPacket

theorem EisensteinDescentFactorSource.r_ne_zero
    {a b c : ℕ} (p : EisensteinDescentFactorSource a b c) :
    p.r ≠ 0 := by
  intro hr
  have hzero : (p.A : ℤ) ^ 3 = 0 := by
    rw [← p.product_eq, hr]
    simp
  have hpos : 0 < (p.A : ℤ) ^ 3 := by
    exact_mod_cast (pow_pos p.A_pos 3)
  exact (ne_of_gt hpos) hzero

theorem EisensteinDescentFactorSource.s_ne_zero
    {a b c : ℕ} (p : EisensteinDescentFactorSource a b c) :
    p.s ≠ 0 := by
  intro hs
  have hzero : (p.A : ℤ) ^ 3 = 0 := by
    rw [← p.product_eq, hs]
    simp
  have hpos : 0 < (p.A : ℤ) ^ 3 := by
    exact_mod_cast (pow_pos p.A_pos 3)
  exact (ne_of_gt hpos) hzero

theorem EisensteinDescentFactorSource.sum_ne_zero
    {a b c : ℕ} (p : EisensteinDescentFactorSource a b c) :
    p.r + p.s ≠ 0 := by
  intro hsum
  have hzero : (p.A : ℤ) ^ 3 = 0 := by
    rw [← p.product_eq, hsum]
    simp
  have hpos : 0 < (p.A : ℤ) ^ 3 := by
    exact_mod_cast (pow_pos p.A_pos 3)
  exact (ne_of_gt hpos) hzero

theorem EisensteinDescentFactorSource.abs_factor_product_eq_A_cube
    {a b c : ℕ} (p : EisensteinDescentFactorSource a b c) :
    p.r.natAbs * p.s.natAbs * (p.r + p.s).natAbs = p.A ^ 3 := by
  have h := congrArg Int.natAbs p.product_eq
  simpa [Int.natAbs_mul, Int.natAbs_pow] using h

private theorem int_dvd_of_natAbs_dvd
    {d : ℕ} {x : ℤ} (h : d ∣ x.natAbs) :
    (d : ℤ) ∣ x := by
  apply (Int.natAbs_dvd_natAbs).mp
  simpa using h

private theorem natAbs_dvd_of_int_dvd
    {d : ℕ} {x : ℤ} (h : (d : ℤ) ∣ x) :
    d ∣ x.natAbs := by
  have h' := (Int.natAbs_dvd_natAbs).mpr h
  simpa using h'

private theorem common_factor_eq_one
    {a b c : ℕ} (p : EisensteinDescentFactorSource a b c)
    {d : ℕ} (hr : d ∣ p.r.natAbs) (hs : d ∣ p.s.natAbs) :
    d = 1 := by
  have hdA3 : d ∣ p.A ^ 3 := by
    rw [← p.abs_factor_product_eq_A_cube]
    simpa [Nat.mul_assoc] using dvd_mul_of_dvd_left hr
      (p.s.natAbs * (p.r + p.s).natAbs)
  have hdr : (d : ℤ) ∣ p.r := int_dvd_of_natAbs_dvd hr
  have hds : (d : ℤ) ∣ p.s := int_dvd_of_natAbs_dvd hs
  have hdNorm : (d : ℤ) ∣
      p.r ^ 2 + p.r * p.s + p.s ^ 2 := by
    exact dvd_add (dvd_add (dvd_pow hdr (by decide))
        (dvd_mul_of_dvd_left hdr p.s))
      (dvd_pow hds (by decide))
  have hdBcast : (d : ℤ) ∣ (p.B : ℤ) := by
    rw [← p.norm_eq]
    exact hdNorm
  have hdB : d ∣ p.B := by
    exact_mod_cast hdBcast
  have hAB : Nat.Coprime (p.A ^ 3) p.B :=
    Nat.Coprime.pow_left 3 p.coprime_A_B
  have hdd : Nat.Coprime d d :=
    Nat.Coprime.of_dvd hdA3 hdB hAB
  exact (Nat.coprime_self d).mp hdd

theorem EisensteinDescentFactorSource.coprime_abs_r_s
    {a b c : ℕ} (p : EisensteinDescentFactorSource a b c) :
    Nat.Coprime p.r.natAbs p.s.natAbs := by
  rw [Nat.coprime_iff_gcd_eq_one]
  exact common_factor_eq_one p (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)

theorem EisensteinDescentFactorSource.coprime_abs_r_sum
    {a b c : ℕ} (p : EisensteinDescentFactorSource a b c) :
    Nat.Coprime p.r.natAbs (p.r + p.s).natAbs := by
  let d := Nat.gcd p.r.natAbs (p.r + p.s).natAbs
  have hr : d ∣ p.r.natAbs := Nat.gcd_dvd_left _ _
  have hsum : d ∣ (p.r + p.s).natAbs := Nat.gcd_dvd_right _ _
  have hdr : (d : ℤ) ∣ p.r := int_dvd_of_natAbs_dvd hr
  have hdsum : (d : ℤ) ∣ p.r + p.s := int_dvd_of_natAbs_dvd hsum
  have hds : (d : ℤ) ∣ p.s := by
    have h := dvd_sub hdsum hdr
    simpa only [add_sub_cancel_left] using h
  have hsnat : d ∣ p.s.natAbs := natAbs_dvd_of_int_dvd hds
  rw [Nat.coprime_iff_gcd_eq_one]
  exact common_factor_eq_one p hr hsnat

theorem EisensteinDescentFactorSource.coprime_abs_s_sum
    {a b c : ℕ} (p : EisensteinDescentFactorSource a b c) :
    Nat.Coprime p.s.natAbs (p.r + p.s).natAbs := by
  let d := Nat.gcd p.s.natAbs (p.r + p.s).natAbs
  have hs : d ∣ p.s.natAbs := Nat.gcd_dvd_left _ _
  have hsum : d ∣ (p.r + p.s).natAbs := Nat.gcd_dvd_right _ _
  have hds : (d : ℤ) ∣ p.s := int_dvd_of_natAbs_dvd hs
  have hdsum : (d : ℤ) ∣ p.r + p.s := int_dvd_of_natAbs_dvd hsum
  have hdr : (d : ℤ) ∣ p.r := by
    have h := dvd_sub hdsum hds
    simpa only [add_sub_cancel_right] using h
  have hrnat : d ∣ p.r.natAbs := natAbs_dvd_of_int_dvd hdr
  rw [Nat.coprime_iff_gcd_eq_one]
  exact common_factor_eq_one p hrnat hs

private theorem nat_cube_of_coprime_mul_eq_cube
    {x y z : ℕ} (hcop : Nat.Coprime x y) (h : x * y = z ^ 3) :
    ∃ t : ℕ, x = t ^ 3 := by
  have hunit : IsUnit (GCDMonoid.gcd x y) := by
    change IsUnit (Nat.gcd x y)
    rw [isUnit_iff_dvd_one]
    simpa [Nat.Coprime] using hcop
  exact exists_eq_pow_of_mul_eq_pow hunit h

private theorem exists_abs_cube_roots
    {a b c : ℕ} (p : EisensteinDescentFactorSource a b c) :
    ∃ R S T : ℕ,
      p.r.natAbs = R ^ 3 ∧
      p.s.natAbs = S ^ 3 ∧
      (p.r + p.s).natAbs = T ^ 3 := by
  have hrs := p.coprime_abs_r_s
  have hrt := p.coprime_abs_r_sum
  have hst := p.coprime_abs_s_sum
  have hRcop : p.r.natAbs.Coprime
      (p.s.natAbs * (p.r + p.s).natAbs) :=
    Nat.Coprime.mul_right hrs hrt
  have hScop : p.s.natAbs.Coprime
      (p.r.natAbs * (p.r + p.s).natAbs) :=
    Nat.Coprime.mul_right hrs.symm hst
  have hTcop : (p.r + p.s).natAbs.Coprime
      (p.r.natAbs * p.s.natAbs) :=
    Nat.Coprime.mul_right hrt.symm hst.symm
  have hRprod : p.r.natAbs *
      (p.s.natAbs * (p.r + p.s).natAbs) = p.A ^ 3 := by
    simpa [Nat.mul_assoc] using p.abs_factor_product_eq_A_cube
  have hSprod : p.s.natAbs *
      (p.r.natAbs * (p.r + p.s).natAbs) = p.A ^ 3 := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      p.abs_factor_product_eq_A_cube
  have hTprod : (p.r + p.s).natAbs *
      (p.r.natAbs * p.s.natAbs) = p.A ^ 3 := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      p.abs_factor_product_eq_A_cube
  rcases nat_cube_of_coprime_mul_eq_cube hRcop hRprod with ⟨R, hR⟩
  rcases nat_cube_of_coprime_mul_eq_cube hScop hSprod with ⟨S, hS⟩
  rcases nat_cube_of_coprime_mul_eq_cube hTcop hTprod with ⟨T, hT⟩
  exact ⟨R, S, T, hR, hS, hT⟩

private theorem roots_pairwise_coprime
    {a b c R S T : ℕ} (p : EisensteinDescentFactorSource a b c)
    (hR : p.r.natAbs = R ^ 3)
    (hS : p.s.natAbs = S ^ 3)
    (hT : (p.r + p.s).natAbs = T ^ 3) :
    Nat.Coprime R S ∧ Nat.Coprime R T ∧ Nat.Coprime S T := by
  have hRS : Nat.Coprime (R ^ 3) (S ^ 3) := by
    simpa [hR, hS] using p.coprime_abs_r_s
  have hRT : Nat.Coprime (R ^ 3) (T ^ 3) := by
    simpa [hR, hT] using p.coprime_abs_r_sum
  have hST : Nat.Coprime (S ^ 3) (T ^ 3) := by
    simpa [hS, hT] using p.coprime_abs_s_sum
  have hRS' : Nat.Coprime R S := by
    exact (Nat.coprime_pow_right_iff (by decide) R S).mp
      ((Nat.coprime_pow_left_iff (by decide) R (S ^ 3)).mp hRS)
  have hRT' : Nat.Coprime R T := by
    exact (Nat.coprime_pow_right_iff (by decide) R T).mp
      ((Nat.coprime_pow_left_iff (by decide) R (T ^ 3)).mp hRT)
  have hST' : Nat.Coprime S T := by
    exact (Nat.coprime_pow_right_iff (by decide) S T).mp
      ((Nat.coprime_pow_left_iff (by decide) S (T ^ 3)).mp hST)
  exact ⟨hRS', hRT', hST'⟩

/-- Signed factors packaged as pairwise-coprime natural cubes. -/
structure EisensteinSignedCubeFactors
    (a b c : ℕ) : Type where
  source : EisensteinDescentFactorSource a b c
  R : ℕ
  S : ℕ
  T : ℕ
  R_pos : 0 < R
  S_pos : 0 < S
  T_pos : 0 < T
  abs_r_eq : source.r.natAbs = R ^ 3
  abs_s_eq : source.s.natAbs = S ^ 3
  abs_sum_eq : (source.r + source.s).natAbs = T ^ 3
  coprime_RS : Nat.Coprime R S
  coprime_RT : Nat.Coprime R T
  coprime_ST : Nat.Coprime S T
  root_product_eq : R * S * T = source.A

noncomputable def eisensteinSignedCubeFactors_of_source
    {a b c : ℕ} (p : EisensteinDescentFactorSource a b c) :
    EisensteinSignedCubeFactors a b c := by
  classical
  let hRoots := exists_abs_cube_roots p
  let R := Classical.choose hRoots
  have hRData := Classical.choose_spec hRoots
  let S := Classical.choose hRData
  have hSData := Classical.choose_spec hRData
  let T := Classical.choose hSData
  have hData := Classical.choose_spec hSData
  have hR : p.r.natAbs = R ^ 3 := by
    simpa [R] using hData.1
  have hS : p.s.natAbs = S ^ 3 := by
    simpa [S] using hData.2.1
  have hT : (p.r + p.s).natAbs = T ^ 3 := by
    simpa [T] using hData.2.2
  have hRpos : 0 < R := by
    have hn : p.r.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr p.r_ne_zero
    have hRne : R ≠ 0 := by
      intro h
      apply hn
      rw [hR, h]
      simp
    exact Nat.pos_of_ne_zero hRne
  have hSpos : 0 < S := by
    have hn : p.s.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr p.s_ne_zero
    have hSne : S ≠ 0 := by
      intro h
      apply hn
      rw [hS, h]
      simp
    exact Nat.pos_of_ne_zero hSne
  have hTpos : 0 < T := by
    have hn : (p.r + p.s).natAbs ≠ 0 :=
      Int.natAbs_ne_zero.mpr p.sum_ne_zero
    have hTne : T ≠ 0 := by
      intro h
      apply hn
      rw [hT, h]
      simp
    exact Nat.pos_of_ne_zero hTne
  have hcop := roots_pairwise_coprime p hR hS hT
  have hcube : (R * S * T) ^ 3 = p.A ^ 3 := by
    calc
      (R * S * T) ^ 3 = R ^ 3 * S ^ 3 * T ^ 3 := by ring
      _ = p.r.natAbs * p.s.natAbs * (p.r + p.s).natAbs := by
        rw [hR, hS, hT]
      _ = p.A ^ 3 := p.abs_factor_product_eq_A_cube
  have hroot : R * S * T = p.A :=
    Nat.pow_left_injective (by decide) hcube
  exact {
    source := p
    R := R
    S := S
    T := T
    R_pos := hRpos
    S_pos := hSpos
    T_pos := hTpos
    abs_r_eq := hR
    abs_s_eq := hS
    abs_sum_eq := hT
    coprime_RS := hcop.1
    coprime_RT := hcop.2.1
    coprime_ST := hcop.2.2
    root_product_eq := hroot }

noncomputable def eisensteinSignedCubeFactors_of_primitive_solution
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hEq : a ^ 3 + b ^ 3 = c ^ 3) :
    EisensteinSignedCubeFactors a b c :=
  eisensteinSignedCubeFactors_of_source
    (eisensteinDescentFactorSource_of_primitive_solution ha hb hc hab hEq)

theorem EisensteinDescentFactorSource.source_A_lt_original_product
    {a b c : ℕ} (p : EisensteinDescentFactorSource a b c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    p.A < a * b * c := by
  have hABpos : 0 < p.A * p.B := Nat.mul_pos p.A_pos p.B_pos
  have hstep : p.A * p.B < 3 * (p.A * p.B) := by
    have h13 : (1 : ℕ) < 3 := by norm_num
    simpa using Nat.mul_lt_mul_of_pos_right h13 hABpos
  have hA_lt : p.A < 3 * p.A * p.B := by
    have hA_le : p.A ≤ p.A * p.B := Nat.le_mul_of_pos_right p.A p.B_pos
    exact hA_le.trans_lt (by simpa [Nat.mul_assoc] using hstep)
  calc
    p.A < 3 * p.A * p.B := hA_lt
    _ = p.origin.packet.distinguished := p.distinguished_eq.symm
    _ ≤ a * b * c :=
      p.origin.distinguished_le_product ha hb hc

theorem EisensteinSignedCubeFactors.strict_product_lt
    {a b c : ℕ} (p : EisensteinSignedCubeFactors a b c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    p.R * p.S * p.T < a * b * c := by
  rw [p.root_product_eq]
  exact p.source.source_A_lt_original_product ha hb hc

end DkMath.FLT.Three
