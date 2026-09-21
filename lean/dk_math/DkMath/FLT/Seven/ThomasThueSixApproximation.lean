/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.ThomasThueSixAudit
import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions

/-!
# Fixed `n = 6` Thomas approximation bridge

This module contains the exact root packet and approximation-to-convergent
bridge used by the R56 audit.  It does not import a published Thomas or
Mignotte classification theorem as an axiom.
-/

namespace DkMath.FLT.Seven

namespace SevenRealCubic

noncomputable section

structure ThomasSixRootPacket where
  lambda1 : ℝ
  lambda2 : ℝ
  lambda3 : ℝ
  lambda1_mem : lambda1 ∈ Set.Icc (-(6 / 5 : ℝ)) (-(11 / 10 : ℝ))
  lambda2_mem : lambda2 ∈ Set.Icc (-(1 / 5 : ℝ)) (-(1 / 10 : ℝ))
  lambda3_mem : lambda3 ∈ Set.Icc (6 : ℝ) (13 / 2 : ℝ)
  lambda1_root : f5Real lambda1 = 0
  lambda2_root : f5Real lambda2 = 0
  lambda3_root : f5Real lambda3 = 0
  lambda1_lambda2_sep : (9 / 10 : ℝ) ≤ lambda2 - lambda1
  lambda2_lambda3_sep : (61 / 10 : ℝ) ≤ lambda3 - lambda2
  lambda1_lambda3_sep : (71 / 10 : ℝ) ≤ lambda3 - lambda1
  lambda1_lt_lambda2 : lambda1 < lambda2
  lambda2_lt_lambda3 : lambda2 < lambda3

noncomputable def thomasSixRoots : ThomasSixRootPacket := by
  have hex : ∃ packet : ThomasSixRootPacket, True := by
    rcases f5Real_root_separation with ⟨lambda1, lambda2, lambda3, h1, h2, h3,
      hz1, hz2, hz3, h12, h23, h13⟩
    let packet : ThomasSixRootPacket :=
      { lambda1 := lambda1
        lambda2 := lambda2
        lambda3 := lambda3
        lambda1_mem := h1
        lambda2_mem := h2
        lambda3_mem := h3
        lambda1_root := hz1
        lambda2_root := hz2
        lambda3_root := hz3
        lambda1_lambda2_sep := h12
        lambda2_lambda3_sep := h23
        lambda1_lambda3_sep := h13
        lambda1_lt_lambda2 := by linarith [h1.2, h2.1]
        lambda2_lt_lambda3 := by linarith [h2.2, h3.1] }
    exact ⟨packet, trivial⟩
  exact Classical.choose hex

theorem thomasSixRoots_spec :
    thomasSixRoots.lambda1 ∈ Set.Icc (-(6 / 5 : ℝ)) (-(11 / 10 : ℝ)) ∧
      thomasSixRoots.lambda2 ∈ Set.Icc (-(1 / 5 : ℝ)) (-(1 / 10 : ℝ)) ∧
      thomasSixRoots.lambda3 ∈ Set.Icc (6 : ℝ) (13 / 2 : ℝ) ∧
      f5Real thomasSixRoots.lambda1 = 0 ∧
      f5Real thomasSixRoots.lambda2 = 0 ∧
      f5Real thomasSixRoots.lambda3 = 0 ∧
      thomasSixRoots.lambda1 < thomasSixRoots.lambda2 ∧
      thomasSixRoots.lambda2 < thomasSixRoots.lambda3 := by
  exact ⟨thomasSixRoots.lambda1_mem, thomasSixRoots.lambda2_mem,
    thomasSixRoots.lambda3_mem, thomasSixRoots.lambda1_root,
    thomasSixRoots.lambda2_root, thomasSixRoots.lambda3_root,
    thomasSixRoots.lambda1_lt_lambda2, thomasSixRoots.lambda2_lt_lambda3⟩

private theorem thomasSix_cubic_factorization (packet : ThomasSixRootPacket) (x : ℝ) :
    f5Real x =
      (x - packet.lambda1) * (x - packet.lambda2) * (x - packet.lambda3) := by
  have h12 : packet.lambda1 ^ 2 + packet.lambda1 * packet.lambda2 +
      packet.lambda2 ^ 2 - 5 * packet.lambda1 - 5 * packet.lambda2 - 8 = 0 := by
    have h := packet.lambda1_root
    have h' := packet.lambda2_root
    dsimp [f5Real] at h h'
    have hfactor : (packet.lambda1 - packet.lambda2) *
        (packet.lambda1 ^ 2 + packet.lambda1 * packet.lambda2 + packet.lambda2 ^ 2 -
          5 * packet.lambda1 - 5 * packet.lambda2 - 8) = 0 := by
      nlinarith [h, h']
    rcases mul_eq_zero.mp hfactor with hzero | hzero
    · linarith [packet.lambda1_lt_lambda2]
    · exact hzero
  have h13 : packet.lambda1 ^ 2 + packet.lambda1 * packet.lambda3 +
      packet.lambda3 ^ 2 - 5 * packet.lambda1 - 5 * packet.lambda3 - 8 = 0 := by
    have h := packet.lambda1_root
    have h' := packet.lambda3_root
    dsimp [f5Real] at h h'
    have hfactor : (packet.lambda1 - packet.lambda3) *
        (packet.lambda1 ^ 2 + packet.lambda1 * packet.lambda3 + packet.lambda3 ^ 2 -
          5 * packet.lambda1 - 5 * packet.lambda3 - 8) = 0 := by
      nlinarith [h, h']
    rcases mul_eq_zero.mp hfactor with hzero | hzero
    · linarith [packet.lambda1_lt_lambda2, packet.lambda2_lt_lambda3]
    · exact hzero
  have hsum : packet.lambda1 + packet.lambda2 + packet.lambda3 = 5 := by
    have hfactor : (packet.lambda2 - packet.lambda3) *
        (packet.lambda1 + packet.lambda2 + packet.lambda3 - 5) = 0 := by
      nlinarith [h12, h13]
    rcases mul_eq_zero.mp hfactor with hzero | hzero
    · linarith [packet.lambda2_lt_lambda3]
    · linarith
  have hpair : packet.lambda1 * packet.lambda2 + packet.lambda1 * packet.lambda3 +
      packet.lambda2 * packet.lambda3 = -8 := by
    have h3eq : packet.lambda3 = 5 - packet.lambda1 - packet.lambda2 := by
      linarith [hsum]
    rw [h3eq]
    nlinarith [h12]
  have hprod : packet.lambda1 * packet.lambda2 * packet.lambda3 = 1 := by
    have hroot := packet.lambda1_root
    dsimp [f5Real] at hroot
    have hfactor : packet.lambda1 ^ 3 -
        (packet.lambda1 + packet.lambda2 + packet.lambda3) * packet.lambda1 ^ 2 +
        (packet.lambda1 * packet.lambda2 + packet.lambda1 * packet.lambda3 +
          packet.lambda2 * packet.lambda3) * packet.lambda1 -
          packet.lambda1 * packet.lambda2 * packet.lambda3 = 0 := by
      ring
    rw [hsum, hpair] at hfactor
    nlinarith [hroot, hfactor]
  dsimp [f5Real]
  calc
    x ^ 3 - 5 * x ^ 2 - 8 * x - 1 =
        x ^ 3 - (packet.lambda1 + packet.lambda2 + packet.lambda3) * x ^ 2 +
          (packet.lambda1 * packet.lambda2 + packet.lambda1 * packet.lambda3 +
            packet.lambda2 * packet.lambda3) * x -
            packet.lambda1 * packet.lambda2 * packet.lambda3 := by
              rw [hsum, hpair, hprod]
              ring
    _ = (x - packet.lambda1) * (x - packet.lambda2) * (x - packet.lambda3) := by
      ring

theorem thomasSix_factorization (R S : ℤ) (packet : ThomasSixRootPacket)
    (hS : S ≠ 0) :
    (F5 R S : ℝ) / (S : ℝ) ^ 3 =
      ((R : ℝ) / S - packet.lambda1) *
        ((R : ℝ) / S - packet.lambda2) *
          ((R : ℝ) / S - packet.lambda3) := by
  have hSreal : (S : ℝ) ≠ 0 := by exact_mod_cast hS
  have hhom : (F5 R S : ℝ) = (S : ℝ) ^ 3 *
      f5Real ((R : ℝ) / S) := by
    simp [F5, f5Real]
    field_simp [f5Real, hSreal]
  rw [hhom, thomasSix_cubic_factorization]
  field_simp [hSreal]

theorem thomasSix_abs_product (R S : ℤ) (packet : ThomasSixRootPacket)
    (hS : S ≠ 0) (hfive : F5 R S = 1) :
    |(R : ℝ) / S - packet.lambda1| *
        |(R : ℝ) / S - packet.lambda2| *
          |(R : ℝ) / S - packet.lambda3| =
      1 / |(S : ℝ)| ^ 3 := by
  have hratio := thomasSix_factorization R S packet hS
  have hfiveR : (F5 R S : ℝ) = 1 := by exact_mod_cast hfive
  have hratio' : (1 : ℝ) / (S : ℝ) ^ 3 =
      ((R : ℝ) / S - packet.lambda1) *
        ((R : ℝ) / S - packet.lambda2) *
          ((R : ℝ) / S - packet.lambda3) := by
    rw [← hfiveR]
    exact hratio
  have habs := congrArg abs hratio'
  rw [abs_div, abs_pow, abs_one, abs_mul, abs_mul] at habs
  simpa [abs_pow] using habs.symm

private theorem abs_distance_lower {a b x c : ℝ} (hc : c ≤ |a - b|) :
    c - |x - a| ≤ |x - b| := by
  have htri : |a - b| ≤ |a - x| + |x - b| := by
    exact abs_sub_le _ _ _
  have hax : |a - x| = |x - a| := abs_sub_comm _ _
  rw [hax] at htri
  linarith

private theorem improve_nearest_distance
    {u d1 d2 d3 : ℝ}
    (hu : 0 < u) (hu6 : 6 ≤ u)
    (hprod : d1 * d2 * d3 = 1 / u ^ 3)
    (_hnear : d1 ≤ 1 / u)
    (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (_hd3 : 0 ≤ d3)
    (h2low : (11 / 15 : ℝ) ≤ d2)
    (h3low : (11 / 15 : ℝ) ≤ d3) :
    d1 < 1 / (2 * u ^ 2) := by
  have hu_inv : 1 / u ≤ (1 / 6 : ℝ) := by
    rw [div_le_iff₀ hu]
    nlinarith
  have hterm1 : 0 ≤ d2 * (d3 - 11 / 15) := by
    exact mul_nonneg hd2 (by linarith)
  have hterm2 : 0 ≤ (11 / 15 : ℝ) * (d2 - 11 / 15) := by
    exact mul_nonneg (by norm_num) (by linarith)
  have hlow : (11 / 15 : ℝ) ^ 2 ≤ d2 * d3 := by
    nlinarith [hterm1, hterm2]
  have hbound : d1 * (11 / 15 : ℝ) ^ 2 ≤ 1 / u ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_left hlow hd1
    calc
      d1 * (11 / 15 : ℝ) ^ 2 ≤ d1 * (d2 * d3) := hmul
      _ = 1 / u ^ 3 := by nlinarith [hprod]
  have hu3 : 0 < 1 / u ^ 3 := by positivity
  have hsmall : (225 / 121 : ℝ) * (1 / u ^ 3) < 2 * (1 / u ^ 3) := by
    exact mul_lt_mul_of_pos_right (by norm_num) hu3
  have hC : d1 ≤ (225 / 121 : ℝ) * (1 / u ^ 3) := by
    norm_num at hbound
    have hbound' : d1 * (121 / 225 : ℝ) ≤ 1 / u ^ 3 := by
      simpa [one_div] using hbound
    calc
      d1 = (d1 * (121 / 225 : ℝ)) * (225 / 121 : ℝ) := by ring
      _ ≤ (1 / u ^ 3) * (225 / 121 : ℝ) :=
        mul_le_mul_of_nonneg_right hbound' (by norm_num)
      _ = (225 / 121 : ℝ) * (1 / u ^ 3) := by ring
  have hfinal : (2 : ℝ) / u ^ 3 < 1 / (2 * u ^ 2) := by
    have hfour : 4 * u ^ 2 < u ^ 3 := by
      have hfour' := mul_lt_mul_of_pos_right (show (4 : ℝ) < u by linarith [hu6])
        (sq_pos_of_pos hu)
      calc
        4 * u ^ 2 < u * (u ^ 2) := hfour'
        _ = u ^ 3 := by ring
    rw [div_lt_div_iff₀ (by positivity : 0 < u ^ 3)
      (by positivity : 0 < 2 * u ^ 2)]
    nlinarith [hfour]
  have hsmall' : (225 / 121 : ℝ) * (1 / u ^ 3) < (2 : ℝ) / u ^ 3 := by
    calc
      (225 / 121 : ℝ) * (1 / u ^ 3) < 2 * (1 / u ^ 3) := hsmall
      _ = (2 : ℝ) / u ^ 3 := by ring
  exact lt_of_le_of_lt hC (lt_trans hsmall' hfinal)

theorem thomasSix_nearest_root_approximation
    (R S : ℤ) (packet : ThomasSixRootPacket)
    (hS : S ≠ 0) (hfive : F5 R S = 1)
    (hsize : (6 : ℝ) ≤ |(S : ℝ)|) :
    |(R : ℝ) / S - packet.lambda1| < 1 / (2 * (S : ℝ) ^ 2) ∨
      |(R : ℝ) / S - packet.lambda2| < 1 / (2 * (S : ℝ) ^ 2) ∨
        |(R : ℝ) / S - packet.lambda3| < 1 / (2 * (S : ℝ) ^ 2) := by
  let x : ℝ := (R : ℝ) / S
  let u : ℝ := |(S : ℝ)|
  have hu : 0 < u := by
    dsimp [u]
    exact abs_pos.mpr (by exact_mod_cast hS)
  have hu6 : 6 ≤ u := by exact hsize
  have hprod :
      |x - packet.lambda1| * |x - packet.lambda2| * |x - packet.lambda3| =
        1 / u ^ 3 := by
    simpa [x, u] using thomasSix_abs_product R S packet hS hfive
  have hnear : |x - packet.lambda1| ≤ 1 / u ∨
      |x - packet.lambda2| ≤ 1 / u ∨ |x - packet.lambda3| ≤ 1 / u := by
    by_contra h
    push Not at h
    have h12 : (1 / u) * (1 / u) <
        |x - packet.lambda1| * |x - packet.lambda2| := by
      calc
        (1 / u) * (1 / u) < |x - packet.lambda1| * (1 / u) :=
          mul_lt_mul_of_pos_right h.1 (by positivity)
        _ < |x - packet.lambda1| * |x - packet.lambda2| :=
          mul_lt_mul_of_pos_left h.2.1
            (lt_trans (one_div_pos.mpr hu) h.1)
    have h123 : (1 / u) * (1 / u) * (1 / u) <
        |x - packet.lambda1| * |x - packet.lambda2| * |x - packet.lambda3| := by
      calc
        (1 / u) * (1 / u) * (1 / u) <
            (|x - packet.lambda1| * |x - packet.lambda2|) * (1 / u) :=
          mul_lt_mul_of_pos_right h12 (by positivity)
        _ < (|x - packet.lambda1| * |x - packet.lambda2|) *
            |x - packet.lambda3| :=
          mul_lt_mul_of_pos_left h.2.2 (mul_pos
            (lt_trans (one_div_pos.mpr hu) h.1)
            (lt_trans (one_div_pos.mpr hu) h.2.1))
    have hpow : (1 / u) * (1 / u) * (1 / u) = 1 / u ^ 3 := by ring
    rw [hpow] at h123
    linarith [hprod, h123]
  have hu_inv : 1 / u ≤ (1 / 6 : ℝ) := by
    rw [div_le_iff₀ hu]
    nlinarith [hu6]
  have hsep12 : (9 / 10 : ℝ) ≤
      |packet.lambda1 - packet.lambda2| := by
    have hpos : 0 < packet.lambda2 - packet.lambda1 :=
      sub_pos.mpr packet.lambda1_lt_lambda2
    calc
      (9 / 10 : ℝ) ≤ packet.lambda2 - packet.lambda1 :=
        packet.lambda1_lambda2_sep
      _ = |packet.lambda1 - packet.lambda2| := by
        rw [abs_sub_comm, abs_of_pos hpos]
  have hsep23 : (61 / 10 : ℝ) ≤
      |packet.lambda2 - packet.lambda3| := by
    have hpos : 0 < packet.lambda3 - packet.lambda2 :=
      sub_pos.mpr packet.lambda2_lt_lambda3
    calc
      (61 / 10 : ℝ) ≤ packet.lambda3 - packet.lambda2 :=
        packet.lambda2_lambda3_sep
      _ = |packet.lambda2 - packet.lambda3| := by
        rw [abs_sub_comm, abs_of_pos hpos]
  have hsep13 : (71 / 10 : ℝ) ≤
      |packet.lambda1 - packet.lambda3| := by
    have hpos : 0 < packet.lambda3 - packet.lambda1 :=
      sub_pos.mpr (lt_trans packet.lambda1_lt_lambda2 packet.lambda2_lt_lambda3)
    calc
      (71 / 10 : ℝ) ≤ packet.lambda3 - packet.lambda1 :=
        packet.lambda1_lambda3_sep
      _ = |packet.lambda1 - packet.lambda3| := by
        rw [abs_sub_comm, abs_of_pos hpos]
  rcases hnear with h1 | h2 | h3
  · have hl2 : (11 / 15 : ℝ) ≤ |x - packet.lambda2| := by
      have h := abs_distance_lower (a := packet.lambda1) (b := packet.lambda2)
        (x := x) (c := 9 / 10) hsep12
      linarith [h, hu_inv]
    have hl3 : (11 / 15 : ℝ) ≤ |x - packet.lambda3| := by
      have h := abs_distance_lower (a := packet.lambda1) (b := packet.lambda3)
        (x := x) (c := 71 / 10) hsep13
      linarith [h, hu_inv]
    left
    simpa [x, u, sq_abs] using
      (improve_nearest_distance hu hu6 hprod h1 (abs_nonneg _) (abs_nonneg _)
        (abs_nonneg _) hl2 hl3)
  · have hl1 : (11 / 15 : ℝ) ≤ |x - packet.lambda1| := by
      have h := abs_distance_lower (a := packet.lambda2) (b := packet.lambda1)
        (x := x) (c := 9 / 10) (by simpa [abs_sub_comm] using hsep12)
      linarith [h, hu_inv]
    have hl3 : (11 / 15 : ℝ) ≤ |x - packet.lambda3| := by
      have h := abs_distance_lower (a := packet.lambda2) (b := packet.lambda3)
        (x := x) (c := 61 / 10) hsep23
      linarith [h, hu_inv]
    right
    left
    have hprod' : |x - packet.lambda2| * |x - packet.lambda1| *
        |x - packet.lambda3| = 1 / u ^ 3 := by
      calc
        _ = |x - packet.lambda1| * |x - packet.lambda2| *
            |x - packet.lambda3| := by ring
        _ = 1 / u ^ 3 := hprod
    simpa [x, u, sq_abs] using
      (improve_nearest_distance hu hu6 hprod' h2 (abs_nonneg _)
        (abs_nonneg _) (abs_nonneg _) hl1 hl3)
  · have hl1 : (11 / 15 : ℝ) ≤ |x - packet.lambda1| := by
      have h := abs_distance_lower (a := packet.lambda3) (b := packet.lambda1)
        (x := x) (c := 71 / 10) (by simpa [abs_sub_comm] using hsep13)
      linarith [h, hu_inv]
    have hl2 : (11 / 15 : ℝ) ≤ |x - packet.lambda2| := by
      have h := abs_distance_lower (a := packet.lambda3) (b := packet.lambda2)
        (x := x) (c := 61 / 10) (by simpa [abs_sub_comm] using hsep23)
      linarith [h, hu_inv]
    right
    right
    have hprod' : |x - packet.lambda3| * |x - packet.lambda1| *
        |x - packet.lambda2| = 1 / u ^ 3 := by
      calc
        _ = |x - packet.lambda1| * |x - packet.lambda2| *
            |x - packet.lambda3| := by ring
        _ = 1 / u ^ 3 := hprod
    simpa [x, u, sq_abs] using
      (improve_nearest_distance hu hu6 hprod' h3 (abs_nonneg _)
        (abs_nonneg _) (abs_nonneg _) hl1 hl2)

theorem thomasSix_legendre_bridge
    (R S : ℤ) (packet : ThomasSixRootPacket)
    (hS : S ≠ 0) (hfive : F5 R S = 1)
    (hcop : IsCoprime R S)
    (hsize : (6 : ℝ) ≤ |(S : ℝ)|) :
    ∃ n, Rat.divInt R S = Real.convergent packet.lambda1 n ∨
      Rat.divInt R S = Real.convergent packet.lambda2 n ∨
        Rat.divInt R S = Real.convergent packet.lambda3 n := by
  let q : ℚ := Rat.divInt R S
  have hcop_nat : Nat.Coprime R.natAbs S.natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hcop
  have hden_real : (q.den : ℝ) = |(S : ℝ)| := by
    rcases lt_or_gt_of_ne hS with hSneg | hSpos
    · have hden : ((q.den : ℤ)) = -S := by
        have hcop' : Nat.Coprime (-R).natAbs (-S).natAbs := by
          simpa using hcop_nat
        have hden' := Rat.den_div_eq_of_coprime (neg_pos.mpr hSneg) hcop'
        simpa [q, Rat.divInt_eq_div] using hden'
      have hden' : (q.den : ℝ) = (-S : ℝ) := by exact_mod_cast hden
      rw [hden', abs_of_neg]
      exact_mod_cast hSneg
    · have hden : ((q.den : ℤ)) = S := by
        have hden' := Rat.den_div_eq_of_coprime hSpos hcop_nat
        simpa [q, Rat.divInt_eq_div] using hden'
      have hden' : (q.den : ℝ) = (S : ℝ) := by exact_mod_cast hden
      rw [hden', abs_of_pos]
      exact_mod_cast hSpos
  have hq_cast : (q : ℝ) = (R : ℝ) / S := by
    simp [q, Rat.cast_divInt]
  have happrox := thomasSix_nearest_root_approximation R S packet hS hfive hsize
  have legendre_of_root {lambda : ℝ}
      (hlambda : |(R : ℝ) / S - lambda| < 1 / (2 * (S : ℝ) ^ 2)) :
      ∃ n, q = Real.convergent lambda n := by
    have hgood : |lambda - (q : ℝ)| <
        1 / (2 * (q.den : ℝ) ^ 2) := by
      rw [hq_cast, hden_real]
      simpa [abs_sub_comm, sq_abs] using hlambda
    exact Real.exists_rat_eq_convergent hgood
  rcases happrox with h1 | h2 | h3
  · obtain ⟨n, hn⟩ := legendre_of_root h1
    exact ⟨n, Or.inl hn⟩
  · obtain ⟨n, hn⟩ := legendre_of_root h2
    exact ⟨n, Or.inr (Or.inl hn)⟩
  · obtain ⟨n, hn⟩ := legendre_of_root h3
    exact ⟨n, Or.inr (Or.inr hn)⟩

end

end SevenRealCubic

end DkMath.FLT.Seven
