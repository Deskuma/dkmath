/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessCubicRealizedModuli
import Mathlib.Data.Nat.Squarefree

#print "file: DkMath.ABC.GNExcessCubicComplement"

/-!
# Canonical repeated/complement coordinates for the cubic GN family

This module freezes the arithmetic coordinate
`a^2 + 3*a + 3 = M*S`, where `M` is the full repeated prime-power part and
`S` is the residual complement.  The complement contains no prime to depth
two or more; in particular it is not the parity squarefree kernel.

No incidence estimate or ABC closure is asserted here.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom DkMath.NumberTheory

/-! ## The exceptional prime three -/

/-- The canonical quadratic is never divisible by `9`. -/
theorem not_nine_dvd_GN_three_one (a : ℕ) :
    ¬ 9 ∣ a ^ 2 + 3 * a + 3 := by
  have h := Nat.mod_lt a (by decide : 0 < 9)
  intro hd
  have hz := Nat.mod_eq_zero_of_dvd hd
  interval_cases he : a % 9 <;>
    norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, he] at hz

/-- The same prime-three depth exclusion stated directly for `GN 3 a 1`. -/
theorem not_nine_dvd_GN_three_one_value (a : ℕ) :
    ¬ 3 ^ 2 ∣ GN 3 a 1 := by
  rw [GN_three_dual_explicit]
  simpa only [mul_one, one_pow, show (3 : ℕ) ^ 2 = 9 from rfl] using
    not_nine_dvd_GN_three_one a

/-! ## Full repeated part and generic complement -/

/-- For the cubic family, removing the exceptional prime does not remove a
prime-power factor of depth at least two. -/
theorem GNNonExceptionalRepeatedPart_three_one_eq_repeatedPrimePowerPart
    (a : ℕ) :
    GNNonExceptionalRepeatedPart 3 a 1 =
      repeatedPrimePowerPart (GN 3 a 1) := by
  have hn : GN 3 a 1 ≠ 0 := by
    rw [GN_three_dual_explicit]
    positivity
  apply Nat.eq_of_factorization_eq
    (repeatedPrimePowerPart_pos _).ne'
    (repeatedPrimePowerPart_pos _).ne'
  intro q
  have hdepth : 2 ≤ (GN 3 a 1).factorization q →
      q ∈ GNNonExceptionalSupport 3 a 1 := by
    intro hv
    have hs : q ∈ (GN 3 a 1).factorization.support :=
      Finsupp.mem_support_iff.mpr (by omega)
    have hp := (mem_support_factorization_iff.mp hs).2.1
    refine Finset.mem_filter.mpr ⟨hs, ?_⟩
    intro hq3
    have heq : q = 3 :=
      ((Nat.dvd_prime Nat.prime_three).mp hq3).resolve_left hp.ne_one
    subst q
    have hd := (Nat.prime_three.pow_dvd_iff_le_factorization hn).mpr hv
    exact (not_nine_dvd_GN_three_one_value a) hd
  rw [repeatedPrimePowerPart_factorization,
    repeatedPrimePowerPart_factorization]
  by_cases hs : q ∈ GNNonExceptionalSupport 3 a 1
  · rw [GNNonExceptionalPart_factorization_support,
      GNNonExceptionalPart_factorization, if_pos hs]
    have hq := (Finset.mem_filter.mp hs).1
    simp only [hs, hq, true_and]
  · have hv : ¬ 2 ≤ (GN 3 a 1).factorization q := fun h => hs (hdepth h)
    rw [GNNonExceptionalPart_factorization_support,
      GNNonExceptionalPart_factorization, if_neg hs]
    simp only [hs, hv, false_and, and_false, if_false]

/-- The full repeated prime-power part, including odd exponents, is the
factor removed by this complement.  It is not the parity squarefree kernel. -/
noncomputable def repeatedPrimePowerComplement (n : ℕ) : ℕ :=
  n / repeatedPrimePowerPart n

/-- Repeated part times complement recovers the original nonzero number. -/
theorem repeatedPrimePowerPart_mul_complement {n : ℕ} (hn : n ≠ 0) :
    repeatedPrimePowerPart n * repeatedPrimePowerComplement n = n := by
  unfold repeatedPrimePowerComplement
  exact Nat.mul_div_cancel' (repeatedPrimePowerPart_dvd hn)

/-- The generic repeated-prime-power complement is squarefree. -/
theorem squarefree_repeatedPrimePowerComplement {n : ℕ} (hn : n ≠ 0) :
    Squarefree (repeatedPrimePowerComplement n) := by
  have hd := repeatedPrimePowerPart_dvd hn
  have hS : repeatedPrimePowerComplement n ≠ 0 := by
    intro hz
    have hrec := repeatedPrimePowerPart_mul_complement hn
    rw [hz, mul_zero] at hrec
    exact hn hrec.symm
  have hfac (q : ℕ) :
      (repeatedPrimePowerComplement n).factorization q =
        n.factorization q - (repeatedPrimePowerPart n).factorization q := by
    unfold repeatedPrimePowerComplement
    rw [Nat.factorization_div hd, Finsupp.tsub_apply]
  rw [Nat.squarefree_iff_factorization_le_one hS]
  intro q
  rw [hfac, repeatedPrimePowerPart_factorization]
  by_cases hv : 2 ≤ n.factorization q
  · have hq : q ∈ n.factorization.support :=
      Finsupp.mem_support_iff.mpr (by omega)
    rw [if_pos ⟨hq, hv⟩]
    omega
  · split_ifs <;> omega

/-- The repeated part and its complement are coprime. -/
theorem coprime_repeatedPrimePowerPart_complement {n : ℕ} (hn : n ≠ 0) :
    Nat.Coprime (repeatedPrimePowerPart n)
      (repeatedPrimePowerComplement n) := by
  have hd := repeatedPrimePowerPart_dvd hn
  have hS : repeatedPrimePowerComplement n ≠ 0 := by
    intro hz
    have hrec := repeatedPrimePowerPart_mul_complement hn
    rw [hz, mul_zero] at hrec
    exact hn hrec.symm
  have hfac (q : ℕ) :
      (repeatedPrimePowerComplement n).factorization q =
        n.factorization q - (repeatedPrimePowerPart n).factorization q := by
    unfold repeatedPrimePowerComplement
    rw [Nat.factorization_div hd, Finsupp.tsub_apply]
  by_contra hc
  obtain ⟨q, hq, hqM, hqS⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  have hsupport := mem_support_factorization_iff.mpr
    ⟨(repeatedPrimePowerPart_pos n).ne', hq, hqM⟩
  rw [repeatedPrimePowerPart_factorization_support] at hsupport
  have hcond := Finset.mem_filter.mp hsupport
  have hvS := (hq.pow_dvd_iff_le_factorization hS).mp
    (by simpa using hqS : q ^ 1 ∣ repeatedPrimePowerComplement n)
  rw [hfac, repeatedPrimePowerPart_factorization,
    if_pos hcond, Nat.sub_self] at hvS
  omega

/-! ## Canonical cubic complement -/

/-- The residual complement of the canonical cubic value. -/
noncomputable def GNExcessCubicComplement (a : ℕ) : ℕ :=
  GN 3 a 1 / GNNonExceptionalRepeatedPart 3 a 1

private theorem GN_three_one_ne_zero (a : ℕ) : GN 3 a 1 ≠ 0 := by
  rw [GN_three_dual_explicit]
  positivity

/-- The canonical repeated part times complement is the complete GN value. -/
theorem GNNonExceptionalRepeatedPart_mul_GNExcessCubicComplement (a : ℕ) :
    GNNonExceptionalRepeatedPart 3 a 1 * GNExcessCubicComplement a =
      GN 3 a 1 := by
  unfold GNExcessCubicComplement
  exact Nat.mul_div_cancel' (GNNonExceptionalRepeatedPart_dvd_GN
    (GN_three_one_ne_zero a))

/-- The canonical decomposition has the explicit quadratic value. -/
theorem GNNonExceptionalRepeatedPart_mul_GNExcessCubicComplement_eq_quadratic
    (a : ℕ) :
    GNNonExceptionalRepeatedPart 3 a 1 * GNExcessCubicComplement a =
      a ^ 2 + 3 * a + 3 := by
  rw [GNNonExceptionalRepeatedPart_mul_GNExcessCubicComplement,
    GN_three_dual_explicit]
  simp only [mul_one, one_pow]

/-- The canonical cubic complement is squarefree. -/
theorem squarefree_GNExcessCubicComplement (a : ℕ) :
    Squarefree (GNExcessCubicComplement a) := by
  rw [GNExcessCubicComplement,
    GNNonExceptionalRepeatedPart_three_one_eq_repeatedPrimePowerPart]
  exact squarefree_repeatedPrimePowerComplement (GN_three_one_ne_zero a)

/-- The canonical repeated part and complement are coprime. -/
theorem coprime_GNNonExceptionalRepeatedPart_GNExcessCubicComplement
    (a : ℕ) :
    Nat.Coprime (GNNonExceptionalRepeatedPart 3 a 1)
      (GNExcessCubicComplement a) := by
  rw [GNExcessCubicComplement,
    GNNonExceptionalRepeatedPart_three_one_eq_repeatedPrimePowerPart]
  exact coprime_repeatedPrimePowerPart_complement (GN_three_one_ne_zero a)

/-! ## Realized-large certificate -/

/-- The sharp residual bound used by the large-modulus consumer API. -/
theorem GNExcessCubicComplement_le_of_large
    {a X M : ℕ} (hX : 0 < X) (ha : a ≤ X)
    (heq : M * GNExcessCubicComplement a = a ^ 2 + 3 * a + 3)
    (hlarge : X + 1 < M) :
    GNExcessCubicComplement a ≤ X := by
  have hsmall : GNExcessCubicComplement a ≤ X + 1 := by
    by_contra hs
    have hM : X + 2 ≤ M := by omega
    have hS : X + 2 ≤ GNExcessCubicComplement a := by omega
    have hprod := Nat.mul_le_mul hM hS
    have hquad : a ^ 2 + 3 * a + 3 ≤ X ^ 2 + 3 * X + 3 := by nlinarith
    nlinarith
  by_contra hs
  have hS : GNExcessCubicComplement a = X + 1 := by omega
  rw [hS] at heq
  have hM : X + 2 ≤ M := by omega
  have hprod := Nat.mul_le_mul_right (X + 1) hM
  have haa : a = X := by
    by_contra hh
    have hlt : a + 1 ≤ X := by omega
    nlinarith [sq_nonneg (X - a)]
  subst a
  have hmm : M = X + 2 ∨ X + 3 ≤ M := by omega
  rcases hmm with hh | hh
  · subst M
    nlinarith
  · have hprod2 := Nat.mul_le_mul_right (X + 1) hh
    nlinarith

/-- Every realized canonical large modulus has a complete complement packet. -/
theorem GNExcessCubicRealizedLargeModulusSpace_exists_complement_packet
    {X M : ℕ} (hX : 0 < X)
    (hM : M ∈ GNExcessCubicRealizedLargeModulusSpace X) :
    ∃ a S : ℕ,
      0 < a ∧ a ≤ X ∧
      M = GNNonExceptionalRepeatedPart 3 a 1 ∧
      S = GNExcessCubicComplement a ∧
      M * S = a ^ 2 + 3 * a + 3 ∧
      Squarefree S ∧ Nat.Coprime M S ∧ S ≤ X := by
  obtain ⟨a, ha, haI, hEq⟩ :=
    GNExcessCubicRealizedLargeModulusSpace_exists_witness hM
  have haX : a ≤ X := (Finset.mem_Icc.mp haI).2
  have hlarge := GNExcessCubicRealizedLargeModulusSpace_interval_lt hM
  refine ⟨a, GNExcessCubicComplement a, ha, haX, hEq, rfl, ?_, ?_, ?_, ?_⟩
  · rw [hEq]
    exact GNNonExceptionalRepeatedPart_mul_GNExcessCubicComplement_eq_quadratic a
  · exact squarefree_GNExcessCubicComplement a
  · rw [hEq]
    exact coprime_GNNonExceptionalRepeatedPart_GNExcessCubicComplement a
  · apply GNExcessCubicComplement_le_of_large
      (a := a) (X := X) (M := M) hX haX
    · rw [hEq]
      exact GNNonExceptionalRepeatedPart_mul_GNExcessCubicComplement_eq_quadratic a
    · exact hlarge

/-! ## Elementary quadratic spacing -/

/-- A common divisor of two canonical quadratic values divides their root
difference product over the integers. -/
theorem cubicQuadratic_commonDivisor_dvd_rootDifference
    {a b M : ℕ}
    (ha : M ∣ a ^ 2 + 3 * a + 3)
    (hb : M ∣ b ^ 2 + 3 * b + 3) :
    (M : ℤ) ∣ ((b : ℤ) - a) * ((a : ℤ) + b + 3) := by
  have ha' : (M : ℤ) ∣ (a : ℤ) ^ 2 + 3 * a + 3 := by exact_mod_cast ha
  have hb' : (M : ℤ) ∣ (b : ℤ) ^ 2 + 3 * b + 3 := by exact_mod_cast hb
  have hid : ((b : ℤ) ^ 2 + 3 * b + 3) -
      ((a : ℤ) ^ 2 + 3 * a + 3) =
      ((b : ℤ) - a) * ((a : ℤ) + b + 3) := by ring
  rw [← hid]
  exact dvd_sub hb' ha'

/-- Distinct natural roots of a common quadratic divisor obey the exact
spacing inequality. -/
theorem cubicQuadratic_commonDivisor_le_spacingProduct
    {a b M : ℕ} (hab : a < b)
    (ha : M ∣ a ^ 2 + 3 * a + 3)
    (hb : M ∣ b ^ 2 + 3 * b + 3) :
    M ≤ (b - a) * (a + b + 3) := by
  have he : b ^ 2 + 3 * b + 3 =
      a ^ 2 + 3 * a + 3 + (b - a) * (a + b + 3) := by
    have := Nat.sub_add_cancel (Nat.le_of_lt hab)
    nlinarith
  have hd := Nat.dvd_sub hb ha
  rw [he, Nat.add_sub_cancel_left] at hd
  exact Nat.le_of_dvd
    (Nat.mul_pos (Nat.sub_pos_of_lt hab) (by omega)) hd

end DkMath.ABC
