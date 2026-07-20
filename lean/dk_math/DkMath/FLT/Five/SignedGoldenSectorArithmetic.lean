/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.SignedGoldenUnitClasses

/-!
# Arithmetic elimination of the nonzero unit sectors

The second-coordinate formula for `phi^i * gamma^5`, reduced modulo five,
shows that each sector `i = 1, 2, 3, 4` forces `5 ∣ goldenNorm gamma`. This
contradicts the packet invariant `5 ∤ b`, because that norm is `b` up to sign.
Only sector zero, where `beta = gamma^5`, survives for the separate descent.
-/

#print "file: DkMath.FLT.Five.SignedGoldenSectorArithmetic"

namespace DkMath.FLT.Five

/-- The quartic `H(r,s)` in `(r + s*phi)^5.snd = 5*s*H(r,s)`. -/
def goldenFifthSndFactor (r s : ℤ) : ℤ :=
  r ^ 4 + 2 * r ^ 3 * s + 4 * r ^ 2 * s ^ 2 +
    3 * r * s ^ 3 + s ^ 4

theorem goldenFifthSndPoly_eq (r s : ℤ) :
    goldenFifthSndPoly r s = 5 * s * goldenFifthSndFactor r s := by
  simp [goldenFifthSndPoly, goldenFifthSndFactor]

/-- A factorization witness fixes the norm of its fifth-power base up to sign. -/
theorem SignedGoldenRamifierStrippedPacket.gamma_norm_eq_or_eq_neg
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {epsilon gamma : GoldenInt} (hepsilon : GoldenUnit epsilon)
    (hbeta : p.beta = goldenMul epsilon (goldenPow gamma 5)) :
    goldenNorm gamma = (p.exceptional.powerSplit.b : ℤ) ∨
      goldenNorm gamma = -(p.exceptional.powerSplit.b : ℤ) := by
  have hnorm := congrArg goldenNorm hbeta
  rw [p.beta_norm, goldenNorm_mul, golden_pow_eq, goldenNorm_pow] at hnorm
  rcases goldenNorm_eq_one_or_neg_one_of_unit hepsilon with he | he
  · rw [he, one_mul] at hnorm
    exact Or.inl ((show Odd 5 by decide).pow_injective hnorm.symm)
  · rw [he, neg_one_mul] at hnorm
    right
    apply (show Odd 5 by decide).pow_injective
    calc
      goldenNorm gamma ^ 5 = -(p.exceptional.powerSplit.b : ℤ) ^ 5 := by
        linarith
      _ = (-(p.exceptional.powerSplit.b : ℤ)) ^ 5 := by ring

/-- Consequently the fifth-power base norm remains prime to five. -/
theorem SignedGoldenRamifierStrippedPacket.five_not_dvd_gamma_norm
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {epsilon gamma : GoldenInt} (hepsilon : GoldenUnit epsilon)
    (hbeta : p.beta = goldenMul epsilon (goldenPow gamma 5)) :
    ¬ (5 : ℤ) ∣ goldenNorm gamma := by
  intro hfive
  rcases p.gamma_norm_eq_or_eq_neg hepsilon hbeta with h | h
  · apply p.five_not_dvd_b
    rw [h] at hfive
    exact_mod_cast hfive
  · apply p.five_not_dvd_b
    rw [h] at hfive
    exact_mod_cast (Int.dvd_neg.mp hfive)

/-- The second-coordinate polynomial always contains its visible factor five. -/
theorem five_dvd_goldenFifthSndPoly (r s : ℤ) :
    (5 : ℤ) ∣ goldenFifthSndPoly r s := by
  rw [goldenFifthSndPoly_eq]
  refine ⟨s * goldenFifthSndFactor r s, ?_⟩
  ring

/-- Modulo five, the first coordinate of a fifth power is `r + 3*s`. -/
theorem five_dvd_goldenFifthFstPoly_sub_linear (r s : ℤ) :
    (5 : ℤ) ∣ goldenFifthFstPoly r s - (r + 3 * s) := by
  have hr := (Int.ModEq.pow_prime_eq_self (by norm_num : Nat.Prime 5) r).dvd
  have hs := (Int.ModEq.pow_prime_eq_self (by norm_num : Nat.Prime 5) s).dvd
  rcases hr with ⟨kr, hkr⟩
  rcases hs with ⟨ks, hks⟩
  refine ⟨2 * r ^ 3 * s ^ 2 + 2 * r ^ 2 * s ^ 3 +
    2 * r * s ^ 4 - kr - 3 * ks, ?_⟩
  simp only [goldenFifthFstPoly]
  linear_combination -hkr - 3 * hks

/-- The golden norm is the square of the same linear form modulo five. -/
theorem five_dvd_goldenNorm_sub_linear_sq (gamma : GoldenInt) :
    (5 : ℤ) ∣ goldenNorm gamma - (gamma.fst + 3 * gamma.snd) ^ 2 := by
  refine ⟨-(gamma.fst * gamma.snd + 2 * gamma.snd ^ 2), ?_⟩
  simp only [goldenNorm]
  ring

/-- Divisibility of the first fifth-power coordinate forces divisibility of the norm. -/
theorem five_dvd_goldenNorm_of_five_dvd_fifthFst
    (gamma : GoldenInt)
    (hF : (5 : ℤ) ∣ goldenFifthFstPoly gamma.fst gamma.snd) :
    (5 : ℤ) ∣ goldenNorm gamma := by
  have hdiff := five_dvd_goldenFifthFstPoly_sub_linear gamma.fst gamma.snd
  have hlinear : (5 : ℤ) ∣ gamma.fst + 3 * gamma.snd := by
    convert dvd_sub hF hdiff using 1 <;> ring
  have hsq : (5 : ℤ) ∣ (gamma.fst + 3 * gamma.snd) ^ 2 :=
    dvd_pow hlinear (by decide)
  have hnormDiff := five_dvd_goldenNorm_sub_linear_sq gamma
  convert dvd_add hnormDiff hsq using 1 <;> ring

private theorem five_dvd_beta_snd
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w) :
    (5 : ℤ) ∣ p.beta.snd := by
  rw [p.beta_snd]
  refine ⟨-(5 ^ 6 * (p.exceptional.powerSplit.a : ℤ) ^ 10), ?_⟩
  ring

/-- Every nonzero representative unit sector contradicts the packet norm. -/
theorem signedGolden_nonzero_unitSector_false
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {i : Fin 5} (hi : i ≠ 0) (gamma : GoldenInt)
    (hbeta : p.beta =
      goldenMul (goldenPow goldenPhi i.val) (goldenPow gamma 5)) : False := by
  have hnotNorm : ¬ (5 : ℤ) ∣ goldenNorm gamma :=
    p.five_not_dvd_gamma_norm (goldenUnit_pow goldenUnit_phi i.val) hbeta
  apply hnotNorm
  apply five_dvd_goldenNorm_of_five_dvd_fifthFst
  have hb := five_dvd_beta_snd p
  have hS := five_dvd_goldenFifthSndPoly gamma.fst gamma.snd
  fin_cases i
  · exact (hi rfl).elim
  · rw [hbeta, golden_unit_one_mul_fifth_snd] at hb
    convert dvd_sub hb hS using 1 <;> ring
  · rw [hbeta, golden_unit_two_mul_fifth_snd] at hb
    convert dvd_sub hb (dvd_mul_of_dvd_right hS 2) using 1 <;> ring
  · rw [hbeta, golden_unit_three_mul_fifth_snd] at hb
    have h2F : (5 : ℤ) ∣ 2 * goldenFifthFstPoly gamma.fst gamma.snd :=
      by convert dvd_sub hb (dvd_mul_of_dvd_right hS 3) using 1 <;> ring
    rcases (show Prime (5 : ℤ) by norm_num).dvd_mul.mp h2F with h52 | hF
    · norm_num at h52
    · exact hF
  · rw [hbeta, golden_unit_four_mul_fifth_snd] at hb
    have h3F : (5 : ℤ) ∣ 3 * goldenFifthFstPoly gamma.fst gamma.snd :=
      by convert dvd_sub hb (dvd_mul_of_dvd_right hS 5) using 1 <;> ring
    rcases (show Prime (5 : ℤ) by norm_num).dvd_mul.mp h3F with h53 | hF
    · norm_num at h53
    · exact hF

/-- The zero-sector contract left after sectors one through four are eliminated. -/
abbrev SignedGoldenZeroSectorExclusion : Prop :=
  ∀ {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    (gamma : GoldenInt),
    p.beta = goldenPow gamma 5 → False

/-- Unit classification plus the zero-sector theorem excludes every unit-times-fifth-power. -/
theorem signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector
    (hClasses : GoldenUnitClassesModFifth)
    (hZero : SignedGoldenZeroSectorExclusion) :
    SignedGoldenUnitFifthPowerExclusion := by
  intro u v w p epsilon gamma hepsilon hbeta
  obtain ⟨i, delta, hdelta⟩ := hClasses epsilon hepsilon
  let theta := goldenMul delta gamma
  have hSector : p.beta =
      goldenMul (goldenPow goldenPhi i.val) (goldenPow theta 5) := by
    rw [hbeta, hdelta]
    simp only [theta, golden_mul_eq, golden_pow_eq, mul_pow]
    ring
  by_cases hi : i = 0
  · subst i
    apply hZero p theta
    simpa [goldenPhi_pow_zero, golden_mul_eq] using hSector
  · exact signedGolden_nonzero_unitSector_false p hi theta hSector

end DkMath.FLT.Five
