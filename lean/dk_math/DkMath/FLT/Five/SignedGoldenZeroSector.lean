/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.SignedGoldenSectorArithmetic

#print "file: DkMath.FLT.Five.SignedGoldenZeroSector"

namespace DkMath.FLT.Five

/-- The zero-sector base has norm equal to the packet base up to sign. -/
theorem SignedGoldenRamifierStrippedPacket.zeroSector_gamma_norm_eq_or_eq_neg
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    goldenNorm gamma = (p.exceptional.powerSplit.b : ℤ) ∨
      goldenNorm gamma = -(p.exceptional.powerSplit.b : ℤ) := by
  apply p.gamma_norm_eq_or_eq_neg goldenUnit_one
  rw [hbeta]
  ext <;> simp [goldenOne, goldenMul]

/-- In the zero sector the base norm is not divisible by five. -/
theorem SignedGoldenRamifierStrippedPacket.zeroSector_five_not_dvd_gamma_norm
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    ¬ (5 : ℤ) ∣ goldenNorm gamma := by
  apply p.five_not_dvd_gamma_norm goldenUnit_one
  rw [hbeta]
  ext <;> simp [goldenOne, goldenMul]

/-- Exact signed second-coordinate equation in the zero sector. -/
theorem SignedGoldenRamifierStrippedPacket.zeroSector_snd_factor_eq
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd =
      -(5 : ℤ) ^ 6 * (p.exceptional.powerSplit.a : ℤ) ^ 10 := by
  have hsnd := congrArg (fun x : GoldenInt => x.snd) hbeta
  change p.beta.snd = (goldenPow gamma 5).snd at hsnd
  rw [p.beta_snd, goldenPow_five_snd, goldenFifthSndPoly_eq] at hsnd
  nlinarith

/-- The quartic factor is the square of the golden norm modulo five. -/
theorem five_dvd_goldenFifthSndFactor_sub_norm_sq (gamma : GoldenInt) :
    (5 : ℤ) ∣
      goldenFifthSndFactor gamma.fst gamma.snd - goldenNorm gamma ^ 2 := by
  refine ⟨gamma.fst * gamma.snd ^ 2 * (gamma.fst + gamma.snd), ?_⟩
  simp only [goldenFifthSndFactor, goldenNorm]
  ring

/-- The zero-sector quartic factor is not divisible by five. -/
theorem SignedGoldenRamifierStrippedPacket.zeroSector_five_not_dvd_sndFactor
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    ¬ (5 : ℤ) ∣ goldenFifthSndFactor gamma.fst gamma.snd := by
  intro hH
  apply p.zeroSector_five_not_dvd_gamma_norm hbeta
  have hdiff := five_dvd_goldenFifthSndFactor_sub_norm_sq gamma
  have hnormSq : (5 : ℤ) ∣ goldenNorm gamma ^ 2 := by
    convert dvd_sub hH hdiff using 1 <;> ring
  exact (show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow hnormSq

/-- Natural absolute-value form of the zero-sector product equation. -/
theorem SignedGoldenRamifierStrippedPacket.zeroSector_natAbs_product_eq
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    gamma.snd.natAbs *
        (goldenFifthSndFactor gamma.fst gamma.snd).natAbs =
      5 ^ 6 * p.exceptional.powerSplit.a ^ 10 := by
  have h := congrArg Int.natAbs (p.zeroSector_snd_factor_eq hbeta)
  simpa [Int.natAbs_mul, pow_succ] using h

/-- The two integer coordinates of a zero-sector fifth-power base are primitive. -/
theorem SignedGoldenRamifierStrippedPacket.zeroSector_coprime_coords
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    Nat.Coprime gamma.fst.natAbs gamma.snd.natAbs := by
  by_contra hcop
  rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with
    ⟨q, hqPrime, hqr, hqs⟩
  have hqrZ : (q : ℤ) ∣ gamma.fst := Int.natCast_dvd.mpr hqr
  have hqsZ : (q : ℤ) ∣ gamma.snd := Int.natCast_dvd.mpr hqs
  have hqNormZ : (q : ℤ) ∣ goldenNorm gamma := by
    simp only [goldenNorm]
    exact dvd_sub (dvd_add (dvd_pow hqrZ (by decide))
      (dvd_mul_of_dvd_left hqrZ gamma.snd)) (dvd_pow hqsZ (by decide))
  have hqb : q ∣ p.exceptional.powerSplit.b := by
    rcases p.zeroSector_gamma_norm_eq_or_eq_neg hbeta with hn | hn
    · rw [hn] at hqNormZ
      exact_mod_cast hqNormZ
    · rw [hn] at hqNormZ
      exact_mod_cast (Int.dvd_neg.mp hqNormZ)
  have hprod := p.zeroSector_natAbs_product_eq hbeta
  have hqRhs : q ∣ 5 ^ 6 * p.exceptional.powerSplit.a ^ 10 := by
    rw [← hprod]
    exact dvd_mul_of_dvd_left hqs _
  rcases hqPrime.dvd_mul.mp hqRhs with hq5pow | hqapow
  · have hq5 : q ∣ 5 := hqPrime.dvd_of_dvd_pow hq5pow
    have hqeq : q = 5 :=
      ((Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hq5).resolve_left
        hqPrime.ne_one
    exact p.five_not_dvd_b (hqeq ▸ hqb)
  · have hqa : q ∣ p.exceptional.powerSplit.a :=
      hqPrime.dvd_of_dvd_pow hqapow
    exact (Nat.not_coprime_of_dvd_of_dvd hqPrime.one_lt hqa hqb)
      p.exceptional.powerSplit.coprime_a_b

/-- The primitive coordinate condition makes `s` coprime to its quartic factor. -/
theorem SignedGoldenRamifierStrippedPacket.zeroSector_coprime_s_sndFactor
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    Nat.Coprime gamma.snd.natAbs
      (goldenFifthSndFactor gamma.fst gamma.snd).natAbs := by
  by_contra hcop
  rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with
    ⟨q, hqPrime, hqs, hqH⟩
  have hqsZ : (q : ℤ) ∣ gamma.snd := Int.natCast_dvd.mpr hqs
  have hqHZ : (q : ℤ) ∣ goldenFifthSndFactor gamma.fst gamma.snd :=
    Int.natCast_dvd.mpr hqH
  have hqR4 : (q : ℤ) ∣ gamma.fst ^ 4 := by
    have htail : (q : ℤ) ∣
        goldenFifthSndFactor gamma.fst gamma.snd - gamma.fst ^ 4 := by
      rcases hqsZ with ⟨k, hk⟩
      refine ⟨k * (2 * gamma.fst ^ 3 + 4 * gamma.fst ^ 2 * gamma.snd +
        3 * gamma.fst * gamma.snd ^ 2 + gamma.snd ^ 3), ?_⟩
      simp only [goldenFifthSndFactor]
      rw [hk]
      ring
    convert dvd_sub hqHZ htail using 1 <;> ring
  have hqr4 : q ∣ gamma.fst.natAbs ^ 4 := by
    simpa [Int.natAbs_pow] using Int.natCast_dvd.mp hqR4
  have hqr : q ∣ gamma.fst.natAbs := hqPrime.dvd_of_dvd_pow hqr4
  exact (Nat.not_coprime_of_dvd_of_dvd hqPrime.one_lt hqr hqs)
    (p.zeroSector_coprime_coords hbeta)

/--
The coprime zero-sector product splits exactly: all six factors of five lie in
the second coordinate, and the remaining coprime factors are tenth powers.
-/
theorem SignedGoldenRamifierStrippedPacket.zeroSector_tenthPower_split
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    ∃ c d : ℕ,
      gamma.snd.natAbs = 5 ^ 6 * c ^ 10 ∧
      (goldenFifthSndFactor gamma.fst gamma.snd).natAbs = d ^ 10 := by
  let H := (goldenFifthSndFactor gamma.fst gamma.snd).natAbs
  have hprod : gamma.snd.natAbs * H =
      5 ^ 6 * p.exceptional.powerSplit.a ^ 10 := by
    simpa [H] using p.zeroSector_natAbs_product_eq hbeta
  have h5H : ¬ 5 ∣ H := by
    intro h
    apply p.zeroSector_five_not_dvd_sndFactor hbeta
    apply Int.natCast_dvd.mpr
    simpa [H] using h
  have hcop5H : Nat.Coprime (5 ^ 6) H :=
    (Nat.Coprime.pow_left 6
      ((by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr h5H))
  have h5dvdProduct : 5 ^ 6 ∣ gamma.snd.natAbs * H := by
    rw [hprod]
    exact dvd_mul_right (5 ^ 6) _
  have h5dvdS : 5 ^ 6 ∣ gamma.snd.natAbs :=
    hcop5H.dvd_of_dvd_mul_right h5dvdProduct
  rcases h5dvdS with ⟨t, ht⟩
  have htProduct : t * H = p.exceptional.powerSplit.a ^ 10 := by
    rw [ht] at hprod
    rw [mul_assoc] at hprod
    exact Nat.mul_left_cancel (by positivity) hprod
  have htDvdS : t ∣ gamma.snd.natAbs := by
    rw [ht]
    exact dvd_mul_left t (5 ^ 6)
  have hcopTH : Nat.Coprime t H :=
    (p.zeroSector_coprime_s_sndFactor hbeta).of_dvd_left htDvdS
  have hunit : IsUnit (gcd t H) := by
    simpa [Nat.Coprime] using hcopTH
  obtain ⟨c, hc⟩ :=
    exists_eq_pow_of_mul_eq_pow hunit htProduct
  have hunit' : IsUnit (gcd H t) := by
    simpa [gcd_comm] using hunit
  obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow hunit'
    (by simpa [mul_comm] using htProduct)
  exact ⟨c, d, by simpa [hc] using ht, hd⟩

end DkMath.FLT.Five
