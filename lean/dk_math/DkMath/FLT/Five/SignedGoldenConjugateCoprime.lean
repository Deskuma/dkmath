/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.SignedGoldenRamifierStripped

#print "file: DkMath.FLT.Five.SignedGoldenConjugateCoprime"

namespace DkMath.FLT.Five

/-!
# Relative primality of a stripped element and its conjugate

A common divisor of `beta` and `conj(beta)` divides both `N(beta)=b^5` and the norm of
their difference, `-5^15*a^20`.  The power-split coprimality says these integer masses
are coprime, so the common divisor has norm `±1` and is a golden unit.  The resulting
`GoldenRelPrime` certificate is precisely the hypothesis needed for fifth-power
factor extraction in the Euclidean domain.
-/

/-- Subtracting the conjugate isolates the square-root-of-five direction. -/
theorem golden_sub_conj_eq_snd_mul_sqrtFive (x : GoldenInt) :
    x - goldenConj x = goldenMul (goldenOfInt x.snd) sqrtFiveElement := by
  apply GoldenInt.ext
  · simp [goldenConj, goldenOfInt, goldenSqrtFive, goldenMul]
  · simp [goldenConj, goldenOfInt, goldenSqrtFive, goldenMul]
    ring

/-- The norm of the conjugate difference is `-5` times the square coordinate. -/
theorem goldenNorm_sub_conj (x : GoldenInt) :
    goldenNorm (x - goldenConj x) = -5 * x.snd ^ 2 := by
  rw [golden_sub_conj_eq_snd_mul_sqrtFive, goldenNorm_mul,
    goldenNorm_sqrtFive]
  simp [goldenNorm, goldenOfInt]
  ring

/-- The packet coordinate makes the conjugate-difference norm explicit. -/
theorem SignedGoldenRamifierStrippedPacket.norm_sub_conj_eq
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w) :
    goldenNorm (p.beta - goldenConj p.beta) =
      -((5 : ℤ) ^ 15 * (p.exceptional.powerSplit.a : ℤ) ^ 20) := by
  rw [goldenNorm_sub_conj, p.beta_snd]
  ring

/-- Every common divisor of a stripped element and its conjugate is a unit. -/
theorem SignedGoldenRamifierStrippedPacket.beta_relPrime_conj
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w) :
    GoldenRelPrime p.beta (goldenConj p.beta) := by
  intro d hdbeta hdconj
  have hddiff : GoldenDivides d (p.beta - goldenConj p.beta) :=
    goldenDivides_sub hdbeta hdconj
  have hnormBeta : goldenNorm d ∣ goldenNorm p.beta :=
    goldenNorm_dvd_of_goldenDivides hdbeta
  have hnormDiff : goldenNorm d ∣
      goldenNorm (p.beta - goldenConj p.beta) :=
    goldenNorm_dvd_of_goldenDivides hddiff
  have hdB : (goldenNorm d).natAbs ∣ p.exceptional.powerSplit.b ^ 5 := by
    apply Int.dvd_natCast.mp
    simpa [p.beta_norm] using hnormBeta
  have hdA : (goldenNorm d).natAbs ∣
      5 ^ 15 * p.exceptional.powerSplit.a ^ 20 := by
    apply Int.dvd_natCast.mp
    have hpos : goldenNorm d ∣
        (5 ^ 15 * p.exceptional.powerSplit.a ^ 20 : ℕ) := by
      exact Int.dvd_neg.mp (by simpa [p.norm_sub_conj_eq] using hnormDiff)
    exact_mod_cast hpos
  have hab := p.exceptional.powerSplit.coprime_b5_scaled_a20
  have habs : Nat.Coprime (p.exceptional.powerSplit.b ^ 5)
      (5 ^ 15 * p.exceptional.powerSplit.a ^ 20) := hab
  have hone : (goldenNorm d).natAbs = 1 :=
    Nat.eq_one_of_dvd_coprimes habs hdB hdA
  apply goldenUnit_of_norm_eq_one_or_neg_one
  omega

/-- A packet retaining the stripped data and certified conjugate coprimality. -/
structure SignedGoldenConjugateCoprimePacket (u v w : ℕ) : Type where
  stripped : SignedGoldenRamifierStrippedPacket u v w
  relPrime : GoldenRelPrime stripped.beta (goldenConj stripped.beta)

/-- Construct the conjugate-coprime packet without any choice. -/
def signedGoldenConjugateCoprimePacket_of_stripped
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w) :
    SignedGoldenConjugateCoprimePacket u v w :=
  ⟨p, p.beta_relPrime_conj⟩

/-- Chosen conjugate-coprime packet directly from a signed normal form. -/
noncomputable def signedGoldenConjugateCoprimePacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedGoldenConjugateCoprimePacket u v w :=
  signedGoldenConjugateCoprimePacket_of_stripped
    (signedGoldenRamifierStrippedPacket_of_normalForm hNF)

/-- Receiver contract for contradictions on packets carrying certified conjugate
relative primality. -/
abbrev SignedGoldenConjugateCoprimeCore : Prop :=
  ∀ {u v w : ℕ}, SignedGoldenConjugateCoprimePacket u v w → False

theorem signedBranchARefuter_of_goldenConjugateCoprimeCore
    (hCore : SignedGoldenConjugateCoprimeCore) : SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedGoldenConjugateCoprimePacket_of_normalForm hNF)

theorem branchB_false_of_goldenConjugateCoprimeCore
    (hCore : SignedGoldenConjugateCoprimeCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) : False := by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_goldenConjugateCoprimeCore hCore) hPack hBranch

end DkMath.FLT.Five
