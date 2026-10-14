/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionSourcePrimeValuationLedger

#print "file: DkMathTest.FLT.Seven.SevenRamifiedFusionSourceConstraintSeparation"

namespace DkMathTest.FLT.Seven
open DkMath.FLT.Seven
open DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

/-- The scalar ledger admits this arithmetic model; no source packet is constructed. -/
theorem scalarLedger29Squared :
    let M := (29 : ℕ)^2
    let N := (1 : ℕ)
    let V := M
    let C := (1 : ℕ)
    M = 841 ∧ 0 < M ∧ 0 < N ∧ 0 < V ∧ 0 < C ∧
      M*N = V*C ∧ Nat.Coprime M N ∧ Nat.Coprime V C ∧
      ¬ 7 ∣ M ∧ ¬ 7 ∣ N ∧ ¬ Nat.Coprime 7 (29-1) := by decide

/-- Every prime in this scalar core is outside the permutation-prime criterion. -/
theorem primeDivisor29Squared {ℓ : ℕ} (hp : Nat.Prime ℓ) (hd : ℓ ∣ 841) : ℓ = 29 := by
  have hpow : ℓ ∣ 29 ^ 2 := by simpa using hd
  exact (Nat.dvd_prime (by decide : Nat.Prime 29)).mp (hp.dvd_of_dvd_pow hpow) |>.resolve_left hp.ne_one

/-- The ledger alone does not force a usable gate016 support prime. -/
theorem scalarLedger_no_permutation_prime :
    ¬ ∃ ℓ : ℕ, Nat.Prime ℓ ∧ ℓ ∣ 841 ∧ ℓ ≠ 2 ∧ ℓ ≠ 7 ∧ Nat.Coprime 7 (ℓ-1) := by
  rintro ⟨ℓ, hp, hd, _, _, hc⟩
  have he := primeDivisor29Squared hp hd
  subst ℓ
  exact (by decide : ¬ Nat.Coprime 7 (29-1)) hc

/-- The actual quadratic cubic-factor identity excludes N=1.
This concerns the complementary root, not a restriction on M alone. -/
theorem sourceComplement_ne_one (K : RamifiedRealCubicNormPacket) {N : ℕ}
    (hN : Int.natAbs (seventhPowerSndCore K.quadratic.innerRoot.fst
      K.quadratic.innerRoot.snd) = N ^ 7) : N ≠ 1 := by
  intro he
  subst N
  let A := K.quadratic.innerRoot.fst
  let B := K.quadratic.innerRoot.snd
  let L := seventhPowerSndLeftCubic A B
  let R := seventhPowerSndRightCubic A B
  have hp : Int.natAbs L * Int.natAbs R = 1 := by
    rw [← Int.natAbs_mul, ← seventhPowerSndCore_factor]
    simpa [A, B] using hN
  have hab : Int.natAbs L = 1 ∧ Int.natAbs R = 1 := by
    simpa only [mul_eq_one] using hp
  have hL : L = 1 ∨ L = -1 := Int.natAbs_eq_iff.mp hab.1
  have hR : R = 1 ∨ R = -1 := Int.natAbs_eq_iff.mp hab.2
  have hA : A ≠ 0 := by
    intro h
    exact K.innerFst_not_seven_dvd (by rw [show K.quadratic.innerRoot.fst = 0 from h]; exact dvd_zero 7)
  have hB : B ≠ 0 := K.quadratic.innerRoot_snd_ne_zero
  have hAB : A+B ≠ 0 := by
    intro h
    exact K.innerFst_add_innerSnd_not_seven_dvd (by rw [show K.quadratic.innerRoot.fst + K.quadratic.innerRoot.snd = 0 from h]; exact dvd_zero 7)
  have hneq : 7*A*B*(A+B) ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hA) hB) hAB
  have hdiff : R-L = 7*A*B*(A+B) := seventhPowerSnd_cubic_sub A B
  have hseven : (7 : ℤ) ∣ R-L := by rw [hdiff]; exact ⟨A*B*(A+B), by ring⟩
  rcases hL with hL | hL <;> rcases hR with hR | hR <;>
    norm_num [hL, hR] at hseven <;> apply hneq <;> simpa [hL, hR] using hdiff.symm


/-- Bare source data provide a complementary root greater than one,
so the scalar N=1 assignment cannot realize the actual complementary root. -/
theorem actualSourceComplement_gt_one (p : RamifiedSignedRootRoutingPacket) :
    let K := p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
    ∃ N : ℕ, 1 < N ∧
      Int.natAbs (seventhPowerSndCore K.quadratic.innerRoot.fst
        K.quadratic.innerRoot.snd) = N ^ 7 ∧
      internalDepthFourSeventhCore p * N =
        K.quadratic.canonical.verticalGapRoot * K.quadratic.compensationRoot ∧
      Nat.Coprime (internalDepthFourSeventhCore p) N := by
  let K := p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
  rcases K.exists_inner_complementary_seventh_root with ⟨N, hpos, hn, hprod, hcop, _⟩
  have hne := sourceComplement_ne_one K hn
  exact ⟨N, by omega, hn, hprod, hcop⟩

-- Signature inspection: these retain actual coordinates/norms and source hypotheses.
#check RamifiedQuadraticInnerRootPacket.innerRoot_coordinates_isCoprime
#check RamifiedQuadraticInnerRootPacket.innerRoot_norm_eq
#check RamifiedRealCubicNormPacket.innerSnd_eq
#check RamifiedRealCubicNormPacket.norm_leftSource_eq
#check RamifiedRealCubicNormPacket.norm_rightSource_eq
#check RamifiedRealCubicNormPacket.signedRootGap_seventhPower_eq
#check RamifiedRealCubicNormPacket.sourceDifference_eq_normalizedAxis_pow_six_mul_pow_seven
#check internalDepthFourReconstruction_core_gt_343
#check internalDepthFour_source_prime_exclusive_valuation

#print axioms DkMathTest.FLT.Seven.scalarLedger29Squared
#print axioms DkMathTest.FLT.Seven.primeDivisor29Squared
#print axioms DkMathTest.FLT.Seven.scalarLedger_no_permutation_prime
#print axioms DkMathTest.FLT.Seven.sourceComplement_ne_one
#print axioms DkMathTest.FLT.Seven.actualSourceComplement_gt_one
end DkMathTest.FLT.Seven
