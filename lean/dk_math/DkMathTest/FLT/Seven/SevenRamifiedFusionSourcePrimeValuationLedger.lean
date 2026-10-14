/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionSourcePrimeValuationLedger

#print "file: DkMathTest.FLT.Seven.SevenRamifiedFusionSourcePrimeValuationLedger"

namespace DkMathTest.FLT.Seven
open DkMath.FLT.Seven
open DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

example (p : RamifiedSignedRootRoutingPacket) :
    let K := p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
    Nat.Coprime K.quadratic.canonical.verticalGapRoot K.quadratic.compensationRoot :=
  internalDepthFour_source_outerRoots_coprime p

example (p : RamifiedSignedRootRoutingPacket) {ℓ : ℕ} (hp : Nat.Prime ℓ)
    (hd : ℓ ∣ internalDepthFourSeventhCore p) :
    let K := p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
    (internalDepthFourSeventhCore p).factorization ℓ =
      K.quadratic.canonical.verticalGapRoot.factorization ℓ +
      K.quadratic.compensationRoot.factorization ℓ := by
  rcases internalDepthFour_source_prime_valuation_balance p hp hd with
    ⟨_, _, _, _, _, hv⟩
  simpa only [Nat.factorization_def _ hp] using hv

example (p : RamifiedSignedRootRoutingPacket) {ℓ : ℕ} (hp : Nat.Prime ℓ)
    (hd : ℓ ∣ internalDepthFourSeventhCore p) :
    let K := p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
    (ℓ ∣ K.quadratic.canonical.verticalGapRoot ∧ ¬ ℓ ∣ K.quadratic.compensationRoot ∧
      padicValNat ℓ (internalDepthFourSeventhCore p) =
        padicValNat ℓ K.quadratic.canonical.verticalGapRoot) ∨
    (ℓ ∣ K.quadratic.compensationRoot ∧ ¬ ℓ ∣ K.quadratic.canonical.verticalGapRoot ∧
      padicValNat ℓ (internalDepthFourSeventhCore p) =
        padicValNat ℓ K.quadratic.compensationRoot) :=
  internalDepthFour_source_prime_exclusive_valuation p hp hd

-- The valuation balance also contains the previous, weaker support disjunction.
example (p : RamifiedSignedRootRoutingPacket) {ℓ : ℕ} (hp : Nat.Prime ℓ)
    (hd : ℓ ∣ internalDepthFourSeventhCore p) :
    let K := p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
    ℓ ∣ K.quadratic.canonical.verticalGapRoot ∨ ℓ ∣ K.quadratic.compensationRoot := by
  exact (internalDepthFour_source_prime_exclusive_valuation p hp hd).elim
    (fun h => .inl h.1) (fun h => .inr h.1)

-- Product positivity is essential to the multiplicative valuation API.
example (p : RamifiedSignedRootRoutingPacket) {ℓ : ℕ} (hp : Nat.Prime ℓ)
    (hd : ℓ ∣ internalDepthFourSeventhCore p) :
    let K := p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
    0 < K.quadratic.canonical.verticalGapRoot ∧ 0 < K.quadratic.compensationRoot := by
  rcases internalDepthFour_source_prime_valuation_balance p hp hd with
    ⟨N, hN, _, hprod, _, _⟩
  have hm := Nat.mul_pos (internalDepthFourSeventhCore_pos p) hN
  rw [hprod] at hm
  have hn := mul_ne_zero_iff.mp hm.ne'
  exact ⟨Nat.pos_of_ne_zero hn.1, Nat.pos_of_ne_zero hn.2⟩

/-- A generic product ledger does not imply exclusive outer ownership.
This is an arithmetic model, not a source-packet counterexample. -/
theorem productOnly_nonexclusive_countermodel :
    (4 : ℕ) * 1 = 2 * 2 ∧ Nat.Coprime 4 1 ∧
    Nat.Prime 2 ∧ 2 ∣ (4 : ℕ) ∧ 2 ∣ (2 : ℕ) ∧ ¬ Nat.Coprime 2 2 := by
  decide

-- Zero valuation convention does not permit unconditional product additivity.
example : padicValNat 2 (2 * 0) = 0 ∧ padicValNat 2 2 = 1 := by
  norm_num

#check padicValNat.mul
#check Nat.factorization_mul
#check internalDepthFourAllocation_prime_support
#check RamifiedSecondCoordinateCanonicalSplit.vertical_coprime_compensation_residual
#print axioms DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFour_source_outerRoots_coprime
#print axioms DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFour_source_prime_valuation_balance
#print axioms DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFour_source_prime_exclusive_valuation
#print axioms DkMathTest.FLT.Seven.productOnly_nonexclusive_countermodel
end DkMathTest.FLT.Seven
