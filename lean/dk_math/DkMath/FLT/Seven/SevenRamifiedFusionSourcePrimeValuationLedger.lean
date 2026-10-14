/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionSixthPowerAllocationSieve

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionSourcePrimeValuationLedger"

namespace DkMath.FLT.Seven
namespace RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

/-- The actual vertical and compensation roots are coprime, inherited from
the canonical source split and its compensation seventh-power identity. -/
theorem internalDepthFour_source_outerRoots_coprime
    (p : RamifiedSignedRootRoutingPacket) :
    let K := p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
    Nat.Coprime K.quadratic.canonical.verticalGapRoot K.quadratic.compensationRoot := by
  let K := p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
  have hd : K.quadratic.compensationRoot ∣ K.quadratic.canonical.compensationCore := by
    rw [K.quadratic.compensationCore_eq]
    exact dvd_pow_self _ (by decide : 7 ≠ 0)
  exact K.quadratic.canonical.vertical_coprime_compensation_residual.of_dvd_right
    (hd.trans (dvd_mul_right _ _))

/-- Every prime in the actual core avoids the actual complementary root
and conserves its multiplicity in the two source outer roots. -/
theorem internalDepthFour_source_prime_valuation_balance
    (p : RamifiedSignedRootRoutingPacket) {ℓ : ℕ} (hℓ : Nat.Prime ℓ)
    (hdiv : ℓ ∣ internalDepthFourSeventhCore p) :
    let K := p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
    ∃ N : ℕ, 0 < N ∧ Nat.Coprime (internalDepthFourSeventhCore p) N ∧
      internalDepthFourSeventhCore p * N =
        K.quadratic.canonical.verticalGapRoot * K.quadratic.compensationRoot ∧
      ¬ ℓ ∣ N ∧
      padicValNat ℓ (internalDepthFourSeventhCore p) =
        padicValNat ℓ K.quadratic.canonical.verticalGapRoot +
        padicValNat ℓ K.quadratic.compensationRoot := by
  have : Fact (Nat.Prime ℓ) := ⟨hℓ⟩
  let K := p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
  rcases K.exists_inner_complementary_seventh_root with
    ⟨N, hN, _, hproduct, hcop, _⟩
  change internalDepthFourSeventhCore p * N = _ at hproduct
  change Nat.Coprime (internalDepthFourSeventhCore p) N at hcop
  have hnot : ¬ ℓ ∣ N := hℓ.coprime_iff_not_dvd.mp (hcop.of_dvd_left hdiv)
  have hM := internalDepthFourSeventhCore_pos p
  have hVC : K.quadratic.canonical.verticalGapRoot * K.quadratic.compensationRoot ≠ 0 := by
    rw [← hproduct]
    exact mul_ne_zero hM.ne' hN.ne'
  have hV := (mul_ne_zero_iff.mp hVC).1
  have hC := (mul_ne_zero_iff.mp hVC).2
  refine ⟨N, hN, hcop, hproduct, hnot, ?_⟩
  have he := congrArg (padicValNat ℓ) hproduct
  rw [padicValNat.mul hM.ne' hN.ne', padicValNat.mul hV hC,
    padicValNat.eq_zero_of_not_dvd hnot, add_zero] at he
  exact he

/-- Source outer-root coprimality puts the entire core-prime valuation
on exactly one of the two source factors. No chart divisor is selected. -/
theorem internalDepthFour_source_prime_exclusive_valuation
    (p : RamifiedSignedRootRoutingPacket) {ℓ : ℕ} (hℓ : Nat.Prime ℓ)
    (hdiv : ℓ ∣ internalDepthFourSeventhCore p) :
    let K := p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
    (ℓ ∣ K.quadratic.canonical.verticalGapRoot ∧ ¬ ℓ ∣ K.quadratic.compensationRoot ∧
      padicValNat ℓ (internalDepthFourSeventhCore p) =
        padicValNat ℓ K.quadratic.canonical.verticalGapRoot) ∨
    (ℓ ∣ K.quadratic.compensationRoot ∧ ¬ ℓ ∣ K.quadratic.canonical.verticalGapRoot ∧
      padicValNat ℓ (internalDepthFourSeventhCore p) =
        padicValNat ℓ K.quadratic.compensationRoot) := by
  let K := p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
  rcases internalDepthFour_source_prime_valuation_balance p hℓ hdiv with
    ⟨N, _, _, hprod, _, hval⟩
  change padicValNat ℓ (internalDepthFourSeventhCore p) =
    padicValNat ℓ K.quadratic.canonical.verticalGapRoot +
    padicValNat ℓ K.quadratic.compensationRoot at hval
  have hcop := internalDepthFour_source_outerRoots_coprime p
  have hs : ℓ ∣ K.quadratic.canonical.verticalGapRoot ∨ ℓ ∣ K.quadratic.compensationRoot := by
    apply hℓ.dvd_mul.mp
    rw [← hprod]
    exact dvd_mul_of_dvd_left hdiv N
  rcases hs with hV | hC
  · have hnC : ¬ ℓ ∣ K.quadratic.compensationRoot :=
      hℓ.coprime_iff_not_dvd.mp (hcop.of_dvd_left hV)
    exact .inl ⟨hV, hnC, by simpa only [padicValNat.eq_zero_of_not_dvd hnC, add_zero] using hval⟩
  · have hnV : ¬ ℓ ∣ K.quadratic.canonical.verticalGapRoot :=
      hℓ.coprime_iff_not_dvd.mp (hcop.symm.of_dvd_left hC)
    exact .inr ⟨hC, hnV, by simpa only [padicValNat.eq_zero_of_not_dvd hnV, zero_add] using hval⟩

end RamifiedSignedRootRoutingPacket.QuotientPrimeSupport
end DkMath.FLT.Seven
