/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaQuantitativePrimePowerPulseMarginAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaCertifiedBlockCreditDebtDominanceAudit"

/-!
# CFZP-024: certified finite block credit and debt dominance

This module sums the one-prime-power quantitative certificates from CFZP-023
over a finite canonical block.  A chosen `Good` subset contributes certified
positive credit, while the complementary `Bad` subset carries the absolute
debt envelope.  The existence of such certificates, and their cofinal
dominance, remain explicit hypotheses.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open Set

/-! ## Gate A: canonical pair blocks -/

/-- The canonical prime-power pairs newly appearing in the right-closed block
`(A, B]`. -/
def cfzp024PrimePowerPairBlockSupport (A B : ℕ) : Finset (ℕ × ℕ) :=
  pascalPrimePowerPairSupportUpTo B \
    pascalPrimePowerPairSupportUpTo A

/-- A block pair is already present in the right endpoint support. -/
theorem cfzp024PrimePowerPairBlockSupport_subset_right
    {A B : ℕ} (_hAB : A ≤ B) :
    cfzp024PrimePowerPairBlockSupport A B ⊆
      pascalPrimePowerPairSupportUpTo B := by
  exact Finset.sdiff_subset

/-- A block pair is absent from the left endpoint support. -/
theorem cfzp024PrimePowerPairBlockSupport_not_mem_left
    {A B : ℕ} {pk : ℕ × ℕ}
    (hpk : pk ∈ cfzp024PrimePowerPairBlockSupport A B) :
    pk ∉ pascalPrimePowerPairSupportUpTo A := by
  exact (Finset.mem_sdiff.mp hpk).2

/-- Every block pair has a prime base and a positive canonical exponent. -/
private theorem cfzp024_prime_and_positive_exponent
    {A B : ℕ} {pk : ℕ × ℕ}
    (hAB : A ≤ B)
    (hpk : pk ∈ cfzp024PrimePowerPairBlockSupport A B) :
    Nat.Prime pk.1 ∧ 0 < pk.2 + 1 := by
  have hs := mem_pascalPrimePowerPairSupportUpTo_iff.mp
    (cfzp024PrimePowerPairBlockSupport_subset_right (A := A) (B := B)
      hAB hpk)
  exact ⟨(mem_pascalPrimeCoordinateSupportUpTo_iff.mp hs.1).1, by omega⟩

/-! ## Gate B: exact finite support-difference sums -/

/-- The positive block increment is the sum over the explicit pair block. -/
theorem cfzp024BlockPositiveEventMass_eq_supportDifferenceSum
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B) :
    cfzp022BlockPositiveEventMass ε W A B =
      ∑ pk ∈ cfzp024PrimePowerPairBlockSupport A B,
        cfzp019PrimePowerEventPositiveMass ε W pk.1 (pk.2 + 1) := by
  unfold cfzp022BlockPositiveEventMass cfzp019BranchFreePositiveEventMass
    cfzp024PrimePowerPairBlockSupport
  rw [Finset.sum_sdiff_eq_sub (cfzp020PrimePowerPairSupportUpTo_mono hAB)]

/-- The negative block increment is the sum over the explicit pair block. -/
theorem cfzp024BlockNegativeEventDebt_eq_supportDifferenceSum
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B) :
    cfzp022BlockNegativeEventDebt ε W A B =
      ∑ pk ∈ cfzp024PrimePowerPairBlockSupport A B,
        cfzp019PrimePowerEventNegativeDebt ε W pk.1 (pk.2 + 1) := by
  unfold cfzp022BlockNegativeEventDebt cfzp019BranchFreeNegativeEventDebt
    cfzp024PrimePowerPairBlockSupport
  rw [Finset.sum_sdiff_eq_sub (cfzp020PrimePowerPairSupportUpTo_mono hAB)]

/-! ## Gate C: Good/Bad split -/

/-- The complement of a chosen finite `Good` certificate inside a block. -/
def cfzp024BadPrimePowerPairBlockSupport
    (A B : ℕ) (Good : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  cfzp024PrimePowerPairBlockSupport A B \ Good

theorem cfzp024GoodUnionBad_eq_block
    {A B : ℕ} (Good : Finset (ℕ × ℕ)) :
    Good ⊆ cfzp024PrimePowerPairBlockSupport A B →
    Good ∪ cfzp024BadPrimePowerPairBlockSupport A B Good =
      cfzp024PrimePowerPairBlockSupport A B := by
  intro hGood
  exact Finset.union_sdiff_of_subset hGood

theorem cfzp024GoodDisjointBad
    {A B : ℕ} (Good : Finset (ℕ × ℕ)) :
    Disjoint Good (cfzp024BadPrimePowerPairBlockSupport A B Good) := by
  unfold cfzp024BadPrimePowerPairBlockSupport
  exact Finset.disjoint_sdiff

theorem cfzp024Bad_subset_block
    {A B : ℕ} (Good : Finset (ℕ × ℕ)) :
    cfzp024BadPrimePowerPairBlockSupport A B Good ⊆
      cfzp024PrimePowerPairBlockSupport A B := by
  exact Finset.sdiff_subset

/-! ## Gate D/F: summed certificates -/

/-- The finite positive credit certified by derivative margins on `Good`. -/
noncomputable def cfzp024CertifiedGoodCredit
    (Good : Finset (ℕ × ℕ)) (κ : ℕ × ℕ → ℝ) : ℝ :=
  ∑ pk ∈ Good,
    2 * Real.log (pk.1 : ℝ) *
      cfzpModeCriticalScale (pk.1 ^ (pk.2 + 1)) * κ pk

/-- The finite debt envelope certified on the complementary `Bad` set. -/
noncomputable def cfzp024CertifiedBadDebtEnvelope
    (Bad : Finset (ℕ × ℕ)) (K : ℕ × ℕ → ℝ) : ℝ :=
  ∑ pk ∈ Bad,
    2 * Real.log (pk.1 : ℝ) *
      cfzpModeCriticalScale (pk.1 ^ (pk.2 + 1)) * K pk

/-- Per-pair data for a finite certified block.  The dominance inequality is
kept separate from this certificate structure. -/
structure Cfzp024FiniteBlockCertificate
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (A B : ℕ) where
  Good : Finset (ℕ × ℕ)
  hGood : Good ⊆ cfzp024PrimePowerPairBlockSupport A B
  κ : ℕ × ℕ → ℝ
  K : ℕ × ℕ → ℝ
  hκ : ∀ pk ∈ Good, 0 ≤ κ pk
  hmargin : ∀ pk ∈ Good,
    Cfzp023CenteredProfileDerivativeDropMargin ε W pk.1 (pk.2 + 1) (κ pk)
  hK : ∀ pk ∈ cfzp024BadPrimePowerPairBlockSupport A B Good, 0 ≤ K pk
  henvelope : ∀ pk ∈ cfzp024BadPrimePowerPairBlockSupport A B Good,
    Cfzp023CenteredProfileDerivativeAbsEnvelope ε W pk.1 (pk.2 + 1) (K pk)

theorem cfzp024CertifiedGoodCredit_le_blockPositiveMass
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B)
    (cert : Cfzp024FiniteBlockCertificate ε W A B) :
    cfzp024CertifiedGoodCredit cert.Good cert.κ ≤
      cfzp022BlockPositiveEventMass ε W A B := by
  rw [cfzp024BlockPositiveEventMass_eq_supportDifferenceSum ε W hAB]
  unfold cfzp024CertifiedGoodCredit
  calc
    (∑ pk ∈ cert.Good,
        2 * Real.log (pk.1 : ℝ) *
          cfzpModeCriticalScale (pk.1 ^ (pk.2 + 1)) * cert.κ pk) ≤
        ∑ pk ∈ cert.Good,
          cfzp019PrimePowerEventPositiveMass ε W pk.1 (pk.2 + 1) := by
      apply Finset.sum_le_sum
      intro pk hpk
      have hpair := cfzp024_prime_and_positive_exponent hAB (cert.hGood hpk)
      exact cfzp023PrimePowerEventPositiveMass_ge_quantitativeCredit
        hε hε2 W hpair.1 hpair.2 (cert.hκ pk hpk) (cert.hmargin pk hpk)
    _ ≤ ∑ pk ∈ cfzp024PrimePowerPairBlockSupport A B,
        cfzp019PrimePowerEventPositiveMass ε W pk.1 (pk.2 + 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg cert.hGood
      intro pk hpk _
      exact cfzp019PrimePowerEventPositiveMass_nonneg ε W pk.1 (pk.2 + 1)

/-! ## Gate E: Good debt vanishes -/

theorem cfzp024GoodNegativeDebt_eq_zero
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B)
    (cert : Cfzp024FiniteBlockCertificate ε W A B) :
    (∑ pk ∈ cert.Good,
    cfzp019PrimePowerEventNegativeDebt ε W pk.1 (pk.2 + 1)) = 0 := by
  apply Finset.sum_eq_zero
  intro pk hpk
  apply cfzp019PrimePowerEventNegativeDebt_eq_zero_of_nonneg W pk.1 (pk.2 + 1)
  exact cfzp023PrimePowerBranchFreeTrigEvent_nonneg_of_zero_margin
    hε hε2 W
    (cfzp024_prime_and_positive_exponent
      hAB (cert.hGood hpk)).1
    (cfzp024_prime_and_positive_exponent
      hAB (cert.hGood hpk)).2
    (fun u hu => le_trans (cert.hmargin pk hpk u hu)
      (by simpa using (neg_nonpos.mpr (cert.hκ pk hpk))))

theorem cfzp024BlockNegativeDebt_le_certifiedBadDebtEnvelope
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B)
    (cert : Cfzp024FiniteBlockCertificate ε W A B) :
    cfzp022BlockNegativeEventDebt ε W A B ≤
      cfzp024CertifiedBadDebtEnvelope
        (cfzp024BadPrimePowerPairBlockSupport A B cert.Good) cert.K := by
  rw [cfzp024BlockNegativeEventDebt_eq_supportDifferenceSum ε W hAB]
  rw [← cfzp024GoodUnionBad_eq_block cert.Good cert.hGood,
    Finset.sum_union (cfzp024GoodDisjointBad cert.Good)]
  unfold cfzp024CertifiedBadDebtEnvelope
  rw [cfzp024GoodNegativeDebt_eq_zero hε hε2 W hAB cert]
  simp only [zero_add]
  apply Finset.sum_le_sum
  intro pk hpk
  have hpair := cfzp024_prime_and_positive_exponent hAB
    (cfzp024Bad_subset_block cert.Good hpk)
  exact cfzp023PrimePowerEventNegativeDebt_le_quantitativeEnvelope
    hε hε2 W hpair.1 hpair.2 (cert.hK pk hpk) (cert.henvelope pk hpk)

/-! ## Gate G: one finite certified payment -/

/-- The finite certificate fields imply the explicit certified block
dominance inequality. -/
def Cfzp024CertifiedBlockDominance
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (A B : ℕ) (η : ℝ) : Prop :=
  ∃ cert : Cfzp024FiniteBlockCertificate ε W A B,
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A +
        cfzp024CertifiedBadDebtEnvelope
          (cfzp024BadPrimePowerPairBlockSupport A B cert.Good) cert.K ≤
      cfzp024CertifiedGoodCredit cert.Good cert.κ + η

theorem cfzp024CertifiedBlockDominance_radialContactDeficit_le
    {ε η : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B)
    (hdom : Cfzp024CertifiedBlockDominance ε W A B η) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B ≤ η := by
  rcases hdom with ⟨cert, hcert⟩
  apply (cfzp022RadialContactDeficit_le_iff_signedBlockBudget
    hε hε2 W hAB).mpr
  have hdebt := cfzp024BlockNegativeDebt_le_certifiedBadDebtEnvelope
    hε hε2 W hAB cert
  have hcredit := cfzp024CertifiedGoodCredit_le_blockPositiveMass
    hε hε2 W hAB cert
  linarith

/-! ## Gate H: conditional cofinal transport -/

/-- A fixed-`ε` cofinal provider of certified block dominance. -/
def Cfzp024CofinalCertifiedBlockDominanceAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ A : ℕ, ∃ B : ℕ, A ≤ B ∧
    Cfzp024CertifiedBlockDominance ε W A B η

theorem cfzp024CofinalCertifiedBlockDominanceAt_implies_cfzp022
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hprovider : Cfzp024CofinalCertifiedBlockDominanceAt ε W) :
    Cfzp022CofinalSignedPulseBlockBudgetAt ε W := by
  intro η hη A
  rcases hprovider η hη A with ⟨B, hAB, hdom⟩
  refine ⟨B, hAB, ?_⟩
  apply (cfzp022RadialContactDeficit_le_iff_signedBlockBudget
    (η := η) hε hε2 W hAB).mp
  exact cfzp024CertifiedBlockDominance_radialContactDeficit_le
    hε hε2 W hAB hdom

/-- The same conditional provider reaches the existing CFZP-018 interface. -/
theorem cfzp024CofinalCertifiedBlockDominanceAt_implies_cfzp018
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hprovider : Cfzp024CofinalCertifiedBlockDominanceAt ε W) :
    Cfzp018CofinalPrimeThresholdApproximateReachAt ε W := by
  exact (cfzp022CofinalSignedPulseBlockBudgetAt_iff_cfzp018
    hε hε2 W).mp
    (cfzp024CofinalCertifiedBlockDominanceAt_implies_cfzp022
      hε hε2 W hprovider)

/-! ## Gate K: explicit provider gap -/

/-- No independent cofinal source of certified Good credit and controlled Bad
debt is supplied by this finite summation module. -/
inductive Cfzp024CertifiedBlockCreditDebtDominanceGap : Prop
  | noIndependentCofinalCertifiedBlockDominanceProvider

end DkMath.RH.CFBRCProjection
