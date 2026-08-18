/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisPeriodicCarrierArcGeometryAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisPositiveCarrierWeightedMassAudit"

/-!
# CFZP-038: positive-carrier weighted mass reduction

This module places the positive carrier hits of CFZP-037 inside the exact
finite signed ledger of CFZP-035.  All statements are finite.  In particular,
prime occupancy, weighted prime density, and residual elimination remain
explicit arithmetic gaps.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open Set

/-! ## Gate A: positive-arc Good supports -/

/-- Eligible prime-axis pairs hit by one translated positive carrier arc. -/
def cfzp038PositiveArcGoodPairSupportAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W)
    (n A B : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (cfzp034EligiblePrimeAxisPairBlockSupport ε A B).filter
    (fun pk => Cfzp037PrimeAxisPositiveArcHitAt ε W arc n pk.1)

/-- The set of eligible pair points hit by at least one cell in a finite window. -/
def cfzp038PositiveArcGoodPairSupport
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W)
    (N₀ N₁ A B : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (cfzp034EligiblePrimeAxisPairBlockSupport ε A B).filter
    (fun pk => ∃ n ∈ Finset.Icc N₀ N₁,
      Cfzp037PrimeAxisPositiveArcHitAt ε W arc n pk.1)

theorem cfzp038PositiveArcGoodPairSupportAt_subset_eligible
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W)
    (n A B : ℕ) :
    cfzp038PositiveArcGoodPairSupportAt ε W arc n A B ⊆
      cfzp034EligiblePrimeAxisPairBlockSupport ε A B := by
  classical
  intro pk hpk
  exact (Finset.mem_filter.mp hpk).1

theorem cfzp038PositiveArcGoodPairSupport_subset_eligible
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W)
    (N₀ N₁ A B : ℕ) :
    cfzp038PositiveArcGoodPairSupport ε W arc N₀ N₁ A B ⊆
      cfzp034EligiblePrimeAxisPairBlockSupport ε A B := by
  classical
  intro pk hpk
  exact (Finset.mem_filter.mp hpk).1

theorem cfzp038PositiveArcGoodPairSupportAt_hit
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow}
    {arc : Cfzp037CarrierPositiveArcData ε W} {n A B : ℕ}
    {pk : ℕ × ℕ}
    (hpk : pk ∈ cfzp038PositiveArcGoodPairSupportAt ε W arc n A B) :
    Cfzp037PrimeAxisPositiveArcHitAt ε W arc n pk.1 := by
  classical
  exact (Finset.mem_filter.mp hpk).2

theorem cfzp038PositiveArcGoodPairSupport_hit
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow}
    {arc : Cfzp037CarrierPositiveArcData ε W}
    {N₀ N₁ A B : ℕ} {pk : ℕ × ℕ}
    (hpk : pk ∈ cfzp038PositiveArcGoodPairSupport ε W arc N₀ N₁ A B) :
    ∃ n ∈ Finset.Icc N₀ N₁,
      Cfzp037PrimeAxisPositiveArcHitAt ε W arc n pk.1 := by
  classical
  exact (Finset.mem_filter.mp hpk).2

/-! ## Gate B: late Good hits give exact signed-mass credit -/

theorem cfzp038GoodSigmaWeight_credit_le_signedMass
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W)
    {Nlate N₀ N₁ A B : ℕ}
    (hNlate : Nlate ≤ N₀)
    (hlate : ∀ m, Nlate ≤ m →
      cfzp037RemainderAbsorptionThreshold ε W arc.margin ≤
        cfzp037PositiveArcLeft arc m)
    (hAB : A ≤ B) :
    (arc.margin / 2) *
        cfzp034PrimeAxisSigmaWeightSum W
          (cfzp038PositiveArcGoodPairSupport ε W arc N₀ N₁ A B) ≤
      cfzp035SignedEfficiencyMassOn ε W
        (cfzp038PositiveArcGoodPairSupport ε W arc N₀ N₁ A B) := by
  classical
  unfold cfzp034PrimeAxisSigmaWeightSum
  rw [Finset.mul_sum]
  apply le_trans ?_ (by
    change (∑ pk ∈ cfzp038PositiveArcGoodPairSupport ε W arc N₀ N₁ A B,
      cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1) *
        cfzp035PrimePowerSignedEfficiency ε W pk.1 (pk.2 + 1)) ≥ _
    exact le_rfl)
  apply Finset.sum_le_sum
  intro pk hpk
  have hGoodMem := cfzp038PositiveArcGoodPairSupport_hit hpk
  obtain ⟨n, hncell, hhit⟩ := hGoodMem
  have hncell' : n ∈ Finset.Icc N₀ N₁ := by simpa using hncell
  have hnlate : Nlate ≤ n := le_trans hNlate (Finset.mem_Icc.mp hncell').1
  have hcredit := cfzp037PrimeAxisEvent_ge_sigmaWeight_mul_margin_of_positiveArcHit
    hε hε2 W arc hnlate hlate hhit
  have haxis := (Finset.mem_filter.mp hpk).1
  have hprimeAxis := (Finset.mem_filter.mp haxis).1
  have hzero := (Finset.mem_filter.mp hprimeAxis).2
  have hs := mem_pascalPrimePowerPairSupportUpTo_iff.mp
    (cfzp024PrimePowerPairBlockSupport_subset_right hAB
      (Finset.mem_filter.mp hprimeAxis).1)
  have hp := (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hs.1).1
  have heq := cfzp035PrimePowerBranchFreeTrigEvent_eq_referenceMass_mul
    hε hε2 W hp (by norm_num : 0 < (1 : ℕ))
  calc
    arc.margin / 2 * cfzp034PrimeAxisSigmaWeight W pk.1 ≤
        cfzp034PrimeAxisSigmaWeight W pk.1 * (arc.margin / 2) := by
      simp [mul_comm]
    _ ≤ cfzpPrimePowerBranchFreeTrigEvent ε W pk.1 1 := hcredit
    _ = cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1) *
        cfzp035PrimePowerSignedEfficiency ε W pk.1 (pk.2 + 1) := by
      simpa [hzero] using heq

/-! ## Gate C: the universal finite debt envelope -/

theorem cfzp038SignedMass_ge_neg_referenceMass
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B)
    (S : Finset (ℕ × ℕ))
    (hS : S ⊆ cfzp024PrimePowerPairBlockSupport A B) :
    -cfzp032GoodReferenceMass ε W S ≤
      cfzp035SignedEfficiencyMassOn ε W S := by
  classical
  unfold cfzp032GoodReferenceMass cfzp035SignedEfficiencyMassOn
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro pk hpk
  have hs := mem_pascalPrimePowerPairSupportUpTo_iff.mp
    (cfzp024PrimePowerPairBlockSupport_subset_right hAB (hS hpk))
  have hp := (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hs.1).1
  have hj : 0 < pk.2 + 1 := by omega
  have hmass := cfzp031PrimePowerReferenceMass_pos hε hε2 W hp hj
  have hscore := cfzp035PrimePowerSignedEfficiency_lower_bound
    hε hε2 W hp hj
  have hmul := mul_le_mul_of_nonneg_left hscore hmass.le
  simpa using hmul

theorem cfzp038ExceptionalSignedMass_ge_neg_referenceMass
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B) :
    -cfzp034ExceptionalPrimeAxisReferenceMass ε W A B ≤
      cfzp035SignedEfficiencyMassOn ε W
        (cfzp034ExceptionalPrimeAxisPairBlockSupport ε A B) := by
  classical
  apply cfzp038SignedMass_ge_neg_referenceMass hε hε2 W hAB
  intro pk hpk
  have haxis := (Finset.mem_filter.mp hpk).1
  exact (Finset.mem_filter.mp haxis).1

theorem cfzp038HigherPowerSignedMass_ge_neg_referenceMass
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B) :
    -cfzp034HigherPowerReferenceMass ε W A B ≤
      cfzp035SignedEfficiencyMassOn ε W
        (cfzp034HigherPowerPairBlockSupport A B) := by
  classical
  apply cfzp038SignedMass_ge_neg_referenceMass hε hε2 W hAB
  intro pk hpk
  exact (Finset.mem_filter.mp hpk).1

/-! ## Gate D: Good/Bad partition inside the eligible support -/

/-- The complement of the positive-carrier Good support in the eligible axis. -/
def cfzp038PositiveArcBadPairSupport
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W)
    (N₀ N₁ A B : ℕ) : Finset (ℕ × ℕ) :=
  cfzp034EligiblePrimeAxisPairBlockSupport ε A B \
    cfzp038PositiveArcGoodPairSupport ε W arc N₀ N₁ A B

theorem cfzp038PositiveArcGoodUnionBad_eq_eligible
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow}
    {arc : Cfzp037CarrierPositiveArcData ε W}
    {N₀ N₁ A B : ℕ} :
    cfzp038PositiveArcGoodPairSupport ε W arc N₀ N₁ A B ∪
        cfzp038PositiveArcBadPairSupport ε W arc N₀ N₁ A B =
      cfzp034EligiblePrimeAxisPairBlockSupport ε A B := by
  exact Finset.union_sdiff_of_subset
    (cfzp038PositiveArcGoodPairSupport_subset_eligible ε W arc N₀ N₁ A B)

theorem cfzp038PositiveArcGoodDisjointBad
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow}
    {arc : Cfzp037CarrierPositiveArcData ε W}
    (N₀ N₁ A B : ℕ) :
    Disjoint (cfzp038PositiveArcGoodPairSupport ε W arc N₀ N₁ A B)
      (cfzp038PositiveArcBadPairSupport ε W arc N₀ N₁ A B) := by
  classical
  rw [Finset.disjoint_left]
  intro pk hgood hbad
  exact (Finset.mem_sdiff.mp hbad).2 hgood

theorem cfzp038PositiveArcBad_subset_eligible
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow}
    {arc : Cfzp037CarrierPositiveArcData ε W}
    (N₀ N₁ A B : ℕ) :
    cfzp038PositiveArcBadPairSupport ε W arc N₀ N₁ A B ⊆
      cfzp034EligiblePrimeAxisPairBlockSupport ε A B := by
  classical
  unfold cfzp038PositiveArcBadPairSupport
  exact Finset.sdiff_subset

theorem cfzp038PositiveArcEligibleSignedMass_eq_good_add_bad
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow}
    {arc : Cfzp037CarrierPositiveArcData ε W}
    (N₀ N₁ A B : ℕ) :
    cfzp035SignedEfficiencyMassOn ε W
        (cfzp034EligiblePrimeAxisPairBlockSupport ε A B) =
      cfzp035SignedEfficiencyMassOn ε W
        (cfzp038PositiveArcGoodPairSupport ε W arc N₀ N₁ A B) +
      cfzp035SignedEfficiencyMassOn ε W
        (cfzp038PositiveArcBadPairSupport ε W arc N₀ N₁ A B) := by
  rw [← cfzp038PositiveArcGoodUnionBad_eq_eligible]
  unfold cfzp035SignedEfficiencyMassOn
  rw [Finset.sum_union (cfzp038PositiveArcGoodDisjointBad N₀ N₁ A B)]

theorem cfzp038PositiveArcEligibleWeightSum_eq_good_add_bad
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow}
    {arc : Cfzp037CarrierPositiveArcData ε W}
    (N₀ N₁ A B : ℕ) :
    cfzp034PrimeAxisSigmaWeightSum W
        (cfzp034EligiblePrimeAxisPairBlockSupport ε A B) =
      cfzp034PrimeAxisSigmaWeightSum W
        (cfzp038PositiveArcGoodPairSupport ε W arc N₀ N₁ A B) +
      cfzp034PrimeAxisSigmaWeightSum W
        (cfzp038PositiveArcBadPairSupport ε W arc N₀ N₁ A B) := by
  rw [← cfzp038PositiveArcGoodUnionBad_eq_eligible]
  unfold cfzp034PrimeAxisSigmaWeightSum
  rw [Finset.sum_union (cfzp038PositiveArcGoodDisjointBad N₀ N₁ A B)]

/-! ## Gate E: the exact carrier-reservoir endpoint -/

theorem cfzp038PositiveCarrierExactReservoir_implies_radialContactDeficit_le
    {ε η : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W)
    {Nlate N₀ N₁ A B : ℕ}
    (hAB : A ≤ B)
    (hNlate : Nlate ≤ N₀)
    (hlate : ∀ m, Nlate ≤ m →
      cfzp037RemainderAbsorptionThreshold ε W arc.margin ≤
        cfzp037PositiveArcLeft arc m)
    (hreservoir :
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A +
        cfzp032GoodReferenceMass ε W
          (cfzp038PositiveArcBadPairSupport ε W arc N₀ N₁ A B) +
        cfzp034ExceptionalPrimeAxisReferenceMass ε W A B +
        cfzp034HigherPowerReferenceMass ε W A B ≤
      (arc.margin / 2) *
        cfzp034PrimeAxisSigmaWeightSum W
          (cfzp038PositiveArcGoodPairSupport ε W arc N₀ N₁ A B) + η) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B ≤ η := by
  classical
  let Good := cfzp038PositiveArcGoodPairSupport ε W arc N₀ N₁ A B
  let Bad := cfzp038PositiveArcBadPairSupport ε W arc N₀ N₁ A B
  have hGoodBlock : Good ⊆ cfzp024PrimePowerPairBlockSupport A B := by
    intro pk hpk
    have helig := cfzp038PositiveArcGoodPairSupport_subset_eligible
      ε W arc N₀ N₁ A B hpk
    have haxis := (Finset.mem_filter.mp helig).1
    exact (Finset.mem_filter.mp haxis).1
  have hBadBlock : Bad ⊆ cfzp024PrimePowerPairBlockSupport A B := by
    intro pk hpk
    have helig := cfzp038PositiveArcBad_subset_eligible
      (ε := ε) (W := W) (arc := arc) N₀ N₁ A B hpk
    have haxis := (Finset.mem_filter.mp helig).1
    exact (Finset.mem_filter.mp haxis).1
  have hcredit := cfzp038GoodSigmaWeight_credit_le_signedMass
    (N₁ := N₁) hε hε2 W arc hNlate hlate hAB
  have hdebt := cfzp038SignedMass_ge_neg_referenceMass
    hε hε2 W hAB Bad hBadBlock
  have hexception := cfzp038ExceptionalSignedMass_ge_neg_referenceMass
    hε hε2 W hAB
  have hhigher := cfzp038HigherPowerSignedMass_ge_neg_referenceMass
    hε hε2 W hAB
  have hsplit := cfzp038PositiveArcEligibleSignedMass_eq_good_add_bad
    (ε := ε) (W := W) (arc := arc) N₀ N₁ A B
  have hthree := cfzp035SignedEfficiencyBlock_eq_three_way_split
    ε W hAB
  have hblock : cfzp035SignedEfficiencyBlock ε W A B =
      cfzp035SignedEfficiencyMassOn ε W Good +
        cfzp035SignedEfficiencyMassOn ε W Bad +
        cfzp035SignedEfficiencyMassOn ε W
          (cfzp034ExceptionalPrimeAxisPairBlockSupport ε A B) +
        cfzp035SignedEfficiencyMassOn ε W
          (cfzp034HigherPowerPairBlockSupport A B) := by
    rw [hthree, hsplit]
  have hbound : pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A ≤
      cfzp035SignedEfficiencyBlock ε W A B + η := by
    rw [hblock]
    dsimp [Good, Bad] at hreservoir hcredit hdebt
    nlinarith
  exact cfzp035SignedEfficiencyBlock_bound_implies_radialContactDeficit_le
    hε hε2 W hAB hbound

/-! ## Gate F: sigma-only coarse reservoir reductions -/

theorem cfzp038PositiveCarrierSigmaReservoir_implies_radialContactDeficit_le
    {ε η : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W)
    {Nlate N₀ N₁ A B : ℕ}
    (hAB : A ≤ B)
    (hNlate : Nlate ≤ N₀)
    (hlate : ∀ m, Nlate ≤ m →
      cfzp037RemainderAbsorptionThreshold ε W arc.margin ≤
        cfzp037PositiveArcLeft arc m)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hreservoir :
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A +
        cfzp034ExceptionalPrimeAxisReferenceMass ε W A B +
        cfzp034HigherPowerReferenceMass ε W A B +
        cfzp034PrimeAxisMassUpperConstant ε W *
          cfzp034PrimeAxisSigmaWeightSum W
            (cfzp038PositiveArcBadPairSupport ε W arc N₀ N₁ A B) ≤
      (arc.margin / 2) *
          cfzp034PrimeAxisSigmaWeightSum W
            (cfzp038PositiveArcGoodPairSupport ε W arc N₀ N₁ A B) + η) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B ≤ η := by
  have hbad := cfzp038PositiveArcBad_subset_eligible
    (ε := ε) (W := W) (arc := arc) N₀ N₁ A B
  have hupper := cfzp034PrimeAxisSigmaWeightSum_upper hε hε2 W hAB hsub
    _ hbad
  apply cfzp038PositiveCarrierExactReservoir_implies_radialContactDeficit_le
    hε hε2 W arc hAB hNlate hlate
  have hreplace :
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A +
          cfzp032GoodReferenceMass ε W
            (cfzp038PositiveArcBadPairSupport ε W arc N₀ N₁ A B) +
          cfzp034ExceptionalPrimeAxisReferenceMass ε W A B +
          cfzp034HigherPowerReferenceMass ε W A B ≤
        pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A +
          cfzp034PrimeAxisMassUpperConstant ε W *
            cfzp034PrimeAxisSigmaWeightSum W
              (cfzp038PositiveArcBadPairSupport ε W arc N₀ N₁ A B) +
          cfzp034ExceptionalPrimeAxisReferenceMass ε W A B +
          cfzp034HigherPowerReferenceMass ε W A B := by
    linarith [hupper]
  have hreservoir' :
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A +
          cfzp034PrimeAxisMassUpperConstant ε W *
            cfzp034PrimeAxisSigmaWeightSum W
              (cfzp038PositiveArcBadPairSupport ε W arc N₀ N₁ A B) +
          cfzp034ExceptionalPrimeAxisReferenceMass ε W A B +
          cfzp034HigherPowerReferenceMass ε W A B ≤
        (arc.margin / 2) *
            cfzp034PrimeAxisSigmaWeightSum W
              (cfzp038PositiveArcGoodPairSupport ε W arc N₀ N₁ A B) + η := by
    simpa [add_assoc, add_left_comm, add_comm] using hreservoir
  exact le_trans hreplace hreservoir'

theorem cfzp038PositiveCarrierTotalWeightReservoir_implies_radialContactDeficit_le
    {ε η : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W)
    {Nlate N₀ N₁ A B : ℕ}
    (hAB : A ≤ B)
    (hNlate : Nlate ≤ N₀)
    (hlate : ∀ m, Nlate ≤ m →
      cfzp037RemainderAbsorptionThreshold ε W arc.margin ≤
        cfzp037PositiveArcLeft arc m)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hreservoir :
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A +
        cfzp034ExceptionalPrimeAxisReferenceMass ε W A B +
        cfzp034HigherPowerReferenceMass ε W A B +
        cfzp034PrimeAxisMassUpperConstant ε W *
          cfzp034PrimeAxisSigmaWeightSum W
            (cfzp034EligiblePrimeAxisPairBlockSupport ε A B) ≤
      (cfzp034PrimeAxisMassUpperConstant ε W + arc.margin / 2) *
          cfzp034PrimeAxisSigmaWeightSum W
            (cfzp038PositiveArcGoodPairSupport ε W arc N₀ N₁ A B) + η) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B ≤ η := by
  have hsplit := cfzp038PositiveArcEligibleWeightSum_eq_good_add_bad
    (ε := ε) (W := W) (arc := arc) N₀ N₁ A B
  apply cfzp038PositiveCarrierSigmaReservoir_implies_radialContactDeficit_le
    hε hε2 W arc hAB hNlate hlate hsub
  rw [hsplit] at hreservoir
  have hnorm :
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A +
          cfzp034ExceptionalPrimeAxisReferenceMass ε W A B +
          cfzp034HigherPowerReferenceMass ε W A B +
          cfzp034PrimeAxisMassUpperConstant ε W *
            (cfzp034PrimeAxisSigmaWeightSum W
                (cfzp038PositiveArcGoodPairSupport ε W arc N₀ N₁ A B) +
             cfzp034PrimeAxisSigmaWeightSum W
                (cfzp038PositiveArcBadPairSupport ε W arc N₀ N₁ A B)) ≤
        cfzp034PrimeAxisMassUpperConstant ε W *
            cfzp034PrimeAxisSigmaWeightSum W
              (cfzp038PositiveArcGoodPairSupport ε W arc N₀ N₁ A B) +
          (arc.margin / 2) *
            cfzp034PrimeAxisSigmaWeightSum W
              (cfzp038PositiveArcGoodPairSupport ε W arc N₀ N₁ A B) + η := by
    convert hreservoir using 1; ring_nf
  have htarget :
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A +
          cfzp034ExceptionalPrimeAxisReferenceMass ε W A B +
          cfzp034HigherPowerReferenceMass ε W A B +
          cfzp034PrimeAxisMassUpperConstant ε W *
            cfzp034PrimeAxisSigmaWeightSum W
              (cfzp038PositiveArcBadPairSupport ε W arc N₀ N₁ A B) ≤
        (arc.margin / 2) *
            cfzp034PrimeAxisSigmaWeightSum W
              (cfzp038PositiveArcGoodPairSupport ε W arc N₀ N₁ A B) + η := by
    linarith [hnorm]
  exact htarget

/-! ## Gates G--I: right-end floors and arithmetic-provider interfaces -/

/-- The sigma weight at the right endpoint of a positive log arc. -/
noncomputable def cfzp038PositiveArcRightSigmaWeight
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W) (n : ℕ) : ℝ :=
  Real.exp (-(W.rectangle.σ) * cfzp037PositiveArcRight arc n)

/-- The right-end sigma floor is strictly positive. -/
theorem cfzp038PositiveArcRightSigmaWeight_pos
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W) (n : ℕ) :
    0 < cfzp038PositiveArcRightSigmaWeight W arc n := by
  unfold cfzp038PositiveArcRightSigmaWeight
  exact Real.exp_pos _

/-- A prime hit has at least the right-end sigma floor as its sigma weight. -/
theorem cfzp038PositiveArcRightSigmaWeight_le_primeWeight
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W) (n p : ℕ)
    (hhit : Cfzp037PrimeAxisPositiveArcHitAt ε W arc n p) :
    cfzp038PositiveArcRightSigmaWeight W arc n ≤
      cfzp034PrimeAxisSigmaWeight W p := by
  have hσ : 0 < W.rectangle.σ :=
    lt_trans (by norm_num : (0 : ℝ) < 1 / 2)
      (cfzp034_rectangleSigma_gt_half W)
  have hlog := hhit.2.2
  have hmul := mul_le_mul_of_nonpos_left hlog
    (neg_nonpos.mpr hσ.le)
  unfold cfzp038PositiveArcRightSigmaWeight cfzp034PrimeAxisSigmaWeight
  exact Real.exp_le_exp.mpr hmul

/-- A single positive cell converts prime cardinality into sigma-weighted mass. -/
theorem cfzp038_card_mul_rightSigmaWeight_le_goodWeightAt
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W)
    (n A B : ℕ) :
    ((cfzp038PositiveArcGoodPairSupportAt ε W arc n A B).card : ℝ) *
        cfzp038PositiveArcRightSigmaWeight W arc n ≤
      cfzp034PrimeAxisSigmaWeightSum W
        (cfzp038PositiveArcGoodPairSupportAt ε W arc n A B) := by
  classical
  let Good := cfzp038PositiveArcGoodPairSupportAt ε W arc n A B
  unfold cfzp034PrimeAxisSigmaWeightSum
  calc
    (Good.card : ℝ) * cfzp038PositiveArcRightSigmaWeight W arc n =
        ∑ _pk ∈ Good, cfzp038PositiveArcRightSigmaWeight W arc n := by
          simp
    _ ≤ ∑ pk ∈ Good, cfzp034PrimeAxisSigmaWeight W pk.1 := by
      apply Finset.sum_le_sum
      intro pk hpk
      exact cfzp038PositiveArcRightSigmaWeight_le_primeWeight W arc n pk.1
        (cfzp038PositiveArcGoodPairSupportAt_hit hpk)

/-- A future arithmetic count theorem can be supplied without asserting one here. -/
def Cfzp038PositiveArcPrimeCountCertificateAt
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W)
    (n A B : ℕ) (C : ℝ) : Prop :=
  C ≤ (cfzp038PositiveArcGoodPairSupportAt ε W arc n A B).card

/-- A count certificate gives a finite weighted-mass certificate. -/
theorem cfzp038_countCertificate_mul_rightSigmaWeight_le_goodWeightAt
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W)
    (n A B : ℕ) (C : ℝ)
    (hC : Cfzp038PositiveArcPrimeCountCertificateAt W arc n A B C) :
    C * cfzp038PositiveArcRightSigmaWeight W arc n ≤
      cfzp034PrimeAxisSigmaWeightSum W
        (cfzp038PositiveArcGoodPairSupportAt ε W arc n A B) := by
  have hfloor : 0 ≤ cfzp038PositiveArcRightSigmaWeight W arc n :=
    (cfzp038PositiveArcRightSigmaWeight_pos W arc n).le
  exact le_trans (mul_le_mul_of_nonneg_right hC hfloor)
    (cfzp038_card_mul_rightSigmaWeight_le_goodWeightAt W arc n A B)

/-! The remaining arithmetic providers are explicit rather than implicit. -/

inductive Cfzp038PrimeAxisPositiveCarrierWeightedMassGap : Prop
  | noPositiveArcPrimeCountProvider
  | noPositiveArcSigmaWeightedMassDominanceProvider
  | noPrimeLogWeightedDistributionProvider
  | noExceptionalPrimeAxisResidualElimination
  | noHigherPrimePowerResidualElimination
  | noAutomaticSubcriticalWindowProvider

end DkMath.RH.CFBRCProjection
