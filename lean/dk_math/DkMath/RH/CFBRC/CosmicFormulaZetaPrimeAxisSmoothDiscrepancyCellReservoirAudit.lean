/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisFiniteAbelPrimeCountingDiscrepancyAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisSmoothDiscrepancyCellReservoirAudit"

/-!
# CFZP-041: smooth/discrepancy cell reservoir reduction

This module keeps the prime-counting input finite.  A carrier cell is written
as the exact smooth Abel contribution plus a named discrepancy functional, and
the latter is passed to the radial reservoir only through an explicit finite
debt bound.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open MeasureTheory
open Set

/-! ## Gate A: ordered natural cell block -/

/-- The floor endpoints of an exponential carrier cell are ordered. -/
theorem cfzp041CarrierCellNaturalLeft_le_right
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) :
    cfzp040CarrierCellNaturalLeft W c n ≤
      cfzp040CarrierCellNaturalRight W c n := by
  apply Nat.floor_mono
  exact (cfzp040CarrierCellExpLeft_lt_right W c n).le

/-! ## Gate B: the natural block is exactly the cell support -/

theorem cfzp041EligiblePrimeAxisBlockSupport_eq_carrierCellSupport
    {ε : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) :
    cfzp034EligiblePrimeAxisPairBlockSupport ε
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) =
      cfzp039PrimeAxisCarrierCellPairSupport ε W c n
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) := by
  classical
  ext pk
  constructor
  · intro hpk
    have haxis : pk ∈ cfzp034PrimeAxisPairBlockSupport
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) :=
      (Finset.mem_filter.mp hpk).1
    have hblock := (Finset.mem_filter.mp haxis).1
    have hzero : pk.2 = 0 := (Finset.mem_filter.mp haxis).2
    have hright : pk ∈ pascalPrimePowerPairSupportUpTo
        (cfzp040CarrierCellNaturalRight W c n) :=
      (Finset.mem_sdiff.mp hblock).1
    have hcoord := mem_pascalPrimeCoordinateSupportUpTo_iff.mp
      (mem_pascalPrimePowerPairSupportUpTo_iff.mp hright).1
    have hp : Nat.Prime pk.1 := hcoord.1
    have hleft : pk ∉ pascalPrimePowerPairSupportUpTo
        (cfzp040CarrierCellNaturalLeft W c n) :=
      (Finset.mem_sdiff.mp hblock).2
    have hpk_gt_left : cfzp040CarrierCellNaturalLeft W c n < pk.1 := by
      by_contra hnot
      have hpk_le_left : pk.1 ≤ cfzp040CarrierCellNaturalLeft W c n :=
        Nat.le_of_not_gt hnot
      have hleft_mem : pk ∈ pascalPrimePowerPairSupportUpTo
          (cfzp040CarrierCellNaturalLeft W c n) := by
        rw [mem_pascalPrimePowerPairSupportUpTo_iff]
        refine ⟨mem_pascalPrimeCoordinateSupportUpTo_iff.mpr
          ⟨hp, hpk_le_left⟩, ?_, ?_⟩
        · have hA2 : 2 ≤ cfzp040CarrierCellNaturalLeft W c n :=
            hp.two_le.trans hpk_le_left
          omega
        · simpa [hzero] using hpk_le_left
      exact hleft hleft_mem
    have hraw : pk.1 ∈ cfzp040RawPrimeCarrierCellSupport W c n := by
      change pk.1 ∈ (Finset.Ioc
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n)).filter Nat.Prime
      exact Finset.mem_filter.mpr ⟨
        Finset.mem_Ioc.mpr ⟨hpk_gt_left, hcoord.2⟩, hp⟩
    have hcell := (cfzp040RawPrimeCarrierCellSupport_mem_iff hp).mp hraw
    have hcell' :
        cfzp039CarrierCellLeft W c n < Real.log (pk.1 : ℝ) ∧
          Real.log (pk.1 : ℝ) ≤ cfzp039CarrierCellRight W c n :=
      ⟨hcell.2.1, hcell.2.2⟩
    have hpk' : pk ∈ cfzp034EligiblePrimeAxisPairBlockSupport ε
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) := hpk
    exact Finset.mem_filter.mpr ⟨hpk', hcell'⟩
  · intro hpk
    exact cfzp039PrimeAxisCarrierCellPairSupport_subset_eligible W hpk

/-! The two 039 cell ledgers can be addressed by the full eligible block. -/

/-- Eligible leading mass written using the natural cell block. -/
noncomputable def cfzp041EligibleLeadingCarrierMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  cfzp039PrimeAxisLeadingCarrierMassOn ε W
    (cfzp034EligiblePrimeAxisPairBlockSupport ε
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n))

/-- Eligible remainder debt written using the natural cell block. -/
noncomputable def cfzp041EligibleRemainderDebt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  cfzp039PrimeAxisRemainderDebtOn ε W
    (cfzp034EligiblePrimeAxisPairBlockSupport ε
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n))

theorem cfzp041EligibleLeadingCarrierMass_eq_cellMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) :
    cfzp041EligibleLeadingCarrierMass ε W c n =
      cfzp039PrimeAxisLeadingCarrierCellMass ε W c n
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) := by
  unfold cfzp041EligibleLeadingCarrierMass
    cfzp039PrimeAxisLeadingCarrierCellMass
  rw [cfzp041EligiblePrimeAxisBlockSupport_eq_carrierCellSupport]

theorem cfzp041EligibleRemainderDebt_eq_cellDebt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) :
    cfzp041EligibleRemainderDebt ε W c n =
      cfzp039PrimeAxisRemainderCellDebt ε W c n
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) := by
  unfold cfzp041EligibleRemainderDebt cfzp039PrimeAxisRemainderCellDebt
  rw [cfzp041EligiblePrimeAxisBlockSupport_eq_carrierCellSupport]

/-! ## Gate C: cell mass decomposition -/

theorem cfzp041CellMass_eq_smooth_add_discrepancy
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hcell : max (3 * ε) 1 ≤ cfzp039CarrierCellLeft W c n)
    (hf_diff : ∀ t ∈ Set.Icc
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n),
      DifferentiableAt ℝ (cfzp040PrimeAxisCarrierTestFunction ε W) t)
    (hf_int : IntegrableOn
      (deriv (cfzp040PrimeAxisCarrierTestFunction ε W)) (Set.Icc
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)))
    (hM_int : IntegrableOn
      (fun t => deriv (cfzp040PrimeAxisCarrierTestFunction ε W) t *
        cfzp040PrimeCountingSmoothModel t) (Set.Ioc
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n)))
    (hD_int : IntegrableOn
      (fun t => deriv (cfzp040PrimeAxisCarrierTestFunction ε W) t *
        cfzp040PrimeCountingDiscrepancy t) (Set.Ioc
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n))) :
    cfzp039PrimeAxisLeadingCarrierCellMass ε W c n
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) =
      cfzp040SmoothAbelCarrierModel ε W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) +
        cfzp040PrimeCountingDiscrepancyFunctional ε W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) := by
  calc
    cfzp039PrimeAxisLeadingCarrierCellMass ε W c n
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) =
        cfzp040PrimeCarrierSumIoc ε W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) :=
      (cfzp040PrimeCarrierSumIoc_cellEndpoints_eq_cfzp039CellMass
        hε W c n hcell).symm
    _ = cfzp040SmoothAbelCarrierModel ε W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) +
        cfzp040PrimeCountingDiscrepancyFunctional ε W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) :=
      cfzp040PrimeCarrierSumIoc_eq_smooth_add_discrepancy
        (ha := (cfzp040CarrierCellExpLeft_pos W c n).le)
        (hab := (cfzp040CarrierCellExpLeft_lt_right W c n).le)
        W hf_diff hf_int hM_int hD_int

/-! ## Gate D: discrepancy functional debt -/

/-- Absolute finite debt carried by one cell's discrepancy functional. -/
noncomputable def cfzp041PrimeCountingDiscrepancyCellDebt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  |cfzp040PrimeCountingDiscrepancyFunctional ε W
      (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n)|

theorem cfzp041PrimeCountingDiscrepancyCellDebt_nonneg
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) :
    0 ≤ cfzp041PrimeCountingDiscrepancyCellDebt ε W c n := by
  exact abs_nonneg _

theorem cfzp041PrimeCountingDiscrepancyCellDebt_lower
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) :
    -cfzp041PrimeCountingDiscrepancyCellDebt ε W c n ≤
      cfzp040PrimeCountingDiscrepancyFunctional ε W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) := by
  exact neg_abs_le _

/-- An external finite bound for one cell's discrepancy functional. -/
def Cfzp041PrimeCountingDiscrepancyFunctionalBoundAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) (D : ℝ) : Prop :=
  |cfzp040PrimeCountingDiscrepancyFunctional ε W
      (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n)| ≤ D

theorem cfzp041PrimeCountingDiscrepancyFunctional_ge_neg
    {ε D : ℝ} (hD : Cfzp041PrimeCountingDiscrepancyFunctionalBoundAt
      ε W c n D) :
    -D ≤ cfzp040PrimeCountingDiscrepancyFunctional ε W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) := by
  exact (neg_le_neg hD).trans (neg_abs_le _)

/-! ## Gate E: the smooth-minus-debt lower bound -/

theorem cfzp041SmoothSubDiscrepancy_le_cellMass
    {ε D : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hcell : max (3 * ε) 1 ≤ cfzp039CarrierCellLeft W c n)
    (hf_diff : ∀ t ∈ Set.Icc
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n),
      DifferentiableAt ℝ (cfzp040PrimeAxisCarrierTestFunction ε W) t)
    (hf_int : IntegrableOn
      (deriv (cfzp040PrimeAxisCarrierTestFunction ε W)) (Set.Icc
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)))
    (hM_int : IntegrableOn
      (fun t => deriv (cfzp040PrimeAxisCarrierTestFunction ε W) t *
        cfzp040PrimeCountingSmoothModel t) (Set.Ioc
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n)))
    (hD_int : IntegrableOn
      (fun t => deriv (cfzp040PrimeAxisCarrierTestFunction ε W) t *
        cfzp040PrimeCountingDiscrepancy t) (Set.Ioc
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n)))
    (hD : Cfzp041PrimeCountingDiscrepancyFunctionalBoundAt
      ε W c n D) :
    cfzp040SmoothAbelCarrierModel ε W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) - D ≤
      cfzp039PrimeAxisLeadingCarrierCellMass ε W c n
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) := by
  have hsplit := cfzp041CellMass_eq_smooth_add_discrepancy
    hε W c n hcell hf_diff hf_int hM_int hD_int
  have hlower := cfzp041PrimeCountingDiscrepancyFunctional_ge_neg hD
  rw [hsplit]
  linarith

/-! ## Gate F: cell reservoir to radial endpoint -/

theorem cfzp041SmoothDiscrepancyCellReservoir_implies_radialContactDeficit_le
    {ε η D : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hcell : max (3 * ε) 1 ≤ cfzp039CarrierCellLeft W c n)
    (hf_diff : ∀ t ∈ Set.Icc
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n),
      DifferentiableAt ℝ (cfzp040PrimeAxisCarrierTestFunction ε W) t)
    (hf_int : IntegrableOn
      (deriv (cfzp040PrimeAxisCarrierTestFunction ε W)) (Set.Icc
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)))
    (hM_int : IntegrableOn
      (fun t => deriv (cfzp040PrimeAxisCarrierTestFunction ε W) t *
        cfzp040PrimeCountingSmoothModel t) (Set.Ioc
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n)))
    (hD_int : IntegrableOn
      (fun t => deriv (cfzp040PrimeAxisCarrierTestFunction ε W) t *
        cfzp040PrimeCountingDiscrepancy t) (Set.Ioc
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n)))
    (hD : Cfzp041PrimeCountingDiscrepancyFunctionalBoundAt
      ε W c n D)
    (hreservoir :
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W
          (cfzp040CarrierCellNaturalLeft W c n) +
        cfzp039PrimeAxisRemainderCellDebt ε W c n
          (cfzp040CarrierCellNaturalLeft W c n)
          (cfzp040CarrierCellNaturalRight W c n) +
        cfzp034ExceptionalPrimeAxisReferenceMass ε W
          (cfzp040CarrierCellNaturalLeft W c n)
          (cfzp040CarrierCellNaturalRight W c n) +
        cfzp034HigherPowerReferenceMass ε W
          (cfzp040CarrierCellNaturalLeft W c n)
          (cfzp040CarrierCellNaturalRight W c n) + D ≤
      cfzp040SmoothAbelCarrierModel ε W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) + η) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W
      (cfzp040CarrierCellNaturalRight W c n) ≤ η := by
  let A := cfzp040CarrierCellNaturalLeft W c n
  let B := cfzp040CarrierCellNaturalRight W c n
  have hAB : A ≤ B := cfzp041CarrierCellNaturalLeft_le_right W c n
  have hcellLower := cfzp041SmoothSubDiscrepancy_le_cellMass
    hε W c n hcell hf_diff hf_int hM_int hD_int hD
  have hdebt := cfzp041EligibleRemainderDebt_eq_cellDebt ε W c n
  have hmass := cfzp041EligibleLeadingCarrierMass_eq_cellMass ε W c n
  have hreservoir0 :
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A +
          cfzp039PrimeAxisRemainderCellDebt ε W c n A B +
          cfzp034ExceptionalPrimeAxisReferenceMass ε W A B +
          cfzp034HigherPowerReferenceMass ε W A B + D ≤
        cfzp040SmoothAbelCarrierModel ε W
            (cfzp040CarrierCellExpLeft W c n)
            (cfzp040CarrierCellExpRight W c n) + η := by
    simpa [A, B] using hreservoir
  have hdebt' :
      cfzp039PrimeAxisRemainderDebtOn ε W
          (cfzp034EligiblePrimeAxisPairBlockSupport ε A B) =
        cfzp039PrimeAxisRemainderCellDebt ε W c n A B := by
    simpa [cfzp041EligibleRemainderDebt, A, B] using hdebt
  have hmass' :
      cfzp039PrimeAxisLeadingCarrierMassOn ε W
          (cfzp034EligiblePrimeAxisPairBlockSupport ε A B) =
        cfzp039PrimeAxisLeadingCarrierCellMass ε W c n A B := by
    simpa [cfzp041EligibleLeadingCarrierMass, A, B] using hmass
  have hreservoir' :
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A +
          cfzp039PrimeAxisRemainderDebtOn ε W
            (cfzp034EligiblePrimeAxisPairBlockSupport ε A B) +
          cfzp034ExceptionalPrimeAxisReferenceMass ε W A B +
          cfzp034HigherPowerReferenceMass ε W A B ≤
        cfzp039PrimeAxisLeadingCarrierMassOn ε W
            (cfzp034EligiblePrimeAxisPairBlockSupport ε A B) + η := by
    rw [hdebt', hmass']
    linarith [hreservoir0, hcellLower]
  exact cfzp039LeadingCarrierReservoir_implies_radialContactDeficit_le
    hε hε2 W hAB hreservoir'

/-! ## Explicit open boundaries -/

/-!
No theorem below supplies a prime-distribution estimate or removes the
exceptional and higher-power ledgers.  Those boundaries remain named. -/
inductive Cfzp041PrimeAxisSmoothDiscrepancyCellReservoirGap : Prop
  | noSmoothAbelCellPositiveLowerBound
  | noPrimeCountingDiscrepancyFunctionalDecayProvider
  | noPointwiseDiscrepancyToFunctionalBound
  | noSmoothAbelDensityIntegralReduction
  | noLogCoordinateDensityIntegralAdapter
  | noCarrierCellAsymptoticDominanceProvider
  | noExceptionalPrimeAxisResidualElimination
  | noHigherPrimePowerResidualElimination

end DkMath.RH.CFBRCProjection
