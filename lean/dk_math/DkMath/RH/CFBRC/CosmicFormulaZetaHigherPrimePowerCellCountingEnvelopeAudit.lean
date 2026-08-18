/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaHigherPrimePowerSigmaTailEnvelopeAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaHigherPrimePowerCellCountingEnvelopeAudit"

/-!
# CFZP-046: deterministic cell counting for higher prime powers

This module bounds the finite higher-power sigma tail by a rectangular box of
all natural bases and exponents.  The deliberate overcount is distribution-free:
no assertion about the density of primes is used.  The resulting floor-free
exponential envelope is then transported to the CFZP-045 radial budget.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open MeasureTheory
open Set

private theorem cfzp046_two_pow_succ_gt
    (k : ℕ) : k < 2 ^ (k + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hpos : 0 < 2 ^ (k + 1) := by positivity
      have hstep : k + 1 < 2 ^ (k + 1) * 2 := by omega
      simpa [Nat.pow_succ, Nat.add_assoc] using hstep

/-! ## Gates A-C: cell coordinates and deterministic caps -/

/-- A higher-power pair has its log-coordinate inside the natural carrier cell. -/
theorem cfzp046HigherPowerPairLogCoordinate_mem_carrierCell
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    {pk : ℕ × ℕ}
    (hpk : pk ∈ cfzp034HigherPowerPairBlockSupport
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n)) :
    cfzp039CarrierCellLeft W c n <
        cfzp033PrimePowerLogCoordinate pk.1 (pk.2 + 1) ∧
      cfzp033PrimePowerLogCoordinate pk.1 (pk.2 + 1) ≤
        cfzp039CarrierCellRight W c n := by
  classical
  have hblock := (Finset.mem_filter.mp hpk).1
  have hright : pk ∈ pascalPrimePowerPairSupportUpTo
      (cfzp040CarrierCellNaturalRight W c n) :=
    (Finset.mem_sdiff.mp hblock).1
  have hleft : pk ∉ pascalPrimePowerPairSupportUpTo
      (cfzp040CarrierCellNaturalLeft W c n) :=
    (Finset.mem_sdiff.mp hblock).2
  have hs := mem_pascalPrimePowerPairSupportUpTo_iff.mp hright
  have hp : Nat.Prime pk.1 :=
    (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hs.1).1
  have hj : 0 < pk.2 + 1 := by omega
  have hqpos : 0 < pk.1 ^ (pk.2 + 1) := Nat.pow_pos hp.pos
  have hqne : pk.1 ^ (pk.2 + 1) ≠ 0 := hqpos.ne'
  have hqgtA : cfzp040CarrierCellNaturalLeft W c n <
      pk.1 ^ (pk.2 + 1) := by
    by_contra hnot
    have hqleA : pk.1 ^ (pk.2 + 1) ≤
        cfzp040CarrierCellNaturalLeft W c n := Nat.le_of_not_gt hnot
    have hpow_exp : pk.2 < pk.1 ^ (pk.2 + 1) := by
      exact (cfzp046_two_pow_succ_gt pk.2).trans_le
        (Nat.pow_le_pow_left hp.two_le (pk.2 + 1))
    have hbase_le : pk.1 ≤ pk.1 ^ (pk.2 + 1) := by
      simpa [pow_one] using
        (Nat.pow_le_pow_right hp.one_lt.le (by omega : 1 ≤ pk.2 + 1))
    have hleft_mem : pk ∈ pascalPrimePowerPairSupportUpTo
        (cfzp040CarrierCellNaturalLeft W c n) := by
      rw [mem_pascalPrimePowerPairSupportUpTo_iff]
      refine ⟨mem_pascalPrimeCoordinateSupportUpTo_iff.mpr
          ⟨hp, le_trans hbase_le hqleA⟩,
        lt_of_lt_of_le hpow_exp hqleA, hqleA⟩
    exact hleft hleft_mem
  have hqL : cfzp040CarrierCellExpLeft W c n <
      ((pk.1 ^ (pk.2 + 1) : ℕ) : ℝ) := by
    apply (Nat.floor_lt' hqne).mp
    simpa [cfzp040CarrierCellNaturalLeft] using hqgtA
  have hqR : ((pk.1 ^ (pk.2 + 1) : ℕ) : ℝ) ≤
      cfzp040CarrierCellExpRight W c n := by
    apply (Nat.le_floor_iff' hqne).mp
    simpa [cfzp040CarrierCellNaturalRight] using hs.2.2
  have hlogL : cfzp039CarrierCellLeft W c n <
      Real.log ((pk.1 ^ (pk.2 + 1) : ℕ) : ℝ) := by
    have hqposR : (0 : ℝ) < ((pk.1 ^ (pk.2 + 1) : ℕ) : ℝ) := by
      exact_mod_cast hqpos
    apply Real.exp_lt_exp.mp
    rw [Real.exp_log hqposR]
    simpa [cfzp040CarrierCellExpLeft] using hqL
  have hlogR : Real.log ((pk.1 ^ (pk.2 + 1) : ℕ) : ℝ) ≤
      cfzp039CarrierCellRight W c n := by
    have hqposR : (0 : ℝ) < ((pk.1 ^ (pk.2 + 1) : ℕ) : ℝ) := by
      exact_mod_cast hqpos
    apply Real.exp_le_exp.mp
    rw [Real.exp_log hqposR]
    simpa [cfzp040CarrierCellExpRight] using hqR
  have hcoord : cfzp033PrimePowerLogCoordinate pk.1 (pk.2 + 1) =
      Real.log ((pk.1 ^ (pk.2 + 1) : ℕ) : ℝ) := by
    simp [cfzp033PrimePowerLogCoordinate, Nat.cast_pow, Real.log_pow]
  exact ⟨by simpa [hcoord] using hlogL, by simpa [hcoord] using hlogR⟩

/-- The right endpoint is the left endpoint plus one carrier period. -/
theorem cfzp046CarrierCellRight_eq_left_add_period
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) :
    cfzp039CarrierCellRight W c n =
      cfzp039CarrierCellLeft W c n +
        cfzp036PrimeAxisCarrierPeriod W := by
  unfold cfzp039CarrierCellRight cfzp039CarrierCellLeft
  norm_num [Nat.cast_add]
  ring

/-- The natural cap for the base of a higher prime power in one cell. -/
noncomputable def cfzp046HigherPowerBaseCap
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℕ :=
  ⌊Real.exp (cfzp039CarrierCellRight W c n / 2)⌋₊

/-- Every higher-power base lies below the exponential right-end cap. -/
theorem cfzp046HigherPower_base_le_baseCap
    {ε : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (_hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n)
    {pk : ℕ × ℕ}
    (hpk : pk ∈ cfzp034HigherPowerPairBlockSupport
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n)) :
    pk.1 ≤ cfzp046HigherPowerBaseCap W c n := by
  have hcoord := cfzp046HigherPowerPairLogCoordinate_mem_carrierCell W c n hpk
  have hp := cfzp045HigherPower_basePrime hpk
  have hj := cfzp045HigherPowerActualExponent_two_le hpk
  have hlogp : 0 < Real.log (pk.1 : ℝ) :=
    Real.log_pos (by exact_mod_cast hp.one_lt)
  have hjr : (2 : ℝ) ≤ pk.2 + 1 := by exact_mod_cast hj
  have h2log : 2 * Real.log (pk.1 : ℝ) ≤
      cfzp033PrimePowerLogCoordinate pk.1 (pk.2 + 1) := by
    unfold cfzp033PrimePowerLogCoordinate
    norm_num [Nat.cast_add]
    nlinarith
  have hlog_le : Real.log (pk.1 : ℝ) ≤
      cfzp039CarrierCellRight W c n / 2 := by
    linarith [hcoord.2, h2log]
  have hp_pos : (0 : ℝ) < (pk.1 : ℝ) := by exact_mod_cast hp.pos
  have hp_le_exp : (pk.1 : ℝ) ≤
      Real.exp (cfzp039CarrierCellRight W c n / 2) := by
    have hexp := Real.exp_le_exp.mpr hlog_le
    simpa [Real.exp_log hp_pos] using hexp
  apply (Nat.le_floor_iff' hp.ne_zero).mpr
  simpa [cfzp046HigherPowerBaseCap] using hp_le_exp

/-- The natural cap for the actual exponent in one cell. -/
noncomputable def cfzp046HigherPowerExponentCap
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℕ :=
  ⌊cfzp039CarrierCellRight W c n / Real.log 2⌋₊

/-- Every actual higher-power exponent lies below the logarithmic cap. -/
theorem cfzp046HigherPower_actualExponent_le_exponentCap
    {ε : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (_hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n)
    {pk : ℕ × ℕ}
    (hpk : pk ∈ cfzp034HigherPowerPairBlockSupport
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n)) :
    pk.2 + 1 ≤ cfzp046HigherPowerExponentCap W c n := by
  have hcoord := cfzp046HigherPowerPairLogCoordinate_mem_carrierCell W c n hpk
  have hp := cfzp045HigherPower_basePrime hpk
  have hj := cfzp045HigherPowerActualExponent_two_le hpk
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog2le : Real.log (2 : ℝ) ≤ Real.log (pk.1 : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hp.two_le
  have hjr : (0 : ℝ) ≤ pk.2 + 1 := by positivity
  have hprod : (pk.2 + 1 : ℝ) * Real.log (2 : ℝ) ≤
      cfzp033PrimePowerLogCoordinate pk.1 (pk.2 + 1) := by
    unfold cfzp033PrimePowerLogCoordinate
    simpa [Nat.cast_add] using
      (mul_le_mul_of_nonneg_left hlog2le hjr)
  have hjR : (pk.2 + 1 : ℝ) * Real.log (2 : ℝ) ≤
      cfzp039CarrierCellRight W c n := hprod.trans hcoord.2
  have hj_le : (pk.2 + 1 : ℝ) ≤
      cfzp039CarrierCellRight W c n / Real.log (2 : ℝ) := by
    exact (le_div_iff₀ hlog2).2 (by simpa [mul_comm] using hjR)
  apply (Nat.le_floor_iff' (by omega : pk.2 + 1 ≠ 0)).mpr
  simpa [cfzp046HigherPowerExponentCap] using hj_le

/-! ## Gate D: the deterministic rectangular box -/

/-- A coarse box containing every base/exponent pair in the cell. -/
noncomputable def cfzp046HigherPowerBoundingBox
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (cfzp046HigherPowerBaseCap W c n + 1)).product
    (Finset.range (cfzp046HigherPowerExponentCap W c n + 1))

/-- The higher-power cell support is contained in the natural rectangular box. -/
theorem cfzp046HigherPowerPairBlockSupport_subset_boundingBox
    {ε : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n) :
    cfzp034HigherPowerPairBlockSupport
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) ⊆
      cfzp046HigherPowerBoundingBox W c n := by
  intro pk hpk
  change pk ∈
      (Finset.range (cfzp046HigherPowerBaseCap W c n + 1)).product
        (Finset.range (cfzp046HigherPowerExponentCap W c n + 1))
  have hbase := cfzp046HigherPower_base_le_baseCap W c n hLate hpk
  have hbase' : pk.1 < cfzp046HigherPowerBaseCap W c n + 1 := by
    exact Nat.lt_succ_of_le hbase
  have hexp := cfzp046HigherPower_actualExponent_le_exponentCap W c n
    hLate hpk
  have hexp0 : pk.2 < cfzp046HigherPowerExponentCap W c n :=
    Nat.lt_of_succ_le hexp
  have hexp' : pk.2 < cfzp046HigherPowerExponentCap W c n + 1 := by
    omega
  exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hbase',
    Finset.mem_range.mpr hexp'⟩

/-- The number of higher-power pairs is bounded by the box cardinality. -/
theorem cfzp046HigherPowerPairBlockSupport_card_le
    {ε : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n) :
    (cfzp034HigherPowerPairBlockSupport
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n)).card ≤
      (cfzp046HigherPowerBaseCap W c n + 1) *
        (cfzp046HigherPowerExponentCap W c n + 1) := by
  have hsub := cfzp046HigherPowerPairBlockSupport_subset_boundingBox
    W c n hLate
  have hcard := Finset.card_le_card hsub
  simpa [cfzp046HigherPowerBoundingBox] using hcard

/-! ## Gates E-F: uniform terms and the finite tail envelope -/

/-- Each higher-power sigma term is uniformly bounded on its cell. -/
theorem cfzp046HigherPowerSigmaTailTerm_le_cellUniform
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    {pk : ℕ × ℕ}
    (hpk : pk ∈ cfzp034HigherPowerPairBlockSupport
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n)) :
    (cfzp034PrimeAxisSigmaWeight W pk.1) ^ (pk.2 + 1) /
        ((pk.2 + 1 : ℕ) : ℝ) ≤
      Real.exp (-(W.rectangle.σ) *
          cfzp039CarrierCellLeft W c n) / 2 := by
  have hcoord := cfzp046HigherPowerPairLogCoordinate_mem_carrierCell W c n hpk
  have hj := cfzp045HigherPowerActualExponent_two_le hpk
  have hσ : 0 < W.rectangle.σ := by
    linarith [cfzp034_rectangleSigma_gt_half W]
  have hpow := cfzp034PrimePowerSigmaWeight_eq_primeAxisWeight_pow
    W pk.1 (pk.2 + 1)
  have hexp : Real.exp (-(W.rectangle.σ) *
      cfzp033PrimePowerLogCoordinate pk.1 (pk.2 + 1)) ≤
      Real.exp (-(W.rectangle.σ) * cfzp039CarrierCellLeft W c n) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hcoord.1]
  have hu_nonneg : 0 ≤ Real.exp (-(W.rectangle.σ) *
      cfzp033PrimePowerLogCoordinate pk.1 (pk.2 + 1)) :=
    (Real.exp_pos _).le
  have hjr : (2 : ℝ) ≤ pk.2 + 1 := by exact_mod_cast hj
  have hjpos : (0 : ℝ) < pk.2 + 1 := by positivity
  calc
    (cfzp034PrimeAxisSigmaWeight W pk.1) ^ (pk.2 + 1) /
          ((pk.2 + 1 : ℕ) : ℝ) =
        Real.exp (-(W.rectangle.σ) *
          cfzp033PrimePowerLogCoordinate pk.1 (pk.2 + 1)) /
          (pk.2 + 1 : ℝ) := by
            rw [hpow]
            norm_num [Nat.cast_add]
    _ ≤ Real.exp (-(W.rectangle.σ) *
          cfzp033PrimePowerLogCoordinate pk.1 (pk.2 + 1)) / 2 := by
      apply (div_le_iff₀ hjpos).2
      nlinarith
    _ ≤ Real.exp (-(W.rectangle.σ) * cfzp039CarrierCellLeft W c n) / 2 :=
      div_le_div_of_nonneg_right hexp (by norm_num)

/-- The finite higher-power tail is bounded by its rectangular-card envelope. -/
theorem cfzp046HigherPowerSigmaTail_le_cardEnvelope
    {ε : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n) :
    cfzp045HigherPowerSigmaTail W
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) ≤
      (((cfzp046HigherPowerBaseCap W c n + 1) *
          (cfzp046HigherPowerExponentCap W c n + 1) : ℕ) : ℝ) *
        (Real.exp (-(W.rectangle.σ) *
          cfzp039CarrierCellLeft W c n) / 2) := by
  let S := cfzp034HigherPowerPairBlockSupport
    (cfzp040CarrierCellNaturalLeft W c n)
    (cfzp040CarrierCellNaturalRight W c n)
  let E := Real.exp (-(W.rectangle.σ) * cfzp039CarrierCellLeft W c n) / 2
  have hsum : ∑ pk ∈ S,
      (cfzp034PrimeAxisSigmaWeight W pk.1) ^ (pk.2 + 1) /
        ((pk.2 + 1 : ℕ) : ℝ) ≤ ∑ _pk ∈ S, E := by
    apply Finset.sum_le_sum
    intro pk hpk
    exact cfzp046HigherPowerSigmaTailTerm_le_cellUniform W c n hpk
  have hsum_const : (∑ _pk ∈ S, E) = (S.card : ℝ) * E := by
    simp
  have hcard := cfzp046HigherPowerPairBlockSupport_card_le W c n hLate
  have hcardR : (S.card : ℝ) ≤
      (((cfzp046HigherPowerBaseCap W c n + 1) *
          (cfzp046HigherPowerExponentCap W c n + 1) : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hE : 0 ≤ E := by positivity
  have hcardMul : (S.card : ℝ) * E ≤
      (((cfzp046HigherPowerBaseCap W c n + 1) *
          (cfzp046HigherPowerExponentCap W c n + 1) : ℕ) : ℝ) * E :=
    mul_le_mul_of_nonneg_right hcardR hE
  unfold cfzp045HigherPowerSigmaTail
  calc
    ∑ pk ∈ cfzp034HigherPowerPairBlockSupport
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n),
        (cfzp034PrimeAxisSigmaWeight W pk.1) ^ (pk.2 + 1) /
          ((pk.2 + 1 : ℕ) : ℝ) =
      ∑ pk ∈ S,
        (cfzp034PrimeAxisSigmaWeight W pk.1) ^ (pk.2 + 1) /
          ((pk.2 + 1 : ℕ) : ℝ) := by rfl
    _ ≤ ∑ _pk ∈ S, E := hsum
    _ = (S.card : ℝ) * E := hsum_const
    _ ≤ (((cfzp046HigherPowerBaseCap W c n + 1) *
          (cfzp046HigherPowerExponentCap W c n + 1) : ℕ) : ℝ) * E := hcardMul
    _ = (((cfzp046HigherPowerBaseCap W c n + 1) *
          (cfzp046HigherPowerExponentCap W c n + 1) : ℕ) : ℝ) *
        (Real.exp (-(W.rectangle.σ) *
          cfzp039CarrierCellLeft W c n) / 2) := by rfl

/-! ## Gates G-I: floor-free exponential envelope and radial adapter -/

/-- The floor-free real exponential envelope for one carrier cell. -/
noncomputable def cfzp046HigherPowerSigmaTailExponentialEnvelope
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  Real.exp (cfzp039CarrierCellRight W c n / 2) *
    (cfzp039CarrierCellRight W c n / Real.log 2 + 1) *
    Real.exp (-(W.rectangle.σ) * cfzp039CarrierCellLeft W c n)

/-- The finite tail is bounded by the floor-free exponential envelope. -/
theorem cfzp046HigherPowerSigmaTail_le_exponentialEnvelope
    {ε : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n) :
    cfzp045HigherPowerSigmaTail W
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) ≤
      cfzp046HigherPowerSigmaTailExponentialEnvelope W c n := by
  let R := cfzp039CarrierCellRight W c n
  let U := cfzp039CarrierCellLeft W c n
  have hcard := cfzp046HigherPowerSigmaTail_le_cardEnvelope W c n hLate
  have hU2 : 2 ≤ U := by
    dsimp [U]
    exact cfzp044_two_le_of_radialLate hLate
  have hUR : U ≤ R := by
    dsimp [U, R]
    unfold cfzp039CarrierCellLeft cfzp039CarrierCellRight
    norm_num [Nat.cast_add]
    nlinarith [cfzp036PrimeAxisCarrierPeriod_pos W]
  have hbase : ((cfzp046HigherPowerBaseCap W c n + 1 : ℕ) : ℝ) ≤
      2 * Real.exp (R / 2) := by
    have hfloor : (cfzp046HigherPowerBaseCap W c n : ℝ) ≤
        Real.exp (R / 2) := by
      exact Nat.floor_le (Real.exp_pos _).le
    rw [Nat.cast_add, Nat.cast_one]
    have hR2 : (2 : ℝ) ≤ R := by linarith
    have hexp_one : (1 : ℝ) ≤ Real.exp (R / 2) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    nlinarith [hfloor, hexp_one]
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hRpos : 0 ≤ R := by linarith
  have hquot : 0 ≤ R / Real.log 2 := by positivity
  have hexponent :
      ((cfzp046HigherPowerExponentCap W c n + 1 : ℕ) : ℝ) ≤
        R / Real.log 2 + 1 := by
    have hfloor : (cfzp046HigherPowerExponentCap W c n : ℝ) ≤
        R / Real.log 2 := by
      exact Nat.floor_le hquot
    dsimp [R]
    dsimp [cfzp046HigherPowerExponentCap] at hfloor ⊢
    norm_num at hfloor ⊢
    linarith
  have hprod :
      (((cfzp046HigherPowerBaseCap W c n + 1) *
          (cfzp046HigherPowerExponentCap W c n + 1) : ℕ) : ℝ) ≤
        (2 * Real.exp (R / 2)) * (R / Real.log 2 + 1) := by
    rw [Nat.cast_mul]
    exact mul_le_mul hbase hexponent (by positivity) (by positivity)
  have hnonneg : 0 ≤ Real.exp (-(W.rectangle.σ) * U) / 2 := by positivity
  calc
    cfzp045HigherPowerSigmaTail W
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) ≤
      (((cfzp046HigherPowerBaseCap W c n + 1) *
          (cfzp046HigherPowerExponentCap W c n + 1) : ℕ) : ℝ) *
        (Real.exp (-(W.rectangle.σ) * U) / 2) := by
          simpa [U] using hcard
    _ ≤ (2 * Real.exp (R / 2)) *
        (R / Real.log 2 + 1) *
          (Real.exp (-(W.rectangle.σ) * U) / 2) := by
          exact mul_le_mul_of_nonneg_right hprod hnonneg
    _ = cfzp046HigherPowerSigmaTailExponentialEnvelope W c n := by
      dsimp [cfzp046HigherPowerSigmaTailExponentialEnvelope, R, U]
      ring

/-- The exponential envelope in canonical period/coordinate normal form. -/
theorem cfzp046HigherPowerSigmaTailExponentialEnvelope_eq_normalForm
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) :
    cfzp046HigherPowerSigmaTailExponentialEnvelope W c n =
      Real.exp (cfzp036PrimeAxisCarrierPeriod W / 2) *
        (cfzp039CarrierCellRight W c n / Real.log 2 + 1) *
      Real.exp ((1 / 2 - W.rectangle.σ) *
          cfzp039CarrierCellLeft W c n) := by
  have hR := cfzp046CarrierCellRight_eq_left_add_period W c n
  unfold cfzp046HigherPowerSigmaTailExponentialEnvelope
  rw [hR]
  have hexp :
      Real.exp ((cfzp039CarrierCellLeft W c n +
          cfzp036PrimeAxisCarrierPeriod W) / 2) *
          Real.exp (-(W.rectangle.σ) * cfzp039CarrierCellLeft W c n) =
        Real.exp (cfzp036PrimeAxisCarrierPeriod W / 2) *
          Real.exp ((1 / 2 - W.rectangle.σ) *
            cfzp039CarrierCellLeft W c n) := by
    calc
      Real.exp ((cfzp039CarrierCellLeft W c n +
          cfzp036PrimeAxisCarrierPeriod W) / 2) *
            Real.exp (-(W.rectangle.σ) * cfzp039CarrierCellLeft W c n) =
          Real.exp ((cfzp039CarrierCellLeft W c n +
            cfzp036PrimeAxisCarrierPeriod W) / 2 +
              (-(W.rectangle.σ) * cfzp039CarrierCellLeft W c n)) :=
        (Real.exp_add _ _).symm
      _ = Real.exp (cfzp036PrimeAxisCarrierPeriod W / 2 +
            ((1 / 2 - W.rectangle.σ) * cfzp039CarrierCellLeft W c n)) := by
        congr 1
        ring
      _ = Real.exp (cfzp036PrimeAxisCarrierPeriod W / 2) *
          Real.exp ((1 / 2 - W.rectangle.σ) *
            cfzp039CarrierCellLeft W c n) := Real.exp_add _ _
  calc
    Real.exp ((cfzp039CarrierCellLeft W c n +
        cfzp036PrimeAxisCarrierPeriod W) / 2) *
        ((cfzp039CarrierCellLeft W c n +
          cfzp036PrimeAxisCarrierPeriod W) / Real.log 2 + 1) *
        Real.exp (-(W.rectangle.σ) * cfzp039CarrierCellLeft W c n) =
      (Real.exp ((cfzp039CarrierCellLeft W c n +
        cfzp036PrimeAxisCarrierPeriod W) / 2) *
        Real.exp (-(W.rectangle.σ) * cfzp039CarrierCellLeft W c n)) *
        ((cfzp039CarrierCellLeft W c n +
          cfzp036PrimeAxisCarrierPeriod W) / Real.log 2 + 1) := by ring
    _ = Real.exp (cfzp036PrimeAxisCarrierPeriod W / 2) *
        Real.exp ((1 / 2 - W.rectangle.σ) *
          cfzp039CarrierCellLeft W c n) *
        ((cfzp039CarrierCellLeft W c n +
          cfzp036PrimeAxisCarrierPeriod W) / Real.log 2 + 1) := by rw [hexp]
    _ = Real.exp (cfzp036PrimeAxisCarrierPeriod W / 2) *
        ((cfzp039CarrierCellLeft W c n +
          cfzp036PrimeAxisCarrierPeriod W) / Real.log 2 + 1) *
        Real.exp ((1 / 2 - W.rectangle.σ) *
          cfzp039CarrierCellLeft W c n) := by ring

/-- The sigma exponent is strictly on the decaying side of one half. -/
theorem cfzp046_half_sub_rectangleSigma_neg
    (W : PascalCenteredXiResidueTransportWindow) :
    (1 / 2 : ℝ) - W.rectangle.σ < 0 := by
  linarith [cfzp034_rectangleSigma_gt_half W]

/-- The raw higher-power mass is bounded by the explicit exponential envelope. -/
theorem cfzp046CarrierCellHigherPowerReferenceMass_le_exponentialEnvelope
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (c : ℝ) (n : ℕ)
    (hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n) :
    cfzp034HigherPowerReferenceMass ε W
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) ≤
      cfzp045HigherPowerReferenceMassConstant ε W *
        cfzp046HigherPowerSigmaTailExponentialEnvelope W c n := by
  exact (cfzp045CarrierCellHigherPowerReferenceMass_le_sigmaTail
    hε hε2 W hsub c n hLate).trans
    (mul_le_mul_of_nonneg_left
      (cfzp046HigherPowerSigmaTail_le_exponentialEnvelope W c n hLate)
      (by
        unfold cfzp045HigherPowerReferenceMassConstant
        positivity))

/-- The 046 budget with the finite tail replaced by its exponential envelope. -/
def Cfzp046ExponentialEnvelopeExplicitSmoothMarginBudgetAt
    (ε η D : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : Prop :=
  pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W
      (cfzp040CarrierCellNaturalLeft W c n) +
    cfzp039PrimeAxisRemainderCellDebt ε W c n
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n) +
    cfzp045HigherPowerReferenceMassConstant ε W *
      cfzp046HigherPowerSigmaTailExponentialEnvelope W c n + D ≤
    cfzp044ExplicitSmoothMargin ε W c n + η

/-- An explicit-envelope budget implies the right radial contact bound. -/
theorem cfzp046ExponentialEnvelopeExplicitSmoothMarginBudget_implies_radialContactDeficit_le
    {ε η D : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (c : ℝ) (n : ℕ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform ε W c)
    (hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n)
    (hSmoothLog :
      cfzp040SmoothAbelCarrierModel ε W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) =
        cfzp042SmoothLogCellIntegral ε W c n)
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
    (hbudget : Cfzp046ExponentialEnvelopeExplicitSmoothMarginBudgetAt
      ε η D W c n) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W
      (cfzp040CarrierCellNaturalRight W c n) ≤ η := by
  have henv := cfzp046HigherPowerSigmaTail_le_exponentialEnvelope
    W c n hLate
  have hbudget045 : Cfzp045SigmaTailExplicitSmoothMarginBudgetAt
      ε η D W c n := by
    unfold Cfzp046ExponentialEnvelopeExplicitSmoothMarginBudgetAt at hbudget
    unfold Cfzp045SigmaTailExplicitSmoothMarginBudgetAt
    have hK : 0 ≤ cfzp045HigherPowerReferenceMassConstant ε W := by
      unfold cfzp045HigherPowerReferenceMassConstant
      positivity
    have hmul := mul_le_mul_of_nonneg_left henv hK
    linarith
  exact cfzp045SigmaTailExplicitSmoothMarginBudget_implies_radialContactDeficit_le
    hε hε2 W hsub c n hM hLate hSmoothLog hf_diff hf_int hM_int hD_int hD
    hbudget045

/-! ## Gate J: the higher-power/smooth-margin competition kernel -/

/-- The finite kernel whose eventual smallness is required by the next stage.

The factor `exp (-U / 2)` is the residual after cancelling the sigma
exponent against the explicit smooth margin.  This definition is deliberately
finite and makes no claim about its eventual decay.
-/
noncomputable def cfzp046HigherPowerMarginCompetitionKernel
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  8 * cfzp039CarrierCellLeft W c n *
    cfzp045HigherPowerReferenceMassConstant ε W *
    Real.exp (cfzp036PrimeAxisCarrierPeriod W / 2) *
    (cfzp039CarrierCellRight W c n / Real.log 2 + 1) *
    Real.exp (-(cfzp039CarrierCellLeft W c n) / 2)

/-- A kernel bound pays at most half of the explicit smooth margin. -/
theorem cfzp046HigherPowerEnvelope_le_half_explicitSmoothMargin_of_kernel
    {ε : ℝ} (_hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform ε W c)
    (hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n)
    (hkernel : cfzp046HigherPowerMarginCompetitionKernel ε W c n ≤
      cfzp039ExponentialCarrierPeriodTransform ε W c) :
    cfzp045HigherPowerReferenceMassConstant ε W *
        cfzp046HigherPowerSigmaTailExponentialEnvelope W c n ≤
      cfzp044ExplicitSmoothMargin ε W c n / 2 := by
  have hU2 : (2 : ℝ) ≤ cfzp039CarrierCellLeft W c n :=
    cfzp044_two_le_of_radialLate hLate
  have hU : 0 < cfzp039CarrierCellLeft W c n := by linarith
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hfactor : 0 ≤
      Real.exp (cfzp039PrimeAxisGrowthExponent W *
          cfzp039CarrierCellLeft W c n) /
        (8 * cfzp039CarrierCellLeft W c n) := by positivity
  have hEq :
      cfzp045HigherPowerReferenceMassConstant ε W *
          cfzp046HigherPowerSigmaTailExponentialEnvelope W c n =
        (Real.exp (cfzp039PrimeAxisGrowthExponent W *
            cfzp039CarrierCellLeft W c n) /
          (8 * cfzp039CarrierCellLeft W c n)) *
          cfzp046HigherPowerMarginCompetitionKernel ε W c n := by
    rw [cfzp046HigherPowerSigmaTailExponentialEnvelope_eq_normalForm]
    unfold cfzp046HigherPowerMarginCompetitionKernel
    have hexp :
        Real.exp (cfzp039PrimeAxisGrowthExponent W *
            cfzp039CarrierCellLeft W c n) *
            Real.exp (-(cfzp039CarrierCellLeft W c n) / 2) =
          Real.exp ((1 / 2 - W.rectangle.σ) *
            cfzp039CarrierCellLeft W c n) := by
      rw [← Real.exp_add]
      congr 1
      unfold cfzp039PrimeAxisGrowthExponent
      ring
    rw [← hexp]
    field_simp [ne_of_gt hU, ne_of_gt hlog2]
  calc
    cfzp045HigherPowerReferenceMassConstant ε W *
        cfzp046HigherPowerSigmaTailExponentialEnvelope W c n =
      (Real.exp (cfzp039PrimeAxisGrowthExponent W *
          cfzp039CarrierCellLeft W c n) /
        (8 * cfzp039CarrierCellLeft W c n)) *
        cfzp046HigherPowerMarginCompetitionKernel ε W c n := hEq
    _ ≤ (Real.exp (cfzp039PrimeAxisGrowthExponent W *
          cfzp039CarrierCellLeft W c n) /
        (8 * cfzp039CarrierCellLeft W c n)) *
        cfzp039ExponentialCarrierPeriodTransform ε W c :=
      mul_le_mul_of_nonneg_left hkernel hfactor
    _ = cfzp044ExplicitSmoothMargin ε W c n / 2 := by
      unfold cfzp044ExplicitSmoothMargin
      field_simp [ne_of_gt hU]
      ring

/-! ## Firewall -/

/-- Open providers for the next asymptotic comparison stage. -/
inductive Cfzp046HigherPrimePowerCellCountingEnvelopeGap : Prop
  | noAutomaticInteriorStripWindowProvider
  | noAutomaticSmoothAbelLogCellReadinessProvider
  | noPrimeCountingDiscrepancyFunctionalDecayProvider
  | noPointwiseDiscrepancyToFunctionalBound
  | noHigherPowerCompetitionKernelEventualDecay
  | noPrimeAxisRemainderCellDebtDecayProvider
  | noCofinalExponentialEnvelopeBudgetProvider

end DkMath.RH.CFBRCProjection
