/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisSigmaStrippedPeriodicCarrierAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisPeriodicCarrierArcGeometryAudit"

/-!
# CFZP-037: periodic carrier arcs and prime-log target intervals

The nonzero periodic carrier from CFZP-036 is turned into finite positive and
negative arcs.  Their translates, late-cell remainder absorption, and
exponential target intervals are recorded without asserting that any prime
lies in one of the intervals.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Set

/-! ## Gate A: half-period sign reversal -/

/-- A half period changes the sign of the leading carrier. -/
theorem cfzp037LeadingCarrier_add_halfPeriod
    {ε : ℝ} (hε : ε ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) :
    cfzp036PrimeAxisLeadingPeriodicCarrier ε W
        (u + cfzp036PrimeAxisCarrierPeriod W / 2) =
      -cfzp036PrimeAxisLeadingPeriodicCarrier ε W u := by
  rw [cfzp036PrimeAxisLeadingPeriodicCarrier_eq_sin_cos_pair hε W,
    cfzp036PrimeAxisLeadingPeriodicCarrier_eq_sin_cos_pair hε W]
  have hT : W.rectangle.T ≠ 0 := W.rectangle.hT.ne'
  have harg : W.rectangle.T *
      (u + cfzp036PrimeAxisCarrierPeriod W / 2) =
      W.rectangle.T * u + Real.pi := by
    unfold cfzp036PrimeAxisCarrierPeriod
    field_simp [hT]
  rw [harg, Real.sin_add_pi, Real.cos_add_pi]
  ring

/-! ## Gate B: explicit positive and negative carrier points -/

/-- The leading carrier is continuous as a function of its coordinate. -/
theorem cfzp037LeadingCarrier_continuous
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) :
    Continuous (fun u => cfzp036PrimeAxisLeadingPeriodicCarrier ε W u) := by
  unfold cfzp036PrimeAxisLeadingPeriodicCarrier cfzp036LinearPhaseCore
  fun_prop

/-- A nonzero carrier has an explicit strictly positive point. -/
theorem cfzp037_exists_positive_carrier_point
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    ∃ uPos : ℝ,
      0 < cfzp036PrimeAxisLeadingPeriodicCarrier ε W uPos := by
  have hpair := cfzp036LeadingCoeff_pair_ne_zero hε W
  have hT : 0 < W.rectangle.T := W.rectangle.hT
  by_cases hC : 0 < cfzp036LeadingCosCoeffNumerator ε W
  · refine ⟨0, ?_⟩
    rw [cfzp036PrimeAxisLeadingPeriodicCarrier_eq_sin_cos_pair hε.ne' W]
    simp only [mul_zero, Real.sin_zero, Real.cos_zero, mul_zero, zero_add]
    simpa using div_pos hC hε
  · have hC' : cfzp036LeadingCosCoeffNumerator ε W ≤ 0 :=
      le_of_not_gt hC
    by_cases hCzero : cfzp036LeadingCosCoeffNumerator ε W = 0
    · have hS : cfzp036LeadingSinCoeffNumerator ε W ≠ 0 := by
        intro hS
        exact hpair.elim (fun hs => hs hS) (fun hc => hc hCzero)
      by_cases hSpos : 0 < cfzp036LeadingSinCoeffNumerator ε W
      · refine ⟨Real.pi / (2 * W.rectangle.T), ?_⟩
        rw [cfzp036PrimeAxisLeadingPeriodicCarrier_eq_sin_cos_pair hε.ne' W]
        have harg : W.rectangle.T *
            (Real.pi / (2 * W.rectangle.T)) = Real.pi / 2 := by
          field_simp [hT.ne']
        rw [harg, Real.sin_pi_div_two, Real.cos_pi_div_two, hCzero]
        simpa using div_pos hSpos hε
      · have hSneg : cfzp036LeadingSinCoeffNumerator ε W < 0 := by
          exact lt_of_le_of_ne (le_of_not_gt hSpos) hS
        refine ⟨-(Real.pi / (2 * W.rectangle.T)), ?_⟩
        rw [cfzp036PrimeAxisLeadingPeriodicCarrier_eq_sin_cos_pair hε.ne' W]
        have harg : W.rectangle.T *
            (-(Real.pi / (2 * W.rectangle.T))) = -(Real.pi / 2) := by
          field_simp [hT.ne']
        rw [harg, Real.sin_neg, Real.cos_neg, Real.sin_pi_div_two,
          Real.cos_pi_div_two, hCzero]
        simpa using div_pos (neg_pos.mpr hSneg) hε
    · refine ⟨Real.pi / W.rectangle.T, ?_⟩
      rw [cfzp036PrimeAxisLeadingPeriodicCarrier_eq_sin_cos_pair hε.ne' W]
      have harg : W.rectangle.T *
          (Real.pi / W.rectangle.T) = Real.pi := by
        field_simp [hT.ne']
      rw [harg, Real.sin_pi, Real.cos_pi]
      simpa using div_pos (neg_pos.mpr (lt_of_le_of_ne hC' hCzero)) hε

/-- A nonzero carrier has an explicit strictly negative point. -/
theorem cfzp037_exists_negative_carrier_point
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    ∃ uNeg : ℝ,
      cfzp036PrimeAxisLeadingPeriodicCarrier ε W uNeg < 0 := by
  obtain ⟨u, hu⟩ := cfzp037_exists_positive_carrier_point hε W
  refine ⟨u + cfzp036PrimeAxisCarrierPeriod W / 2, ?_⟩
  rw [cfzp037LeadingCarrier_add_halfPeriod hε.ne' W u]
  linarith

/-! ## Gate C: uniform carrier arc data -/

/-- A closed positive carrier arc with an explicit margin. -/
structure Cfzp037CarrierPositiveArcData
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) where
  center : ℝ
  halfWidth : ℝ
  margin : ℝ
  hhalfWidth : 0 < halfWidth
  hmargin : 0 < margin
  hcarrier : ∀ u ∈ Set.Icc (center - halfWidth) (center + halfWidth),
    2 * margin ≤ cfzp036PrimeAxisLeadingPeriodicCarrier ε W u

/-- A closed negative carrier arc with an explicit margin. -/
structure Cfzp037CarrierNegativeArcData
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) where
  center : ℝ
  halfWidth : ℝ
  margin : ℝ
  hhalfWidth : 0 < halfWidth
  hmargin : 0 < margin
  hcarrier : ∀ u ∈ Set.Icc (center - halfWidth) (center + halfWidth),
    cfzp036PrimeAxisLeadingPeriodicCarrier ε W u ≤ -2 * margin

/-- A positive point contains a fixed-width closed positive carrier arc. -/
theorem cfzp037_exists_positive_carrier_arc
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    ∃ _arc : Cfzp037CarrierPositiveArcData ε W, True := by
  obtain ⟨u₀, hu₀⟩ := cfzp037_exists_positive_carrier_point hε W
  have hcont := cfzp037LeadingCarrier_continuous ε W
  let U : Set ℝ := {u | cfzp036PrimeAxisLeadingPeriodicCarrier ε W u >
    cfzp036PrimeAxisLeadingPeriodicCarrier ε W u₀ / 2}
  have hUopen : IsOpen U := by
    exact isOpen_Ioi.preimage hcont
  have huU : u₀ ∈ U := by
    dsimp [U]
    linarith
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds huU)
  let δ := r / 2
  let m := cfzp036PrimeAxisLeadingPeriodicCarrier ε W u₀ / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hm : 0 < m := by dsimp [m]; linarith
  refine ⟨⟨u₀, δ, m, hδ, hm, ?_⟩, trivial⟩
  intro u hu
  have hdist : u ∈ Metric.ball u₀ r := by
    rw [Metric.mem_ball, Real.dist_eq]
    apply lt_of_le_of_lt (b := r / 2) ?_ (by linarith)
    rw [abs_le]
    have hlo : -(r / 2) ≤ u - u₀ := by
      dsimp [δ] at hu
      linarith [hu.1]
    have hhi : u - u₀ ≤ r / 2 := by
      dsimp [δ] at hu
      linarith [hu.2]
    exact ⟨hlo, hhi⟩
  have hgt := hball hdist
  dsimp [U, m] at hgt ⊢
  linarith

/-! ## Gate D: natural-period translated arcs -/

noncomputable def cfzp037PositiveArcLeft
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow}
    (arc : Cfzp037CarrierPositiveArcData ε W) (n : ℕ) : ℝ :=
  arc.center + (n : ℝ) * cfzp036PrimeAxisCarrierPeriod W - arc.halfWidth

noncomputable def cfzp037PositiveArcRight
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow}
    (arc : Cfzp037CarrierPositiveArcData ε W) (n : ℕ) : ℝ :=
  arc.center + (n : ℝ) * cfzp036PrimeAxisCarrierPeriod W + arc.halfWidth

/-- Periodicity extends from one period to every natural multiple. -/
theorem cfzp037LeadingCarrier_add_nat_mul_period
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) (n : ℕ) :
    cfzp036PrimeAxisLeadingPeriodicCarrier ε W
        (u + (n : ℝ) * cfzp036PrimeAxisCarrierPeriod W) =
      cfzp036PrimeAxisLeadingPeriodicCarrier ε W u := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : u + ((n + 1 : ℕ) : ℝ) *
          cfzp036PrimeAxisCarrierPeriod W =
        (u + (n : ℝ) * cfzp036PrimeAxisCarrierPeriod W) +
          cfzp036PrimeAxisCarrierPeriod W := by
        push_cast
        ring
      rw [hstep, cfzp036PrimeAxisLeadingPeriodicCarrier_periodic]
      exact ih

/-- Every translated positive arc has the same carrier margin. -/
theorem cfzp037_positive_arc_margin_on_translate
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow}
    (arc : Cfzp037CarrierPositiveArcData ε W) (n : ℕ) {u : ℝ}
    (hu : u ∈ Set.Icc (cfzp037PositiveArcLeft arc n)
      (cfzp037PositiveArcRight arc n)) :
    2 * arc.margin ≤ cfzp036PrimeAxisLeadingPeriodicCarrier ε W u := by
  let v := u - (n : ℝ) * cfzp036PrimeAxisCarrierPeriod W
  have hv : v ∈ Set.Icc (arc.center - arc.halfWidth)
      (arc.center + arc.halfWidth) := by
    dsimp [v, cfzp037PositiveArcLeft, cfzp037PositiveArcRight] at hu ⊢
    constructor <;> linarith [hu.1, hu.2]
  have hbase := arc.hcarrier v hv
  have hper := cfzp037LeadingCarrier_add_nat_mul_period (ε := ε) W v n
  have huv : u = v + (n : ℝ) * cfzp036PrimeAxisCarrierPeriod W := by
    dsimp [v]
    ring
  rw [huv, hper]
  exact hbase

/-- A negative arc is obtained by shifting the positive arc by half a period. -/
noncomputable def cfzp037NegativeArcOfPositive
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow}
    (hε : ε ≠ 0) (arc : Cfzp037CarrierPositiveArcData ε W) :
    Cfzp037CarrierNegativeArcData ε W :=
  { center := arc.center + cfzp036PrimeAxisCarrierPeriod W / 2
    halfWidth := arc.halfWidth
    margin := arc.margin
    hhalfWidth := arc.hhalfWidth
    hmargin := arc.hmargin
    hcarrier := by
      intro u hu
      let v := u - cfzp036PrimeAxisCarrierPeriod W / 2
      have hv : v ∈ Set.Icc (arc.center - arc.halfWidth)
          (arc.center + arc.halfWidth) := by
        dsimp [v]
        constructor <;> linarith [hu.1, hu.2]
      have hbase := arc.hcarrier v hv
      have hhalf := cfzp037LeadingCarrier_add_halfPeriod
        (ε := ε) hε W v
      have huv : u = v + cfzp036PrimeAxisCarrierPeriod W / 2 := by
        dsimp [v]
        ring
      rw [huv, hhalf]
      linarith }

/-! ## Gate E: finite late-cell threshold -/

noncomputable def cfzp037RemainderAbsorptionThreshold
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (κ : ℝ) : ℝ :=
  max 1 (max (2 * ε)
    (2 * cfzp036PrimeAxisRemainderConstant ε W / κ))

theorem cfzp037RemainderAbsorptionThreshold_le_coordinate
    {ε κ u : ℝ} (hε : 0 < ε) (hκ : 0 < κ)
    (W : PascalCenteredXiResidueTransportWindow)
    (hth : cfzp037RemainderAbsorptionThreshold ε W κ ≤ u) :
    1 ≤ u ∧ 2 * ε ≤ u ∧
      cfzp036PrimeAxisRemainderConstant ε W / u ≤ κ / 2 := by
  have hu : 0 < u := lt_of_lt_of_le (by norm_num) (le_trans
    (le_max_left 1 (max (2 * ε)
      (2 * cfzp036PrimeAxisRemainderConstant ε W / κ))) hth)
  have h1 : 1 ≤ u := le_trans
    (le_max_left 1 (max (2 * ε)
      (2 * cfzp036PrimeAxisRemainderConstant ε W / κ))) hth
  have h2 : 2 * ε ≤ u := le_trans
    (le_trans (le_max_left (2 * ε)
      (2 * cfzp036PrimeAxisRemainderConstant ε W / κ))
      (le_max_right 1 (max (2 * ε)
        (2 * cfzp036PrimeAxisRemainderConstant ε W / κ)))) hth
  have hK : 0 ≤ cfzp036PrimeAxisRemainderConstant ε W :=
    (cfzp036PrimeAxisRemainderConstant_pos hε W).le
  have hKκ : 2 * cfzp036PrimeAxisRemainderConstant ε W / κ ≤ u :=
    le_trans
      (le_trans (le_max_right (2 * ε)
        (2 * cfzp036PrimeAxisRemainderConstant ε W / κ))
        (le_max_right 1 (max (2 * ε)
          (2 * cfzp036PrimeAxisRemainderConstant ε W / κ)))) hth
  refine ⟨h1, h2, ?_⟩
  apply (div_le_iff₀ hu).2
  have hmul := mul_le_mul_of_nonneg_left hKκ hκ.le
  have hscaled : 2 * cfzp036PrimeAxisRemainderConstant ε W ≤ κ * u := by
    calc
      2 * cfzp036PrimeAxisRemainderConstant ε W =
          κ * (2 * cfzp036PrimeAxisRemainderConstant ε W / κ) := by
            field_simp [hκ.ne']
      _ ≤ κ * u := hmul
  nlinarith

/-! ## Gates E--F: late translated cells and actual amplitude signs -/

noncomputable def cfzp037NegativeArcLeft
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow}
    (arc : Cfzp037CarrierNegativeArcData ε W) (n : ℕ) : ℝ :=
  arc.center + (n : ℝ) * cfzp036PrimeAxisCarrierPeriod W - arc.halfWidth

noncomputable def cfzp037NegativeArcRight
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow}
    (arc : Cfzp037CarrierNegativeArcData ε W) (n : ℕ) : ℝ :=
  arc.center + (n : ℝ) * cfzp036PrimeAxisCarrierPeriod W + arc.halfWidth

/-- The negative translated arc inherits the margin from its base cell. -/
theorem cfzp037_negative_arc_margin_on_translate
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow}
    (_hε : ε ≠ 0) (arc : Cfzp037CarrierNegativeArcData ε W) (n : ℕ) {u : ℝ}
    (hu : u ∈ Set.Icc (cfzp037NegativeArcLeft arc n)
      (cfzp037NegativeArcRight arc n)) :
    cfzp036PrimeAxisLeadingPeriodicCarrier ε W u ≤ -2 * arc.margin := by
  let v := u - (n : ℝ) * cfzp036PrimeAxisCarrierPeriod W
  have hv : v ∈ Set.Icc (arc.center - arc.halfWidth)
      (arc.center + arc.halfWidth) := by
    dsimp [v, cfzp037NegativeArcLeft, cfzp037NegativeArcRight] at hu ⊢
    constructor <;> linarith [hu.1, hu.2]
  have hbase := arc.hcarrier v hv
  have hper := cfzp037LeadingCarrier_add_nat_mul_period (ε := ε) W v n
  have huv : u = v + (n : ℝ) * cfzp036PrimeAxisCarrierPeriod W := by
    dsimp [v]
    ring
  rw [huv, hper]
  exact hbase

/-- A positive translated arc is eventually beyond the remainder threshold. -/
theorem cfzp037_exists_late_positive_arc_index
    {ε : ℝ} (_hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      cfzp037RemainderAbsorptionThreshold ε W arc.margin ≤
        cfzp037PositiveArcLeft arc n := by
  have hP : 0 < cfzp036PrimeAxisCarrierPeriod W :=
    cfzp036PrimeAxisCarrierPeriod_pos W
  let b := cfzp037RemainderAbsorptionThreshold ε W arc.margin
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt
    ((b - arc.center + arc.halfWidth) /
      cfzp036PrimeAxisCarrierPeriod W)
  refine ⟨N₀, ?_⟩
  intro n hn
  have hnreal : (N₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hNmul := (div_lt_iff₀ hP).mp hN₀
  have hmon : (N₀ : ℝ) * cfzp036PrimeAxisCarrierPeriod W ≤
      (n : ℝ) * cfzp036PrimeAxisCarrierPeriod W :=
    mul_le_mul_of_nonneg_right hnreal hP.le
  dsimp [b, cfzp037PositiveArcLeft] at hNmul ⊢
  nlinarith

/-- The analogous late-index statement for a negative translated arc. -/
theorem cfzp037_exists_late_negative_arc_index
    {ε : ℝ} (_hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierNegativeArcData ε W) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      cfzp037RemainderAbsorptionThreshold ε W arc.margin ≤
        cfzp037NegativeArcLeft arc n := by
  have hP : 0 < cfzp036PrimeAxisCarrierPeriod W :=
    cfzp036PrimeAxisCarrierPeriod_pos W
  let b := cfzp037RemainderAbsorptionThreshold ε W arc.margin
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt
    ((b - arc.center + arc.halfWidth) /
      cfzp036PrimeAxisCarrierPeriod W)
  refine ⟨N₀, ?_⟩
  intro n hn
  have hnreal : (N₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hNmul := (div_lt_iff₀ hP).mp hN₀
  have hmon : (N₀ : ℝ) * cfzp036PrimeAxisCarrierPeriod W ≤
      (n : ℝ) * cfzp036PrimeAxisCarrierPeriod W :=
    mul_le_mul_of_nonneg_right hnreal hP.le
  dsimp [b, cfzp037NegativeArcLeft] at hNmul ⊢
  nlinarith

/-- Every point in a sufficiently late positive arc has positive amplitude. -/
theorem cfzp037_positive_arc_coordinate_amplitude_ge_margin_half
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W)
    {N₀ n : ℕ} (hn : N₀ ≤ n) {u : ℝ}
    (hu : u ∈ Set.Icc (cfzp037PositiveArcLeft arc n)
      (cfzp037PositiveArcRight arc n))
    (hlate : ∀ m, N₀ ≤ m →
      cfzp037RemainderAbsorptionThreshold ε W arc.margin ≤
        cfzp037PositiveArcLeft arc m) :
    arc.margin / 2 ≤ cfzp036PrimeAxisCoordinateAmplitude ε W u := by
  have hbudget := cfzp037RemainderAbsorptionThreshold_le_coordinate
    hε arc.hmargin W (le_trans (hlate n hn) hu.1)
  have hcar := cfzp037_positive_arc_margin_on_translate arc n hu
  have hmargin : arc.margin ≤
      cfzp036PrimeAxisLeadingPeriodicCarrier ε W u := by
    nlinarith [hcar, arc.hmargin]
  exact cfzp036PrimeAxisCoordinateAmplitude_ge_half_of_le_leading
    hε hbudget.1 hbudget.2.1 arc.hmargin W hmargin hbudget.2.2

/-- Every point in a sufficiently late negative arc has negative amplitude. -/
theorem cfzp037_negative_arc_coordinate_amplitude_le_neg_margin_half
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierNegativeArcData ε W)
    {N₀ n : ℕ} (hn : N₀ ≤ n) {u : ℝ}
    (hu : u ∈ Set.Icc (cfzp037NegativeArcLeft arc n)
      (cfzp037NegativeArcRight arc n))
    (hlate : ∀ m, N₀ ≤ m →
      cfzp037RemainderAbsorptionThreshold ε W arc.margin ≤
        cfzp037NegativeArcLeft arc m) :
    cfzp036PrimeAxisCoordinateAmplitude ε W u ≤ -arc.margin / 2 := by
  have hbudget := cfzp037RemainderAbsorptionThreshold_le_coordinate
    hε arc.hmargin W (le_trans (hlate n hn) hu.1)
  have hcar := cfzp037_negative_arc_margin_on_translate hε.ne' arc n hu
  have hmargin : cfzp036PrimeAxisLeadingPeriodicCarrier ε W u ≤ -arc.margin := by
    nlinarith [hcar, arc.hmargin]
  exact cfzp036PrimeAxisCoordinateAmplitude_le_neg_half_of_le_leading
    hε hbudget.1 hbudget.2.1 arc.hmargin W hmargin hbudget.2.2

/-! ## Gate G: logarithmic arcs and multiplicative target intervals -/

noncomputable def cfzp037PositivePrimeIntervalLeft
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow}
    (arc : Cfzp037CarrierPositiveArcData ε W) (n : ℕ) : ℝ :=
  Real.exp (cfzp037PositiveArcLeft arc n)

noncomputable def cfzp037PositivePrimeIntervalRight
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow}
    (arc : Cfzp037CarrierPositiveArcData ε W) (n : ℕ) : ℝ :=
  Real.exp (cfzp037PositiveArcRight arc n)

noncomputable def cfzp037PositiveArcMultiplicativeRatio
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow}
    (arc : Cfzp037CarrierPositiveArcData ε W) : ℝ :=
  Real.exp (2 * arc.halfWidth)

/-- The multiplicative interval has a fixed ratio strictly larger than one. -/
theorem cfzp037PositiveArcMultiplicativeRatio_gt_one
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow}
    (arc : Cfzp037CarrierPositiveArcData ε W) :
    1 < cfzp037PositiveArcMultiplicativeRatio arc := by
  unfold cfzp037PositiveArcMultiplicativeRatio
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by linarith [arc.hhalfWidth])

/-- The right endpoint is the fixed ratio times the left endpoint. -/
theorem cfzp037PositivePrimeIntervalRight_eq_ratio_mul_left
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow}
    (arc : Cfzp037CarrierPositiveArcData ε W) (n : ℕ) :
    cfzp037PositivePrimeIntervalRight arc n =
      cfzp037PositiveArcMultiplicativeRatio arc *
        cfzp037PositivePrimeIntervalLeft arc n := by
  unfold cfzp037PositivePrimeIntervalRight
    cfzp037PositivePrimeIntervalLeft cfzp037PositiveArcMultiplicativeRatio
  rw [← Real.exp_add]
  congr 1
  dsimp [cfzp037PositiveArcLeft, cfzp037PositiveArcRight]
  ring

/-- Exponentiation transports closed logarithmic intervals exactly. -/
theorem cfzp037_log_mem_positive_arc_iff_mem_exp_interval
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow}
    (arc : Cfzp037CarrierPositiveArcData ε W) (n : ℕ)
    {x : ℝ} (hx : 0 < x) :
    Real.log x ∈ Set.Icc (cfzp037PositiveArcLeft arc n)
      (cfzp037PositiveArcRight arc n) ↔
    x ∈ Set.Icc (cfzp037PositivePrimeIntervalLeft arc n)
      (cfzp037PositivePrimeIntervalRight arc n) := by
  constructor
  · intro h
    constructor
    · change Real.exp (cfzp037PositiveArcLeft arc n) ≤ x
      simpa [Real.exp_log hx] using (Real.exp_le_exp.mpr h.1)
    · change x ≤ Real.exp (cfzp037PositiveArcRight arc n)
      simpa [Real.exp_log hx] using (Real.exp_le_exp.mpr h.2)
  · intro h
    constructor
    · have hleft : Real.exp (cfzp037PositiveArcLeft arc n) ≤
          Real.exp (Real.log x) := by
        have hleft0 : Real.exp (cfzp037PositiveArcLeft arc n) ≤ x := by
          simpa only [cfzp037PositivePrimeIntervalLeft] using h.1
        simpa [Real.exp_log hx] using hleft0
      exact (Real.exp_le_exp.mp hleft)
    · have hright : Real.exp (Real.log x) ≤
          Real.exp (cfzp037PositiveArcRight arc n) := by
        have hright0 : x ≤ Real.exp (cfzp037PositiveArcRight arc n) := by
          simpa only [cfzp037PositivePrimeIntervalRight] using h.2
        simpa [Real.exp_log hx] using hright0
      exact (Real.exp_le_exp.mp hright)

/-- Prime-log specialization of the interval adapter. -/
theorem cfzp037_prime_log_mem_positive_arc_iff_mem_exp_interval
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow}
    (arc : Cfzp037CarrierPositiveArcData ε W) (n : ℕ)
    {p : ℕ} (hp : Nat.Prime p) :
    Real.log (p : ℝ) ∈ Set.Icc (cfzp037PositiveArcLeft arc n)
      (cfzp037PositiveArcRight arc n) ↔
    (p : ℝ) ∈ Set.Icc (cfzp037PositivePrimeIntervalLeft arc n)
      (cfzp037PositivePrimeIntervalRight arc n) :=
  cfzp037_log_mem_positive_arc_iff_mem_exp_interval arc n
    (by exact_mod_cast hp.pos : (0 : ℝ) < (p : ℝ))

/-! ## Gates H--I: prime hits, event transport, and the arithmetic frontier -/

def Cfzp037PrimeAxisPositiveArcHitAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W)
    (n p : ℕ) : Prop :=
  Nat.Prime p ∧ Real.log (p : ℝ) ∈
    Set.Icc (cfzp037PositiveArcLeft arc n)
      (cfzp037PositiveArcRight arc n)

theorem cfzp037PrimeAxisEvent_ge_sigmaWeight_mul_margin_of_positiveArcHit
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W)
    {N₀ n p : ℕ} (hn : N₀ ≤ n)
    (hlate : ∀ m, N₀ ≤ m →
      cfzp037RemainderAbsorptionThreshold ε W arc.margin ≤
        cfzp037PositiveArcLeft arc m)
    (hhit : Cfzp037PrimeAxisPositiveArcHitAt ε W arc n p) :
    cfzp034PrimeAxisSigmaWeight W p * (arc.margin / 2) ≤
      cfzpPrimePowerBranchFreeTrigEvent ε W p 1 := by
  have hamp := cfzp037_positive_arc_coordinate_amplitude_ge_margin_half
    hε W arc hn hhit.2 hlate
  have hsigned := cfzp035PrimeAxisSignedAmplitude_eq_cfzp036CoordinateAmplitude_log
    hε hε2 W hhit.1
  have htransport := cfzp035PrimeAxisEvent_eq_sigmaWeight_mul_signedAmplitude
    hε hε2 W hhit.1
  calc
    cfzp034PrimeAxisSigmaWeight W p * (arc.margin / 2) ≤
        cfzp034PrimeAxisSigmaWeight W p *
          cfzp035PrimeAxisSignedAmplitude ε W p := by
      rw [hsigned]
      exact mul_le_mul_of_nonneg_left hamp
        (cfzp034PrimeAxisSigmaWeight_pos W p).le
    _ = cfzpPrimePowerBranchFreeTrigEvent ε W p 1 := htransport.symm

theorem cfzp037PrimeAxisEvent_pos_of_positiveArcHit
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W)
    {N₀ n p : ℕ} (hn : N₀ ≤ n)
    (hlate : ∀ m, N₀ ≤ m →
      cfzp037RemainderAbsorptionThreshold ε W arc.margin ≤
        cfzp037PositiveArcLeft arc m)
    (hhit : Cfzp037PrimeAxisPositiveArcHitAt ε W arc n p) :
    0 < cfzpPrimePowerBranchFreeTrigEvent ε W p 1 := by
  have hmass := cfzp037PrimeAxisEvent_ge_sigmaWeight_mul_margin_of_positiveArcHit
    hε hε2 W arc hn hlate hhit
  have hm : 0 < cfzp034PrimeAxisSigmaWeight W p * (arc.margin / 2) :=
    mul_pos (cfzp034PrimeAxisSigmaWeight_pos W p)
      (div_pos arc.hmargin (by norm_num))
  linarith

noncomputable def cfzp037PositiveArcPrimeSigmaWeightMass
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W)
    (n : ℕ) (S : Finset ℕ) : ℝ :=
  by
    classical
    exact (S.filter (fun p =>
      Cfzp037PrimeAxisPositiveArcHitAt ε W arc n p)).sum
      (fun p => cfzp034PrimeAxisSigmaWeight W p)

/-! The following constructors record the arithmetic and analytic bridges that
are intentionally not supplied by this finite geometric module. -/
inductive Cfzp037PrimeAxisPeriodicCarrierArcGeometryGap : Prop
  | noPrimeInEveryPositiveArcProvider
  | noPrimeAxisPositiveArcWeightedMassLowerBound
  | noPrimeLogEquidistributionProvider
  | noExceptionalHigherPowerResidualElimination
  | noAutomaticSubcriticalWindowProvider

end DkMath.RH.CFBRCProjection
