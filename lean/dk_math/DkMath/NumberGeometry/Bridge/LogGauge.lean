/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberGeometry.Bridge.UnitCycle

namespace DkMath.NumberGeometry
noncomputable section

/-!
# Logarithmic coordinates for positive square-mass gauges

The denominator-free multiplicative gauge API remains primary.  This module
provides an analytic observer coordinate for active kernels, reusing the
positive-real DHNT unit bridge.
-/

namespace Bridge.LogGauge

/-- The logarithm of an active kernel's square-mass gauge. -/
def logMassGauge
    (K : TwoPointKernel) (hK : K.Active) : ℝ :=
  DkMath.DHNT.DUnit.logU
    (Bridge.UnitCycle.massUnit K hK)

/-- The mass-log coordinate is the real logarithm of the mass gauge. -/
@[simp]
theorem logMassGauge_eq_log_massGauge
    (K : TwoPointKernel) (hK : K.Active) :
    logMassGauge K hK = Real.log (massGauge K) := by
  rfl

/-- A gauge transition forces its factor to be positive. -/
theorem massGaugeRatio_pos
    {K1 K2 : TwoPointKernel}
    (h1 : K1.Active) (h2 : K2.Active) :
    0 < massGaugeRatio K1 K2 := by
  unfold massGaugeRatio
  exact div_pos
    ((massGauge_pos_iff_active K2).2 h2)
    ((massGauge_pos_iff_active K1).2 h1)

/-- A multiplicative gauge transition becomes an additive mass-log increment. -/
theorem logMassGauge_eq_add_log_factor
    {u : ℝ} {K1 K2 : TwoPointKernel}
    (h : MassScalesBy u K1 K2)
    (h1 : K1.Active) (h2 : K2.Active) :
    logMassGauge K2 h2 =
      Real.log u + logMassGauge K1 h1 := by
  have hu : 0 < u := MassScalesBy.factor_pos h h1 h2
  have h1pos : 0 < massGauge K1 :=
    (massGauge_pos_iff_active K1).2 h1
  calc
    logMassGauge K2 h2 = Real.log (massGauge K2) :=
      logMassGauge_eq_log_massGauge K2 h2
    _ = Real.log (u * massGauge K1) := by rw [h]
    _ = Real.log u + Real.log (massGauge K1) := by
      rw [Real.log_mul (ne_of_gt hu) (ne_of_gt h1pos)]
    _ = Real.log u + logMassGauge K1 h1 := by
      rw [logMassGauge_eq_log_massGauge K1 h1]

/-- The mass-log difference of a transition is the logarithm of its factor. -/
theorem logMassGauge_sub_eq_log_factor
    {u : ℝ} {K1 K2 : TwoPointKernel}
    (h : MassScalesBy u K1 K2)
    (h1 : K1.Active) (h2 : K2.Active) :
    logMassGauge K2 h2 - logMassGauge K1 h1 =
      Real.log u := by
  rw [logMassGauge_eq_add_log_factor h h1 h2]
  ring

/-- The logarithm of the gauge ratio is the difference of mass-log coordinates. -/
theorem log_massGaugeRatio
    {K1 K2 : TwoPointKernel}
    (h1 : K1.Active) (h2 : K2.Active) :
    Real.log (massGaugeRatio K1 K2) =
      logMassGauge K2 h2 - logMassGauge K1 h1 := by
  have h1pos : 0 < massGauge K1 :=
    (massGauge_pos_iff_active K1).2 h1
  have h2pos : 0 < massGauge K2 :=
    (massGauge_pos_iff_active K2).2 h2
  calc
    Real.log (massGaugeRatio K1 K2) =
        Real.log (massGauge K2 / massGauge K1) := by rfl
    _ = Real.log (massGauge K2) - Real.log (massGauge K1) := by
      rw [Real.log_div (ne_of_gt h2pos) (ne_of_gt h1pos)]
    _ = logMassGauge K2 h2 - logMassGauge K1 h1 := by
      rw [logMassGauge_eq_log_massGauge K2 h2,
        logMassGauge_eq_log_massGauge K1 h1]

/-- Multiplicative gauge-ratio composition becomes additive log composition. -/
theorem log_massGaugeRatio_trans
    {K1 K2 K3 : TwoPointKernel}
    (h1 : K1.Active) (h2 : K2.Active) (h3 : K3.Active) :
    Real.log (massGaugeRatio K1 K3) =
      Real.log (massGaugeRatio K1 K2) +
        Real.log (massGaugeRatio K2 K3) := by
  rw [massGaugeRatio_trans h1 h2]
  rw [Real.log_mul
    (ne_of_gt (massGaugeRatio_pos h1 h2))
    (ne_of_gt (massGaugeRatio_pos h2 h3))]

end Bridge.LogGauge

open Bridge.LogGauge

namespace PrimeScaleStep

/-- A prime scale step has logarithmic mass increment `log p`. -/
theorem logMassGauge_sub_eq_log_prime
    {p : ℕ} {K1 K2 : TwoPointKernel}
    (h : PrimeScaleStep p K1 K2)
    (h1 : K1.Active) :
    logMassGauge K2 (h.target_active h1) -
        logMassGauge K1 h1 =
      Real.log (p : ℝ) := by
  exact logMassGauge_sub_eq_log_factor
    h.massScalesBy h1 (h.target_active h1)

end PrimeScaleStep

namespace PrimeScaleChain

/-- A prime chain has logarithmic mass increment equal to the log product. -/
theorem logMassGauge_sub_eq_log_prod
    {K1 K2 : TwoPointKernel} {ps : List ℕ}
    (h : PrimeScaleChain K1 K2 ps)
    (h1 : K1.Active) :
    logMassGauge K2 (h.target_active h1) -
        logMassGauge K1 h1 =
      Real.log ((ps.prod : ℕ) : ℝ) := by
  exact logMassGauge_sub_eq_log_factor
    h.massScalesBy_prod h1 (h.target_active h1)

/-- Repeated equal prime labels give the expected prime-power mass-log increment. -/
theorem logMassGauge_sub_eq_mul_log_prime
    {p k : ℕ} {K1 K2 : TwoPointKernel}
    (h : PrimeScaleChain K1 K2 (List.replicate k p))
    (h1 : K1.Active) :
    logMassGauge K2 (h.target_active h1) -
        logMassGauge K1 h1 =
      (k : ℝ) * Real.log (p : ℝ) := by
  simpa [List.prod_replicate, Nat.cast_pow, Real.log_pow] using
    (logMassGauge_sub_eq_log_prod h h1)

end PrimeScaleChain

namespace Bridge.LogGauge

/-- The ordinary distance of an active kernel is positive. -/
theorem dist_pos_of_active
    (K : TwoPointKernel) (hK : K.Active) :
    0 < dist K.source K.target := by
  have hmass : 0 < massGauge K :=
    (massGauge_pos_iff_active K).2 hK
  have hdist_ne : dist K.source K.target ≠ 0 := by
    intro hzero
    apply (ne_of_gt hmass)
    rw [massGauge, pairMass_eq_dist_sq, hzero]
    simp
  exact lt_of_le_of_ne dist_nonneg hdist_ne.symm

/-- The logarithm of an active kernel's ordinary distance. -/
def logDistanceGauge
    (K : TwoPointKernel) (_hK : K.Active) : ℝ :=
  Real.log (dist K.source K.target)

/-- Square-mass log is twice the ordinary distance log. -/
theorem logMassGauge_eq_two_mul_logDistanceGauge
    (K : TwoPointKernel) (hK : K.Active) :
    logMassGauge K hK =
      2 * logDistanceGauge K hK := by
  rw [logMassGauge_eq_log_massGauge, massGauge,
    pairMass_eq_dist_sq, Real.log_pow]
  rfl

end Bridge.LogGauge

namespace PrimeScaleStep

/-- A prime square-mass step gives half-log-prime distance growth. -/
theorem logDistanceGauge_sub_eq_half_log_prime
    {p : ℕ} {K1 K2 : TwoPointKernel}
    (h : PrimeScaleStep p K1 K2)
    (h1 : K1.Active) :
    logDistanceGauge K2 (h.target_active h1) -
        logDistanceGauge K1 h1 =
      (1 / 2 : ℝ) * Real.log (p : ℝ) := by
  have hlog := PrimeScaleStep.logMassGauge_sub_eq_log_prime h h1
  rw [logMassGauge_eq_two_mul_logDistanceGauge,
    logMassGauge_eq_two_mul_logDistanceGauge] at hlog
  linarith

end PrimeScaleStep

end
end DkMath.NumberGeometry
