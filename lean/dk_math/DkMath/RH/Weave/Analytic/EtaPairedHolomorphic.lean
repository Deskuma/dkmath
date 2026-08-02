/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.Weave.Analytic.EtaPairedIdentification
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

#print "file: DkMath.RH.Weave.Analytic.EtaPairedHolomorphic"

noncomputable section

namespace DkMath.RH.Weave.Analytic

open Set
open DkMath.RH.CFBRCProjection

/-- The genuine infinite paired eta value. -/
noncomputable def etaPairedValue (s : ℂ) : ℂ :=
  ∑' k : ℕ, etaPairTerm s k

/-- The open right half-plane on which paired eta is absolutely convergent. -/
def etaRightHalfPlane : Set ℂ :=
  {s : ℂ | 0 < s.re}

/--
A bounded control region separated from the imaginary axis.  Such regions
supply one summable majorant for the whole set.
-/
def etaControlRegion (δ M : ℝ) : Set ℂ :=
  {s : ℂ | δ < s.re ∧ ‖s‖ < M}

/-- The right half-plane is open. -/
theorem isOpen_etaRightHalfPlane : IsOpen etaRightHalfPlane := by
  exact isOpen_lt continuous_const Complex.continuous_re

/-- Every bounded control region is open. -/
theorem isOpen_etaControlRegion (δ M : ℝ) :
    IsOpen (etaControlRegion δ M) := by
  exact
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)

/-- Each paired eta term is an entire function of the complex exponent. -/
theorem etaPairTerm_differentiable (k : ℕ) :
    Differentiable ℂ (fun s : ℂ => etaPairTerm s k) := by
  unfold etaPairTerm etaUnsignedVector
  fun_prop

/-- The fixed majorant on a control region is summable. -/
theorem summable_etaPairControlMajorant
    {δ M : ℝ} (hδ : 0 < δ) :
    Summable
      (fun k : ℕ =>
        M * (((k + 1 : ℕ) : ℝ) ^ (-δ - 1))) := by
  have hp : 1 < δ + 1 := by linarith
  have hbase :
      Summable (fun n : ℕ => (n : ℝ) ^ (-(δ + 1))) := by
    simpa only [one_div, Real.rpow_neg (Nat.cast_nonneg _)] using
      (Real.summable_one_div_nat_rpow.2 hp)
  have hshift :
      Summable
        (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ (-(δ + 1)))) := by
    exact (summable_nat_add_iff 1).2 hbase
  have hmul := hshift.mul_left M
  simpa [show -δ - 1 = -(δ + 1) by ring] using hmul

/--
The one-extra-decay estimate becomes uniform on every bounded control region.
-/
theorem norm_etaPairTerm_le_controlMajorant
    {δ M : ℝ} (hδ : 0 < δ) {s : ℂ}
    (hs : s ∈ etaControlRegion δ M) (k : ℕ) :
    ‖etaPairTerm s k‖ ≤
      M * (((k + 1 : ℕ) : ℝ) ^ (-δ - 1)) := by
  have hre : 0 < s.re := hδ.trans hs.1
  have hpoint := norm_etaPairTerm_le_summableMajorant hre k
  have hnorm : ‖s‖ ≤ M := le_of_lt hs.2
  have hM : 0 ≤ M := (norm_nonneg s).trans hnorm
  have hbase : 1 ≤ (((k + 1 : ℕ) : ℝ)) := by positivity
  have hexp : -s.re - 1 ≤ -δ - 1 := by linarith
  have hrpow :
      (((k + 1 : ℕ) : ℝ) ^ (-s.re - 1)) ≤
        (((k + 1 : ℕ) : ℝ) ^ (-δ - 1)) :=
    Real.rpow_le_rpow_of_exponent_le hbase hexp
  calc
    ‖etaPairTerm s k‖ ≤
        ‖s‖ * (((k + 1 : ℕ) : ℝ) ^ (-s.re - 1)) := hpoint
    _ ≤ M * (((k + 1 : ℕ) : ℝ) ^ (-s.re - 1)) :=
      mul_le_mul_of_nonneg_right hnorm (Real.rpow_nonneg _ _)
    _ ≤ M * (((k + 1 : ℕ) : ℝ) ^ (-δ - 1)) :=
      mul_le_mul_of_nonneg_left hrpow hM

/--
The paired eta value is holomorphic on every bounded control region separated
from the imaginary axis.
-/
theorem etaPairedValue_differentiableOn_controlRegion
    {δ M : ℝ} (hδ : 0 < δ) :
    DifferentiableOn ℂ etaPairedValue (etaControlRegion δ M) := by
  unfold etaPairedValue
  exact
    Complex.differentiableOn_tsum_of_summable_norm
      (summable_etaPairControlMajorant hδ)
      (fun k => (etaPairTerm_differentiable k).differentiableOn)
      (isOpen_etaControlRegion δ M)
      (fun k s hs => norm_etaPairTerm_le_controlMajorant hδ hs k)

/-- Every point of the right half-plane lies in a bounded control region. -/
theorem mem_etaControlRegion_self
    {s : ℂ} (hs : 0 < s.re) :
    s ∈ etaControlRegion (s.re / 2) (‖s‖ + 1) := by
  constructor
  · linarith
  · linarith

/-- The paired eta infinite sum is holomorphic throughout `re s > 0`. -/
theorem etaPairedValue_differentiableOn_rightHalfPlane :
    DifferentiableOn ℂ etaPairedValue etaRightHalfPlane := by
  intro s hs
  have hδ : 0 < s.re / 2 := by
    exact half_pos hs
  have hmem := mem_etaControlRegion_self hs
  have hlocal := etaPairedValue_differentiableOn_controlRegion hδ
  have hat : DifferentiableAt ℂ etaPairedValue s :=
    (hlocal s hmem).differentiableAt
      ((isOpen_etaControlRegion (s.re / 2) (‖s‖ + 1)).mem_nhds hmem)
  exact hat.differentiableWithinAt

end DkMath.RH.Weave.Analytic
