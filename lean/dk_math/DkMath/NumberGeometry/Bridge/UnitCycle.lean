/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberGeometry.PrimeScale
import DkMath.DHNT.DHNT_Base
import DkMath.UnitCycle.Core

namespace DkMath.NumberGeometry
noncomputable section

/-!
# NumberGeometry bridges to DHNT units and UnitCycle no-cycle logic

This module connects an active square-mass gauge to the exact positive-real
`DkMath.DHNT.Unit` type.  The older `DkMath.NP` phase lattice and the
quantizing `UnitNatLayers` bridges remain separate APIs.
-/

/-- The subtype of active two-point kernels. -/
abbrev ActiveKernel := {K : TwoPointKernel // K.Active}

namespace Bridge.UnitCycle

/-- The exact DHNT positive-real unit represented by an active kernel gauge. -/
def massUnit (K : TwoPointKernel) (hK : K.Active) : DkMath.DHNT.Unit :=
  ⟨massGauge K, (massGauge_pos_iff_active K).2 hK⟩

/-- The value of `massUnit` is exactly the source kernel mass gauge. -/
@[simp]
theorem massUnit_val (K : TwoPointKernel) (hK : K.Active) :
    (massUnit K hK).val = massGauge K := rfl

/-- DHNT ratio agrees with the target-over-source NumberGeometry ratio. -/
theorem dhnt_ratio_massUnit
    {K1 K2 : TwoPointKernel}
    (h1 : K1.Active) (h2 : K2.Active) :
    DkMath.DHNT.Unit.ratio
      (massUnit K2 h2)
      (massUnit K1 h1) =
    massGaugeRatio K1 K2 := by
  rfl

/-- A mass transition is measured by the same factor in DHNT ratio notation. -/
theorem dhnt_ratio_eq_factor_of_massScalesBy
    {u : ℝ} {K1 K2 : TwoPointKernel}
    (h1 : K1.Active) (h2 : K2.Active)
    (h : MassScalesBy u K1 K2) :
    DkMath.DHNT.Unit.ratio
      (massUnit K2 h2)
      (massUnit K1 h1) = u := by
  rw [dhnt_ratio_massUnit h1 h2]
  exact massGaugeRatio_eq_of_massScalesBy h1 h

/-- DHNT's ratio composition has the same target-first orientation. -/
theorem dhnt_ratio_comp_massUnit
    {K1 K2 K3 : TwoPointKernel}
    (h1 : K1.Active) (h2 : K2.Active) (h3 : K3.Active) :
    DkMath.DHNT.Unit.ratio
        (massUnit K3 h3) (massUnit K1 h1) =
      DkMath.DHNT.Unit.ratio
          (massUnit K3 h3) (massUnit K2 h2) *
        DkMath.DHNT.Unit.ratio
          (massUnit K2 h2) (massUnit K1 h1) := by
  exact DkMath.DHNT.Unit.ratio_comp
    (massUnit K3 h3) (massUnit K2 h2) (massUnit K1 h1)

end Bridge.UnitCycle

namespace PrimeScaleStep

/-- An active prime scale step strictly increases the mass gauge. -/
theorem massGauge_lt
    {p : ℕ} {K1 K2 : TwoPointKernel}
    (h : PrimeScaleStep p K1 K2)
    (h1 : K1.Active) :
    massGauge K1 < massGauge K2 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast h.prime.two_le
  have hp1 : (1 : ℝ) < (p : ℝ) :=
    lt_of_lt_of_le (by norm_num) hp2
  have h1pos : 0 < massGauge K1 :=
    (massGauge_pos_iff_active K1).2 h1
  calc
    massGauge K1 = 1 * massGauge K1 := by ring
    _ < (p : ℝ) * massGauge K1 :=
      mul_lt_mul_of_pos_right hp1 h1pos
    _ = massGauge K2 := h.massScalesBy.symm

end PrimeScaleStep

namespace PrimeScaleChain

/-- A closed active prime chain has natural total product one. -/
theorem closed_prod_eq_one
    {K : TwoPointKernel} {ps : List ℕ}
    (h : PrimeScaleChain K K ps)
    (hK : K.Active) :
    ps.prod = 1 := by
  have hreal : (ps.prod : ℝ) = (1 : ℝ) :=
    MassScalesBy.factor_unique hK h.massScalesBy_prod (massScalesBy_refl K)
  exact_mod_cast hreal

/-- A nonempty prime chain strictly increases the endpoint mass gauge. -/
theorem massGauge_lt_of_nonempty
    {K1 K2 : TwoPointKernel} {ps : List ℕ}
    (h : PrimeScaleChain K1 K2 ps)
    (h1 : K1.Active)
    (hne : ps ≠ []) :
    massGauge K1 < massGauge K2 := by
  revert h1 hne
  induction h with
  | nil K =>
      intro _ hne
      exact (hne rfl).elim
  | @cons p K1 K2 K3 ps hStep hTail ih =>
      intro h1 hne
      have h12 : massGauge K1 < massGauge K2 :=
        hStep.massGauge_lt h1
      cases ps with
      | nil =>
          cases hTail
          exact h12
      | cons q qs =>
          have h23 : massGauge K2 < massGauge K3 :=
            ih (hStep.target_active h1) (by simp)
          exact lt_trans h12 h23

/-- An active prime chain returning to its source must be empty. -/
theorem eq_nil_of_closed_active
    {K : TwoPointKernel} {ps : List ℕ}
    (h : PrimeScaleChain K K ps)
    (hK : K.Active) :
    ps = [] := by
  by_contra hne
  exact (lt_irrefl (massGauge K))
    (massGauge_lt_of_nonempty h hK hne)

end PrimeScaleChain

namespace PrimeScaleStep

/-- A prime step has DHNT ratio equal to its natural prime label. -/
theorem dhnt_ratio_eq_prime
    {p : ℕ} {K1 K2 : TwoPointKernel}
    (h : PrimeScaleStep p K1 K2)
    (h1 : K1.Active) :
    DkMath.DHNT.Unit.ratio
      (Bridge.UnitCycle.massUnit K2 (h.target_active h1))
      (Bridge.UnitCycle.massUnit K1 h1) = (p : ℝ) := by
  rw [Bridge.UnitCycle.dhnt_ratio_massUnit h1 (h.target_active h1)]
  exact massGaugeRatio_eq_of_massScalesBy h1 h.massScalesBy

end PrimeScaleStep

/-- A deterministic choice of prime-labelled successor on active kernels. -/
structure PrimeScaleDynamics where
  step : ActiveKernel → ActiveKernel
  label : ActiveKernel → ℕ
  primeStep : ∀ K, PrimeScaleStep (label K) K.1 (step K).1

namespace PrimeScaleDynamics

/-- A deterministic prime-scale dynamics strictly increases the mass gauge. -/
theorem massGauge_strict
    (D : PrimeScaleDynamics) (K : ActiveKernel) :
    massGauge K.1 < massGauge (D.step K).1 :=
  PrimeScaleStep.massGauge_lt (D.primeStep K) K.2

/-- A deterministic strict prime-scale dynamics has no nontrivial cycle. -/
theorem no_nontrivial_cycle
    (D : PrimeScaleDynamics) :
    ∀ k K,
      DkMath.UnitCycle.iterate D.step k K = K →
      k = 0 := by
  exact DkMath.UnitCycle.no_nontrivial_cycle_of_strict_invariant
    (T := D.step)
    (I := fun K : ActiveKernel => massGauge K.1)
    (fun K => D.massGauge_strict K)

end PrimeScaleDynamics

end
end DkMath.NumberGeometry
