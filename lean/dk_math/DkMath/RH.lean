/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.Basic  -- Basic Definitions and Utilities
import DkMath.RH.Basic
import DkMath.RH.Defs
import DkMath.RH.Lemmas

-- ----------------------------------------------------------------------------

namespace DkMath.RH

open DkMath.Basic
open DkMath.RH.Basic

#eval printValue ident
#eval printValue name

end DkMath.RH

-- ----------------------------------------------------------------------------

namespace DkMath.RH

-- Lemmas for Riemann Hypothesis Module

open scoped Real
open Complex

/-- 位相速度の微分可能性 -/
theorem phaseUnwrap_hasDerivAt
    (f : ℝ → ℂ) (t0 θ0 t : ℝ)
    (hcont : Continuous (phaseVel f)) :
    HasDerivAt (fun x => phaseUnwrap f t0 θ0 x) (phaseVel f t) t := by
  -- 定義を展開
  unfold phaseUnwrap
  -- 積分の微分定理を使う
  have h_integral : HasDerivAt (fun x => ∫ u in t0..x, phaseVel f u) (phaseVel f t) t := by
    have hint : IntervalIntegrable (fun u => phaseVel f u) MeasureTheory.volume t0 t :=
      Continuous.intervalIntegrable hcont t0 t
    -- Continuous から StronglyMeasurableAtFilter を導く
    have hmeas : StronglyMeasurableAtFilter (fun u => phaseVel f u) (nhds t) MeasureTheory.volume :=
      hcont.stronglyMeasurableAtFilter MeasureTheory.volume (nhds t)
    have h := intervalIntegral.integral_hasDerivAt_right hint hmeas
    have hcont_at : ContinuousAt (phaseVel f) t := hcont.continuousAt
    exact h hcont_at
  -- 定数を足しても微分は変わらない
  have h_eq :
    (fun x => θ0 + ∫ u in t0..x, phaseVel f u) =
    (fun x => (∫ u in t0..x, phaseVel f u) + θ0) := by
    ext; ring
  rw [h_eq]
  exact h_integral.add_const θ0

end DkMath.RH
