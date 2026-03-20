/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

import DkMath.CosmicFormula.CosmicDifferenceKernel

#print "file: DkMath.CosmicFormula.CosmicDerivativeBasic"

namespace DkMath.CosmicFormula

/--
Derivative criterion in cosmic-kernel form.

This is the `ℝ`-specialized bridge from `HasDerivAt` to a punctured-limit
statement of the difference kernel `cosmicKernel`.
-/
theorem hasDerivAt_iff_tendsto_cosmicKernel
    {f : ℝ → ℝ} {x L : ℝ} :
    HasDerivAt f L x ↔
      Filter.Tendsto (fun u : ℝ => cosmicKernel f x u)
        (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ))) (nhds L) := by
  simpa [cosmicKernel, delta, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (hasDerivAt_iff_tendsto_slope_zero (f := f) (f' := L) (x := x))

theorem tendsto_cosmicKernel_of_hasDerivAt
    {f : ℝ → ℝ} {x L : ℝ}
    (h : HasDerivAt f L x) :
    Filter.Tendsto (fun u : ℝ => cosmicKernel f x u)
      (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ))) (nhds L) :=
  (hasDerivAt_iff_tendsto_cosmicKernel).1 h

theorem hasDerivAt_of_tendsto_cosmicKernel
    {f : ℝ → ℝ} {x L : ℝ}
    (h :
      Filter.Tendsto (fun u : ℝ => cosmicKernel f x u)
        (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ))) (nhds L)) :
    HasDerivAt f L x :=
  (hasDerivAt_iff_tendsto_cosmicKernel).2 h

theorem hasDerivAt_id_cosmic (x : ℝ) :
    HasDerivAt (fun y : ℝ => y) 1 x := by
  simpa using (hasDerivAt_id x)

theorem tendsto_cosmicKernel_id (x : ℝ) :
    Filter.Tendsto (fun u : ℝ => cosmicKernel (fun y : ℝ => y) x u)
      (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ))) (nhds (1 : ℝ)) := by
  exact tendsto_cosmicKernel_of_hasDerivAt (hasDerivAt_id_cosmic x)

theorem hasDerivAt_const_cosmic (x c : ℝ) :
    HasDerivAt (fun _ : ℝ => c) 0 x := by
  simpa using (hasDerivAt_const x c)

theorem tendsto_cosmicKernel_const (x c : ℝ) :
    Filter.Tendsto (fun u : ℝ => cosmicKernel (fun _ : ℝ => c) x u)
      (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ))) (nhds (0 : ℝ)) := by
  exact tendsto_cosmicKernel_of_hasDerivAt (hasDerivAt_const_cosmic x c)

end DkMath.CosmicFormula
