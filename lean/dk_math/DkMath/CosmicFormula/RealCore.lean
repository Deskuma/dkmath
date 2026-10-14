/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Choose.Sum

namespace DkMath.CosmicFormulaDim

open scoped BigOperators

/-! The real-valued algebraic kernel shared with the analytic dimension layer. -/

/-- The real-valued body term in the dimensional cosmic formula. -/
noncomputable def GReal (d : ℕ) (x u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range d,
    (Nat.choose d (k + 1) : ℝ) * x ^ k * u ^ (d - 1 - k)

end DkMath.CosmicFormulaDim
