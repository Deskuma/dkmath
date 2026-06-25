/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.CosmicFormula.CoreBeamGap
import DkMath.CosmicFormula.ResidualNat
import DkMath.CosmicFormula.ResidualInt

#print "file: DkMath.CosmicFormula.Mass.Core"

namespace DkMath.CosmicFormula.Mass

/--
Minimal nonnegative mass container.

This is intentionally small: the current phase only needs a reusable record for
nonnegative rational mass before the more structured branching API is added.
-/
structure MassSpace (α : Type _) where
  μ : α → ℚ
  nonneg : ∀ a, 0 ≤ μ a

/-- Named parts in the Big/Body/Gap/Core/Beam decomposition. -/
inductive CosmicPart
  | big
  | body
  | gap
  | core
  | beam
deriving DecidableEq, Repr

/--
Minimal API bundle for the Big/Body/Gap/Core/Beam layer.

The codomain is left generic so the same record can package the existing `ℕ`,
`ℤ`, and generic semiring versions.
-/
structure CosmicMassAPI (R : Type _) where
  massBig : ℕ → R → R → R
  massBody : ℕ → R → R → R
  massGap : ℕ → R → R → R
  massCore : ℕ → R → R → R
  massBeam : ℕ → R → R → R

/--
Extension of `CosmicMassAPI` that also carries the residual mass
`Big - Body`.
-/
structure CosmicResidualMassAPI (R : Type _) extends CosmicMassAPI R where
  massResidual : ℕ → R → R → R

namespace CosmicMassAPI

/-- Generic semiring API induced by `CoreBeamGap`. -/
def ofCoreBeamGap (R : Type _) [CommSemiring R] : CosmicMassAPI R where
  massBig := DkMath.CosmicFormula.CoreBeamGap.Big
  massBody := DkMath.CosmicFormulaBinom.BodyN
  massGap := fun d _x u => DkMath.CosmicFormula.CoreBeamGap.Gap d u
  massCore := fun d x _u => DkMath.CosmicFormula.CoreBeamGap.Core d x
  massBeam := DkMath.CosmicFormula.CoreBeamGap.Beam

end CosmicMassAPI

namespace CosmicResidualMassAPI

/-- `Nat` residual API induced by `ResidualNat`. -/
def ofResidualNat : CosmicResidualMassAPI ℕ where
  massBig := DkMath.CosmicFormula.big
  massBody := DkMath.CosmicFormula.body
  massGap := DkMath.CosmicFormula.gap
  massCore := DkMath.CosmicFormula.core
  massBeam := DkMath.CosmicFormula.beam
  massResidual := DkMath.CosmicFormula.residual

/-- `Int` residual API induced by `ResidualInt`. -/
def ofResidualInt : CosmicResidualMassAPI ℤ where
  massBig := DkMath.CosmicFormula.bigInt
  massBody := DkMath.CosmicFormula.bodyInt
  massGap := DkMath.CosmicFormula.gapInt
  massCore := DkMath.CosmicFormula.coreInt
  massBeam := DkMath.CosmicFormula.beamInt
  massResidual := DkMath.CosmicFormula.residualInt

end CosmicResidualMassAPI

end DkMath.CosmicFormula.Mass
