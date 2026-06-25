/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Mass.Core

#print "file: DkMath.CosmicFormula.Mass.Branch"

open scoped BigOperators

namespace DkMath.CosmicFormula.Mass

/-- Finite branching skeleton used by the first mass-flow layer. -/
structure Branching (α : Type _) where
  children : α → Finset α

/-- Total outgoing mass from a node to its finite children set. -/
def outgoingMass {α : Type _} [DecidableEq α]
    (M : MassSpace α) (B : Branching α) (a : α) : ℚ :=
  (B.children a).sum fun b => M.μ b

/--
Subconservative branching: the total child mass never exceeds the parent mass.

This is the finite combinatorial spine that later specializations can interpret
as a truncated adjoint/sub-Markov inequality.
-/
class SubConservative {α : Type _} [DecidableEq α]
    (M : MassSpace α) (B : Branching α) : Prop where
  outgoing_le : ∀ a, outgoingMass M B a ≤ M.μ a

section Basic

variable {α : Type _} [DecidableEq α]

/-- Outgoing mass is nonnegative when the node mass is pointwise nonnegative. -/
theorem outgoingMass_nonneg
    (M : MassSpace α) (B : Branching α) (a : α) :
    0 ≤ outgoingMass M B a := by
  simpa [outgoingMass] using Finset.sum_nonneg fun b _hb => M.nonneg b

/-- Core subconservative inequality in theorem form. -/
theorem outgoingMass_le_mass
    (M : MassSpace α) (B : Branching α) [hB : SubConservative M B] (a : α) :
    outgoingMass M B a ≤ M.μ a :=
  hB.outgoing_le a

/-- Alias with the `branch sum <= parent` wording used in the design notes. -/
theorem branch_sum_le_parent
    (M : MassSpace α) (B : Branching α) [SubConservative M B] (a : α) :
    outgoingMass M B a ≤ M.μ a :=
  outgoingMass_le_mass M B a

/-- Empty branching emits no mass. -/
@[simp] theorem outgoingMass_empty
    (M : MassSpace α) (a : α) :
    outgoingMass M { children := fun _ => ∅ } a = 0 := by
  simp [outgoingMass]

end Basic

end DkMath.CosmicFormula.Mass
