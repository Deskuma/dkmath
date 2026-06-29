/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.Basic
import Mathlib.Topology.Constructions.SumProd

#print "file: DkMath.CosmicFormula.Rotation.CF2D.Topology"

/-!
# Product topology for CF2D states

This module gives `Vec R` the topology transported from `R × R`. It is a
structural bridge only: no metric, norm, orthogonality, circle, or angle is
introduced.
-/

namespace DkMath.CosmicFormula.Rotation.CF2D

namespace Vec

variable {R : Type*}

/-- Read a CF2D state as its ordered pair of coordinates. -/
def toProd (z : Vec R) : R × R :=
  (z.core, z.beam)

/-- Build a CF2D state from an ordered pair of coordinates. -/
def ofProd (p : R × R) : Vec R :=
  Vec.mk p.1 p.2

/-- CF2D states are equivalent to ordered coordinate pairs. -/
def equivProd : Vec R ≃ R × R where
  toFun := toProd
  invFun := ofProd
  left_inv z := by cases z; rfl
  right_inv p := by cases p; rfl

@[simp]
theorem toProd_mk (x y : R) :
    toProd (Vec.mk x y) = (x, y) := rfl

@[simp]
theorem ofProd_toProd (z : Vec R) :
    ofProd (toProd z) = z :=
  equivProd.left_inv z

@[simp]
theorem toProd_ofProd (p : R × R) :
    toProd (ofProd p) = p :=
  equivProd.right_inv p

end Vec

section Topology

variable {R : Type*} [TopologicalSpace R]

/--
The coordinate-product topology on `Vec R`.

This instance is induced by `Vec.toProd`, making coordinatewise continuity
the canonical topological interpretation of a CF2D state.
-/
instance : TopologicalSpace (Vec R) :=
  TopologicalSpace.induced Vec.toProd inferInstance

/-- The coordinate-pair representation is continuous by construction. -/
theorem continuous_vecToProd :
    Continuous (Vec.toProd : Vec R → R × R) :=
  continuous_induced_dom

/-- A map into `Vec R` is continuous exactly when both coordinates are. -/
theorem continuous_vec_iff
    {X : Type*} [TopologicalSpace X] {f : X → Vec R} :
    Continuous f ↔
      Continuous (fun x => (f x).core) ∧
        Continuous (fun x => (f x).beam) := by
  constructor
  · intro hf
    have hpair : Continuous (fun x => Vec.toProd (f x)) :=
      continuous_vecToProd.comp hf
    exact ⟨continuous_fst.comp hpair, continuous_snd.comp hpair⟩
  · rintro ⟨hcore, hbeam⟩
    rw [continuous_induced_rng]
    exact hcore.prodMk hbeam

/-- Coordinatewise continuous functions assemble to a continuous CF2D state. -/
theorem Continuous.vec_mk
    {X : Type*} [TopologicalSpace X] {f g : X → R}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => Vec.mk (f x) (g x)) :=
  continuous_vec_iff.mpr ⟨hf, hg⟩

section LevelSet

variable [Semiring R] (rho2 : R)

/--
The topology on a square-mass level set is the subtype topology inherited
from the coordinate-product topology on `Vec R`.
-/
instance : TopologicalSpace (LevelSet R rho2) :=
  inferInstanceAs (TopologicalSpace {z : Vec R // Vec.q2 z = rho2})

/-- Forgetting level-set membership is continuous. -/
theorem continuous_levelSet_val :
    Continuous (fun z : LevelSet R rho2 => z.1) :=
  continuous_subtype_val

end LevelSet

end Topology

end DkMath.CosmicFormula.Rotation.CF2D
