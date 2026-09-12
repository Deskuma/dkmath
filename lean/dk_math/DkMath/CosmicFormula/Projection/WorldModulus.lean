/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/

import DkMath.CosmicFormula.Projection.CF2DBridge
import DkMath.NumberTheory.PrimeGauge.PrimorialSync

#print "file: DkMath.CosmicFormula.Projection.WorldModulus"

/-!
# Finite world-modulus projection and mesh

The finite product modulus supplies a real projection gap `1 / M`.  A fresh
prime insertion multiplies `M` by that prime and therefore divides the mesh by
the same factor.  These are exact finite coordinate identities; no density,
limit, or prime-realization statement is introduced.
-/

namespace DkMath.CosmicFormula.Projection

open DkMath.NumberTheory
open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.CosmicFormula.Rotation.CF2D

private theorem primeWorldModulus_pos
    {S : Finset ℕ} (hS : KnownPrimeScales S) :
    0 < primeWorldModulus S := by
  simpa [primeWorldModulus] using
    (Finset.prod_pos (s := S) (f := fun p : ℕ => p)
      (fun p hp => (hS hp).pos))

/-- The finite world modulus has projection gap `1 / M`. -/
theorem worldModulus_projection_gap
    {S : Finset ℕ} (hS : KnownPrimeScales S) :
    U ((primeWorldModulus S : ℝ) - 1) =
      1 / (primeWorldModulus S : ℝ) := by
  have hM : 0 < primeWorldModulus S := primeWorldModulus_pos hS
  simpa [regularPhaseStep, DkMath.Analysis.DkNNRealQ.normalizedCycleStep] using
    (projectionGap_eq_regularPhaseStep (k := primeWorldModulus S) hM)

/-- The finite world modulus has projection coordinate `-1 + 1 / M`. -/
theorem worldModulus_projection_add_one
    {S : Finset ℕ} (hS : KnownPrimeScales S) :
    Pi ((primeWorldModulus S : ℝ) - 1) + 1 =
      1 / (primeWorldModulus S : ℝ) := by
  calc
    Pi ((primeWorldModulus S : ℝ) - 1) + 1 =
        U ((primeWorldModulus S : ℝ) - 1) := by
      apply cosmicProjection_gap_eq
      have hM : 0 < primeWorldModulus S := primeWorldModulus_pos hS
      rw [show (primeWorldModulus S : ℝ) - 1 + 1 =
          (primeWorldModulus S : ℝ) by ring]
      exact_mod_cast hM.ne'
    _ = 1 / (primeWorldModulus S : ℝ) := worldModulus_projection_gap hS

/-- A fresh-prime insertion refines the finite mesh by the factor `q`. -/
theorem freshPrime_refinement_mesh
    {S : Finset ℕ} (hS : KnownPrimeScales S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) :
    1 / (primeWorldModulus (insert q S) : ℝ) =
      (1 / (primeWorldModulus S : ℝ)) / (q : ℝ) := by
  have hM : 0 < primeWorldModulus S := primeWorldModulus_pos hS
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hMR : (primeWorldModulus S : ℝ) ≠ 0 := by
    exact_mod_cast hM.ne'
  rw [primeWorldModulus_insert hqS]
  norm_num [Nat.cast_mul, hqR, hMR]
  field_simp [hqR, hMR]

end DkMath.CosmicFormula.Projection
