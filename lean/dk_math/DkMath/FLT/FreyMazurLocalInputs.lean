/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTriadicComponentObstruction
import DkMath.Lib.NumberTheory.EllipticRationalLocalTransport

#print "file: DkMath.FLT.FreyMazurLocalInputs"

/-!
# The local point inputs for Mazur Step Three

A Cofixed residual line yields one rational exact-order `2*p` point `Q` on
the existing integer quotient.  Its doubled base change has exact order `p`,
is Galois fixed, and is outside the smooth zero component at every extension
valuation above `2` and `3`.  The same point is used at both primes.

These are the point and local inputs to the external Step Three theorem.
The modular-curve theorem which derives exclusion at the other bad primes,
and its later global torsion argument, are separate mathematical obligations.
-/

namespace DkMath.FLT.Frey.Source

open WeierstrassCurve
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open FreyLocalReduction EllipticGoodReductionSeparation EllipticSmoothReduction
open EllipticTorsionRepresentation EllipticRationalLocalTransport
open EllipticLocalComponentObstructionCharTwo WeierstrassVariableChange

noncomputable section
variable {p : ℕ} [Fact p.Prime] (S : Source p)

/-- The dyadic presentation is the same coefficientwise integer model. -/
theorem residualDyadicValuationModel_eq_integer_map
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    S.residualDyadicValuationModel L hline hcofixed =
      (S.residualIntegerKernelModel L hline hcofixed.isStable).map
        (Int.castRingHom (localValuationSubring 2)) := by
  ext <;> simp [residualDyadicValuationModel, mapModelToValuationSubring]

/-- The integer-model inputs at the two anchor primes, including the nonzero
generic discriminant.  No semistability condition at all other primes is
inserted as an additional hypothesis. -/
theorem residual_cofixed_mazur_integer_invariants
    (hp5 : 5 ≤ p) (hbe : Even S.b)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    (S.residualIntegerKernelModel L hline hcofixed.isStable).Δ ≠ 0 ∧
      ∀ q : ℕ, q = 2 ∨ q = 3 →
        (q : ℤ) ∣ (S.residualIntegerKernelModel L hline hcofixed.isStable).Δ ∧
        ¬ (q : ℤ) ∣ (S.residualIntegerKernelModel L hline hcofixed.isStable).c₄ := by
  refine ⟨S.residual_integer_kernel_model_discriminant_ne_zero (by omega)
    L hline hcofixed.isStable, ?_⟩
  intro q hq
  rcases hq with rfl | rfl
  · have hr := S.residualDyadicValuationModel_residue_invariants hp5 L hline hcofixed
    rw [S.residualDyadicValuationModel_eq_integer_map L hline hcofixed] at hr
    exact (integer_residue_invariants_iff _ (localValuationSubring 2)
      Nat.prime_two (localValuationSubring_liesOverPrime 2)).mp hr
  · have hr := S.residualTriadicValuationModel_residue_invariants hp5 hbe L hline hcofixed
    exact (integer_residue_invariants_iff _ (localValuationSubring 3)
      Nat.prime_three (localValuationSubring_liesOverPrime 3)).mp hr

/-- Every rational `2*p` point supplied by the same Cofixed quotient has its
double outside the rational dyadic zero component. -/
theorem residual_cofixed_two_nsmul_not_smooth_at_two
    (hp5 : 5 ≤ p) (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (Q : ((S.residualIntegerKernelModel L hline hcofixed.isStable).map
      (Int.castRingHom ℚ)).toAffine.Point) (hQ : addOrderOf Q = 2 * p) :
    ¬ HasSmoothReduction
      ((S.residualIntegerKernelModel L hline hcofixed.isStable).map
        (Int.castRingHom (localValuationSubring 2))) (2 • Q) := by
  let Wv := S.residualDyadicValuationModel L hline hcofixed
  let e := pointEquivOfModelEq
    (S.residualDyadicValuationModel_map_subtype L hline hcofixed).symm
  obtain ⟨hΔ, hc4⟩ := S.residualDyadicValuationModel_residue_invariants hp5 L hline hcofixed
  have hn := localValuationSubring_two_double_not_mem_zeroComponent_of_residue_invariants
    hp5 Wv hΔ hc4 ((e.addOrderOf_eq Q).trans hQ)
  have hWv : Wv = (S.residualIntegerKernelModel L hline hcofixed.isStable).map
      (Int.castRingHom (localValuationSubring 2)) := by
    exact S.residualDyadicValuationModel_eq_integer_map L hline hcofixed
  have hn' : ¬ HasSmoothReduction Wv (2 • e Q) := hn
  rw [← map_nsmul e] at hn'
  have hs := hasSmoothReduction_pointEquivOfModelEq Wv
    (S.residualDyadicValuationModel_map_subtype L hline hcofixed).symm (2 • Q)
  rw [← hWv]
  exact fun h => hn' (hs.mpr h)

/-- The single doubled rational point is outside every geometric local zero
component above `2` and `3`.  Only the rational residue fields are counted;
`hasSmoothReduction_localValuationSubring_baseChange_iff` transports the result. -/
theorem residual_cofixed_two_nsmul_not_smooth_above_two_three
    (hp5 : 5 ≤ p) (hbe : Even S.b)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (Q : ((S.residualIntegerKernelModel L hline hcofixed.isStable).map
      (Int.castRingHom ℚ)).toAffine.Point) (hQ : addOrderOf Q = 2 * p) :
    ∀ q : ℕ, q = 2 ∨ q = 3 →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), ValuationInertia.LiesOverPrime A q →
        ¬ HasSmoothReduction
          ((S.residualIntegerKernelModel L hline hcofixed.isStable).map (Int.castRingHom A))
          (baseChangePoint
            ((S.residualIntegerKernelModel L hline hcofixed.isStable).map (Int.castRingHom ℚ))
            (2 • Q)) := by
  intro q hq A hA
  rcases hq with rfl | rfl
  · rw [hasSmoothReduction_localValuationSubring_baseChange_iff _ A hA]
    exact S.residual_cofixed_two_nsmul_not_smooth_at_two hp5 L hline hcofixed Q hQ
  · rw [hasSmoothReduction_localValuationSubring_baseChange_iff _ A hA]
    have hn := S.residual_cofixed_two_nsmul_not_mem_triadic_zeroComponent
      hp5 hbe L hline hcofixed Q hQ
    let e := pointEquivOfModelEq
      (S.residualTriadicValuationModel_map_subtype L hline hcofixed).symm
    have hn' : ¬ HasSmoothReduction (S.residualTriadicValuationModel L hline hcofixed)
        (2 • e Q) := hn
    rw [← map_nsmul e] at hn'
    exact fun h => hn' ((hasSmoothReduction_pointEquivOfModelEq _
      (S.residualTriadicValuationModel_map_subtype L hline hcofixed).symm (2 • Q)).mpr h)

/-- Cofixedness supplies all pointwise local data at `2` and `3` for a single
Galois-fixed geometric point of exact order `p` on the integer quotient.
This theorem assumes neither local transport nor the global Mazur theorem. -/
theorem residual_cofixed_implies_geometric_prime_torsion_local_inputs
    (hp5 : 5 ≤ p) (hbe : Even S.b)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ P : Points ((S.residualIntegerKernelModel L hline hcofixed.isStable).map
        (Int.castRingHom ℚ)),
      addOrderOf P = p ∧
      (∀ σ : Field.absoluteGaloisGroup ℚ,
        pointAction
          ((S.residualIntegerKernelModel L hline hcofixed.isStable).map
            (Int.castRingHom ℚ)) σ P = P) ∧
      ∀ q : ℕ, q = 2 ∨ q = 3 →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), ValuationInertia.LiesOverPrime A q →
          ¬ HasSmoothReduction
            ((S.residualIntegerKernelModel L hline hcofixed.isStable).map
              (Int.castRingHom A)) P := by
  obtain ⟨Q, hQ, hP, hfix⟩ := S.residual_cofixed_implies_geometric_rational_prime_torsion
    (by omega) hbe L hline hcofixed
  exact ⟨_, hP, hfix, S.residual_cofixed_two_nsmul_not_smooth_above_two_three
    hp5 hbe L hline hcofixed Q hQ⟩

end
end DkMath.FLT.Frey.Source
