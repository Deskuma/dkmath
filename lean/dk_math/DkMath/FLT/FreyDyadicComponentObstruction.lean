/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.FreyFiniteKernelNodalReduction
import DkMath.FLT.FreyRationalTwoPTorsion
import DkMath.Lib.NumberTheory.EllipticLocalComponentObstructionCharTwo
import DkMath.Lib.NumberTheory.FreyLocalValuationSubring
import DkMath.Lib.NumberTheory.ValuationPrimeExistence
import DkMath.Lib.NumberTheory.ValuationPrimeSupport
import DkMath.Lib.NumberTheory.WeierstrassResidueModel
import DkMath.Lib.NumberTheory.EllipticSmoothReduction
import DkMath.Lib.Algebra.FiniteAdditiveTorsionQuotient
import DkMath.Lib.RepresentationTheory.FixedCofixed
import DkMath.Lib.NumberTheory.WeierstrassVariableChange

#print "file: DkMath.FLT.FreyDyadicComponentObstruction"

/-!
# Cofixed Frey quotients at the dyadic address

This is the first concrete Frey specialization of the characteristic-two
component obstruction.  The proof is deliberately a transport diagram rather
than a new local-reduction theory:

1. `residual_cofixed_implies_rational_two_p_torsion` supplies a rational point
   of exact order `2 * p` on the integral quotient model.
2. `residual_integer_target_nodal_conditions`, evaluated at a valuation ring
   above `2`, supplies the integer divisibility facts
   `2 ∣ Δ` and `¬ 2 ∣ c₄`.
3. Those divisibility facts are transported to the concrete valuation
   subring `localValuationSubring 2`.
4. `localValuationSubring_two_component_prime_dvd_of_residue_invariants`
   excludes the transported point from the smooth zero component and forces
   `p` to divide the resulting abstract component quotient.

The conclusion is intentionally still about the quotient by the smooth
zero-component subgroup.  It does not identify that quotient with a Néron
component group and therefore does not by itself prove the global `hno`.
-/

namespace DkMath.FLT.Frey.Source

open WeierstrassCurve IsLocalRing
open DkMath.Lib.NumberTheory
open DkMath.Lib.NumberTheory.FreyLocalReduction
open DkMath.Lib.NumberTheory.ValuationPrimeExistence
open DkMath.Lib.NumberTheory.ValuationPrimeSupport
open DkMath.Lib.NumberTheory.WeierstrassResidueModel
open DkMath.Lib.Algebra
open DkMath.Lib.RepresentationTheory
open DkMath.Lib.NumberTheory.EllipticSmoothReduction
open DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation
open DkMath.Lib.NumberTheory.WeierstrassVariableChange
open DkMath.Lib.NumberTheory.EllipticLocalComponentObstructionCharTwo

noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)

local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- The dyadic valuation-subring presentation of a Cofixed quotient model. -/
noncomputable def residualDyadicValuationModel
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    WeierstrassCurve (localValuationSubring 2) :=
  mapModelToValuationSubring 2
    ((S.residualIntegerKernelModel L hline hcofixed.isStable).map
      (algebraMap ℤ (LocalRing 2)))

/--
The dyadic model has the same rational generic fibre as the integral quotient.
This is the coefficient identity used to transport the exact-order point.
-/
theorem residualDyadicValuationModel_map_subtype
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    (S.residualDyadicValuationModel L hline hcofixed).map
        (localValuationSubring 2).subtype =
      (S.residualIntegerKernelModel L hline hcofixed.isStable).map
        (Int.castRingHom ℚ) := by
  ext <;> simp [residualDyadicValuationModel, mapModelToValuationSubring]

/--
The nodal valuation conditions on the integral Frey quotient force the
dyadic residue invariants required by the finite-residue component theorem.
The only arithmetic conversion is elementary: a valuation `< 1` contradicts
the unit valuation of an integer not divisible by `2`, while valuation `= 1`
contradicts the `< 1` value of a divisible integer.
-/
theorem residualDyadicValuationModel_residue_invariants
    (hp5 : 5 ≤ p) (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ((S.residualDyadicValuationModel L hline hcofixed).map
          (residue (localValuationSubring 2))).Δ = 0 ∧
      ((S.residualDyadicValuationModel L hline hcofixed).map
          (residue (localValuationSubring 2))).c₄ ≠ 0 := by
  obtain ⟨A, hA⟩ := exists_liesOverPrime (L := AlgebraicClosure ℚ) Nat.prime_two
  obtain ⟨C, D, -, -⟩ := S.exists_dyadic_geometry hp5 A hA
  have hi := S.residual_integer_target_nodal_conditions (by omega) L hline
    hcofixed.isStable Nat.prime_two (by omega) A hA C D
  let Wint := S.residualIntegerKernelModel L hline hcofixed.isStable
  let Wv := S.residualDyadicValuationModel L hline hcofixed
  have h2A : A.valuation (2 : AlgebraicClosure ℚ) < 1 :=
    (ValuationSubring.mem_nonunits_iff _).mp hA
  have h2v : (localValuationSubring 2).valuation (2 : ℚ) < 1 :=
    (ValuationSubring.mem_nonunits_iff _).mp (localValuationSubring_liesOverPrime 2)
  have hΔdvd : (2 : ℤ) ∣ Wint.Δ := by
    by_contra hnd
    have hv := valuation_intCast_eq_one_of_not_dvd A Nat.prime_two h2A hnd
    have hlt : A.valuation ((Wint.Δ : ℤ) : AlgebraicClosure ℚ) < 1 := by
      simpa [Wint] using hi.1
    rw [hv] at hlt
    exact (lt_irrefl _ hlt)
  have hc4nd : ¬ (2 : ℤ) ∣ Wint.c₄ := by
    intro hd
    have hv := valuation_intCast_lt_one_of_dvd A h2A hd
    rw [hi.2] at hv
    exact (lt_irrefl _ hv)
  have hΔv : (localValuationSubring 2).valuation (Wv.Δ : ℚ) < 1 := by
    have hcoeff : (Wv.Δ : ℚ) = (Wint.Δ : ℚ) := by
      have h := congrArg WeierstrassCurve.Δ
        (S.residualDyadicValuationModel_map_subtype L hline hcofixed)
      change (localValuationSubring 2).subtype Wv.Δ =
        (Int.castRingHom ℚ) Wint.Δ
      simpa [Wint, Wv, WeierstrassCurve.map_Δ] using h
    rw [hcoeff]
    exact valuation_intCast_lt_one_of_dvd (localValuationSubring 2) h2v hΔdvd
  have hc4v : (localValuationSubring 2).valuation (Wv.c₄ : ℚ) = 1 := by
    have hcoeff : (Wv.c₄ : ℚ) = (Wint.c₄ : ℚ) := by
      have h := congrArg WeierstrassCurve.c₄
        (S.residualDyadicValuationModel_map_subtype L hline hcofixed)
      change (localValuationSubring 2).subtype Wv.c₄ =
        (Int.castRingHom ℚ) Wint.c₄
      simpa [Wint, Wv, WeierstrassCurve.map_c₄] using h
    rw [hcoeff]
    exact valuation_intCast_eq_one_of_not_dvd (localValuationSubring 2) Nat.prime_two h2v
      hc4nd
  refine ⟨?_, ?_⟩
  · rw [WeierstrassCurve.map_Δ]
    exact (residue_zero_iff (localValuationSubring 2) Wv.Δ).mpr hΔv
  · rw [WeierstrassCurve.map_c₄]
    exact (residue_ne_zero_iff (localValuationSubring 2) Wv.c₄).mpr hc4v

/--
Main NOTE-032 dyadic Frey endpoint.

A Cofixed stable line therefore yields an exact `2*p` rational point on the
explicit dyadic valuation model, that point is outside the smooth zero
component, and `p` divides the corresponding abstract component quotient.
All hypotheses needed to construct the residue invariants are supplied by the
existing Frey valuation geometry; no critical centre, tangent directions,
finite-residue instance, or Néron model is exposed to the caller.
-/
theorem residual_cofixed_forces_dyadic_component_prime_dvd
    (hp5 : 5 ≤ p) (hbe : Even S.b)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ Q : (S.residualDyadicValuationModel L hline hcofixed).map
        (localValuationSubring 2).subtype |>.toAffine.Point,
      addOrderOf Q = 2 * p ∧
        ¬ HasSmoothReduction (S.residualDyadicValuationModel L hline hcofixed) Q ∧
        p ∣ Nat.card (((S.residualDyadicValuationModel L hline hcofixed).map
          (localValuationSubring 2).subtype).toAffine.Point ⧸
            zeroComponentSubgroup (S.residualDyadicValuationModel L hline hcofixed)) := by
  obtain ⟨Q, hQ⟩ := S.residual_cofixed_implies_rational_two_p_torsion
    (by omega) hbe L hline hcofixed
  let Wint := S.residualIntegerKernelModel L hline hcofixed.isStable
  let Wv := S.residualDyadicValuationModel L hline hcofixed
  have hbase : Wv.map (localValuationSubring 2).subtype =
      Wint.map (Int.castRingHom ℚ) :=
    S.residualDyadicValuationModel_map_subtype L hline hcofixed
  let Qv : (Wv.map (localValuationSubring 2).subtype).toAffine.Point :=
    pointEquivOfModelEq hbase.symm Q
  have hQv : addOrderOf Qv = 2 * p := by
    exact (pointEquivOfModelEq hbase.symm).addOrderOf_eq Q |>.trans hQ
  obtain ⟨hΔ, hc4⟩ := residualDyadicValuationModel_residue_invariants S
    hp5 L hline hcofixed
  obtain ⟨hnot, hdiv⟩ :=
    localValuationSubring_two_component_prime_dvd_of_residue_invariants
      hp5 (by omega) Wv hΔ hc4 hQv
  exact ⟨Qv, hQv, hnot, hdiv⟩

end
end DkMath.FLT.Frey.Source
