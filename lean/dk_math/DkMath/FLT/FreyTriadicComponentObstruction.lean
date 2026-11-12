/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.FreyDyadicComponentObstruction
import DkMath.FLT.FreyHnoSmallGoodPrime
import DkMath.Lib.NumberTheory.EllipticLocalComponentObstructionCharThree

#print "file: DkMath.FLT.FreyTriadicComponentObstruction"

/-!
# Cofixed Frey quotients at the triadic address

Cofixedness forces `3 ∣ abc`.  The existing bad-prime nodal geometry then
supplies `3 ∣ Δ` and `3 ∤ c₄` for the same integer quotient model.  Over the
actual rational valuation subring at `3`, the explicit characteristic-three
centre and `#E_sm ≤ 4 < p` exclude `2 • Q` from the smooth zero component
for every exact-order `2*p` point.  This universal pointwise form lets the
2-adic and 3-adic conditions use a single rational point.
-/

namespace DkMath.FLT.Frey.Source

open WeierstrassCurve IsLocalRing
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open FreyLocalReduction ValuationPrimeSupport ValuationPrimeExistence
open EllipticSmoothReduction EllipticGoodReductionSeparation
open EllipticLocalComponentObstructionCharThree WeierstrassVariableChange
open WeierstrassResidueModel

noncomputable section
variable {p : ℕ} [Fact p.Prime] (S : Source p)

/-- The same integer quotient, presented over the actual triadic subring. -/
def residualTriadicValuationModel
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    WeierstrassCurve (localValuationSubring 3) :=
  (S.residualIntegerKernelModel L hline hcofixed.isStable).map
    (Int.castRingHom (localValuationSubring 3))

/-- The triadic presentation has the original rational generic fibre. -/
theorem residualTriadicValuationModel_map_subtype
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    (S.residualTriadicValuationModel L hline hcofixed).map
        (localValuationSubring 3).subtype =
      (S.residualIntegerKernelModel L hline hcofixed.isStable).map
        (Int.castRingHom ℚ) := by
  ext <;> simp [residualTriadicValuationModel]

/-- Cofixedness supplies the triadic residue invariants without an extra
bad-reduction or singular-centre assumption. -/
theorem residualTriadicValuationModel_residue_invariants
    (hp5 : 5 ≤ p) (hbe : Even S.b)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ((S.residualTriadicValuationModel L hline hcofixed).map
          (residue (localValuationSubring 3))).Δ = 0 ∧
      ((S.residualTriadicValuationModel L hline hcofixed).map
          (residue (localValuationSubring 3))).c₄ ≠ 0 := by
  have hbad : (3 : ℤ) ∣ S.a * S.b * S.c :=
    S.residual_cofixed_forces_small_prime_support hp5 hbe hline hcofixed.isStable
      hcofixed 3 Nat.prime_three (by decide) (by omega)
  obtain ⟨A, hA⟩ := exists_liesOverPrime (L := AlgebraicClosure ℚ) Nat.prime_three
  obtain ⟨C, D, -, -⟩ := S.exists_criticalCentre_directions_at_bad_prime
    (Nat.Prime.pos (Fact.out : p.Prime)) (by decide : 3 ≠ 2) hbad A hA
  have hi := S.residual_integer_target_nodal_conditions (by omega) L hline
    hcofixed.isStable Nat.prime_three (by omega) A hA C D
  let Wint := S.residualIntegerKernelModel L hline hcofixed.isStable
  have h3A := (ValuationSubring.mem_nonunits_iff A).mp hA
  have h3v := (ValuationSubring.mem_nonunits_iff (localValuationSubring 3)).mp
    (localValuationSubring_liesOverPrime 3)
  have hΔdvd : (3 : ℤ) ∣ Wint.Δ := by
    by_contra hn
    exact hi.1.ne (valuation_intCast_eq_one_of_not_dvd A Nat.prime_three h3A hn)
  have hc4nd : ¬ (3 : ℤ) ∣ Wint.c₄ := by
    intro hd
    have hv := valuation_intCast_lt_one_of_dvd A h3A hd
    rw [hi.2] at hv
    exact lt_irrefl _ hv
  constructor
  · rw [WeierstrassCurve.map_Δ]
    apply (residue_zero_iff (localValuationSubring 3) _).mpr
    change (localValuationSubring 3).valuation
      (((Wint.map (Int.castRingHom (localValuationSubring 3))).Δ :
        localValuationSubring 3) : ℚ) < 1
    rw [WeierstrassCurve.map_Δ]
    simpa only [Int.coe_castRingHom, SubringClass.coe_intCast] using
      valuation_intCast_lt_one_of_dvd (localValuationSubring 3) h3v hΔdvd
  · rw [WeierstrassCurve.map_c₄]
    apply (residue_ne_zero_iff (localValuationSubring 3) _).mpr
    change (localValuationSubring 3).valuation
      (((Wint.map (Int.castRingHom (localValuationSubring 3))).c₄ :
        localValuationSubring 3) : ℚ) = 1
    rw [WeierstrassCurve.map_c₄]
    simpa only [Int.coe_castRingHom, SubringClass.coe_intCast] using
      valuation_intCast_eq_one_of_not_dvd (localValuationSubring 3) Nat.prime_three h3v hc4nd

/-- Every rational exact-order `2*p` point has its double outside the triadic
zero component of the same quotient. -/
theorem residual_cofixed_two_nsmul_not_mem_triadic_zeroComponent
    (hp5 : 5 ≤ p) (hbe : Even S.b)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (Q : ((S.residualIntegerKernelModel L hline hcofixed.isStable).map
      (Int.castRingHom ℚ)).toAffine.Point) (hQ : addOrderOf Q = 2 * p) :
    2 • pointEquivOfModelEq
      (S.residualTriadicValuationModel_map_subtype L hline hcofixed).symm Q ∉
        zeroComponentSubgroup (S.residualTriadicValuationModel L hline hcofixed) := by
  obtain ⟨hΔ, hc4⟩ := S.residualTriadicValuationModel_residue_invariants
    hp5 hbe L hline hcofixed
  apply localValuationSubring_three_double_not_mem_zeroComponent_of_residue_invariants
    hp5 _ hΔ hc4
  exact (pointEquivOfModelEq
    (S.residualTriadicValuationModel_map_subtype L hline hcofixed).symm).addOrderOf_eq Q |>.trans hQ

end
end DkMath.FLT.Frey.Source
