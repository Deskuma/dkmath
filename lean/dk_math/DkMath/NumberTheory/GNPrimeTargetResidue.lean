/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.GNDegreeFactorization
import DkMath.NumberTheory.WeightedGNBridge

#print "file: DkMath.NumberTheory.GNPrimeTargetResidue"

namespace DkMath.NumberTheory

open DkMath.CosmicFormulaBinom

/-!
## Prime-target residue filter for positive GN representations

For a positive representation of a prime target, GNPC-003 first makes the
degree prime.  The prime-row congruence then rules out divisibility of the
boundary by that degree, and forces the target to be `1` modulo the degree.
The resulting divisibility condition is a necessary filter only; it is not a
classification or a converse construction theorem.
-/

/-- A prime GN target cannot have its prime degree divide the boundary. -/
theorem GNPositiveRepresentation.degree_not_dvd_boundary_of_target_prime
    {p d x u : ℕ}
    (hrep : GNPositiveRepresentation p d x u)
    (hp : Nat.Prime p) :
    ¬ d ∣ x := by
  have hdegree : Nat.Prime d :=
    GNPositiveRepresentation.degree_prime_of_target_prime hrep hp
  have hbounds := GNPositiveRepresentation.bounds hrep
  rcases hbounds with ⟨_, _, _, hdp, _, _⟩
  rcases hrep with ⟨hd, _, _, hvalue⟩
  intro hdx
  have hxp : d ∣ x ^ (d - 1) := by
    exact dvd_pow hdx (by omega)
  have hright :
      DkMath.CosmicFormulaBinom.GN d x u ≡ x ^ (d - 1) [MOD d] :=
    prime_GN_modEq_rightBoundary hdegree
  have hzero_right : x ^ (d - 1) ≡ 0 [MOD d] :=
    Nat.modEq_zero_iff_dvd.mpr hxp
  have hzero :
      DkMath.CosmicFormulaBinom.GN d x u ≡ 0 [MOD d] :=
    hright.trans hzero_right
  have hdivGN : d ∣ DkMath.CosmicFormulaBinom.GN d x u :=
    Nat.modEq_zero_iff_dvd.mp hzero
  have hdivp : d ∣ p := by
    rw [← hvalue]
    exact hdivGN
  have hdp_eq : d = p :=
    (Nat.prime_dvd_prime_iff_eq hdegree hp).mp hdivp
  exact (Nat.ne_of_lt hdp) hdp_eq

/-- A prime target is congruent to one modulo its positive GN degree. -/
theorem GNPositiveRepresentation.target_modEq_one_degree_of_target_prime
    {p d x u : ℕ}
    (hrep : GNPositiveRepresentation p d x u)
    (hp : Nat.Prime p) :
    p ≡ 1 [MOD d] := by
  have hdegree : Nat.Prime d :=
    GNPositiveRepresentation.degree_prime_of_target_prime hrep hp
  have hnotdvd : ¬ d ∣ x :=
    GNPositiveRepresentation.degree_not_dvd_boundary_of_target_prime hrep hp
  have hmodGN :
      DkMath.CosmicFormulaBinom.GN d x u ≡ 1 [MOD d] :=
    prime_GN_modEq_one_of_not_dvd_x hdegree hnotdvd
  rcases hrep with ⟨_, _, _, hvalue⟩
  rw [hvalue] at hmodGN
  exact hmodGN

/-- The prime degree of a positive representation divides the target minus one. -/
theorem GNPositiveRepresentation.degree_dvd_target_sub_one_of_target_prime
    {p d x u : ℕ}
    (hrep : GNPositiveRepresentation p d x u)
    (hp : Nat.Prime p) :
    d ∣ p - 1 := by
  have hmod : p ≡ 1 [MOD d] :=
    GNPositiveRepresentation.target_modEq_one_degree_of_target_prime hrep hp
  have hp1 : 1 ≤ p := hp.one_lt.le
  exact (Nat.modEq_iff_dvd' hp1).mp hmod.symm

/-- The prime-degree, residue, and diagonal-floor filters for a prime target. -/
theorem GNPositiveRepresentation.prime_degree_constraints
    {p d x u : ℕ}
    (hrep : GNPositiveRepresentation p d x u)
    (hp : Nat.Prime p) :
    Nat.Prime d ∧ d ∣ p - 1 ∧ 2 ^ d - 1 ≤ p := by
  have hdegree : Nat.Prime d :=
    GNPositiveRepresentation.degree_prime_of_target_prime hrep hp
  have hdvd : d ∣ p - 1 :=
    GNPositiveRepresentation.degree_dvd_target_sub_one_of_target_prime hrep hp
  have hfloor := (GNPositiveRepresentation.bounds hrep).1
  exact ⟨hdegree, hdvd, hfloor⟩

end DkMath.NumberTheory
