/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.ValuationFlow.Basic
import DkMath.NumberTheory.PrimitiveBeam
import DkMath.NumberTheory.ZsigmondyCyclotomicSquarefree

#print "file: DkMath.NumberTheory.ValuationFlow.Primitive"

open DkMath.CosmicFormulaBinom

namespace DkMath.NumberTheory.ValuationFlow

open DkMath.NumberTheory.PrimitiveBeam

/-- Re-export the primitive-prime predicate under the valuation-flow namespace. -/
abbrev PrimitivePrimeFlowWitness (q a b d : ℕ) : Prop :=
  PrimitivePrimeFactorOfDiffPow q a b d

/-- A primitive-flow witness carries its prime channel. -/
theorem primitivePrimeFlow_prime
    {q a b d : ℕ}
    (hq : PrimitivePrimeFlowWitness q a b d) :
    Nat.Prime q :=
  hq.1

/-- A primitive-flow witness contributes a prime channel on the diff side. -/
theorem primitivePrimeFlow_dvd_diff
    {q a b d : ℕ}
    (hq : PrimitivePrimeFlowWitness q a b d) :
    q ∣ a ^ d - b ^ d :=
  hq.2.1

/-- A primitive prime contributes no boundary mass. -/
theorem primitivePrimeFlow_boundaryMass_eq_zero
    {q a b d : ℕ}
    (hq : PrimitivePrimeFlowWitness q a b d)
    (hd1 : 1 < d) :
    boundaryMass q a b = 0 := by
  exact boundaryMass_eq_zero_of_not_dvd (primitive_prime_not_dvd_boundary hq hd1)

/-- A primitive prime reaches the beam / `GN` factor. -/
theorem primitivePrimeFlow_reaches_beam
    {q a b d : ℕ}
    (hq : PrimitivePrimeFlowWitness q a b d)
    (hd : 0 < d) (hd1 : 1 < d)
    (hab_lt : b < a) :
    q ∣ GN d (a - b) b := by
  exact primitive_prime_dvd_GN hq hd hd1 hab_lt

/-- The primitive-prime diff mass equals the beam mass. -/
theorem primitivePrimeFlow_diffMass_eq_beamMass
    {q a b d : ℕ}
    (hq : PrimitivePrimeFlowWitness q a b d)
    (hd : 0 < d) (hd1 : 1 < d)
    (hab_lt : b < a) :
    diffMass q a b d = beamMass q a b d := by
  exact primitive_prime_padic_eq_GN hq hd hd1 hab_lt

/--
Under a squarefree beam hypothesis, the primitive-prime diff mass is at most `1`.
-/
theorem primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
    {q a b d : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hpnd : ¬ d ∣ a - b)
    (hq : PrimitivePrimeFlowWitness q a b d)
    (hG_sq : Squarefree (GN d (a - b) b)) :
    diffMass q a b d ≤ 1 := by
  exact primitive_prime_padic_bound_diff_of_squarefree_GN
    hd_prime hd_ge hab_lt hb hab hpnd hq hG_sq

#print axioms primitivePrimeFlow_diffMass_le_one_of_squarefree_beam

end DkMath.NumberTheory.ValuationFlow
