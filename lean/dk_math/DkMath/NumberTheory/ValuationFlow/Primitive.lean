/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.ValuationFlow.Basic
import DkMath.NumberTheory.PrimitiveBeam

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
Under a local no-lift beam hypothesis, the primitive-prime diff mass is at most
`1`.

This is the thin valuation-flow surface over the `PrimitiveBeam` no-lift route.
-/
theorem primitivePrimeFlow_diffMass_le_one_of_noLift_beam
    {q a b d : ℕ}
    (hq : PrimitivePrimeFlowWitness q a b d)
    (hd : 0 < d) (hd1 : 1 < d)
    (hab_lt : b < a)
    (hNoLift : ¬ q ^ 2 ∣ GN d (a - b) b) :
    diffMass q a b d ≤ 1 := by
  exact primitive_prime_padic_bound_diff_of_noLift_GN hq hd hd1 hab_lt hNoLift

/--
Under a local squarefree beam hypothesis, the primitive-prime diff mass is at
most `1`.

This is a sufficient-condition wrapper over the no-lift route.
-/
theorem primitivePrimeFlow_diffMass_le_one_of_squarefree_beam_local
    {q a b d : ℕ}
    (hq : PrimitivePrimeFlowWitness q a b d)
    (hd : 0 < d) (hd1 : 1 < d)
    (hab_lt : b < a)
    (hG_sq : Squarefree (GN d (a - b) b)) :
    diffMass q a b d ≤ 1 := by
  exact primitive_prime_padic_bound_diff_of_squarefree_GN_local
    hq hd hd1 hab_lt hG_sq

/--
Compatibility wrapper with the old heavier squarefree-beam signature.

New callers should prefer `primitivePrimeFlow_diffMass_le_one_of_noLift_beam`
or `primitivePrimeFlow_diffMass_le_one_of_squarefree_beam_local`.
-/
theorem primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
    {q a b d : ℕ}
    (hd_prime : Nat.Prime d) (_hd_ge : 3 ≤ d)
    (hab_lt : b < a) (_hb : 0 < b) (_hab : Nat.Coprime a b)
    (_hpnd : ¬ d ∣ a - b)
    (hq : PrimitivePrimeFlowWitness q a b d)
    (hG_sq : Squarefree (GN d (a - b) b)) :
    diffMass q a b d ≤ 1 := by
  have hd : 0 < d := hd_prime.pos
  have hd1 : 1 < d := by omega
  exact primitivePrimeFlow_diffMass_le_one_of_squarefree_beam_local
    hq hd hd1 hab_lt hG_sq

#print axioms primitivePrimeFlow_diffMass_le_one_of_squarefree_beam

end DkMath.NumberTheory.ValuationFlow
