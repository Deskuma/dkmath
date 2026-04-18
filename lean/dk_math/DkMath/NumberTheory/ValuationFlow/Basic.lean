/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.ABC.PadicValNat
import DkMath.CosmicFormula.CosmicFormulaBinom

#print "file: DkMath.NumberTheory.ValuationFlow.Basic"

open DkMath.CosmicFormulaBinom

namespace DkMath.NumberTheory.ValuationFlow

/--
Minimal wrapper for a fixed-prime valuation profile.

At this stage the profile is deliberately lightweight: it only remembers the
prime and the associated `padicValNat` observation.
-/
structure ValuationProfile where
  prime : ℕ
  value : ℕ → ℕ

/-- The canonical valuation profile attached to a fixed prime `q`. -/
def profileOfPrime (q : ℕ) : ValuationProfile where
  prime := q
  value := padicValNat q

/-- `q`-adic load on the difference-power body `a^d - b^d`. -/
def diffMass (q a b d : ℕ) : ℕ :=
  padicValNat q (a ^ d - b ^ d)

/-- `q`-adic load on the boundary term `a - b`. -/
def boundaryMass (q a b : ℕ) : ℕ :=
  padicValNat q (a - b)

/-- `q`-adic load on the beam / cyclotomic factor `GN d (a - b) b`. -/
def beamMass (q a b d : ℕ) : ℕ :=
  padicValNat q (GN d (a - b) b)

@[simp] theorem profileOfPrime_apply (q n : ℕ) :
    (profileOfPrime q).value n = padicValNat q n := rfl

@[simp] theorem diffMass_def (q a b d : ℕ) :
    diffMass q a b d = padicValNat q (a ^ d - b ^ d) := rfl

@[simp] theorem boundaryMass_def (q a b : ℕ) :
    boundaryMass q a b = padicValNat q (a - b) := rfl

@[simp] theorem beamMass_def (q a b d : ℕ) :
    beamMass q a b d = padicValNat q (GN d (a - b) b) := rfl

theorem boundaryMass_eq_zero_of_not_dvd
    {q a b : ℕ} (hq : ¬ q ∣ a - b) :
    boundaryMass q a b = 0 := by
  exact padicValNat.eq_zero_of_not_dvd hq

end DkMath.NumberTheory.ValuationFlow
