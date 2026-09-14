/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/

import DkMath.Gnomon.CosmicBridge
import DkMath.NumberTheory.MultiGauge.PrimeTransport

#print "file: DkMath.NumberTheory.MultiGauge.GnomonPetalTransition"

/-!
# Degree-two gnomon / Petal primitive transition provider

This module turns the production Petal multiplication law

`oddGnomon (petalMul a b) = oddGnomon a * oddGnomon b`

into a genuine degree-two `GNGaugeTransition`.  The transition numerator is
not copied from an endpoint: it is the independent Petal factor
`oddGnomon b`, while the denominator is `1`.

Thus the transition records a concrete primitive-shape multiplication in the
same natural GN observer used by `MultiGauge`.
-/

namespace DkMath.NumberTheory.MultiGauge

open DkMath.Gnomon

/-- The canonical degree-two GN stage whose value is the odd gnomon `2*n+1`. -/
def oddGnomonGaugeStage (n : ℕ) : GNGaugeStage 2 :=
  { x := 1
    u := n
    coprime := by simp }

/-- The normalized GN value of the canonical stage is the odd gnomon. -/
theorem oddGnomonGaugeStage_gnValue (n : ℕ) :
    (oddGnomonGaugeStage n).gnValue = oddGnomon n := by
  change DkMath.CosmicFormula.GTail 2 1 1 n = oddGnomon n
  exact (oddGnomon_eq_GTail_two_one_unit n).symm

/-- The full stage observer is also the odd gnomon because its boundary is `1`. -/
theorem oddGnomonGaugeStage_value (n : ℕ) :
    (oddGnomonGaugeStage n).value = oddGnomon n := by
  change 1 * (oddGnomonGaugeStage n).gnValue = oddGnomon n
  simpa using oddGnomonGaugeStage_gnValue n

/--
Petal multiplication supplies an unconditional degree-two primitive gauge
transition.  The independent factor `oddGnomon b` is exactly the numerator
support that can introduce new prime visibility.
-/
def gnomonPetalTransition (a b : ℕ) : GNGaugeTransition 2 :=
  { first := oddGnomonGaugeStage a
    second := oddGnomonGaugeStage (petalMul a b)
    numerator := oddGnomon b
    denominator := 1
    numerator_pos := oddGnomon_pos b
    denominator_pos := by simp
    balance := by
      simpa [oddGnomonGaugeStage_value] using oddGnomon_petalMul a b }

@[simp] theorem gnomonPetalTransition_numerator (a b : ℕ) :
    (gnomonPetalTransition a b).numerator = oddGnomon b := rfl

@[simp] theorem gnomonPetalTransition_denominator (a b : ℕ) :
    (gnomonPetalTransition a b).denominator = 1 := rfl

@[simp] theorem gnomonPetalTransition_first (a b : ℕ) :
    (gnomonPetalTransition a b).first = oddGnomonGaugeStage a := rfl

@[simp] theorem gnomonPetalTransition_second (a b : ℕ) :
    (gnomonPetalTransition a b).second =
      oddGnomonGaugeStage (petalMul a b) := rfl

/-- A prime escaping the first Petal stage remains invisible after multiplying
by a Petal factor that it does not divide. -/
theorem primeEscapes_gnomonPetalTransition_second_of_first
    {q a b : ℕ}
    (hq : Nat.Prime q)
    (hEscape : PrimeEscapes q (oddGnomonGaugeStage a))
    (hFactor : ¬ q ∣ oddGnomon b) :
    PrimeEscapes q (oddGnomonGaugeStage (petalMul a b)) := by
  exact primeEscapes_second_of_first_of_not_dvd_numerator
    hq (gnomonPetalTransition a b) hEscape hFactor

/-- If a prime is newly captured after Petal multiplication, it must divide the
independent Petal factor carried by the transition numerator. -/
theorem prime_dvd_oddGnomon_factor_of_petal_new_capture
    {q a b : ℕ}
    (hq : Nat.Prime q)
    (hEscape : PrimeEscapes q (oddGnomonGaugeStage a))
    (hCaught : PrimeCaught q (oddGnomonGaugeStage (petalMul a b))) :
    q ∣ oddGnomon b := by
  have hCaught' : q ∣ (gnomonPetalTransition a b).second.value := by
    simpa using hCaught
  rcases prime_dvd_second_value_imp_dvd_first_or_numerator
      hq (gnomonPetalTransition a b) hCaught' with hOld | hNew
  · exact False.elim (hEscape (by simpa using hOld))
  · simpa using hNew

end DkMath.NumberTheory.MultiGauge

#print axioms DkMath.NumberTheory.MultiGauge.oddGnomonGaugeStage_value
#print axioms DkMath.NumberTheory.MultiGauge.gnomonPetalTransition
#print axioms DkMath.NumberTheory.MultiGauge.prime_dvd_oddGnomon_factor_of_petal_new_capture
