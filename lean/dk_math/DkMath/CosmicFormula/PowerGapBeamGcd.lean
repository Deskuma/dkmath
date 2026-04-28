/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.PowerGapBeam
import DkMath.NumberTheory.GdcDivD

#print "file: DkMath.CosmicFormula.PowerGapBeamGcd"

/-!
# GCD Control for Power Gap/Beam

This file connects the Power Gap/Beam vocabulary to the existing
`GcdDiffPow` divisibility theorem.
-/

namespace DkMath.CosmicFormula.PowerGapBeam

open DkMath.Algebra.DiffPow

/-! ## GCD Bridge -/

/-- Under the primitive condition `gcd z x = 1`, the common divisor of the
    Power Gap and Power Beam divides the degree `d`.

This is the Power Gap/Beam wrapper around
`DkMath.NumberTheory.GcdDiffPow.gcd_divides_d`. -/
theorem gcd_powerGap_powerBeam_dvd_d_of_coprime_int
    {d : ℕ} {x z : ℤ}
    (hd : 1 ≤ d)
    (hcop : Int.gcd z x = 1) :
    Int.gcd (powerGap x z) (powerBeam d x z) ∣ d := by
  simpa [powerGap, powerBeam, DkMath.Algebra.DiffPow.diffPowSum] using
    DkMath.NumberTheory.GcdDiffPow.gcd_divides_d (a := z) (b := x) (d := d) hd hcop

/-- If a prime `p` does not divide `d`, then under `gcd z x = 1` it cannot
    divide both the Power Gap and the Power Beam. -/
theorem prime_not_dvd_d_not_dvd_powerGap_and_powerBeam
    {d p : ℕ} {x z : ℤ}
    (hd : 1 ≤ d)
    (hcop : Int.gcd z x = 1)
    (hpnd : ¬ p ∣ d) :
    ¬ (p ∣ (powerGap x z).natAbs ∧ p ∣ (powerBeam d x z).natAbs) := by
  intro hboth
  have hgcd_dvd_d : Int.gcd (powerGap x z) (powerBeam d x z) ∣ d :=
    gcd_powerGap_powerBeam_dvd_d_of_coprime_int (d := d) (x := x) (z := z) hd hcop
  have hp_dvd_gcd : p ∣ Int.gcd (powerGap x z) (powerBeam d x z) := by
    rw [Int.gcd_eq_natAbs]
    exact Nat.dvd_gcd hboth.1 hboth.2
  exact hpnd (dvd_trans hp_dvd_gcd hgcd_dvd_d)

end DkMath.CosmicFormula.PowerGapBeam
