/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.PowerGapBeamGN
import DkMath.CosmicFormula.PowerGapBeamGcd
import DkMath.NumberTheory.PrimitiveBeam

#print "file: DkMath.CosmicFormula.PowerGapBeamPrimitive"

/-!
# Primitive Power Beam Bridge

This file keeps the heavier `PrimitiveBeam` and FLT contradiction dependencies
out of the lightweight `PowerGapBeamGN` bridge.
-/

namespace DkMath.CosmicFormula.PowerGapBeam

/-- Primitive-prime divisibility from the Nat `GN` API, transported to the
    integer endpoint Power Beam used by the valuation engine. -/
theorem primitive_prime_dvd_powerBeam_three_natAbs
    {q a b : ℕ}
    (hq : DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q a b 3)
    (hab_lt : b < a) :
    q ∣ (powerBeam 3 (b : ℤ) (a : ℤ)).natAbs := by
  have hGN_nat :
      q ∣ DkMath.CosmicFormulaBinom.GN 3 (a - b) b :=
    DkMath.NumberTheory.PrimitiveBeam.primitive_prime_dvd_GN
      (q := q) (a := a) (b := b) (d := 3)
      hq (by norm_num) (by norm_num) hab_lt
  have hbeam_nat :
      q ∣ (DkMath.CosmicFormulaBinom.GN 3 ((a : ℤ) - (b : ℤ)) (b : ℤ)).natAbs := by
    have hsub_cast : ((a - b : ℕ) : ℤ) = (a : ℤ) - (b : ℤ) :=
      Nat.cast_sub (Nat.le_of_lt hab_lt)
    have hGN_cast :
        ((DkMath.CosmicFormulaBinom.GN 3 (a - b) b : ℕ) : ℤ) =
          DkMath.CosmicFormulaBinom.GN 3 ((a : ℤ) - (b : ℤ)) (b : ℤ) := by
      rw [← hsub_cast]
      simp
    have hGN_int :
        (q : ℤ) ∣
          DkMath.CosmicFormulaBinom.GN 3 ((a : ℤ) - (b : ℤ)) (b : ℤ) := by
      rw [← hGN_cast]
      exact_mod_cast hGN_nat
    exact Int.natCast_dvd.mp hGN_int
  simpa [powerBeam_three_eq_GN_of_gap] using hbeam_nat

/-- Cubic FLT contradiction from a `GN` valuation upper bound for the observed
    endpoint Beam. -/
theorem flt_three_beam_GN_val_le_one_contradiction
    {p : ℕ} {x y z : ℤ}
    (hcop : Int.gcd z x = 1)
    (hflt : x ^ 3 + y ^ 3 = z ^ 3)
    (hy_ne : y.natAbs ≠ 0)
    (hp : Nat.Prime p)
    (hpnd : ¬ p ∣ 3)
    (hbeam : p ∣ (powerBeam 3 x z).natAbs)
    (hbeam_ne : (powerBeam 3 x z).natAbs ≠ 0)
    (hGN_le_one :
      padicValNat p (DkMath.CosmicFormulaBinom.GN 3 (z - x) x).natAbs ≤ 1) :
    False :=
  flt_beam_prime_val_le_one_contradiction
    (d := 3) (p := p) (x := x) (y := y) (z := z)
    (by norm_num) (by norm_num) hcop hflt hy_ne hp hpnd hbeam hbeam_ne
    (powerBeam_three_padicValNat_le_one_of_GN_le_one
      (p := p) (a := z) (b := x) hGN_le_one)

/-- Cubic FLT contradiction from squarefreeness of the corresponding `GN`
    endpoint Beam. -/
theorem flt_three_beam_GN_squarefree_contradiction
    {p : ℕ} {x y z : ℤ}
    (hcop : Int.gcd z x = 1)
    (hflt : x ^ 3 + y ^ 3 = z ^ 3)
    (hy_ne : y.natAbs ≠ 0)
    (hp : Nat.Prime p)
    (hpnd : ¬ p ∣ 3)
    (hbeam : p ∣ (powerBeam 3 x z).natAbs)
    (hbeam_ne : (powerBeam 3 x z).natAbs ≠ 0)
    (hGN_sq :
      Squarefree (DkMath.CosmicFormulaBinom.GN 3 (z - x) x).natAbs) :
    False :=
  flt_beam_squarefree_prime_contradiction
    (d := 3) (p := p) (x := x) (y := y) (z := z)
    (by norm_num) (by norm_num) hcop hflt hy_ne hp hpnd hbeam hbeam_ne
    (powerBeam_three_squarefree_of_GN_squarefree
      (a := z) (b := x) hGN_sq)

/-- Cubic FLT contradiction from a Nat primitive-prime witness and a `GN`
    valuation upper bound. -/
theorem flt_three_primitive_GN_val_le_one_contradiction
    {q a b : ℕ} {y : ℤ}
    (hq : DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q a b 3)
    (hab_lt : b < a)
    (hcop : Int.gcd (a : ℤ) (b : ℤ) = 1)
    (hflt : (b : ℤ) ^ 3 + y ^ 3 = (a : ℤ) ^ 3)
    (hy_ne : y.natAbs ≠ 0)
    (hqnd : ¬ q ∣ 3)
    (hbeam_ne : (powerBeam 3 (b : ℤ) (a : ℤ)).natAbs ≠ 0)
    (hGN_le_one :
      padicValNat q
        (DkMath.CosmicFormulaBinom.GN 3 ((a : ℤ) - (b : ℤ)) (b : ℤ)).natAbs ≤ 1) :
    False :=
  flt_three_beam_GN_val_le_one_contradiction
    (p := q) (x := (b : ℤ)) (y := y) (z := (a : ℤ))
    hcop hflt hy_ne hq.1 hqnd
    (primitive_prime_dvd_powerBeam_three_natAbs hq hab_lt)
    hbeam_ne hGN_le_one

/-- Cubic FLT contradiction from a Nat primitive-prime witness and
    squarefreeness of the corresponding `GN` Beam. -/
theorem flt_three_primitive_GN_squarefree_contradiction
    {q a b : ℕ} {y : ℤ}
    (hq : DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q a b 3)
    (hab_lt : b < a)
    (hcop : Int.gcd (a : ℤ) (b : ℤ) = 1)
    (hflt : (b : ℤ) ^ 3 + y ^ 3 = (a : ℤ) ^ 3)
    (hy_ne : y.natAbs ≠ 0)
    (hqnd : ¬ q ∣ 3)
    (hbeam_ne : (powerBeam 3 (b : ℤ) (a : ℤ)).natAbs ≠ 0)
    (hGN_sq :
      Squarefree
        (DkMath.CosmicFormulaBinom.GN 3 ((a : ℤ) - (b : ℤ)) (b : ℤ)).natAbs) :
    False :=
  flt_three_beam_GN_squarefree_contradiction
    (p := q) (x := (b : ℤ)) (y := y) (z := (a : ℤ))
    hcop hflt hy_ne hq.1 hqnd
    (primitive_prime_dvd_powerBeam_three_natAbs hq hab_lt)
    hbeam_ne hGN_sq

end DkMath.CosmicFormula.PowerGapBeam
