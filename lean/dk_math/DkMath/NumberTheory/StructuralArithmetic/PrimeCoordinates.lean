/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.PadicValNat
import DkMath.NumberTheory.StructuralArithmetic.PowerGauge

#print "file: DkMath.NumberTheory.StructuralArithmetic.PrimeCoordinates"

/-!
## Prime coordinates for structural arithmetic

This module specializes the abstract coordinate projection kernel to ordinary
prime-valuation coordinates on nonzero natural numbers.

The key bridge is the standard valuation identity

```text
v_p(n * a^d) = v_p(n) + d * v_p(a)
```

for prime `p` and nonzero `n`, `a`.  Projecting the exponent coordinate modulo
`d` removes the second term.  Therefore multiplication by a `d`-th power is
invisible in the period-`d` observation while the raw prime-coordinate source
remains available.
-/

namespace DkMath.NumberTheory.StructuralArithmetic

/-- Prime directions used as coordinate indices. -/
abbrev PrimeIndex := {p : ℕ // Nat.Prime p}

/-- Raw prime-exponent coordinate vector of a natural number. -/
def primeExponentCoordinates (n : ℕ) : PrimeIndex → ℕ :=
  fun p => padicValNat p.1 n

/-- Period-`d` observation of the raw prime-exponent coordinate vector. -/
def projectPrimeCoordinates (d n : ℕ) : PrimeIndex → ℕ :=
  projectCoordinates d (primeExponentCoordinates n)

/--
Multiplication by a `d`-th power adds exactly `d * v_p(a)` in the `p` direction.
-/
theorem padicValNat_mul_pow
    {p n a d : ℕ}
    (hp : Nat.Prime p)
    (hn : n ≠ 0)
    (ha : a ≠ 0) :
    padicValNat p (n * a ^ d) =
      padicValNat p n + d * padicValNat p a := by
  haveI : Fact p.Prime := ⟨hp⟩
  calc
    padicValNat p (n * a ^ d)
        = padicValNat p n + padicValNat p (a ^ d) := by
            exact padicValNat.mul hn (pow_ne_zero d ha)
    _ = padicValNat p n + d * padicValNat p a := by
          rw [DkMath.ABC.padicValNat_pow hp d ha]

/-- Coordinate-vector form of `padicValNat_mul_pow`. -/
theorem primeExponentCoordinates_mul_pow
    {n a d : ℕ}
    (hn : n ≠ 0)
    (ha : a ≠ 0) :
    primeExponentCoordinates (n * a ^ d) =
      fun p => primeExponentCoordinates n p + d * primeExponentCoordinates a p := by
  funext p
  exact padicValNat_mul_pow p.2 hn ha

/--
Prime-coordinate red-ribbon theorem: multiplying by a `d`-th power does not
change the period-`d` projected prime structure.
-/
theorem projectPrimeCoordinates_mul_pow
    {n a d : ℕ}
    (hn : n ≠ 0)
    (ha : a ≠ 0) :
    projectPrimeCoordinates d (n * a ^ d) =
      projectPrimeCoordinates d n := by
  unfold projectPrimeCoordinates
  rw [primeExponentCoordinates_mul_pow hn ha]
  exact projectCoordinates_add_period d
    (primeExponentCoordinates n) (primeExponentCoordinates a)

/--
Equivalent relation form of the prime-coordinate red-ribbon theorem.
-/
theorem samePowerStructure_primeCoordinates_mul_pow
    {n a d : ℕ}
    (hn : n ≠ 0)
    (ha : a ≠ 0) :
    SamePowerStructure d
      (primeExponentCoordinates n)
      (primeExponentCoordinates (n * a ^ d)) := by
  unfold SamePowerStructure
  exact (projectPrimeCoordinates_mul_pow hn ha).symm

/-- The raw period-zero prime observation is exactly the valuation vector. -/
@[simp] theorem projectPrimeCoordinates_period_zero (n : ℕ) :
    projectPrimeCoordinates 0 n = primeExponentCoordinates n := by
  simp [projectPrimeCoordinates]

/-- The period-one prime observation collapses all prime-exponent coordinates. -/
@[simp] theorem projectPrimeCoordinates_period_one (n : ℕ) :
    projectPrimeCoordinates 1 n = fun _ => 0 := by
  simp [projectPrimeCoordinates]

end DkMath.NumberTheory.StructuralArithmetic
