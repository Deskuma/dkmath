/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimeGauge.Return

#print "file: DkMathTest.NumberTheory.PrimeGaugeReturn"

/-!
# Prime Gauge return bridge regressions

These examples exercise the public bridge at the requested small periods and
boundary phases.  They are finite regressions only; no prime-existence or
Goldbach conclusion is attached to them.
-/

namespace DkMathTest.NumberTheory.PrimeGaugeReturn

open DkMath.CosmicFormula.Rotation.CF2D
open DkMath.NumberTheory.PrimeGauge

example : regularKernel 2 ^ (0 : ℕ) = 1 := by
  apply (regularKernel_pow_eq_one_iff_dvd (k := 2) (n := 0) (by decide)).2
  decide

example : regularKernel 2 ^ (4 : ℕ) = 1 := by
  apply (regularKernel_pow_eq_one_iff_dvd (k := 2) (n := 4) (by decide)).2
  decide

example : regularKernel 3 ^ (3 : ℕ) = 1 := by
  apply (regularKernel_pow_eq_one_iff_dvd (k := 3) (n := 3) (by decide)).2
  decide

example : regularKernel 5 ^ (10 : ℕ) = 1 := by
  apply (regularKernel_pow_eq_one_iff_dvd (k := 5) (n := 10) (by decide)).2
  decide

example : regularKernel 6 ^ (12 : ℕ) = 1 := by
  apply (regularKernel_pow_eq_one_iff_dvd (k := 6) (n := 12) (by decide)).2
  decide

example : regularKernel 2 ^ (3 : ℕ) ≠ 1 := by
  intro h
  have hd : (2 : ℕ) ∣ 3 :=
    (regularKernel_pow_eq_one_iff_dvd (k := 2) (n := 3) (by decide)).1 h
  norm_num at hd

example : regularKernel 3 ^ (4 : ℕ) ≠ 1 := by
  intro h
  have hd : (3 : ℕ) ∣ 4 :=
    (regularKernel_pow_eq_one_iff_dvd (k := 3) (n := 4) (by decide)).1 h
  norm_num at hd

example : regularKernel 5 ^ (6 : ℕ) ≠ 1 := by
  intro h
  have hd : (5 : ℕ) ∣ 6 :=
    (regularKernel_pow_eq_one_iff_dvd (k := 5) (n := 6) (by decide)).1 h
  norm_num at hd

example : regularKernel 6 ^ (7 : ℕ) ≠ 1 := by
  intro h
  have hd : (6 : ℕ) ∣ 7 :=
    (regularKernel_pow_eq_one_iff_dvd (k := 6) (n := 7) (by decide)).1 h
  norm_num at hd

example : regularKernel 5 ^ (1 : ℕ) = regularKernel 5 ^ (6 : ℕ) := by
  apply (regularKernel_pow_eq_pow_iff_modEq
    (k := 5) (a := 1) (b := 6) (by decide)).2
  decide

example : regularKernel 5 ^ (1 : ℕ) ≠ regularKernel 5 ^ (2 : ℕ) := by
  intro h
  have hmod : Nat.ModEq 5 1 2 :=
    (regularKernel_pow_eq_pow_iff_modEq
      (k := 5) (a := 1) (b := 2) (by decide)).1 h
  norm_num [Nat.ModEq] at hmod

#print axioms regularKernel_pow_eq_one_iff_dvd
#print axioms regularKernel_pow_eq_pow_iff_modEq

end DkMathTest.NumberTheory.PrimeGaugeReturn
