/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTail

#print "file: DkMath.Lib.Cosmic.CoreNested"

/-!
# Nested power differences

`powerCore d base step` uses the order (base, increment). The canonical
`GTail` uses (degree, cut, increment, base). These are differences of powers,
with no assertion that a Core is itself a perfect power. Splitting an increment
preserves the endpoint value; it does not construct a Kummer descent state.
-/

namespace DkMath.Lib.Cosmic

variable {R : Type*} [CommRing R]

/-- The difference between the endpoint power and the starting power. -/
def powerCore (d : ℕ) (base step : R) : R := (base + step) ^ d - base ^ d

@[simp] theorem powerCore_zero_degree (base step : R) : powerCore 0 base step = 0 := by
  simp [powerCore]

@[simp] theorem powerCore_zero_step (d : ℕ) (base : R) : powerCore d base 0 = 0 := by
  simp [powerCore]

/-- This form includes degree zero, when the subtracted starting power is one. -/
theorem powerCore_zero_base (d : ℕ) (step : R) :
    powerCore d 0 step = step ^ d - (0 : R) ^ d := by
  simp [powerCore]

/-- Big is the starting power plus the difference Core. -/
theorem pow_add_powerCore (d : ℕ) (base step : R) :
    base ^ d + powerCore d base step = (base + step) ^ d := by
  simp [powerCore]

/-- N1: split an increment, using the first endpoint as the second base. -/
theorem powerCore_split (d : ℕ) (base a b : R) :
    powerCore d base (a + b) = powerCore d base a + powerCore d (base + a) b := by
  simp only [powerCore, add_assoc]
  ring

/-- N2: the two orders of movement have the same total difference. -/
theorem powerCore_swap (d : ℕ) (base a b : R) :
    powerCore d base a + powerCore d (base + a) b =
      powerCore d base b + powerCore d (base + b) a := by
  rw [← powerCore_split, ← powerCore_split, add_comm a b]

/-- N3: three consecutive differences telescope to the same endpoint. -/
theorem powerCore_split_three (d : ℕ) (base a b c : R) :
    powerCore d base (a + b + c) =
      powerCore d base a + powerCore d (base + a) b + powerCore d (base + a + b) c := by
  rw [powerCore_split d base (a + b) c, powerCore_split d base a b, ← add_assoc base]

/-- The GN bridge, valid also at zero increment and degree zero. -/
theorem powerCore_eq_gtail_one (d : ℕ) (base step : R) :
    powerCore d base step = step * DkMath.CosmicFormula.GTail d 1 step base := by
  unfold powerCore
  rw [add_comm base step, DkMath.CosmicFormula.add_pow_eq_mul_GTail_one_add_gap,
    add_sub_cancel_right]

/-- N4: transport the two-stage difference into canonical GN coordinates. -/
theorem mul_gtail_one_split (d : ℕ) (base a b : R) :
    (a + b) * DkMath.CosmicFormula.GTail d 1 (a + b) base =
      a * DkMath.CosmicFormula.GTail d 1 a base +
        b * DkMath.CosmicFormula.GTail d 1 b (base + a) := by
  simpa only [powerCore_eq_gtail_one] using powerCore_split d base a b

/-- Exchange of paths in GN coordinates. -/
theorem mul_gtail_one_swap (d : ℕ) (base a b : R) :
    a * DkMath.CosmicFormula.GTail d 1 a base +
        b * DkMath.CosmicFormula.GTail d 1 b (base + a) =
      b * DkMath.CosmicFormula.GTail d 1 b base +
        a * DkMath.CosmicFormula.GTail d 1 a (base + b) := by
  simpa only [powerCore_eq_gtail_one] using powerCore_swap d base a b

/-- An odd-power sum is a difference Core; no FLT hypothesis is involved. -/
theorem powerCore_neg_sum {d : ℕ} (hd : Odd d) (x y : R) :
    powerCore d (-y) (x + y) = x ^ d + y ^ d := by
  simp [powerCore, hd.neg_pow, add_comm]

/-- The complete Gap times GN carrier of an odd-power sum. -/
theorem odd_sum_eq_mul_gtail_one {d : ℕ} (hd : Odd d) (x y : R) :
    x ^ d + y ^ d = (x + y) * DkMath.CosmicFormula.GTail d 1 (x + y) (-y) := by
  rw [← powerCore_neg_sum hd, powerCore_eq_gtail_one]

end DkMath.Lib.Cosmic
