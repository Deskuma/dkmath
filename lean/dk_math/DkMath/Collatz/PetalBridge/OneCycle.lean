/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.Basic

#print "file: DkMath.Collatz.PetalBridge.OneCycle"

namespace DkMath.Collatz

/-
Checkpoint 150: the scaled `1 -> 4 -> 2 -> 1` obstruction.

This file is deliberately tiny and does not live in `PressureAccounting`.
It proves only that the one-step accelerated odd cycle equation

  3 * n + 1 = 2 ^ h * n

has no positive scaled copies except the genuine boundary point `n = 1`,
`h = 2`.  It does not rule out arbitrary nontrivial Collatz cycles and does
not prove convergence.

Interruption research note after checkpoint 151: relation to
`DkMath.ABC.ValuationFlowBridge`.

The tempting bridge is:

```text
ABC.ValuationFlowBridge:
  non-unit diff/support produces primitive prime channels and support mass.

Collatz.OneCycle:
  a one-step return to the same odd state forces
  3*n + 1 = 2^h*n, hence ((2^h)-3)*n = 1.
```

So this file should first expose the Collatz side as a **unit-boundary**
statement.  Do not import the ABC bridge here yet: its main primitive-flow
subject is `a^d - b^d`, while this file's subject is the local Collatz equation
`3*n + 1 = 2^h*n`.  The safe common language is:

```text
closed one-step loop -> unit product -> no prime channel remains
```

This is exactly the information a later thin
`DkMath.Collatz.PetalBridge.ValuationFlowBridge` can consume.
-/

/--
If the scaled one-step odd cycle equation has height at least `3`, then it
contradicts positivity.

For `h ≥ 3`, the right-hand side is at least `8 * n`, while the left-hand side
is only `3 * n + 1`.
-/
theorem collatz_scaled_one_cycle_h_not_ge_three
    {n h : ℕ}
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    ¬ 3 ≤ h := by
  intro hh
  have hpow : 8 ≤ 2 ^ h := by
    have hpow' := Nat.pow_le_pow_right (by omega : 0 < 2) hh
    norm_num at hpow'
    exact hpow'
  have hmul : 8 * n ≤ 2 ^ h * n :=
    Nat.mul_le_mul_right n hpow
  rw [← hcycle] at hmul
  omega

/-- Height `0` cannot satisfy the positive scaled one-step cycle equation. -/
theorem collatz_scaled_one_cycle_h_ne_zero
    {n h : ℕ}
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    h ≠ 0 := by
  intro hh
  subst h
  norm_num at hcycle
  omega

/-- Height `1` cannot satisfy the positive scaled one-step cycle equation. -/
theorem collatz_scaled_one_cycle_h_ne_one
    {n h : ℕ}
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    h ≠ 1 := by
  intro hh
  subst h
  norm_num at hcycle
  omega

/--
The scaled `1 -> 4 -> 2 -> 1` one-cycle equation has only the positive
solution `n = 1`, `h = 2`.

This is a one-cycle obstruction only: it rules out scaled copies where one
accelerated odd step returns to the same odd state.  It is not a theorem about
all Collatz cycles or Collatz convergence.
-/
theorem collatz_scaled_one_cycle_eq_one
    {n h : ℕ}
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    n = 1 ∧ h = 2 := by
  have hnot3 := collatz_scaled_one_cycle_h_not_ge_three hn hcycle
  have hhcases : h = 0 ∨ h = 1 ∨ h = 2 := by
    omega
  rcases hhcases with rfl | rfl | rfl
  · norm_num at hcycle
    omega
  · norm_num at hcycle
    omega
  · norm_num at hcycle
    constructor <;> omega

/--
The `4 * n` boundary equation for the familiar one-cycle has the unique
positive scale `n = 1`.
-/
theorem collatz_one_four_two_one_scaled_boundary_unique
    {n : ℕ} (_hn : 0 < n)
    (h : 3 * n + 1 = 4 * n) :
    n = 1 := by
  omega

/-- The genuine `1 -> 4 -> 2 -> 1` boundary satisfies the scaled equation. -/
theorem collatz_one_four_two_one_scaled_boundary_exists :
    3 * 1 + 1 = 2 ^ 2 * 1 := by
  norm_num

/-- No positive scaled one-step cycle exists at a height other than `2`. -/
theorem collatz_scaled_one_cycle_no_wrong_height
    {n h : ℕ}
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n)
    (hh : h ≠ 2) :
    False := by
  have hsol := collatz_scaled_one_cycle_eq_one hn hcycle
  exact hh hsol.2

/-- No positive scaled one-step cycle exists away from the base `n = 1`. -/
theorem collatz_scaled_one_cycle_no_wrong_base
    {n h : ℕ}
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n)
    (hn1 : n ≠ 1) :
    False := by
  have hsol := collatz_scaled_one_cycle_eq_one hn hcycle
  exact hn1 hsol.1

/--
Iff form of the positive scaled one-step cycle obstruction.

The forward direction is `collatz_scaled_one_cycle_eq_one`; the reverse
direction is the concrete `1 -> 4 -> 2 -> 1` boundary equation.  This remains
only a statement about `3 * n + 1 = 2 ^ h * n`.
-/
theorem collatz_scaled_one_cycle_iff
    {n h : ℕ}
    (hn : 0 < n) :
    3 * n + 1 = 2 ^ h * n ↔ n = 1 ∧ h = 2 := by
  constructor
  · exact collatz_scaled_one_cycle_eq_one hn
  · intro hsol
    rcases hsol with ⟨rfl, rfl⟩
    norm_num

/--
Project-facing alias for the scaled `1 -> 4 -> 2 -> 1` Petal one-cycle
uniqueness theorem.
-/
theorem one_four_two_one_petal_scaled_cycle_unique
    {n h : ℕ}
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    n = 1 ∧ h = 2 :=
  collatz_scaled_one_cycle_eq_one hn hcycle

/--
Integer unit-product form of the scaled one-step cycle equation.

This is the algebraic bridge to the valuation-flow reading: a closed one-step
loop has no room for a non-unit support channel, because the product
`((2^h)-3) * n` is exactly `1`.
-/
theorem collatz_scaled_one_cycle_int_unit_product
    {n h : ℕ}
    (_hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    (((2 ^ h : ℕ) : ℤ) - 3) * (n : ℤ) = 1 := by
  have hcycle_int :
      (3 : ℤ) * (n : ℤ) + 1 =
        ((2 ^ h : ℕ) : ℤ) * (n : ℤ) := by
    exact_mod_cast hcycle
  calc
    (((2 ^ h : ℕ) : ℤ) - 3) * (n : ℤ)
        = ((2 ^ h : ℕ) : ℤ) * (n : ℤ) - (3 : ℤ) * (n : ℤ) := by
          ring
    _ = ((3 : ℤ) * (n : ℤ) + 1) - (3 : ℤ) * (n : ℤ) := by
          rw [← hcycle_int]
    _ = 1 := by
          ring

/--
Natural-number unit-product form of the scaled one-step cycle equation.

This uses the uniqueness theorem to avoid Nat-subtraction noise.  In the only
positive solution, `2^h - 3 = 1` and `n = 1`.
-/
theorem collatz_scaled_one_cycle_nat_unit_product
    {n h : ℕ}
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    n * (2 ^ h - 3) = 1 := by
  have hsol := collatz_scaled_one_cycle_eq_one hn hcycle
  rcases hsol with ⟨rfl, rfl⟩
  norm_num

/--
Project-facing alias: the scaled one-cycle closes only at the unit boundary.

The phrase "unit boundary" is intentional.  It marks the shared vocabulary with
the valuation-flow view without importing the ABC bridge into this local file.
-/
theorem collatz_scaled_one_cycle_is_unit_boundary
    {n h : ℕ}
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    n = 1 ∧ h = 2 :=
  collatz_scaled_one_cycle_eq_one hn hcycle

/--
No prime channel can remain on the base `n` of a positive scaled one-step
cycle.

Valuation-flow reading: if the loop closes, the base support has collapsed to
the unit `1`.
-/
theorem collatz_scaled_one_cycle_no_prime_channel_on_base
    {p n h : ℕ}
    (hp : Nat.Prime p)
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    ¬ p ∣ n := by
  intro hpn
  have hsol := collatz_scaled_one_cycle_eq_one hn hcycle
  rw [hsol.1] at hpn
  exact hp.not_dvd_one hpn

/--
No prime channel can remain on the scale gap `2^h - 3` of a positive scaled
one-step cycle.

Valuation-flow reading: the scale gap is also forced to the unit `1`.
-/
theorem collatz_scaled_one_cycle_no_prime_channel_on_scale_gap
    {p n h : ℕ}
    (hp : Nat.Prime p)
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    ¬ p ∣ 2 ^ h - 3 := by
  intro hpgap
  have hsol := collatz_scaled_one_cycle_eq_one hn hcycle
  rw [hsol.2] at hpgap
  norm_num at hpgap
  have hp_two : 2 ≤ p := hp.two_le
  omega

/--
No prime channel can divide the explicit unit product of a positive scaled
one-step cycle.

This is the most compact no-channel form for later bridge files.
-/
theorem collatz_scaled_one_cycle_no_prime_channel_on_unit_product
    {p n h : ℕ}
    (hp : Nat.Prime p)
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    ¬ p ∣ n * (2 ^ h - 3) := by
  intro hpdiv
  have hunit := collatz_scaled_one_cycle_nat_unit_product hn hcycle
  rw [hunit] at hpdiv
  exact hp.not_dvd_one hpdiv

end DkMath.Collatz
