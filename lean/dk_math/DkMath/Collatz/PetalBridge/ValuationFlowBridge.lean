/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.OneCycle
import DkMath.ABC.ValuationFlowBridge

#print "file: DkMath.Collatz.PetalBridge.ValuationFlowBridge"

namespace DkMath.Collatz

/-
Checkpoint 151-b / 152 sub root: thin valuation-flow bridge for the one-cycle
unit boundary.

This file is intentionally a bridge, not a new Collatz cycle theorem.  The
ABC valuation-flow API talks about primitive channels for `a^d - b^d`; the
one-cycle obstruction talks about the local equation

  3 * n + 1 = 2^h * n.

The shared vocabulary exposed here is therefore deliberately thin:

  closed one-step loop -> unit product -> no prime channel -> unit support mass.

Do not read this as general cycle uniqueness or convergence.
-/

/-- The scaled one-cycle equation closes only at the unit boundary. -/
theorem oneCycle_unit_boundary_only
    {n h : ℕ}
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    n = 1 ∧ h = 2 :=
  collatz_scaled_one_cycle_is_unit_boundary hn hcycle

/-- Natural unit-product form for the scaled one-cycle bridge. -/
theorem oneCycle_unit_product_nat
    {n h : ℕ}
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    n * (2 ^ h - 3) = 1 :=
  collatz_scaled_one_cycle_nat_unit_product hn hcycle

/-- Integer unit-product form for the scaled one-cycle bridge. -/
theorem oneCycle_unit_product_int
    {n h : ℕ}
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    (((2 ^ h : ℕ) : ℤ) - 3) * (n : ℤ) = 1 :=
  collatz_scaled_one_cycle_int_unit_product hn hcycle

/-- No prime valuation-flow channel remains on the base of a closed one-cycle. -/
theorem oneCycle_no_prime_channel_on_base
    {p n h : ℕ}
    (hp : Nat.Prime p)
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    ¬ p ∣ n :=
  collatz_scaled_one_cycle_no_prime_channel_on_base hp hn hcycle

/-- No prime valuation-flow channel remains on the scale gap of a closed one-cycle. -/
theorem oneCycle_no_prime_channel_on_scaleGap
    {p n h : ℕ}
    (hp : Nat.Prime p)
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    ¬ p ∣ 2 ^ h - 3 :=
  collatz_scaled_one_cycle_no_prime_channel_on_scale_gap hp hn hcycle

/-- No prime valuation-flow channel remains on the explicit unit product. -/
theorem oneCycle_no_prime_channel_on_unitProduct
    {p n h : ℕ}
    (hp : Nat.Prime p)
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    ¬ p ∣ n * (2 ^ h - 3) :=
  collatz_scaled_one_cycle_no_prime_channel_on_unit_product hp hn hcycle

/-- The ABC support mass of the closed one-cycle unit product is `1`. -/
theorem oneCycle_supportMass_unitProduct_eq_one
    {n h : ℕ}
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    DkMath.ABC.supportMass (n * (2 ^ h - 3)) = 1 := by
  have hunit := oneCycle_unit_product_nat hn hcycle
  rw [hunit]
  simp [DkMath.ABC.supportMass]

/-- The ABC radical of the closed one-cycle unit product is `1`. -/
theorem oneCycle_rad_unitProduct_eq_one
    {n h : ℕ}
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    DkMath.ABC.rad (n * (2 ^ h - 3)) = 1 := by
  have hunit := oneCycle_unit_product_nat hn hcycle
  rw [hunit]
  simp

/--
Closed one-cycle support has no growth beyond the unit.

This is a convenience inequality for later valuation-flow bridge code.
-/
theorem oneCycle_no_supportMass_growth
    {n h : ℕ}
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    DkMath.ABC.supportMass (n * (2 ^ h - 3)) ≤ 1 := by
  rw [oneCycle_supportMass_unitProduct_eq_one hn hcycle]

end DkMath.Collatz
