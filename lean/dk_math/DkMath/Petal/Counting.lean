/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Petal.Basic

#print "file: DkMath.Petal.Counting"

/-!
# Petal Counting

This file fixes the first counting vocabulary for relative Petal systems.

The arithmetic is ordinary natural-number arithmetic.  The important point is
the naming: `n + 1` is exposed as a lap base made from a base unit core and one
inheritance slot.
-/

namespace DkMath
namespace Petal

/-- Base unit core: the number of Petal directions. -/
def baseUnitCore (n : Nat) : Nat := n

/-- The single channel that carries the core to the next lap. -/
def inheritanceSlot (_n : Nat) : Nat := 1

/-- Lap base: Petal directions plus the inheritance slot. -/
def lapBase (n : Nat) : Nat :=
  baseUnitCore n + inheritanceSlot n

/-- Total count after `lap` relative-Petal expansions. -/
def relPetalTotal (n lap : Nat) : Nat :=
  baseUnitCore n * lapBase n ^ lap

/-- The one-lap relative polygon kernel. -/
def relPolygonKernel (n : Nat) : Nat :=
  baseUnitCore n * lapBase n

/-- The lap base computes to `n + 1`, but keeps the Petal meaning in the API. -/
theorem lapBase_eq_succ (n : Nat) :
    lapBase n = n + 1 := by
  rfl

/-- Zero laps return the base unit core. -/
theorem relPetalTotal_zero (n : Nat) :
    relPetalTotal n 0 = n := by
  simp [relPetalTotal, baseUnitCore]

/-- One more lap multiplies the current total by the lap base. -/
theorem relPetalTotal_succ (n lap : Nat) :
    relPetalTotal n (lap + 1) = relPetalTotal n lap * lapBase n := by
  simp [relPetalTotal, pow_succ, Nat.mul_assoc]

/--
Dynamic orbit total.

This is the product of a lap-base sequence over the first `k` laps.
-/
def dynamicOrbitTotal (b : Nat → Nat) (k : Nat) : Nat :=
  Finset.prod (Finset.range k) b

/--
Dynamic Petal total.

The base unit core is allowed to vary by lap.  The initial core is `a 0`, and
each lap uses the dynamic lap base `a i + 1`.
-/
def dynamicPetalTotal (a : Nat → Nat) (k : Nat) : Nat :=
  a 0 * dynamicOrbitTotal (fun i => a i + 1) k

/-- The dynamic orbit total at zero laps is empty-product `1`. -/
theorem dynamicOrbitTotal_zero (b : Nat → Nat) :
    dynamicOrbitTotal b 0 = 1 := by
  simp [dynamicOrbitTotal]

/-- One more dynamic lap multiplies by the next lap base. -/
theorem dynamicOrbitTotal_succ (b : Nat → Nat) (k : Nat) :
    dynamicOrbitTotal b (k + 1) = dynamicOrbitTotal b k * b k := by
  simp [dynamicOrbitTotal, Finset.prod_range_succ]

/-- A dynamic orbit prefix product divides the next prefix product. -/
theorem dynamicOrbitTotal_dvd_succ
    (b : Nat → Nat) (k : Nat) :
    dynamicOrbitTotal b k ∣ dynamicOrbitTotal b (k + 1) := by
  rw [dynamicOrbitTotal_succ]
  exact Nat.dvd_mul_right _ _

/--
Dynamic orbit prefix products are monotone for divisibility.

If `k ≤ l`, then every factor already present at lap `k` is still present in
the longer prefix product at lap `l`.
-/
theorem dynamicOrbitTotal_dvd_of_le
    (b : Nat → Nat) {k l : Nat} (hkl : k ≤ l) :
    dynamicOrbitTotal b k ∣ dynamicOrbitTotal b l := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hkl
  have hstep : ∀ t : Nat, dynamicOrbitTotal b k ∣ dynamicOrbitTotal b (k + t) := by
    intro t
    induction t with
    | zero =>
        simp
    | succ t ih =>
        exact Nat.dvd_trans ih (by
          simpa [Nat.add_assoc] using dynamicOrbitTotal_dvd_succ b (k + t))
  exact hstep t

/-- A constant dynamic orbit is an ordinary power. -/
theorem dynamicOrbitTotal_const (b k : Nat) :
    dynamicOrbitTotal (fun _ => b) k = b ^ k := by
  induction k with
  | zero =>
      simp [dynamicOrbitTotal_zero]
  | succ k ih =>
      rw [dynamicOrbitTotal_succ, ih]
      rw [pow_succ]

/--
Every base already passed by a dynamic orbit divides the current prefix product.
-/
theorem dynamicOrbitTotal_base_dvd_of_lt
    (b : Nat → Nat) {i k : Nat} (hi : i < k) :
    b i ∣ dynamicOrbitTotal b k := by
  exact Finset.dvd_prod_of_mem b (by simpa [dynamicOrbitTotal] using hi)

/--
Factorial orbit.

The dynamic orbit with lap base `i + 1` is the ordinary factorial.
-/
theorem dynamicOrbitTotal_succIndex_eq_factorial (k : Nat) :
    dynamicOrbitTotal (fun i => i + 1) k = Nat.factorial k := by
  induction k with
  | zero =>
      simp [dynamicOrbitTotal_zero]
  | succ k ih =>
      rw [dynamicOrbitTotal_succ, ih, Nat.factorial_succ]
      rw [Nat.mul_comm]

/--
Abstract prime-base orbit total.

This is a thin Petal-facing name for a dynamic orbit whose bases are intended
to be prime values.  The concrete prime sequence is kept abstract here.
-/
def primeBaseOrbitTotal (p : Nat → Nat) (k : Nat) : Nat :=
  dynamicOrbitTotal p k

/-- A prime-base sequence assigns a prime base to every lap. -/
def IsPrimeBaseSequence (p : Nat → Nat) : Prop :=
  ∀ i, Nat.Prime (p i)

/--
A distinct prime-base sequence assigns prime bases without repetition.

This keeps the order of bases abstract; it only records primality and
injectivity.
-/
def IsDistinctPrimeBaseSequence (p : Nat → Nat) : Prop :=
  IsPrimeBaseSequence p ∧ Function.Injective p

/-- The prime-base orbit at zero laps is empty-product `1`. -/
theorem primeBaseOrbitTotal_zero (p : Nat → Nat) :
    primeBaseOrbitTotal p 0 = 1 := by
  simp [primeBaseOrbitTotal, dynamicOrbitTotal_zero]

/-- One more abstract prime-base lap multiplies by the next prime base. -/
theorem primeBaseOrbitTotal_succ (p : Nat → Nat) (k : Nat) :
    primeBaseOrbitTotal p (k + 1) = primeBaseOrbitTotal p k * p k := by
  simp [primeBaseOrbitTotal, dynamicOrbitTotal_succ]

/-- A prime-base prefix product divides the next prefix product. -/
theorem primeBaseOrbitTotal_dvd_succ
    (p : Nat → Nat) (k : Nat) :
    primeBaseOrbitTotal p k ∣ primeBaseOrbitTotal p (k + 1) := by
  rw [primeBaseOrbitTotal_succ]
  exact Nat.dvd_mul_right _ _

/--
Prime-base orbit prefix products are monotone for divisibility.

This is the prime-base alias of `dynamicOrbitTotal_dvd_of_le`.
-/
theorem primeBaseOrbitTotal_dvd_of_le
    (p : Nat → Nat) {k l : Nat} (hkl : k ≤ l) :
    primeBaseOrbitTotal p k ∣ primeBaseOrbitTotal p l := by
  exact dynamicOrbitTotal_dvd_of_le p hkl

/--
The next base divides the next prime-base prefix product.

The primality assumption records the intended interpretation of `p` as a
prime-base sequence; the divisibility itself only uses the product structure.
-/
theorem primeBaseOrbitTotal_nextPrime_dvd_succ
    {p : Nat → Nat} (hp : IsPrimeBaseSequence p) (k : Nat) :
    p k ∣ primeBaseOrbitTotal p (k + 1) := by
  have _hp_k : Nat.Prime (p k) := hp k
  rw [primeBaseOrbitTotal_succ]
  exact Nat.dvd_mul_left _ _

/-- Every earlier prime base divides the current prime-base prefix product. -/
theorem primeBaseOrbitTotal_base_dvd_of_lt
    (p : Nat → Nat) {i k : Nat} (hi : i < k) :
    p i ∣ primeBaseOrbitTotal p k := by
  exact dynamicOrbitTotal_base_dvd_of_lt p hi

/--
Every earlier prime base divides the current prime-base prefix product, with
the prime-sequence interpretation recorded in the hypothesis.
-/
theorem primeBaseOrbitTotal_prime_dvd_of_lt
    {p : Nat → Nat} (hp : IsPrimeBaseSequence p) {i k : Nat} (hi : i < k) :
    p i ∣ primeBaseOrbitTotal p k := by
  have _hp_i : Nat.Prime (p i) := hp i
  exact primeBaseOrbitTotal_base_dvd_of_lt p hi

/--
An already adopted prime base remains a divisor of every later prime-base
prefix product.

This packages the two prefix facts: adopted bases divide their current prefix,
and prefix products are monotone for divisibility.
-/
theorem primeBaseOrbitTotal_prime_dvd_of_lt_of_le
    {p : Nat → Nat} (hp : IsPrimeBaseSequence p)
    {i k l : Nat} (hi : i < k) (hkl : k ≤ l) :
    p i ∣ primeBaseOrbitTotal p l := by
  exact Nat.dvd_trans
    (primeBaseOrbitTotal_prime_dvd_of_lt hp hi)
    (primeBaseOrbitTotal_dvd_of_le p hkl)

/-- A prime-base sequence supplies a prime at each lap. -/
theorem IsPrimeBaseSequence.prime_at
    {p : Nat → Nat} (hp : IsPrimeBaseSequence p) (i : Nat) :
    Nat.Prime (p i) :=
  hp i

/-- A distinct prime-base sequence supplies a prime at each lap. -/
theorem IsDistinctPrimeBaseSequence.prime_at
    {p : Nat → Nat} (hp : IsDistinctPrimeBaseSequence p) (i : Nat) :
    Nat.Prime (p i) :=
  hp.1 i

/-- A distinct prime-base sequence is injective. -/
theorem IsDistinctPrimeBaseSequence.injective
    {p : Nat → Nat} (hp : IsDistinctPrimeBaseSequence p) :
    Function.Injective p :=
  hp.2

/-- The dynamic Petal total at zero laps is the initial base unit core. -/
theorem dynamicPetalTotal_zero (a : Nat → Nat) :
    dynamicPetalTotal a 0 = a 0 := by
  simp [dynamicPetalTotal, dynamicOrbitTotal_zero]

/-- One more dynamic Petal lap multiplies by the next dynamic lap base. -/
theorem dynamicPetalTotal_succ (a : Nat → Nat) (k : Nat) :
    dynamicPetalTotal a (k + 1) = dynamicPetalTotal a k * (a k + 1) := by
  simp [dynamicPetalTotal, dynamicOrbitTotal_succ, Nat.mul_assoc]

/-- Fixed-core Petal counting is the constant-core dynamic Petal total. -/
theorem dynamicPetalTotal_const (n k : Nat) :
    dynamicPetalTotal (fun _ => n) k = relPetalTotal n k := by
  simp [dynamicPetalTotal, dynamicOrbitTotal_const, relPetalTotal, lapBase_eq_succ, baseUnitCore]

/-- The one-lap total is the relative polygon kernel. -/
theorem relPetalTotal_one (n : Nat) :
    relPetalTotal n 1 = relPolygonKernel n := by
  simp [relPetalTotal, relPolygonKernel]

/-- The relative polygon kernel is the first Petal-orbit total. -/
theorem relPolygonKernel_eq_relPetalTotal_one (n : Nat) :
    relPolygonKernel n = relPetalTotal n 1 := by
  exact (relPetalTotal_one n).symm

/-- The fixed `n = 5` zero-lap example. -/
theorem relPetalTotal_five_zero :
    relPetalTotal 5 0 = 5 := by
  decide

/-- The fixed `n = 5` one-lap example. -/
theorem relPetalTotal_five_one :
    relPetalTotal 5 1 = 30 := by
  decide

/-- The fixed `n = 5` two-lap example. -/
theorem relPetalTotal_five_two :
    relPetalTotal 5 2 = 180 := by
  decide

/--
Relative unit-core orbit equivalence.

Two values are in the same fixed-core Petal orbit if both are lap totals for the
same base unit core.
-/
def SameRelPetalOrbit (n a b : Nat) : Prop :=
  ∃ i j, a = relPetalTotal n i ∧ b = relPetalTotal n j

/-- The base unit and first one-lap total of the pentagonal Petal orbit agree as orbit members. -/
theorem sameRelPetalOrbit_five_5_30 :
    SameRelPetalOrbit 5 5 30 := by
  refine ⟨0, 1, ?_, ?_⟩ <;> decide

/-- The first and second lap totals of the pentagonal Petal orbit agree as orbit members. -/
theorem sameRelPetalOrbit_five_30_180 :
    SameRelPetalOrbit 5 30 180 := by
  refine ⟨1, 2, ?_, ?_⟩ <;> decide

/-- The base unit and second lap total of the pentagonal Petal orbit agree as orbit members. -/
theorem sameRelPetalOrbit_five_5_180 :
    SameRelPetalOrbit 5 5 180 := by
  refine ⟨0, 2, ?_, ?_⟩ <;> decide

end Petal
end DkMath
