/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Order

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

/-!
## Core validity

The natural-number counting layer distinguishes a degenerate zero core from a
valid Petal core.  This is independent of the existing `CoreUnit` alias,
which belongs to the FLT phase-space model.
-/

/-- A natural-number core is valid when it is positive. -/
def IsValidPetalCore (n : Nat) : Prop :=
  0 < n

/-- The zero natural-number core is the degenerate Petal case. -/
def IsDegeneratePetalCore (n : Nat) : Prop :=
  n = 0

/-- A positive natural-number type for valid Petal counting cores. -/
abbrev PositivePetalCore := {n : Nat // IsValidPetalCore n}

/-- The least valid Petal counting core. -/
def unitPetalCore : PositivePetalCore :=
  ⟨1, by
    change 0 < (1 : Nat)
    decide⟩

/-- The unit natural number is a valid Petal core. -/
theorem validPetalCore_one : IsValidPetalCore 1 := by
  change 0 < (1 : Nat)
  decide

/-- Every valid Petal core is at least the unit core. -/
theorem one_le_of_validPetalCore
    {n : Nat} (hn : IsValidPetalCore n) :
    1 ≤ n := by
  change 0 < n at hn
  omega

/-- The distinguished unit core is minimal among positive Petal cores. -/
theorem unitPetalCore_is_minimum
    (c : PositivePetalCore) :
    unitPetalCore.1 ≤ c.1 := by
  exact one_le_of_validPetalCore c.2

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

/-- A zero core is degenerate at every lap. -/
@[simp]
theorem relPetalTotal_zero_core (lap : Nat) :
    relPetalTotal 0 lap = 0 := by
  simp [relPetalTotal, baseUnitCore]

/-- A positive core produces a positive fixed-base Petal total. -/
theorem relPetalTotal_pos_of_pos_core
    {n : Nat} (hn : IsValidPetalCore n) (lap : Nat) :
    0 < relPetalTotal n lap := by
  change 0 < n at hn
  unfold relPetalTotal baseUnitCore lapBase inheritanceSlot
  exact Nat.mul_pos hn (Nat.pow_pos (by omega))

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

/-!
## Canonical Petal orbit

`dynamicOrbitTotal` is the raw prefix product.  `petalOrbitTotal` adds an
independently chosen initial core, so zero laps preserve that core while a
zero core remains degenerate.
-/

/-- The canonical Petal total with an independent initial core and base list. -/
def petalOrbitTotal
    (core : Nat) (base : Nat → Nat) (lap : Nat) : Nat :=
  core * dynamicOrbitTotal base lap

/-- Zero laps preserve the initial Petal core. -/
@[simp]
theorem petalOrbitTotal_zero
    (core : Nat) (base : Nat → Nat) :
    petalOrbitTotal core base 0 = core := by
  simp [petalOrbitTotal, dynamicOrbitTotal_zero]

/-- A zero initial core is degenerate at every lap. -/
@[simp]
theorem petalOrbitTotal_zero_core
    (base : Nat → Nat) (lap : Nat) :
    petalOrbitTotal 0 base lap = 0 := by
  simp [petalOrbitTotal]

/-- One more lap multiplies the current total by the next base. -/
theorem petalOrbitTotal_succ
    (core : Nat) (base : Nat → Nat) (lap : Nat) :
    petalOrbitTotal core base (lap + 1) =
      petalOrbitTotal core base lap * base lap := by
  simp [petalOrbitTotal, dynamicOrbitTotal_succ, Nat.mul_assoc]

/-- A constant base list gives the usual geometric Petal growth. -/
theorem petalOrbitTotal_const
    (core base lap : Nat) :
    petalOrbitTotal core (fun _ => base) lap = core * base ^ lap := by
  simp [petalOrbitTotal, dynamicOrbitTotal_const]

/-- A positive core and positive base list give a positive Petal total. -/
theorem petalOrbitTotal_pos
    {core : Nat} (hcore : 0 < core)
    {base : Nat → Nat} (hbase : ∀ i, 0 < base i)
    (lap : Nat) :
    0 < petalOrbitTotal core base lap := by
  unfold petalOrbitTotal
  have hprod : 0 < Finset.prod (Finset.range lap) base := by
    induction lap with
    | zero => simp
    | succ lap ih =>
      rw [Finset.prod_range_succ]
      exact Nat.mul_pos ih (hbase lap)
  exact Nat.mul_pos hcore hprod

/-- The existing dynamic Petal form is a canonical Petal orbit specialization. -/
theorem dynamicPetalTotal_eq_petalOrbitTotal
    (a : Nat → Nat) (k : Nat) :
    dynamicPetalTotal a k =
      petalOrbitTotal (a 0) (fun i => a i + 1) k := by
  rfl

/-- The fixed relative Petal is the constant-base canonical orbit. -/
theorem relPetalTotal_eq_petalOrbitTotal_const
    (n lap : Nat) :
    relPetalTotal n lap =
      petalOrbitTotal n (fun _ => lapBase n) lap := by
  simp [relPetalTotal, petalOrbitTotal, dynamicOrbitTotal_const, baseUnitCore]

/--
Every base already passed by a dynamic orbit divides the current prefix product.
-/
theorem dynamicOrbitTotal_base_dvd_of_lt
    (b : Nat → Nat) {i k : Nat} (hi : i < k) :
    b i ∣ dynamicOrbitTotal b k := by
  exact Finset.dvd_prod_of_mem b (by simpa [dynamicOrbitTotal] using hi)

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

/--
A strict prime-base sequence assigns prime bases in strictly increasing order.

This is the ordered version of a distinct prime-base sequence.
-/
def IsStrictPrimeBaseSequence (p : Nat → Nat) : Prop :=
  IsPrimeBaseSequence p ∧ StrictMono p

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

/-- Different laps in a distinct prime-base sequence have different bases. -/
theorem IsDistinctPrimeBaseSequence.ne_of_ne
    {p : Nat → Nat} (hp : IsDistinctPrimeBaseSequence p)
    {i j : Nat} (hij : i ≠ j) :
    p i ≠ p j := by
  intro hpij
  exact hij (hp.injective hpij)

/-- Earlier and later laps in a distinct prime-base sequence have different bases. -/
theorem IsDistinctPrimeBaseSequence.ne_of_lt
    {p : Nat → Nat} (hp : IsDistinctPrimeBaseSequence p)
    {i j : Nat} (hij : i < j) :
    p i ≠ p j := by
  exact hp.ne_of_ne (Nat.ne_of_lt hij)

/-- A strict prime-base sequence supplies a prime at each lap. -/
theorem IsStrictPrimeBaseSequence.prime_at
    {p : Nat → Nat} (hp : IsStrictPrimeBaseSequence p) (i : Nat) :
    Nat.Prime (p i) :=
  hp.1 i

/-- A strict prime-base sequence is strictly monotone. -/
theorem IsStrictPrimeBaseSequence.strictMono
    {p : Nat → Nat} (hp : IsStrictPrimeBaseSequence p) :
    StrictMono p :=
  hp.2

/-- A strict prime-base sequence is injective. -/
theorem IsStrictPrimeBaseSequence.injective
    {p : Nat → Nat} (hp : IsStrictPrimeBaseSequence p) :
    Function.Injective p :=
  hp.strictMono.injective

/-- A strict prime-base sequence is a distinct prime-base sequence. -/
theorem IsStrictPrimeBaseSequence.distinct
    {p : Nat → Nat} (hp : IsStrictPrimeBaseSequence p) :
    IsDistinctPrimeBaseSequence p :=
  ⟨hp.1, hp.injective⟩

/-- Earlier laps have smaller bases in a strict prime-base sequence. -/
theorem IsStrictPrimeBaseSequence.base_lt_of_lt
    {p : Nat → Nat} (hp : IsStrictPrimeBaseSequence p)
    {i j : Nat} (hij : i < j) :
    p i < p j :=
  hp.strictMono hij

/-- Earlier and later laps in a strict prime-base sequence have different bases. -/
theorem IsStrictPrimeBaseSequence.ne_of_lt
    {p : Nat → Nat} (hp : IsStrictPrimeBaseSequence p)
    {i j : Nat} (hij : i < j) :
    p i ≠ p j :=
  hp.distinct.ne_of_lt hij

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

/-! Small canonical-orbit examples fixing the zero-lap and constant-base cases. -/

example : petalOrbitTotal 5 (fun _ => 6) 0 = 5 := by
  decide

example : petalOrbitTotal 5 (fun _ => 6) 1 = 30 := by
  decide

example : petalOrbitTotal 5 (fun _ => 6) 2 = 180 := by
  decide

example (base : Nat → Nat) (lap : Nat) :
    petalOrbitTotal 0 base lap = 0 := by
  simp

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
