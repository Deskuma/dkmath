/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.DescentBridge

#print "file: DkMath.NumberTheory.PrimitiveSet.PrimeDescent"

namespace DkMath.NumberTheory.PrimitiveSet

open DkMath.CosmicFormula.Mass

/-- One divisibility descent step from `n` down to `m`. -/
def DvdDescentStep (n m : ℕ) : Prop :=
  m ∣ n

/-- A proper divisibility descent step from `n` down to a different divisor `m`. -/
def ProperDvdDescentStep (n m : ℕ) : Prop :=
  m ∣ n ∧ m ≠ n

/--
One prime descent step from `n` down to `m`.

The step records a prime divisor `p` of `n` and the quotient `m = n / p`.
This is the finite skeleton of the later `n -> n / p` descent used before
adding von Mangoldt weights.
-/
def PrimeDescentStep (n m : ℕ) : Prop :=
  ∃ p, Nat.Prime p ∧ p ∣ n ∧ m = n / p

/--
One prime-power descent step from `n` down to `m`.

This is included as a lightweight sibling for future von Mangoldt-style
prime-power channels.
-/
def PrimePowerDescentStep (n m : ℕ) : Prop :=
  ∃ p k, Nat.Prime p ∧ 0 < k ∧ p ^ k ∣ n ∧ m = n / p ^ k

namespace DvdDescentStep

/-- A divisibility descent step is exactly a divisibility witness. -/
theorem dvd {n m : ℕ} (h : DvdDescentStep n m) : m ∣ n :=
  h

end DvdDescentStep

namespace ProperDvdDescentStep

/-- A proper divisibility descent step forgets to a divisibility step. -/
theorem toDvdDescentStep {n m : ℕ} (h : ProperDvdDescentStep n m) :
    DvdDescentStep n m :=
  h.1

/-- A proper divisibility descent step gives a divisor of the source. -/
theorem dvd {n m : ℕ} (h : ProperDvdDescentStep n m) : m ∣ n :=
  h.1

/-- A proper divisibility descent step is not stationary. -/
theorem ne {n m : ℕ} (h : ProperDvdDescentStep n m) : m ≠ n :=
  h.2

end ProperDvdDescentStep

namespace PrimeDescentStep

/-- A prime descent step gives a divisibility descent step. -/
theorem toDvdDescentStep {n m : ℕ} (h : PrimeDescentStep n m) :
    DvdDescentStep n m := by
  rcases h with ⟨p, hp, hpdvd, rfl⟩
  exact Nat.div_dvd_of_dvd hpdvd

/-- A prime descent step lands on a divisor of its source. -/
theorem dvd_source {n m : ℕ} (h : PrimeDescentStep n m) : m ∣ n :=
  h.toDvdDescentStep

/-- A prime descent step carries a witnessing prime. -/
theorem exists_prime_witness {n m : ℕ} (h : PrimeDescentStep n m) :
    ∃ p, Nat.Prime p ∧ p ∣ n ∧ m = n / p :=
  h

end PrimeDescentStep

namespace PrimePowerDescentStep

/-- A prime-power descent step gives a divisibility descent step. -/
theorem toDvdDescentStep {n m : ℕ} (h : PrimePowerDescentStep n m) :
    DvdDescentStep n m := by
  rcases h with ⟨p, k, hp, hk, hpkdvd, rfl⟩
  exact Nat.div_dvd_of_dvd hpkdvd

/-- A prime-power descent step lands on a divisor of its source. -/
theorem dvd_source {n m : ℕ} (h : PrimePowerDescentStep n m) : m ∣ n :=
  h.toDvdDescentStep

end PrimePowerDescentStep

/--
A finite chain family controlled by prime descent from chosen sources.

Every point on the `i`-th chain is reached from `source i` by one prime
descent step.  This is intentionally one-step; finite multi-step paths can be
added later without changing the `DvdControlledChainFamily` target.
-/
structure PrimeStepControlledChainFamily
    (ι : Type _) [DecidableEq ι]
    extends DivisibilityChainFamily ι where
  source : ι → ℕ
  chain_prime_step :
    ∀ i ∈ index, ∀ h ∈ chain i, PrimeDescentStep (source i) h

namespace PrimeStepControlledChainFamily

/-- Forget prime-step control to divisibility control. -/
def toDvdControlled
    {ι : Type _} [DecidableEq ι]
    (F : PrimeStepControlledChainFamily ι) :
    DvdControlledChainFamily ι where
  index := F.index
  chain := F.chain
  chain_is_chain := F.chain_is_chain
  source := F.source
  chain_dvd_source := by
    intro i hi h hh
    exact (F.chain_prime_step i hi h hh).dvd_source

@[simp] theorem toDvdControlled_index
    {ι : Type _} [DecidableEq ι]
    (F : PrimeStepControlledChainFamily ι) :
    F.toDvdControlled.index = F.index := rfl

@[simp] theorem toDvdControlled_chain
    {ι : Type _} [DecidableEq ι]
    (F : PrimeStepControlledChainFamily ι) :
    F.toDvdControlled.chain = F.chain := rfl

@[simp] theorem toDvdControlled_source
    {ι : Type _} [DecidableEq ι]
    (F : PrimeStepControlledChainFamily ι) :
    F.toDvdControlled.source = F.source := rfl

/--
Primitive hitting bound supplied by prime descent plus divisibility-monotone
mass.
-/
theorem primitive_hitMass_le_sourceMass
    {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ} {S : Finset ℕ}
    (hS : PrimitiveOn S)
    (F : PrimeStepControlledChainFamily ι)
    (hM : DvdMonotoneMass M) :
    (F.toDvdControlled.toSourceControlled hM).hitMass S ≤
      (F.toDvdControlled.toSourceControlled hM).sourceMass := by
  exact F.toDvdControlled.primitive_hitMass_le_sourceMass hS hM

end PrimeStepControlledChainFamily

/-- Concrete prime descent step: `8 -> 4`. -/
theorem primeDescentStep_eight_four :
    PrimeDescentStep 8 4 := by
  refine ⟨2, by norm_num, by norm_num, ?_⟩
  norm_num

/-- Concrete prime descent step: `9 -> 3`. -/
theorem primeDescentStep_nine_three :
    PrimeDescentStep 9 3 := by
  refine ⟨3, by norm_num, by norm_num, ?_⟩
  norm_num

/-- A Bool-indexed one-step prime descent sample. -/
def samplePrimeStepControlledBoolChainFamily :
    PrimeStepControlledChainFamily Bool where
  index := {false, true}
  chain := fun b => if b then ({3} : Finset ℕ) else ({4} : Finset ℕ)
  chain_is_chain := by
    intro b hb
    cases b
    · intro a c ha hc
      simp only [Bool.false_eq_true, ↓reduceIte, Finset.mem_singleton] at ha hc
      subst a
      subst c
      exact Or.inl dvd_rfl
    · intro a c ha hc
      simp only [↓reduceIte, Finset.mem_singleton] at ha hc
      subst a
      subst c
      exact Or.inl dvd_rfl
  source := fun b => if b then 9 else 8
  chain_prime_step := by
    intro b hb h hh
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, Finset.mem_singleton] at hh
      subst h
      simpa only [Bool.false_eq_true, ↓reduceIte] using primeDescentStep_eight_four
    · simp only [↓reduceIte, Finset.mem_singleton] at hh
      subst h
      simpa only [↓reduceIte] using primeDescentStep_nine_three

/--
Concrete prime-step sample: `{3, 4}` hitting the two one-step prime descent
chains has indexed unit hit mass bounded by source mass.
-/
theorem primitive_three_four_samplePrimeStepControlledBoolChainFamily_hitMass_le_sourceMass :
    (samplePrimeStepControlledBoolChainFamily.toDvdControlled.toSourceControlled
      unitNatMassSpace_dvdMonotone).hitMass ({3, 4} : Finset ℕ) ≤
      (samplePrimeStepControlledBoolChainFamily.toDvdControlled.toSourceControlled
        unitNatMassSpace_dvdMonotone).sourceMass := by
  have hS : PrimitiveOn ({3, 4} : Finset ℕ) := by
    exact primitiveOn_pair (by norm_num) (by norm_num)
  exact samplePrimeStepControlledBoolChainFamily.primitive_hitMass_le_sourceMass
    hS unitNatMassSpace_dvdMonotone

end DkMath.NumberTheory.PrimitiveSet
