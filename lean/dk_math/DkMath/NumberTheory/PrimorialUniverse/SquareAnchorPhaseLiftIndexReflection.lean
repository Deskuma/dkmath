/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseLiftIndexAffine
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseLiftIndexReflection"

/-!
# Fresh-prime lift-index reflection

The deleted fresh-prime lift index is the center of an involutive reflection
on the `ZMod q` index circle.  The affine raw-lift residue map is negated by
this reflection, so the two phase signs are exchanged and neutral surviving
indices occur in fixed-point-free pairs.  This is finite provider-side
congruence geometry only; it does not assert primality or escape.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

/-! ## Reflection coordinate and affine residue -/

/-- Reflection of an index in the deleted center on the `ZMod q` circle. -/
def freshPrimeLiftIndexReflection (q : ℕ) (jzero j : ZMod q) : ZMod q :=
  2 * jzero - j

/-- The affine fresh-prime residue map on the index circle. -/
def freshPrimeLiftResidue (S : Finset ℕ) (q b : ℕ) (j : ZMod q) : ZMod q :=
  (b : ZMod q) + j * (finitePrimeBasisProduct S : ZMod q)

/-- A canonical natural representative of the reflection coordinate. -/
def freshPrimeLiftIndexReflectionNat
    (q jzero j : ℕ) : ℕ :=
  (freshPrimeLiftIndexReflection q (jzero : ZMod q) (j : ZMod q)).val

/-- The reflection fixes its deleted center. -/
theorem freshPrimeLiftIndexReflection_center_fixed
    {q : ℕ} {jzero : ZMod q} :
    freshPrimeLiftIndexReflection q jzero jzero = jzero := by
  simp [freshPrimeLiftIndexReflection]
  ring

/-- Reflection is an involution on the fresh-prime index circle. -/
theorem freshPrimeLiftIndexReflection_involutive
    {q : ℕ} {jzero j : ZMod q} :
    freshPrimeLiftIndexReflection q jzero
        (freshPrimeLiftIndexReflection q jzero j) = j := by
  simp [freshPrimeLiftIndexReflection]

/-- The natural reflection representative casts back to its `ZMod q` value. -/
theorem freshPrimeLiftIndexReflectionNat_cast
    {q jzero j : ℕ} [NeZero q] :
    (freshPrimeLiftIndexReflectionNat q jzero j : ZMod q) =
      freshPrimeLiftIndexReflection q (jzero : ZMod q) (j : ZMod q) := by
  simp [freshPrimeLiftIndexReflectionNat]

/-- The affine residue of a raw natural lift agrees with the circle map. -/
theorem freshPrimeLiftResidue_cast
    {S : Finset ℕ} {q b j : ℕ} :
    freshPrimeLiftResidue S q b (j : ZMod q) =
      ((primeBasisWheelLift S b j : ℕ) : ZMod q) := by
  simp [freshPrimeLiftResidue, primeBasisWheelLift,
    Nat.cast_add, Nat.cast_mul]

/-! ## Negation under reflection -/

/-- Reflection about a deleted index negates every raw lift residue. -/
theorem freshPrimeLiftResidue_reflection_neg
    {S : Finset ℕ} {q b jzero : ℕ}
    (hzero : IsFreshPrimeDeletedLiftIndex S q b jzero) :
    ∀ j : ZMod q,
      freshPrimeLiftResidue S q b
          (freshPrimeLiftIndexReflection q (jzero : ZMod q) j) =
        -freshPrimeLiftResidue S q b j := by
  intro j
  have hzero' : freshPrimeLiftResidue S q b (jzero : ZMod q) = 0 := by
    rw [freshPrimeLiftResidue_cast]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr hzero.2
  simp only [freshPrimeLiftIndexReflection, freshPrimeLiftResidue]
  simp only [freshPrimeLiftResidue] at hzero'
  linear_combination 2 * hzero'

/-! ## Phase exchange and the fixed point -/

/-- Reflection sends the unique `+a` phase index to the `-a` phase index. -/
theorem freshPrime_plus_reflection_eq_minus
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a b jplus jminus jzero : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hq2 : q ≠ 2)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    (hplus : IsFreshPrimePlusLiftIndex S q a b jplus)
    (hminus : IsFreshPrimeMinusLiftIndex S q a b jminus)
    (hzero : IsFreshPrimeDeletedLiftIndex S q b jzero) :
    freshPrimeLiftIndexReflection q (jzero : ZMod q) (jplus : ZMod q) =
      (jminus : ZMod q) := by
  have h := freshPrime_plus_reflects_to_minus_about_deleted hS hq hqS hq2
    hcop hplus hminus hzero
  simpa [freshPrimeLiftIndexReflection] using h.symm

/-- Reflection sends the unique `-a` phase index to the `+a` phase index. -/
theorem freshPrime_minus_reflection_eq_plus
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a b jplus jminus jzero : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hq2 : q ≠ 2)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    (hplus : IsFreshPrimePlusLiftIndex S q a b jplus)
    (hminus : IsFreshPrimeMinusLiftIndex S q a b jminus)
    (hzero : IsFreshPrimeDeletedLiftIndex S q b jzero) :
    freshPrimeLiftIndexReflection q (jzero : ZMod q) (jminus : ZMod q) =
      (jplus : ZMod q) := by
  have hmid := freshPrime_deleted_index_is_phase_midpoint hS hq hqS hq2 hcop
    hplus hminus hzero
  simp [freshPrimeLiftIndexReflection]
  linear_combination -hmid

/-- For an odd fresh prime, the deleted center is the unique fixed point. -/
theorem freshPrimeLiftIndexReflection_fixed_unique
    {q : ℕ} (hq : Nat.Prime q) (hq2 : q ≠ 2)
    {jzero j : ZMod q}
    (hfix : freshPrimeLiftIndexReflection q jzero j = j) :
    j = jzero := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  have h2 : (2 : ZMod q) ≠ 0 := by
    intro h2zero
    have hdiv : q ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).mp h2zero
    have hqle : q ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    have hqge2 : 2 ≤ q := hq.two_le
    omega
  simp only [freshPrimeLiftIndexReflection] at hfix
  have hEq : (2 : ZMod q) * j = 2 * jzero := by
    linear_combination -hfix
  exact mul_left_cancel₀ h2 hEq

/-! ## Survivor and neutral preservation -/

/-- A natural index below `q` and its reflection are both canonical. -/
private theorem freshPrimeLiftIndexReflectionNat_lt
    {q jzero j : ℕ} [NeZero q] :
    freshPrimeLiftIndexReflectionNat q jzero j < q := by
  exact ZMod.val_lt _

/-- Reflection preserves deletion/nondeletion of a canonical raw lift. -/
theorem freshPrimeSurvivingLiftIndex_reflection_iff
    {S : Finset ℕ}
    {q b jzero j : ℕ}
    (hzero : IsFreshPrimeDeletedLiftIndex S q b jzero)
    (hq : Nat.Prime q) (hj : j < q) :
    j ∈ freshPrimeSurvivingLiftIndices S q b ↔
      freshPrimeLiftIndexReflectionNat q jzero j ∈
        freshPrimeSurvivingLiftIndices S q b := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  let k := freshPrimeLiftIndexReflectionNat q jzero j
  have hk : k < q := freshPrimeLiftIndexReflectionNat_lt
  have hcast : (k : ZMod q) =
      freshPrimeLiftIndexReflection q (jzero : ZMod q) (j : ZMod q) := by
    exact freshPrimeLiftIndexReflectionNat_cast
  have hneg := freshPrimeLiftResidue_reflection_neg hzero
    (j : ZMod q)
  have hres : freshPrimeLiftResidue S q b (j : ZMod q) =
      ((primeBasisWheelLift S b j : ℕ) : ZMod q) :=
    freshPrimeLiftResidue_cast
  have hkres : freshPrimeLiftResidue S q b (k : ZMod q) =
      ((primeBasisWheelLift S b k : ℕ) : ZMod q) :=
    freshPrimeLiftResidue_cast
  rw [mem_freshPrimeSurvivingLiftIndices_iff,
    mem_freshPrimeSurvivingLiftIndices_iff]
  rw [hres] at hneg
  rw [← hcast, hkres] at hneg
  constructor <;> intro h
  · refine ⟨hk, ?_⟩
    intro hdiv
    have hz : ((primeBasisWheelLift S b k : ℕ) : ZMod q) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
    have hzj : ((primeBasisWheelLift S b j : ℕ) : ZMod q) = 0 := by
      have hzj' : -((primeBasisWheelLift S b j : ℕ) : ZMod q) = 0 :=
        hneg.symm.trans hz
      simpa using hzj'
    exact h.2 ((ZMod.natCast_eq_zero_iff _ _).mp hzj)
  · refine ⟨hj, ?_⟩
    intro hdiv
    have hz : ((primeBasisWheelLift S b j : ℕ) : ZMod q) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
    have hkzero : ((primeBasisWheelLift S b k : ℕ) : ZMod q) = 0 := by
      rw [hneg, hz]
      simp
    exact h.2 (ZMod.natCast_eq_zero_iff _ _ |>.mp hkzero)

/-- Reflection exchanges the two phase signs on canonical natural indices. -/
theorem freshPrimePhaseLiftIndex_reflection_iff
    {S : Finset ℕ} {q a b jzero j : ℕ}
    (hzero : IsFreshPrimeDeletedLiftIndex S q b jzero)
    (hq : Nat.Prime q) (hj : j < q) :
    j ∈ freshPrimePhaseLiftIndices S q a b ↔
      freshPrimeLiftIndexReflectionNat q jzero j ∈
        freshPrimePhaseLiftIndices S q a b := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  let k := freshPrimeLiftIndexReflectionNat q jzero j
  have hk : k < q := freshPrimeLiftIndexReflectionNat_lt
  have hcast : (k : ZMod q) =
      freshPrimeLiftIndexReflection q (jzero : ZMod q) (j : ZMod q) := by
    exact freshPrimeLiftIndexReflectionNat_cast
  have hneg := freshPrimeLiftResidue_reflection_neg hzero
    (j : ZMod q)
  have hres : freshPrimeLiftResidue S q b (j : ZMod q) =
      ((primeBasisWheelLift S b j : ℕ) : ZMod q) :=
    freshPrimeLiftResidue_cast
  have hkres : freshPrimeLiftResidue S q b (k : ZMod q) =
      ((primeBasisWheelLift S b k : ℕ) : ZMod q) :=
    freshPrimeLiftResidue_cast
  rw [← hcast, hres, hkres] at hneg
  rw [mem_freshPrimePhaseLiftIndices_iff,
    mem_freshPrimePhaseLiftIndices_iff]
  constructor
  · intro h
    rcases h with hplus | hminus
    · right
      refine ⟨hk, ?_⟩
      calc
          (primeBasisWheelLift S b k : ZMod q) =
              -((primeBasisWheelLift S b j : ℕ) : ZMod q) := hneg
          _ = -(a : ZMod q) := by rw [hplus.2]
    · left
      refine ⟨hk, ?_⟩
      calc
          (primeBasisWheelLift S b k : ZMod q) =
              -((primeBasisWheelLift S b j : ℕ) : ZMod q) := hneg
          _ = (a : ZMod q) := by rw [hminus.2]; simp
  · intro h
    have hneg' : ((primeBasisWheelLift S b j : ℕ) : ZMod q) =
        -((primeBasisWheelLift S b k : ℕ) : ZMod q) := by
      have hnegk := freshPrimeLiftResidue_reflection_neg hzero
        (k : ZMod q)
      have hreturn : freshPrimeLiftIndexReflection q (jzero : ZMod q)
          (k : ZMod q) = (j : ZMod q) := by
        calc
          freshPrimeLiftIndexReflection q (jzero : ZMod q) (k : ZMod q) =
              freshPrimeLiftIndexReflection q (jzero : ZMod q)
                (freshPrimeLiftIndexReflection q (jzero : ZMod q) (j : ZMod q)) := by
                  rw [hcast]
          _ = (j : ZMod q) := freshPrimeLiftIndexReflection_involutive
      rw [hreturn, hres, hkres] at hnegk
      exact hnegk
    rcases h with hplus | hminus
    · right
      refine ⟨hj, ?_⟩
      calc
          (primeBasisWheelLift S b j : ZMod q) =
              -((primeBasisWheelLift S b k : ℕ) : ZMod q) := hneg'
          _ = -(a : ZMod q) := by rw [hplus.2]
    · left
      refine ⟨hj, ?_⟩
      calc
          (primeBasisWheelLift S b j : ZMod q) =
              -((primeBasisWheelLift S b k : ℕ) : ZMod q) := hneg'
          _ = (a : ZMod q) := by rw [hminus.2]; simp

/-- Reflection preserves the neutral surviving-index set. -/
theorem freshPrimeNeutralLiftIndex_reflection_iff
    {S : Finset ℕ} {q a b jzero j : ℕ}
    (hzero : IsFreshPrimeDeletedLiftIndex S q b jzero)
    (hq : Nat.Prime q) (hj : j < q) :
    j ∈ freshPrimeNeutralLiftIndices S q a b ↔
      freshPrimeLiftIndexReflectionNat q jzero j ∈
        freshPrimeNeutralLiftIndices S q a b := by
  rw [mem_freshPrimeNeutralLiftIndices_iff,
    mem_freshPrimeNeutralLiftIndices_iff]
  have hsurv := freshPrimeSurvivingLiftIndex_reflection_iff hzero hq hj
  have hphase := freshPrimePhaseLiftIndex_reflection_iff (a := a) hzero hq hj
  constructor
  · intro h
    exact ⟨hsurv.mp h.1, fun hk => h.2 (hphase.mpr hk)⟩
  · intro h
    exact ⟨hsurv.mpr h.1, fun hj' => h.2 (hphase.mp hj')⟩

/-! ## Fixed-point-free neutral partners -/

/-- Every neutral canonical index has a unique distinct neutral reflection partner. -/
theorem freshPrimeNeutralLiftIndex_existsUnique_reflected_partner
    {S : Finset ℕ} {q a b jzero j : ℕ}
    (hzero : IsFreshPrimeDeletedLiftIndex S q b jzero)
    (hq : Nat.Prime q) (hq2 : q ≠ 2) (hj : j < q)
    (hneutral : j ∈ freshPrimeNeutralLiftIndices S q a b) :
    ∃! k : ℕ,
      k < q ∧
      k ∈ freshPrimeNeutralLiftIndices S q a b ∧
      k ≠ j ∧
      (k : ZMod q) =
        freshPrimeLiftIndexReflection q (jzero : ZMod q) (j : ZMod q) := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  let k := freshPrimeLiftIndexReflectionNat q jzero j
  have hk : k < q := freshPrimeLiftIndexReflectionNat_lt
  have hcast : (k : ZMod q) =
      freshPrimeLiftIndexReflection q (jzero : ZMod q) (j : ZMod q) := by
    exact freshPrimeLiftIndexReflectionNat_cast
  have hkn : k ∈ freshPrimeNeutralLiftIndices S q a b :=
    (freshPrimeNeutralLiftIndex_reflection_iff hzero hq hj).mp hneutral
  have hkj : k ≠ j := by
    intro hEq
    have hfix : freshPrimeLiftIndexReflection q (jzero : ZMod q)
        (j : ZMod q) = (j : ZMod q) := by
      calc
        freshPrimeLiftIndexReflection q (jzero : ZMod q) (j : ZMod q) =
            (k : ZMod q) := hcast.symm
        _ = (j : ZMod q) := by rw [hEq]
    have hjzero : (j : ZMod q) = (jzero : ZMod q) :=
      freshPrimeLiftIndexReflection_fixed_unique hq hq2 hfix
    have hjzero' : j = jzero := by
      have hmod := (ZMod.natCast_eq_natCast_iff j jzero q).mp hjzero
      change j % q = jzero % q at hmod
      simpa [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hzero.1] using hmod
    have hneutral' := (mem_freshPrimeNeutralLiftIndices_iff
      (S := S) (q := q) (a := a) (b := b) (j := j)).mp hneutral
    have hsurv' := (mem_freshPrimeSurvivingLiftIndices_iff
      (S := S) (q := q) (r := b) (j := j)).mp hneutral'.1
    exact hsurv'.2 (by simpa [hjzero'] using hzero.2)
  have hreturn :
      (freshPrimeLiftIndexReflectionNat q jzero k : ZMod q) = (j : ZMod q) := by
    have hcastk : (freshPrimeLiftIndexReflectionNat q jzero k : ZMod q) =
        freshPrimeLiftIndexReflection q (jzero : ZMod q) (k : ZMod q) :=
      freshPrimeLiftIndexReflectionNat_cast
    calc
      (freshPrimeLiftIndexReflectionNat q jzero k : ZMod q) =
          freshPrimeLiftIndexReflection q (jzero : ZMod q) (k : ZMod q) := hcastk
      _ = freshPrimeLiftIndexReflection q (jzero : ZMod q)
          (freshPrimeLiftIndexReflection q (jzero : ZMod q) (j : ZMod q)) := by
            rw [hcast]
      _ = (j : ZMod q) := freshPrimeLiftIndexReflection_involutive
  refine ⟨k, ⟨hk, hkn, hkj, hcast⟩, ?_⟩
  intro y hy
  have hycast : (y : ZMod q) = (k : ZMod q) := hy.2.2.2.trans hcast.symm
  have hmod := (ZMod.natCast_eq_natCast_iff y k q).mp hycast
  change y % q = k % q at hmod
  simpa [Nat.mod_eq_of_lt hy.1, Nat.mod_eq_of_lt hk] using hmod

/-! ## A nonempty two-cycle above `3` -/

/-- For `3 < q`, neutral survivors provide a genuine reflected two-cycle. -/
theorem freshPrimeNeutralLiftIndices_exists_two_cycle_of_three_lt
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {q a b : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hq3 : 3 < q)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    (hb : b ∈ squareAnchorPhaseFiber S a) :
    ∃ jzero j k,
      IsFreshPrimeDeletedLiftIndex S q b jzero ∧
      j ∈ freshPrimeNeutralLiftIndices S q a b ∧
      k ∈ freshPrimeNeutralLiftIndices S q a b ∧
      j ≠ k ∧
      (k : ZMod q) =
        freshPrimeLiftIndexReflection q (jzero : ZMod q) (j : ZMod q) := by
  obtain ⟨j, hj⟩ :=
    Finset.card_pos.mp (by
      rw [card_freshPrimeNeutralLiftIndices hS hSne hq hqS (by omega) hcop hb]
      omega)
  have hj' := (mem_freshPrimeNeutralLiftIndices_iff
    (S := S) (q := q) (a := a) (b := b) (j := j)).mp hj
  have hjlt := (mem_freshPrimeSurvivingLiftIndices_iff
    (S := S) (q := q) (r := b) (j := j)).mp hj'.1 |>.1
  obtain ⟨jzero, hzero, _⟩ := existsUnique_freshPrime_deleted_lift_index
    hS hSne hq hqS hcop hb
  obtain ⟨k, hkprop, _⟩ :=
    freshPrimeNeutralLiftIndex_existsUnique_reflected_partner hzero hq
      (by omega) hjlt hj
  rcases hkprop with ⟨hklt, hkneutral, hkj, hkref⟩
  exact ⟨jzero, j, k, hzero, hj, hkneutral, hkj.symm, hkref⟩

/-- At fresh `q = 3`, the L022 neutral set has no index to pair. -/
theorem freshPrimeNeutralLiftIndices_no_neutral_of_q_eq_three
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {a b : ℕ}
    (h3S : 3 ∉ S)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert 3 S)))
    (hb : b ∈ squareAnchorPhaseFiber S a) :
    freshPrimeNeutralLiftIndices S 3 a b = ∅ := by
  exact freshPrimeNeutralLiftIndices_eq_empty_of_q_eq_three
    hS hSne h3S hcop hb

/-! ## Visible `6 -> 30` regression -/

/-- The `6 -> 30` raw index circle has phase, neutral, and deleted orbits. -/
theorem freshPrimeLiftIndexReflection_two_three_five_regression :
    freshPrimeLiftIndexReflectionNat 5 4 0 = 3 ∧
      freshPrimeLiftIndexReflectionNat 5 4 3 = 0 ∧
      freshPrimeLiftIndexReflectionNat 5 4 1 = 2 ∧
      freshPrimeLiftIndexReflectionNat 5 4 2 = 1 ∧
      freshPrimeLiftIndexReflectionNat 5 4 4 = 4 ∧
      freshPrimePhaseLiftIndices ({2, 3} : Finset ℕ) 5 1 1 = {0, 3} ∧
      freshPrimeNeutralLiftIndices ({2, 3} : Finset ℕ) 5 1 1 = {1, 2} := by
  rcases freshPrimeLiftIndex_two_three_five_regression with
    ⟨_, _, _, _, _, _, _, _, hphase, _, hneutral⟩
  exact ⟨by decide, by decide, by decide, by decide, by decide, hphase, hneutral⟩

end DkMath.NumberTheory.PrimorialUniverse
