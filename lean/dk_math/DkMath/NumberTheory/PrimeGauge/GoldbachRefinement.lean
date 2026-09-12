/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Goldbach.PrimeWorld
import DkMath.NumberTheory.PrimeGauge.GoldbachPhase
import DkMath.NumberTheory.Primitive.PrimeWorldRefinement

#print "file: DkMath.NumberTheory.PrimeGauge.GoldbachRefinement"

/-!
# Paired Goldbach child refinement

This module packages the two raw `ZMod q` targets on a bounded old-world
fiber.  It is a finite coordinate observer: reserved children and surviving
children are not asserted to be prime, and proper endpoint exceptions remain
outside this phase layer.
-/

namespace DkMath.NumberTheory.PrimeGauge

open DkMath.NumberTheory
open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic

noncomputable section

/-- The left raw Goldbach target on a bounded child fiber. -/
def goldbachLeftReservedChildIndices
    (n : ℕ) (S : Finset ℕ) (q r : ℕ) : Finset ℕ :=
  (primeWorldChildIndices q).filter
    (fun j => (primeWorldChild S r j : ZMod q) = (n : ZMod q))

/-- The right raw Goldbach target on a bounded child fiber. -/
def goldbachRightReservedChildIndices
    (n : ℕ) (S : Finset ℕ) (q r : ℕ) : Finset ℕ :=
  (primeWorldChildIndices q).filter
    (fun j => (primeWorldChild S r j : ZMod q) = -(n : ZMod q))

/-- The union of the two raw Goldbach reserved-child index sets. -/
def pairedReservedChildIndices
    (n : ℕ) (S : Finset ℕ) (q r : ℕ) : Finset ℕ :=
  goldbachLeftReservedChildIndices n S q r ∪
    goldbachRightReservedChildIndices n S q r

/-- Bounded child indices avoiding both raw Goldbach targets. -/
def pairedSurvivingChildIndices
    (n : ℕ) (S : Finset ℕ) (q r : ℕ) : Finset ℕ :=
  primeWorldChildIndices q \ pairedReservedChildIndices n S q r

/-- Exactly one bounded child realizes the left raw Goldbach target. -/
theorem existsUnique_leftReservedChild
    {S : Finset ℕ} (hS : KnownPrimeScales S)
    {q r : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hr : r < primeWorldModulus S)
    (n : ℕ) :
    ∃! j : ℕ,
      j < q ∧
      (primeWorldChild S r j : ZMod q) = (n : ZMod q) := by
  exact existsUnique_child_eq_target hS hq hqS hr (n : ZMod q)

/-- Exactly one bounded child realizes the right conjugate Goldbach target. -/
theorem existsUnique_rightReservedChild
    {S : Finset ℕ} (hS : KnownPrimeScales S)
    {q r : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hr : r < primeWorldModulus S)
    (n : ℕ) :
    ∃! j : ℕ,
      j < q ∧
      (primeWorldChild S r j : ZMod q) = -(n : ZMod q) := by
  exact existsUnique_child_eq_target hS hq hqS hr (-(n : ZMod q))

/-- The two reserved indices are distinct when the two raw targets are distinct. -/
theorem leftReservedChild_ne_rightReservedChild_of_not_dvd_two_center
    {S : Finset ℕ}
    {q r n jL jR : ℕ}
    (hL : jL < q ∧
      (primeWorldChild S r jL : ZMod q) = (n : ZMod q))
    (hR : jR < q ∧
      (primeWorldChild S r jR : ZMod q) = -(n : ZMod q))
    (hnot : ¬ q ∣ 2 * n) :
    jL ≠ jR := by
  intro heq
  have htargets : (n : ZMod q) = -(n : ZMod q) := by
    exact hL.2.symm.trans ((congrArg (fun j : ℕ =>
      (primeWorldChild S r j : ZMod q)) heq).trans hR.2)
  exact hnot ((goldbach_residue_eq_neg_iff n q).mp htargets)

/-- The two reserved child indices have the parent-independent relative shape. -/
theorem goldbach_reservedChild_relative_shape
    {S : Finset ℕ} {q r n jL jR : ℕ}
    (hL :
      (primeWorldChild S r jL : ZMod q) = (n : ZMod q))
    (hR :
      (primeWorldChild S r jR : ZMod q) = -(n : ZMod q)) :
    ((jL : ZMod q) - (jR : ZMod q)) *
        (primeWorldModulus S : ZMod q)
      = (2 * n : ℕ) := by
  calc
      ((jL : ZMod q) - (jR : ZMod q)) *
          (primeWorldModulus S : ZMod q) =
        (jL * primeWorldModulus S : ZMod q) -
          (jR * primeWorldModulus S : ZMod q) := by
            ring
    _ = (primeWorldChild S r jL : ZMod q) -
          (primeWorldChild S r jR : ZMod q) := by
            simp only [primeWorldChild, Nat.cast_add, Nat.cast_mul]
            ring
    _ = (n : ZMod q) - -(n : ZMod q) := by rw [hL, hR]
    _ = (2 * n : ℕ) := by
      push_cast
      ring

/-- The relative shape advances by two when the center advances by one. -/
theorem goldbach_reservedChild_relative_shape_succ
    {S : Finset ℕ}
    {q r r' n jL jR jL' jR' : ℕ}
    (hL :
      (primeWorldChild S r jL : ZMod q) = (n : ZMod q))
    (hR :
      (primeWorldChild S r jR : ZMod q) = -(n : ZMod q))
    (hL' :
      (primeWorldChild S r' jL' : ZMod q) = (n + 1 : ℕ))
    (hR' :
      (primeWorldChild S r' jR' : ZMod q) = -(n + 1 : ℕ)) :
    (((jL' : ZMod q) - jR') - ((jL : ZMod q) - jR)) *
        (primeWorldModulus S : ZMod q) = 2 := by
  have hshape := goldbach_reservedChild_relative_shape hL hR
  have hshape' := goldbach_reservedChild_relative_shape hL' hR'
  calc
    (((jL' : ZMod q) - jR') - ((jL : ZMod q) - jR)) *
          (primeWorldModulus S : ZMod q) =
        ((jL' : ZMod q) - jR') *
            (primeWorldModulus S : ZMod q) -
          ((jL : ZMod q) - jR) *
            (primeWorldModulus S : ZMod q) := by
              ring
    _ = (2 * (n + 1) : ℕ) - (2 * n : ℕ) := by
      rw [hshape', hshape]
    _ = 2 := by
      push_cast
      ring

/-- The paired reserved-child set has two elements when the targets do not merge. -/
theorem pairedReservedChildIndices_card_eq_two
    {S : Finset ℕ} (hS : KnownPrimeScales S)
    {q r n : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hr : r < primeWorldModulus S)
    (hnot : ¬ q ∣ 2 * n) :
    (pairedReservedChildIndices n S q r).card = 2 := by
  obtain ⟨jL, hL, hLuniq⟩ :=
    existsUnique_leftReservedChild hS hq hqS hr n
  obtain ⟨jR, hR, hRuniq⟩ :=
    existsUnique_rightReservedChild hS hq hqS hr n
  have hjne : jL ≠ jR :=
    leftReservedChild_ne_rightReservedChild_of_not_dvd_two_center
      hL hR hnot
  have hleft : goldbachLeftReservedChildIndices n S q r = {jL} := by
    ext j
    simp only [goldbachLeftReservedChildIndices, primeWorldChildIndices,
      Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · intro hj
      exact hLuniq j hj
    · intro hj
      subst j
      exact hL
  have hright : goldbachRightReservedChildIndices n S q r = {jR} := by
    ext j
    simp only [goldbachRightReservedChildIndices, primeWorldChildIndices,
      Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · intro hj
      exact hRuniq j hj
    · intro hj
      subst j
      exact hR
  rw [pairedReservedChildIndices, hleft, hright,
    Finset.union_singleton]
  exact Finset.card_pair hjne.symm

/-- Exactly `q - 2` bounded children avoid both distinct raw targets. -/
theorem pairedSurvivingChildIndices_card_eq_q_sub_two
    {S : Finset ℕ} (hS : KnownPrimeScales S)
    {q r n : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hr : r < primeWorldModulus S)
    (hnot : ¬ q ∣ 2 * n) :
    (pairedSurvivingChildIndices n S q r).card = q - 2 := by
  have hsubset :
      pairedReservedChildIndices n S q r ⊆ primeWorldChildIndices q := by
    intro j hj
    exact (Finset.mem_union.mp hj).elim
      (fun h => (Finset.mem_filter.mp h).1)
      (fun h => (Finset.mem_filter.mp h).1)
  rw [pairedSurvivingChildIndices,
    Finset.card_sdiff_of_subset hsubset,
    pairedReservedChildIndices_card_eq_two hS hq hqS hr hnot]
  simp [primeWorldChildIndices]

end

end DkMath.NumberTheory.PrimeGauge
