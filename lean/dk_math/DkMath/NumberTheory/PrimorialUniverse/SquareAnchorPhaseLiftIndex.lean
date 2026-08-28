/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseSurvivorSubcover
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseLiftIndex"

/-!
# Fresh-prime phase lift indices

For a fresh odd prime `q`, the `q` raw lifts of an old survivor split into
three local residue classes: one `+a` phase lift, one `-a` phase lift, and one
deleted zero lift.  The remaining `q - 3` indices are surviving but neutral
with respect to the square phase.

This is a finite provider-side refinement of the phase/survivor subcover.  It
does not assert that any lift is prime and does not introduce escape,
Legendre, gap, PowerSwap, GN/CosmicFormula, PNT, or RH statements.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

/-! ## Index predicates and finite sets -/

/-- A raw lift index whose fresh-prime residue is `+a`. -/
def IsFreshPrimePlusLiftIndex
    (S : Finset ℕ) (q a b j : ℕ) : Prop :=
  j < q ∧
    ((primeBasisWheelLift S b j : ZMod q) = (a : ZMod q))

/-- A raw lift index whose fresh-prime residue is `-a`. -/
def IsFreshPrimeMinusLiftIndex
    (S : Finset ℕ) (q a b j : ℕ) : Prop :=
  j < q ∧
    ((primeBasisWheelLift S b j : ZMod q) = -(a : ZMod q))

/-- A raw lift index deleted by divisibility by the fresh prime. -/
def IsFreshPrimeDeletedLiftIndex
    (S : Finset ℕ) (q b j : ℕ) : Prop :=
  j < q ∧ q ∣ primeBasisWheelLift S b j

/-- The two sign-selected raw lift indices. -/
noncomputable def freshPrimePhaseLiftIndices
    (S : Finset ℕ) (q a b : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range q).filter (fun j =>
    IsFreshPrimePlusLiftIndex S q a b j ∨
      IsFreshPrimeMinusLiftIndex S q a b j)

@[simp] theorem mem_freshPrimePhaseLiftIndices_iff
    {S : Finset ℕ} {q a b j : ℕ} :
    j ∈ freshPrimePhaseLiftIndices S q a b ↔
      IsFreshPrimePlusLiftIndex S q a b j ∨
        IsFreshPrimeMinusLiftIndex S q a b j := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨
      Finset.mem_range.mpr (h.elim (fun hp => hp.1) (fun hm => hm.1)), h⟩

/-- Surviving indices not selected by either square-phase sign. -/
noncomputable def freshPrimeNeutralLiftIndices
    (S : Finset ℕ) (q a b : ℕ) : Finset ℕ :=
  freshPrimeSurvivingLiftIndices S q b \
    freshPrimePhaseLiftIndices S q a b

@[simp] theorem mem_freshPrimeNeutralLiftIndices_iff
    {S : Finset ℕ} {q a b j : ℕ} :
    j ∈ freshPrimeNeutralLiftIndices S q a b ↔
      j ∈ freshPrimeSurvivingLiftIndices S q b ∧
        j ∉ freshPrimePhaseLiftIndices S q a b := by
  simp [freshPrimeNeutralLiftIndices]

/-! ## Raw lift coordinates -/

private theorem exists_raw_lift_index_of_phaseProjection_mem
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a b x : ℕ}
    (_hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hx : x ∈ squareAnchorPhaseProjectionFiber S q a b) :
    ∃ j, j < q ∧ x = primeBasisWheelLift S b j := by
  have hMpos : 0 < finitePrimeBasisProduct S :=
    Nat.pos_of_ne_zero (finitePrimeBasisProduct_ne_zero hS)
  have hx' := mem_squareAnchorPhaseProjectionFiber.mp hx
  have hxf := mem_squareAnchorPhaseFiber.mp hx'.1
  let j := x / finitePrimeBasisProduct S
  have hdecomp : x = x % finitePrimeBasisProduct S +
      j * finitePrimeBasisProduct S := by
    dsimp [j]
    rw [Nat.mod_add_div' x (finitePrimeBasisProduct S)]
  have hrepr : x = primeBasisWheelLift S b j := by
    rw [hdecomp, primeBasisWheelLift]
    have hproj : x % finitePrimeBasisProduct S = b := hx'.2
    rw [hproj]
  have hMq : finitePrimeBasisProduct S * j <
      finitePrimeBasisProduct S * q := by
    have hMj : finitePrimeBasisProduct S * j ≤ x := by
      rw [hdecomp]
      rw [Nat.mul_comm j]
      exact Nat.le_add_left _ _
    apply lt_of_le_of_lt hMj
    rw [finitePrimeBasisProduct_insert hqS] at hxf
    simpa [j, Nat.mul_comm] using hxf.1
  have hj : j < q := (Nat.mul_lt_mul_left hMpos).mp hMq
  exact ⟨j, hj, hrepr⟩

private theorem same_residue_raw_lift_index_eq
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q b j k : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hj : j < q) (hk : k < q)
    (hjk : (primeBasisWheelLift S b j : ZMod q) =
      (primeBasisWheelLift S b k : ZMod q)) :
    j = k := by
  have hmod : primeBasisWheelLift S b j ≡
      primeBasisWheelLift S b k [MOD q] :=
    (ZMod.natCast_eq_natCast_iff _ _ q).mp hjk
  have hmod' : j * finitePrimeBasisProduct S ≡
      k * finitePrimeBasisProduct S [MOD q] := by
    have hmod'' : b + j * finitePrimeBasisProduct S ≡
        b + k * finitePrimeBasisProduct S [MOD q] := by
      simpa [primeBasisWheelLift] using hmod
    exact Nat.ModEq.rfl.add_left_cancel hmod''
  have hjk' : j ≡ k [MOD q] := by
    apply Nat.ModEq.cancel_right_of_coprime
      (freshPrime_coprime_finitePrimeBasisProduct hS hq hqS).gcd_eq_one
    simpa [Nat.mul_comm] using hmod'
  change j % q = k % q at hjk'
  simpa [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hk] using hjk'

/-! A phase lift index can be recovered from a phase projection seat. -/
private theorem phase_projection_mem_of_raw_phase_index
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {q a b j : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    (hb : b ∈ squareAnchorPhaseFiber S a)
    (hj : IsFreshPrimePlusLiftIndex S q a b j ∨
      IsFreshPrimeMinusLiftIndex S q a b j) :
    primeBasisWheelLift S b j ∈
      squareAnchorPhaseProjectionFiber S q a b := by
  have hsurv := squareAnchorPhaseFiber_mem_wheelSurvivor_of_coprime_anchor
    hS hSne (hcop.of_dvd_right (by
      rw [finitePrimeBasisProduct_insert hqS]
      exact dvd_mul_left _ _)) hb
  have hjlt : j < q := hj.elim (fun hp => hp.1) (fun hm => hm.1)
  have hbound := primeBasisWheelLift_mem_enlarged_period hS hq hqS
    (r := b) (j := j) hsurv hjlt
  have hS' : IsFinitePrimeBasis (insert q S) := by
    intro p hp
    simp only [Finset.mem_insert] at hp
    rcases hp with rfl | hp
    · exact hq
    · exact hS p hp
  have hprofileB : SameSquarePrimeSignProfile S a b :=
    (sameSquareAnchorPhase_iff_primeSignProfile hS).mp
      (mem_squareAnchorPhaseFiber.mp hb).2
  have hprofile : SameSquarePrimeSignProfile
      (insert q S) a (primeBasisWheelLift S b j) := by
    intro p hp
    simp only [Finset.mem_insert] at hp
    rcases hp with hpq | hpS
    · subst p
      rcases hj with hjplus | hjminus
      · left
        exact (hjplus.2).symm
      · right
        have hneg : (primeBasisWheelLift S b j : ZMod q) =
            -(a : ZMod q) := hjminus.2
        calc
          (a : ZMod q) = -(-(a : ZMod q)) := by simp
          _ = -(primeBasisWheelLift S b j : ZMod q) := by rw [hneg]
    · have hpM : p ∣ finitePrimeBasisProduct S :=
        mem_dvd_finitePrimeBasisProduct hpS
      have hcast : (primeBasisWheelLift S b j : ZMod p) =
          (b : ZMod p) := by
        apply (ZMod.natCast_eq_natCast_iff _ _ p).mpr
        change (b + j * finitePrimeBasisProduct S) % p = b % p
        rw [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd hpM]
        simp
      rcases hprofileB p hpS with h | h
      · left
        exact h.trans hcast.symm
      · right
        rw [hcast]
        exact h
  refine mem_squareAnchorPhaseProjectionFiber.mpr ⟨?_, ?_⟩
  · exact mem_squareAnchorPhaseFiber.mpr
      ⟨hbound.2, primeSignProfile_implies_sameSquareAnchorPhase hS' hprofile⟩
  · change primeBasisWheelLift S b j % finitePrimeBasisProduct S = b
    simp [primeBasisWheelLift, Nat.add_mod, Nat.mul_mod_left,
      Nat.mod_eq_of_lt (mem_squareAnchorPhaseFiber.mp hb).1]

/-! ## Unique sign and deleted indices -/

/-- There is exactly one raw lift with fresh-prime residue `+a`. -/
theorem existsUnique_freshPrime_plus_phase_lift_index
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (_hSne : S.Nonempty)
    {q a b : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hq2 : q ≠ 2)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    (hb : b ∈ squareAnchorPhaseFiber S a) :
    ∃! j : ℕ, IsFreshPrimePlusLiftIndex S q a b j := by
  obtain ⟨x, hx, hxa⟩ :=
    exists_squareAnchorPhaseProjectionFiber_plus hS hq hqS hq2 hcop hb
  obtain ⟨j, hj, hrepr⟩ :=
    exists_raw_lift_index_of_phaseProjection_mem hS hq hqS hx
  refine ⟨j, ⟨hj, ?_⟩, ?_⟩
  · simpa [hrepr] using hxa
  · intro k hk
    have hxa' : (primeBasisWheelLift S b j : ZMod q) = (a : ZMod q) := by
      simpa [hrepr] using hxa
    have hres : (primeBasisWheelLift S b k : ZMod q) =
        (primeBasisWheelLift S b j : ZMod q) := hk.2.trans hxa'.symm
    exact same_residue_raw_lift_index_eq hS hq hqS hk.1 hj hres

/-- There is exactly one raw lift with fresh-prime residue `-a`. -/
theorem existsUnique_freshPrime_minus_phase_lift_index
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (_hSne : S.Nonempty)
    {q a b : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hq2 : q ≠ 2)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    (hb : b ∈ squareAnchorPhaseFiber S a) :
    ∃! j : ℕ, IsFreshPrimeMinusLiftIndex S q a b j := by
  obtain ⟨x, hx, hxa⟩ :=
    exists_squareAnchorPhaseProjectionFiber_minus hS hq hqS hq2 hcop hb
  obtain ⟨j, hj, hrepr⟩ :=
    exists_raw_lift_index_of_phaseProjection_mem hS hq hqS hx
  refine ⟨j, ⟨hj, ?_⟩, ?_⟩
  · simpa [hrepr] using hxa
  · intro k hk
    have hxa' : (primeBasisWheelLift S b j : ZMod q) = -(a : ZMod q) := by
      simpa [hrepr] using hxa
    have hres : (primeBasisWheelLift S b k : ZMod q) =
        (primeBasisWheelLift S b j : ZMod q) := hk.2.trans hxa'.symm
    exact same_residue_raw_lift_index_eq hS hq hqS hk.1 hj hres

/-- The unique deleted raw lift is inherited from the wheel deletion theorem. -/
theorem existsUnique_freshPrime_deleted_lift_index
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {q a b : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    (hb : b ∈ squareAnchorPhaseFiber S a) :
    ∃! j : ℕ, IsFreshPrimeDeletedLiftIndex S q b j := by
  have hsurv := squareAnchorPhaseFiber_mem_wheelSurvivor_of_coprime_anchor
    hS hSne (hcop.of_dvd_right (by
      rw [finitePrimeBasisProduct_insert hqS]
      exact dvd_mul_left _ _)) hb
  exact existsUnique_freshPrime_dvd_lift hS hq hqS hsurv

/-! ## The three distinguished indices -/

/-! The phase index set is exactly the pair supplied by the two sign witnesses. -/
/-- The phase index set is exactly the pair of sign-selected indices. -/
theorem freshPrimePhaseLiftIndices_eq_pair
    {S : Finset ℕ} {q a b jplus jminus : ℕ}
    (hplus : IsFreshPrimePlusLiftIndex S q a b jplus)
    (hminus : IsFreshPrimeMinusLiftIndex S q a b jminus)
    (hplus_unique : ∀ j, IsFreshPrimePlusLiftIndex S q a b j → j = jplus)
    (hminus_unique : ∀ j, IsFreshPrimeMinusLiftIndex S q a b j → j = jminus) :
    freshPrimePhaseLiftIndices S q a b = {jplus, jminus} := by
  ext j
  rw [mem_freshPrimePhaseLiftIndices_iff]
  constructor
  · intro h
    rcases h with hp | hm
    · exact Finset.mem_insert.mpr (Or.inl (hplus_unique j hp))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
        (hminus_unique j hm)))
  · intro h
    rcases Finset.mem_insert.mp h with h | h
    · subst j
      exact Or.inl hplus
    · have hjm : j = jminus := Finset.mem_singleton.mp h
      subst j
      exact Or.inr hminus

/-! The two phase indices are distinct for an odd fresh prime. -/
/-- The plus and minus phase indices are distinct for an odd fresh prime. -/
theorem freshPrime_phase_indices_ne
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a b : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hq2 : q ≠ 2)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    {jplus jminus : ℕ}
    (hplus : IsFreshPrimePlusLiftIndex S q a b jplus)
    (hminus : IsFreshPrimeMinusLiftIndex S q a b jminus) :
    jplus ≠ jminus := by
  have hS' : IsFinitePrimeBasis (insert q S) := by
    intro p hp
    simp only [Finset.mem_insert] at hp
    rcases hp with rfl | hpS
    · exact hq
    · exact hS p hpS
  have hsign := primeSign_plus_ne_minus_of_coprime_anchor
    hS' hcop (Finset.mem_insert_self q S) hq2
  intro heq
  apply hsign
  have hplus' : (primeBasisWheelLift S b jminus : ZMod q) = (a : ZMod q) := by
    simpa [heq] using hplus.2
  exact hplus'.symm.trans hminus.2

/-! The phase set has cardinality two. -/
/-- The phase index set has cardinality two. -/
theorem card_freshPrimePhaseLiftIndices_two
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a b : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hq2 : q ≠ 2)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    {jplus jminus : ℕ}
    (hplus : IsFreshPrimePlusLiftIndex S q a b jplus)
    (hminus : IsFreshPrimeMinusLiftIndex S q a b jminus)
    (hplus_unique : ∀ j, IsFreshPrimePlusLiftIndex S q a b j → j = jplus)
    (hminus_unique : ∀ j, IsFreshPrimeMinusLiftIndex S q a b j → j = jminus) :
    (freshPrimePhaseLiftIndices S q a b).card = 2 := by
  rw [freshPrimePhaseLiftIndices_eq_pair hplus hminus hplus_unique hminus_unique]
  simp [freshPrime_phase_indices_ne hS hq hqS hq2 hcop hplus hminus]

/-! A phase index is always one of the surviving lift indices. -/
/-- Every phase index is a surviving wheel index. -/
theorem freshPrimePhaseLiftIndices_subset_surviving
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (_hSne : S.Nonempty)
    {q a b : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    (_hb : b ∈ squareAnchorPhaseFiber S a) :
    freshPrimePhaseLiftIndices S q a b ⊆
      freshPrimeSurvivingLiftIndices S q b := by
  intro j hj
  have hphase := (mem_freshPrimePhaseLiftIndices_iff.mp hj)
  have hjlt : j < q := hphase.elim (fun hp => hp.1) (fun hm => hm.1)
  apply mem_freshPrimeSurvivingLiftIndices_iff.mpr
  refine ⟨hjlt, ?_⟩
  intro hdiv
  have hzero : (primeBasisWheelLift S b j : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  have hS' : IsFinitePrimeBasis (insert q S) := by
    intro p hp
    simp only [Finset.mem_insert] at hp
    rcases hp with rfl | hpS
    · exact hq
    · exact hS p hpS
  have ha0 : (a : ZMod q) ≠ 0 :=
    prime_anchor_cast_ne_zero hS' hcop (Finset.mem_insert_self q S)
  rcases hphase with hplus | hminus
  · exact ha0 (hplus.2.symm.trans hzero)
  · apply ha0
    calc
      (a : ZMod q) = -(-(a : ZMod q)) := by simp
      _ = -(primeBasisWheelLift S b j : ZMod q) := by rw [hminus.2]
      _ = 0 := by rw [hzero]; simp

/-! The deleted index cannot belong to either phase sheet. -/
/-- The unique deleted index is outside the phase index set. -/
theorem freshPrimeDeletedLiftIndex_not_mem_phase
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a b j : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    (hzero : IsFreshPrimeDeletedLiftIndex S q b j) :
    j ∉ freshPrimePhaseLiftIndices S q a b := by
  intro hphase
  have hcast : (primeBasisWheelLift S b j : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hzero.2
  have hS' : IsFinitePrimeBasis (insert q S) := by
    intro p hp
    simp only [Finset.mem_insert] at hp
    rcases hp with rfl | hpS
    · exact hq
    · exact hS p hpS
  have ha0 : (a : ZMod q) ≠ 0 :=
    prime_anchor_cast_ne_zero hS' hcop (Finset.mem_insert_self q S)
  rcases mem_freshPrimePhaseLiftIndices_iff.mp hphase with hplus | hminus
  · exact ha0 (hplus.2.symm.trans hcast)
  · apply ha0
    calc
      (a : ZMod q) = -(-(a : ZMod q)) := by simp
      _ = -(primeBasisWheelLift S b j : ZMod q) := by rw [hminus.2]
      _ = 0 := by rw [hcast]; simp

/-! The two sign indices and the deleted index are pairwise distinct. -/
/-- The plus, minus, and deleted indices are pairwise distinct. -/
theorem freshPrime_three_distinguished_lift_indices_pairwise
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a b : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hq2 : q ≠ 2)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    {jplus jminus jzero : ℕ}
    (hplus : IsFreshPrimePlusLiftIndex S q a b jplus)
    (hminus : IsFreshPrimeMinusLiftIndex S q a b jminus)
    (hzero : IsFreshPrimeDeletedLiftIndex S q b jzero) :
    jplus ≠ jminus ∧ jplus ≠ jzero ∧ jminus ≠ jzero := by
  have hpm := freshPrime_phase_indices_ne hS hq hqS hq2 hcop hplus hminus
  have hpz : jplus ≠ jzero := by
    intro heq
    have hzero' : (primeBasisWheelLift S b jplus : ZMod q) = 0 := by
      simpa [heq] using (ZMod.natCast_eq_zero_iff _ _).mpr hzero.2
    have hS' : IsFinitePrimeBasis (insert q S) := by
      intro p hp
      simp only [Finset.mem_insert] at hp
      rcases hp with rfl | hpS
      · exact hq
      · exact hS p hpS
    exact (prime_anchor_cast_ne_zero hS' hcop
      (Finset.mem_insert_self q S)) (hplus.2.symm.trans hzero')
  have hmz : jminus ≠ jzero := by
    intro heq
    have hzero' : (primeBasisWheelLift S b jminus : ZMod q) = 0 := by
      simpa [heq] using (ZMod.natCast_eq_zero_iff _ _).mpr hzero.2
    have hS' : IsFinitePrimeBasis (insert q S) := by
      intro p hp
      simp only [Finset.mem_insert] at hp
      rcases hp with rfl | hpS
      · exact hq
      · exact hS p hpS
    apply prime_anchor_cast_ne_zero hS' hcop (Finset.mem_insert_self q S)
    calc
      (a : ZMod q) = -(-(a : ZMod q)) := by simp
      _ = -(primeBasisWheelLift S b jminus : ZMod q) := by rw [hminus.2]
      _ = 0 := by rw [hzero']; simp
  exact ⟨hpm, hpz, hmz⟩

/-! The phase projection fiber is the image of its two raw phase indices. -/
/-- The L020 phase seats are the image of the two raw phase indices. -/
theorem squareAnchorPhaseProjectionFiber_eq_phaseLiftIndexImage
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {q a b : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hq2 : q ≠ 2)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    (hb : b ∈ squareAnchorPhaseFiber S a) :
    squareAnchorPhaseProjectionFiber S q a b =
      (freshPrimePhaseLiftIndices S q a b).image
        (fun j => primeBasisWheelLift S b j) := by
  classical
  have hS' : IsFinitePrimeBasis (insert q S) := by
    intro p hp
    simp only [Finset.mem_insert] at hp
    rcases hp with rfl | hpS
    · exact hq
    · exact hS p hpS
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj, hrepr⟩ :=
      exists_raw_lift_index_of_phaseProjection_mem hS hq hqS hx
    have hxphase := (mem_squareAnchorPhaseProjectionFiber.mp hx).1
    have hprofile := sameSquareAnchorPhase_implies_primeSignProfile hS'
      (mem_squareAnchorPhaseFiber.mp hxphase).2
    have hsign := hprofile q (Finset.mem_insert_self q S)
    have hpred : IsFreshPrimePlusLiftIndex S q a b j ∨
        IsFreshPrimeMinusLiftIndex S q a b j := by
      rcases hsign with hplus | hminus
      · left
        refine ⟨hj, ?_⟩
        simpa [hrepr] using hplus.symm
      · right
        refine ⟨hj, ?_⟩
        calc
          (primeBasisWheelLift S b j : ZMod q) =
              (x : ZMod q) := by
                simp [hrepr]
          _ = -(a : ZMod q) := by
            calc
              (x : ZMod q) = -(-((x : ZMod q))) := by simp
              _ = -(a : ZMod q) := by rw [hminus]
    apply Finset.mem_image.mpr
    exact ⟨j, mem_freshPrimePhaseLiftIndices_iff.mpr hpred, hrepr.symm⟩
  · intro hx
    obtain ⟨j, hj, hxeq⟩ := Finset.mem_image.mp hx
    have hmem := phase_projection_mem_of_raw_phase_index hS hSne hq hqS hcop hb
      (mem_freshPrimePhaseLiftIndices_iff.mp hj)
    simpa [hxeq] using hmem

/-! The neutral indices are the surviving indices outside the two phase sheets. -/
/-- The surviving non-phase indices have cardinality `q - 3`. -/
theorem card_freshPrimeNeutralLiftIndices
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {q a b : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hq2 : q ≠ 2)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    (hb : b ∈ squareAnchorPhaseFiber S a) :
    (freshPrimeNeutralLiftIndices S q a b).card = q - 3 := by
  obtain ⟨jplus, hplus, hplus_unique⟩ :=
    existsUnique_freshPrime_plus_phase_lift_index hS hSne hq hqS hq2 hcop hb
  obtain ⟨jminus, hminus, hminus_unique⟩ :=
    existsUnique_freshPrime_minus_phase_lift_index hS hSne hq hqS hq2 hcop hb
  have hphasecard := card_freshPrimePhaseLiftIndices_two hS hq hqS hq2 hcop
    hplus hminus hplus_unique hminus_unique
  have hsurv := squareAnchorPhaseFiber_mem_wheelSurvivor_of_coprime_anchor
    hS hSne (hcop.of_dvd_right (by
      rw [finitePrimeBasisProduct_insert hqS]
      exact dvd_mul_left _ _)) hb
  have hsub := freshPrimePhaseLiftIndices_subset_surviving hS hSne hq hqS hcop hb
  rw [freshPrimeNeutralLiftIndices, Finset.card_sdiff_of_subset hsub,
    card_freshPrimeSurvivingLiftIndices hS hq hqS hsurv, hphasecard]
  omega

/-! For `q = 3`, the neutral index set is empty. -/
/-- For fresh `q = 3`, there are no neutral surviving indices. -/
theorem freshPrimeNeutralLiftIndices_eq_empty_of_q_eq_three
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {a b : ℕ}
    (h3S : 3 ∉ S)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert 3 S)))
    (hb : b ∈ squareAnchorPhaseFiber S a) :
    freshPrimeNeutralLiftIndices S 3 a b = ∅ := by
  apply Finset.card_eq_zero.mp
  simpa using (card_freshPrimeNeutralLiftIndices hS hSne Nat.prime_three h3S
    (by norm_num) hcop hb)

/-! For every fresh prime above `3`, a neutral surviving index exists. -/
/-- A fresh prime above `3` leaves at least one neutral survivor. -/
theorem freshPrimeNeutralLiftIndices_nonempty_of_three_lt
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {q a b : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hq3 : 3 < q)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    (hb : b ∈ squareAnchorPhaseFiber S a) :
    (freshPrimeNeutralLiftIndices S q a b).Nonempty := by
  apply Finset.card_pos.mp
  rw [card_freshPrimeNeutralLiftIndices hS hSne hq hqS (by omega) hcop hb]
  omega

/-! Concrete `6 -> 30` regression for the five raw lifts `1,7,13,19,25`. -/
/-- The `6 -> 30` example records the concrete index trichotomy. -/
theorem freshPrimeLiftIndex_two_three_five_regression :
    primeBasisWheelLift ({2, 3} : Finset ℕ) 1 0 = 1 ∧
      primeBasisWheelLift ({2, 3} : Finset ℕ) 1 1 = 7 ∧
      primeBasisWheelLift ({2, 3} : Finset ℕ) 1 2 = 13 ∧
      primeBasisWheelLift ({2, 3} : Finset ℕ) 1 3 = 19 ∧
      primeBasisWheelLift ({2, 3} : Finset ℕ) 1 4 = 25 ∧
      IsFreshPrimePlusLiftIndex ({2, 3} : Finset ℕ) 5 1 1 0 ∧
      IsFreshPrimeMinusLiftIndex ({2, 3} : Finset ℕ) 5 1 1 3 ∧
      IsFreshPrimeDeletedLiftIndex ({2, 3} : Finset ℕ) 5 1 4 ∧
      freshPrimePhaseLiftIndices ({2, 3} : Finset ℕ) 5 1 1 = {0, 3} ∧
      freshPrimeSurvivingLiftIndices ({2, 3} : Finset ℕ) 5 1 = {0, 1, 2, 3} ∧
      freshPrimeNeutralLiftIndices ({2, 3} : Finset ℕ) 5 1 1 = {1, 2} := by
  have hM : finitePrimeBasisProduct ({2, 3} : Finset ℕ) = 6 := by
    norm_num [finitePrimeBasisProduct]
  have hphase : freshPrimePhaseLiftIndices ({2, 3} : Finset ℕ) 5 1 1 = {0, 3} := by
    ext x
    by_cases hx : x < 5
    · interval_cases x <;> norm_num [freshPrimePhaseLiftIndices,
        IsFreshPrimePlusLiftIndex, IsFreshPrimeMinusLiftIndex,
        primeBasisWheelLift, hM] <;> decide
    · simp [freshPrimePhaseLiftIndices, IsFreshPrimePlusLiftIndex,
        IsFreshPrimeMinusLiftIndex, primeBasisWheelLift, hM, hx]
      omega
  have hsurv : freshPrimeSurvivingLiftIndices ({2, 3} : Finset ℕ) 5 1 =
      {0, 1, 2, 3} := by
    ext x
    by_cases hx : x < 5
    · interval_cases x <;> norm_num [freshPrimeSurvivingLiftIndices,
        primeBasisWheelLift, hM]
    · simp [freshPrimeSurvivingLiftIndices, primeBasisWheelLift, hM, hx]
      omega
  have hneutral : freshPrimeNeutralLiftIndices ({2, 3} : Finset ℕ) 5 1 1 =
      {1, 2} := by
    rw [freshPrimeNeutralLiftIndices, hsurv, hphase]
    decide
  refine ⟨by norm_num [primeBasisWheelLift, hM],
    by norm_num [primeBasisWheelLift, hM],
    by norm_num [primeBasisWheelLift, hM],
    by norm_num [primeBasisWheelLift, hM],
    by norm_num [primeBasisWheelLift, hM], ?_, ?_, ?_, hphase, hsurv, hneutral⟩
  · refine ⟨by norm_num, ?_⟩
    exact (ZMod.natCast_eq_natCast_iff 1 1 5).mpr (by norm_num)
  · refine ⟨by norm_num, ?_⟩
    have h4 : ((4 : ℕ) : ZMod 5) = -((1 : ℕ) : ZMod 5) := by decide
    exact (ZMod.natCast_eq_natCast_iff 19 4 5).mpr (by norm_num) |>.trans h4
  · refine ⟨by norm_num, ?_⟩
    norm_num [primeBasisWheelLift, hM]

end DkMath.NumberTheory.PrimorialUniverse
