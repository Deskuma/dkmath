/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseFiber
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseFiberProjection"

/-!
# Fresh-prime projection of square-phase fibers

Adjoining a fresh prime gives a finite cover of the old square-phase fiber.
For an odd fresh prime, the cover has exactly two sheets, selected by the two
local signs modulo that prime.  The prime `2` is treated separately: it adds
no sign degree.

This is provider-side finite congruence geometry.  It does not compare this
two-sheet cover with wheel-survivor replication and does not provide an escape,
Legendre, PowerSwap, GN/CosmicFormula, PNT, or RH conclusion.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

/-! ## Projection and its fiber -/

/-! Reduction modulo the old product sends an enlarged phase fiber to the old one. -/
theorem enlargedPhaseFiber_projects_to_old
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a x : ℕ}
    (_hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hx : x ∈ squareAnchorPhaseFiber (insert q S) a) :
    primeBasisWheelProjection S x ∈ squareAnchorPhaseFiber S a := by
  have hM : finitePrimeBasisProduct S ≠ 0 :=
    finitePrimeBasisProduct_ne_zero hS
  have hx' := mem_squareAnchorPhaseFiber.mp hx
  have hphase : a ^ 2 % finitePrimeBasisProduct (insert q S) =
      x ^ 2 % finitePrimeBasisProduct (insert q S) := hx'.2
  have hdiv : finitePrimeBasisProduct S ∣
      finitePrimeBasisProduct (insert q S) := by
    rw [finitePrimeBasisProduct_insert hqS]
    exact dvd_mul_left _ _
  have hphaseOld := congrArg (fun n => n % finitePrimeBasisProduct S) hphase
  have hphaseOld' : a ^ 2 % finitePrimeBasisProduct S =
      (primeBasisWheelProjection S x) ^ 2 % finitePrimeBasisProduct S := by
    simpa [primeBasisWheelProjection, Nat.mod_mod_of_dvd _ hdiv,
      Nat.pow_mod] using hphaseOld
  refine mem_squareAnchorPhaseFiber.mpr ⟨?_, hphaseOld'⟩
  exact Nat.mod_lt x (Nat.pos_of_ne_zero hM)

/-! The enlarged phase-fiber representatives above one old representative. -/
noncomputable def squareAnchorPhaseProjectionFiber
    (S : Finset ℕ) (q a b : ℕ) : Finset ℕ := by
  classical
  exact (squareAnchorPhaseFiber (insert q S) a).filter
    (fun x => primeBasisWheelProjection S x = b)

@[simp] theorem mem_squareAnchorPhaseProjectionFiber
    {S : Finset ℕ} {q a b x : ℕ} :
    x ∈ squareAnchorPhaseProjectionFiber S q a b ↔
      x ∈ squareAnchorPhaseFiber (insert q S) a ∧
        primeBasisWheelProjection S x = b := by
  simp [squareAnchorPhaseProjectionFiber]

/-! ## CRT sign lifts -/

private theorem neg_residue_in_zmod_projection
    {p a : ℕ} (hp : Nat.Prime p) :
    ((p - a % p : ℕ) : ZMod p) = -(a : ZMod p) := by
  have hle : a % p ≤ p := le_of_lt (Nat.mod_lt a hp.pos)
  rw [Nat.cast_sub hle]
  have hzero : (p : ZMod p) = 0 := by
    exact (ZMod.natCast_eq_zero_iff p p).mpr dvd_rfl
  rw [hzero, zero_sub]
  simp

private theorem phaseFiber_insert_isFinitePrimeBasis
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) :
    IsFinitePrimeBasis (insert q S) := by
  intro p hp
  simp only [Finset.mem_insert] at hp
  rcases hp with rfl | hp
  · exact hq
  · exact hS p hp

private theorem phaseFiber_insert_lift_mem
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a b x : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hxlt : x < finitePrimeBasisProduct (insert q S))
    (hxb : x ≡ b [MOD finitePrimeBasisProduct S])
    (hxq : x ≡ a [MOD q] ∨
      x ≡ (q - a % q) [MOD q])
    (hb : b ∈ squareAnchorPhaseFiber S a) :
    x ∈ squareAnchorPhaseFiber (insert q S) a := by
  have hS' := phaseFiber_insert_isFinitePrimeBasis hS hq hqS
  have hb' := mem_squareAnchorPhaseFiber.mp hb
  have hprofileB : SameSquarePrimeSignProfile S a b :=
    (sameSquareAnchorPhase_iff_primeSignProfile hS).mp hb'.2
  have hprofile : SameSquarePrimeSignProfile (insert q S) a x := by
    intro p hp
    simp only [Finset.mem_insert] at hp
    rcases hp with hpq | hpS
    · rcases hxq with hxq | hxq
      · subst p
        left
        exact (ZMod.natCast_eq_natCast_iff x a q).mpr hxq |>.symm
      · subst p
        right
        have hcast : (x : ZMod q) = -(a : ZMod q) :=
          (ZMod.natCast_eq_natCast_iff x (q - a % q) q).mpr hxq |>.trans
            (neg_residue_in_zmod_projection hq)
        have hneg : -(x : ZMod q) = (a : ZMod q) := by
          rw [hcast]
          simp
        exact hneg.symm
    · have hpM : p ∣ finitePrimeBasisProduct S :=
        mem_dvd_finitePrimeBasisProduct hpS
      have hxp : (x : ZMod p) = (b : ZMod p) :=
        (ZMod.natCast_eq_natCast_iff x b p).mpr (hxb.of_dvd hpM)
      rcases hprofileB p hpS with h | h
      · left
        exact h.trans hxp.symm
      · right
        rw [hxp]
        exact h
  refine mem_squareAnchorPhaseFiber.mpr ⟨?_, ?_⟩
  · exact hxlt
  exact primeSignProfile_implies_sameSquareAnchorPhase hS' hprofile

private theorem phaseFiber_insert_crt_lift
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a b : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hb : b ∈ squareAnchorPhaseFiber S a)
    (hminus : Bool) :
    ∃ x, x ∈ squareAnchorPhaseProjectionFiber S q a b ∧
      (if hminus = true then
        (x : ZMod q) = (a : ZMod q)
      else
        (x : ZMod q) = -(a : ZMod q)) := by
  let c : ℕ := if hminus = true then a else q - a % q
  let x : ℕ := Nat.chineseRemainder
    (freshPrime_coprime_finitePrimeBasisProduct hS hq hqS) c b
  have hxq : x ≡ c [MOD q] :=
    (Nat.chineseRemainder (freshPrime_coprime_finitePrimeBasisProduct hS hq hqS)
      c b).property.1
  have hxb : x ≡ b [MOD finitePrimeBasisProduct S] :=
    (Nat.chineseRemainder (freshPrime_coprime_finitePrimeBasisProduct hS hq hqS)
      c b).property.2
  have hxmem : x ∈ squareAnchorPhaseFiber (insert q S) a := by
    refine phaseFiber_insert_lift_mem hS hq hqS (by
      rw [finitePrimeBasisProduct_insert hqS]
      exact Nat.chineseRemainder_lt_mul
        (freshPrime_coprime_finitePrimeBasisProduct hS hq hqS)
        c b hq.ne_zero (finitePrimeBasisProduct_ne_zero hS)) hxb ?_ hb
    by_cases hs : hminus = true
    · left
      simpa [x, c, hs] using hxq
    · right
      simpa [x, c, hs] using hxq
  have hxproj : primeBasisWheelProjection S x = b := by
    have hb' := mem_squareAnchorPhaseFiber.mp hb
    change x % finitePrimeBasisProduct S = b
    change x % finitePrimeBasisProduct S = b % finitePrimeBasisProduct S at hxb
    simpa [Nat.mod_eq_of_lt hb'.1] using hxb
  refine ⟨x, mem_squareAnchorPhaseProjectionFiber.mpr ⟨hxmem, hxproj⟩, ?_⟩
  · by_cases hs : hminus = true
    · have hxa : (x : ZMod q) = (a : ZMod q) := by
        apply (ZMod.natCast_eq_natCast_iff x a q).mpr
        simpa [c, hs] using hxq
      simpa [hs] using hxa
    · have hxc : (x : ZMod q) = ((q - a % q : ℕ) : ZMod q) := by
        apply (ZMod.natCast_eq_natCast_iff x (q - a % q) q).mpr
        simpa [c, hs] using hxq
      have hxa : (x : ZMod q) = -(a : ZMod q) :=
        hxc.trans (neg_residue_in_zmod_projection hq)
      simpa [hs] using hxa

/-! The semantic plus and minus lifts above an old fiber representative. -/
theorem exists_squareAnchorPhaseProjectionFiber_plus
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a b : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (_hq2 : q ≠ 2)
    (_hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    (hb : b ∈ squareAnchorPhaseFiber S a) :
    ∃ x, x ∈ squareAnchorPhaseProjectionFiber S q a b ∧
      (x : ZMod q) = (a : ZMod q) := by
  obtain ⟨x, hx, hplus⟩ :=
    phaseFiber_insert_crt_lift hS hq hqS hb true
  exact ⟨x, hx, hplus⟩

theorem exists_squareAnchorPhaseProjectionFiber_minus
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a b : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (_hq2 : q ≠ 2)
    (_hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    (hb : b ∈ squareAnchorPhaseFiber S a) :
    ∃ x, x ∈ squareAnchorPhaseProjectionFiber S q a b ∧
      (x : ZMod q) = -(a : ZMod q) := by
  obtain ⟨x, hx, hminus⟩ :=
    phaseFiber_insert_crt_lift hS hq hqS hb false
  exact ⟨x, hx, hminus⟩

/-! ## Exact local two-sheet structure -/

private theorem eq_of_fresh_crt_residues
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q x y : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hx : x < finitePrimeBasisProduct (insert q S))
    (hy : y < finitePrimeBasisProduct (insert q S))
    (hqx : x ≡ y [MOD q])
    (hMx : x ≡ y [MOD finitePrimeBasisProduct S]) :
    x = y := by
  have hmod : x ≡ y [MOD finitePrimeBasisProduct (insert q S)] := by
    rw [finitePrimeBasisProduct_insert hqS]
    exact (Nat.modEq_and_modEq_iff_modEq_mul
      (freshPrime_coprime_finitePrimeBasisProduct hS hq hqS)).mp ⟨hqx, hMx⟩
  change x % finitePrimeBasisProduct (insert q S) =
      y % finitePrimeBasisProduct (insert q S) at hmod
  calc
    x = x % finitePrimeBasisProduct (insert q S) := (Nat.mod_eq_of_lt hx).symm
    _ = y % finitePrimeBasisProduct (insert q S) := hmod
    _ = y := Nat.mod_eq_of_lt hy

theorem squareAnchorPhaseProjectionFiber_eq_two_sheet
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a b : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hq2 : q ≠ 2)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    (hb : b ∈ squareAnchorPhaseFiber S a) :
    ∃ xplus xminus,
      xplus ∈ squareAnchorPhaseProjectionFiber S q a b ∧
      xminus ∈ squareAnchorPhaseProjectionFiber S q a b ∧
      (xplus : ZMod q) = (a : ZMod q) ∧
      (xminus : ZMod q) = -(a : ZMod q) ∧
      xplus ≠ xminus ∧
      squareAnchorPhaseProjectionFiber S q a b = {xplus, xminus} := by
  obtain ⟨xplus, hxp, hxpq⟩ :=
    exists_squareAnchorPhaseProjectionFiber_plus hS hq hqS hq2 hcop hb
  obtain ⟨xminus, hxm, hxmq⟩ :=
    exists_squareAnchorPhaseProjectionFiber_minus hS hq hqS hq2 hcop hb
  have hne : xplus ≠ xminus := by
    intro heq
    have : (a : ZMod q) = -(a : ZMod q) := hxpq.symm.trans (heq ▸ hxmq)
    exact primeSign_plus_ne_minus_of_coprime_anchor
      (S := insert q S) (a := a)
      (phaseFiber_insert_isFinitePrimeBasis hS hq hqS) hcop
      (p := q) (Finset.mem_insert_self q S) hq2 this
  have hset : squareAnchorPhaseProjectionFiber S q a b = {xplus, xminus} := by
    ext x
    constructor
    · intro hx
      have hx' := mem_squareAnchorPhaseProjectionFiber.mp hx
      have hxFiber := mem_squareAnchorPhaseFiber.mp hx'.1
      have hphase := hxFiber.2
      have hsign := sameSquareAnchorPhase_implies_primeSign
        (phaseFiber_insert_isFinitePrimeBasis hS hq hqS) hphase
          (Finset.mem_insert_self q S)
      have hMx : x ≡ b [MOD finitePrimeBasisProduct S] := by
        change x % finitePrimeBasisProduct S = b % finitePrimeBasisProduct S
        simpa [primeBasisWheelProjection,
          Nat.mod_eq_of_lt (mem_squareAnchorPhaseFiber.mp hb).1]
          using hx'.2
      rcases hsign with h | h
      · have hxp' := mem_squareAnchorPhaseProjectionFiber.mp hxp
        have hxpFiber := mem_squareAnchorPhaseFiber.mp hxp'.1
        have hMxPlus : xplus ≡ b [MOD finitePrimeBasisProduct S] := by
          change xplus % finitePrimeBasisProduct S = b % finitePrimeBasisProduct S
          simpa [primeBasisWheelProjection,
            Nat.mod_eq_of_lt (mem_squareAnchorPhaseFiber.mp hb).1]
            using hxp'.2
        have heq : x = xplus := eq_of_fresh_crt_residues hS hq hqS hxFiber.1
          hxpFiber.1
          (by
            apply (ZMod.natCast_eq_natCast_iff x xplus q).mp
            exact h.symm.trans hxpq.symm)
          (hMx.trans hMxPlus.symm)
        exact Finset.mem_insert.mpr (Or.inl heq)
      · have hxm' := mem_squareAnchorPhaseProjectionFiber.mp hxm
        have hxmFiber := mem_squareAnchorPhaseFiber.mp hxm'.1
        have hMxMinus : xminus ≡ b [MOD finitePrimeBasisProduct S] := by
          change xminus % finitePrimeBasisProduct S = b % finitePrimeBasisProduct S
          simpa [primeBasisWheelProjection,
            Nat.mod_eq_of_lt (mem_squareAnchorPhaseFiber.mp hb).1]
            using hxm'.2
        have heq : x = xminus := eq_of_fresh_crt_residues hS hq hqS hxFiber.1
          hxmFiber.1
          (by
            apply (ZMod.natCast_eq_natCast_iff x xminus q).mp
            have hxneg : (x : ZMod q) = -(a : ZMod q) := by
              rw [h]
              simp
            exact hxneg.trans hxmq.symm)
          (hMx.trans hMxMinus.symm)
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr heq))
    · intro hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hxp
      · exact hxm
  exact ⟨xplus, xminus, hxp, hxm, hxpq, hxmq, hne, hset⟩

/-! Every fresh odd-prime projection fiber has exactly two elements. -/
theorem card_squareAnchorPhaseProjectionFiber_fresh_odd
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a b : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hq2 : q ≠ 2)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    (hb : b ∈ squareAnchorPhaseFiber S a) :
    (squareAnchorPhaseProjectionFiber S q a b).card = 2 := by
  obtain ⟨xplus, xminus, _, _, _, _, hne, hset⟩ :=
    squareAnchorPhaseProjectionFiber_eq_two_sheet hS hq hqS hq2 hcop hb
  rw [hset, Finset.card_pair hne]

/-! Projection from the enlarged fiber is surjective for a fresh odd prime. -/
theorem squareAnchorPhaseFiber_projection_surjective_fresh_odd
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hq2 : q ≠ 2)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S))) :
    ∀ b, b ∈ squareAnchorPhaseFiber S a →
      ∃ x, x ∈ squareAnchorPhaseFiber (insert q S) a ∧
        primeBasisWheelProjection S x = b := by
  intro b hb
  have hcard := card_squareAnchorPhaseProjectionFiber_fresh_odd
    hS hq hqS hq2 hcop hb
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega :
      0 < (squareAnchorPhaseProjectionFiber S q a b).card)
  exact ⟨x, (mem_squareAnchorPhaseProjectionFiber.mp hx).1,
    (mem_squareAnchorPhaseProjectionFiber.mp hx).2⟩

/-! ## Global growth laws -/

/-! A fresh odd prime doubles the one-period coprime phase-fiber cardinality. -/
theorem squareAnchorPhaseFiber_card_insert_fresh_odd
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hq2 : q ≠ 2)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S))) :
    (squareAnchorPhaseFiber (insert q S) a).card =
      2 * (squareAnchorPhaseFiber S a).card := by
  have hS' := phaseFiber_insert_isFinitePrimeBasis hS hq hqS
  rw [squareAnchorPhaseFiber_card_of_coprime_anchor hS' hcop,
    squareAnchorPhaseFiber_card_of_coprime_anchor hS
      (hcop.of_dvd_right (by
        rw [finitePrimeBasisProduct_insert hqS]
        exact dvd_mul_left _ _))]
  have hqOdd : q ∉ S.erase 2 := by
    intro hqOdd
    exact hqS (Finset.mem_erase.mp hqOdd).2
  rw [Finset.erase_insert_of_ne hq2,
    Finset.card_insert_of_notMem hqOdd]
  simp [Nat.pow_succ, Nat.mul_comm]

/-! Fresh `2` adds no sign degree to the phase-fiber cardinality. -/
theorem squareAnchorPhaseFiber_card_insert_two
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {a : ℕ}
    (h2S : 2 ∉ S)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert 2 S))) :
    (squareAnchorPhaseFiber (insert 2 S) a).card =
      (squareAnchorPhaseFiber S a).card := by
  have hS' := phaseFiber_insert_isFinitePrimeBasis hS Nat.prime_two h2S
  rw [squareAnchorPhaseFiber_card_of_coprime_anchor hS' hcop,
    squareAnchorPhaseFiber_card_of_coprime_anchor hS
      (hcop.of_dvd_right (by
        rw [finitePrimeBasisProduct_insert h2S]
        exact dvd_mul_left _ _))]
  rw [Finset.erase_insert h2S, Finset.erase_eq_of_notMem h2S]

/-! ## Visible `6 -> 30` regression -/

private theorem isFinitePrimeBasis_two_three_projection :
    IsFinitePrimeBasis ({2, 3} : Finset ℕ) := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl <;> norm_num

/-! In the `6 -> 30` tower, both old phase representatives have two lifts. -/
theorem squareAnchorPhaseProjectionFiber_two_three_five_regression :
    (squareAnchorPhaseProjectionFiber ({2, 3} : Finset ℕ) 5 1 1).card = 2 ∧
      (squareAnchorPhaseProjectionFiber ({2, 3} : Finset ℕ) 5 1 5).card = 2 ∧
      1 ∈ squareAnchorPhaseProjectionFiber ({2, 3} : Finset ℕ) 5 1 1 ∧
      19 ∈ squareAnchorPhaseProjectionFiber ({2, 3} : Finset ℕ) 5 1 1 ∧
      11 ∈ squareAnchorPhaseProjectionFiber ({2, 3} : Finset ℕ) 5 1 5 ∧
      29 ∈ squareAnchorPhaseProjectionFiber ({2, 3} : Finset ℕ) 5 1 5 := by
  have hS := isFinitePrimeBasis_two_three_projection
  have hcop : Nat.Coprime 1 (finitePrimeBasisProduct
      (insert 5 ({2, 3} : Finset ℕ))) := by simp
  have hb1 : 1 ∈ squareAnchorPhaseFiber ({2, 3} : Finset ℕ) 1 := by
    apply mem_squareAnchorPhaseFiber.mpr
    constructor
    · norm_num [finitePrimeBasisProduct]
    · change 1 ^ 2 % finitePrimeBasisProduct ({2, 3} : Finset ℕ) =
        1 ^ 2 % finitePrimeBasisProduct ({2, 3} : Finset ℕ)
      rfl
  have hb5 : 5 ∈ squareAnchorPhaseFiber ({2, 3} : Finset ℕ) 1 := by
    apply mem_squareAnchorPhaseFiber.mpr
    constructor
    · norm_num [finitePrimeBasisProduct]
    · change 1 ^ 2 % finitePrimeBasisProduct ({2, 3} : Finset ℕ) =
        5 ^ 2 % finitePrimeBasisProduct ({2, 3} : Finset ℕ)
      norm_num [finitePrimeBasisProduct]
  have hcard1 := card_squareAnchorPhaseProjectionFiber_fresh_odd hS (q := 5)
      (a := 1) (b := 1) (by norm_num) (by simp) (by norm_num) hcop hb1
  have hcard5 := card_squareAnchorPhaseProjectionFiber_fresh_odd hS (q := 5)
      (a := 1) (b := 5) (by norm_num) (by simp) (by norm_num) hcop hb5
  refine ⟨hcard1, hcard5, ?_, ?_, ?_, ?_⟩
  all_goals
    norm_num [squareAnchorPhaseProjectionFiber, squareAnchorPhaseFiber,
      squareAnchorWheelProjection, primeBasisWheelProjection,
      SameSquareAnchorPhase, finitePrimeBasisProduct]

end DkMath.NumberTheory.PrimorialUniverse
