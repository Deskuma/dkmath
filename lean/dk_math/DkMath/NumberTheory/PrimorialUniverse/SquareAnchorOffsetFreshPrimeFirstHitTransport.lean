/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOffsetSuccessorPairAudit
import Mathlib.Tactic

/-!
# Fresh-prime transport of positive first hits

This provider-side module studies one fresh-prime basis extension.  An old
positive first-hit seat persists precisely when the new prime does not divide
the corresponding raw square-shell point; otherwise the first hit is delayed
strictly.  The result is finite reservation geometry only, with no shell-width,
primality, Jacobsthal, Legendre, or analytic conclusion.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

/-! ## Reservation classification under insertion -/

/-- Inserting a fresh prime adds exactly one reservation channel. -/
theorem reservedByPrimeBasis_insert_fresh_iff
    {S : Finset ℕ} {q x : ℕ} (hqS : q ∉ S) :
    ReservedByPrimeBasis (insert q S) x ↔
      ReservedByPrimeBasis S x ∨ q ∣ x := by
  unfold ReservedByPrimeBasis
  constructor
  · rintro ⟨p, hp, hpx⟩
    simp only [Finset.mem_insert] at hp
    rcases hp with rfl | hpS
    · exact Or.inr hpx
    · exact Or.inl ⟨p, hpS, hpx⟩
  · rintro (hSx | hqx)
    · obtain ⟨p, hpS, hpx⟩ := hSx
      exact ⟨p, Finset.mem_insert_of_mem hpS, hpx⟩
    · exact ⟨q, Finset.mem_insert_self q S, hqx⟩

/-- Reservation is monotone when a fresh prime is inserted. -/
theorem reservedByPrimeBasis_mono_insert
    {S : Finset ℕ} {q x : ℕ} (hqS : q ∉ S)
    (hx : ReservedByPrimeBasis S x) :
    ReservedByPrimeBasis (insert q S) x := by
  exact (reservedByPrimeBasis_insert_fresh_iff hqS).mpr (Or.inl hx)

/-- At an old-unreserved point, insertion changes reservation exactly when
the fresh prime divides that point. -/
theorem not_reserved_insert_fresh_iff_of_not_reserved_old
    {S : Finset ℕ} {q x : ℕ} (hqS : q ∉ S)
    (hx : ¬ ReservedByPrimeBasis S x) :
    (¬ ReservedByPrimeBasis (insert q S) x) ↔ ¬ q ∣ x := by
  constructor
  · intro hnew hqdiv
    apply hnew
    exact (reservedByPrimeBasis_insert_fresh_iff hqS).mpr (Or.inr hqdiv)
  · intro hqnot hnew
    rcases (reservedByPrimeBasis_insert_fresh_iff hqS).mp hnew with hold | hqdiv
    · exact hx hold
    · exact hqnot hqdiv

/-- Adjoining a fresh prime preserves the finite-prime-basis property. -/
theorem isFinitePrimeBasis_insert_fresh
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) :
    IsFinitePrimeBasis (insert q S) := by
  intro p hp
  simp only [Finset.mem_insert] at hp
  rcases hp with rfl | hpS
  · exact hq
  · exact hS p hpS

/-! ## Raw-seat and first-hit transport helpers -/

private theorem squareAnchorFirstPositiveUnreservedOffset_le_of_not_reserved
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n t : ℕ) (htpos : 0 < t)
    (htperiod : t ≤ finitePrimeBasisProduct S)
    (ht : ¬ ReservedByPrimeBasis S (n ^ 2 + t)) :
    squareAnchorFirstPositiveUnreservedOffset S n hS hSne ≤ t := by
  rw [squareAnchorFirstPositiveUnreservedOffset_eq_generic hS hSne n]
  apply Finset.min'_le
    (genericPositiveUnreservedOffsetProfile S
      (squareAnchorWheelProjection S n)) t
  rw [mem_genericPositiveUnreservedOffsetProfile_iff]
  refine ⟨htpos, htperiod, ?_⟩
  have hsurv := (squareShell_not_reserved_iff_projection_survivor
    hS hSne n t).mp ht
  rw [squareShellWheelProjection_eq_anchor_add hS n t] at hsurv
  exact hsurv

private theorem squareAnchorFirstPositiveUnreservedOffset_eq_of_profile_min
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n k : ℕ)
    (hk : k ∈ genericPositiveUnreservedOffsetProfile S
      (squareAnchorWheelProjection S n))
    (hmin : ∀ t, t ∈ genericPositiveUnreservedOffsetProfile S
      (squareAnchorWheelProjection S n) → k ≤ t) :
    squareAnchorFirstPositiveUnreservedOffset S n hS hSne = k := by
  rw [squareAnchorFirstPositiveUnreservedOffset_eq_generic hS hSne n]
  apply le_antisymm
  · exact Finset.min'_le _ k hk
  · exact Finset.le_min' _
      (genericPositiveUnreservedOffsetProfile_nonempty hS hSne
        (squareAnchorWheelProjection S n)) k hmin

private theorem squareAnchorFirstPositiveUnreservedOffset_le_of_profile_mem
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n k : ℕ)
    (hk : k ∈ genericPositiveUnreservedOffsetProfile S
      (squareAnchorWheelProjection S n)) :
    squareAnchorFirstPositiveUnreservedOffset S n hS hSne ≤ k := by
  rw [squareAnchorFirstPositiveUnreservedOffset_eq_generic hS hSne n]
  have hle := Finset.min'_le
    (genericPositiveUnreservedOffsetProfile S
      (squareAnchorWheelProjection S n)) k hk
  simpa [genericFirstPositiveUnreservedOffset] using hle

private theorem squareAnchorFirstPositiveUnreservedOffset_not_reserved
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n : ℕ) :
    ¬ ReservedByPrimeBasis S
      (n ^ 2 + squareAnchorFirstPositiveUnreservedOffset S n hS hSne) := by
  apply (squareShell_not_reserved_iff_projection_survivor hS hSne n _).mpr
  rw [squareShellWheelProjection_eq_anchor_add hS n]
  exact squareAnchorFirstPositiveUnreservedOffset_survivor hS hSne n

/-! ## Single-anchor basis growth -/

/-- A fresh insertion cannot move a positive first hit backwards. -/
theorem squareAnchorFirstPositiveUnreservedOffset_le_insert_fresh
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n : ℕ) :
    squareAnchorFirstPositiveUnreservedOffset S n hS hSne ≤
      squareAnchorFirstPositiveUnreservedOffset (insert q S) n
        (isFinitePrimeBasis_insert_fresh hS hq hqS)
        (by simp) := by
  let hS' := isFinitePrimeBasis_insert_fresh hS hq hqS
  let hSne' : (insert q S).Nonempty := by simp
  let t := squareAnchorFirstPositiveUnreservedOffset (insert q S) n hS' hSne'
  have hnewnot : ¬ ReservedByPrimeBasis (insert q S) (n ^ 2 + t) := by
    apply (squareShell_not_reserved_iff_projection_survivor hS' hSne' n t).mpr
    rw [squareShellWheelProjection_eq_anchor_add hS' n t]
    exact squareAnchorFirstPositiveUnreservedOffset_survivor hS' hSne' n
  have holdnot : ¬ ReservedByPrimeBasis S (n ^ 2 + t) := by
    intro hold
    exact hnewnot (reservedByPrimeBasis_mono_insert hqS hold)
  have hnewpos : 0 < t :=
    squareAnchorFirstPositiveUnreservedOffset_pos hS' hSne' n
  by_contra hnot
  have hlt : t < squareAnchorFirstPositiveUnreservedOffset S n hS hSne :=
    Nat.lt_of_not_ge hnot
  have holdmin := squareAnchorFirstPositiveUnreservedOffset_minimal
    hS hSne n t hnewpos hlt
  have holdsurv := (squareShell_not_reserved_iff_projection_survivor
    hS hSne n t).mp holdnot
  rw [squareShellWheelProjection_eq_anchor_add hS n t] at holdsurv
  exact holdmin holdsurv

/-- The old positive first hit persists exactly when the fresh prime does not
delete its raw seat. -/
theorem squareAnchorFirstPositiveUnreservedOffset_insert_fresh_eq_iff
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n : ℕ) :
    squareAnchorFirstPositiveUnreservedOffset (insert q S) n
        (isFinitePrimeBasis_insert_fresh hS hq hqS) (by simp) =
      squareAnchorFirstPositiveUnreservedOffset S n hS hSne ↔
    ¬ q ∣ (n ^ 2 + squareAnchorFirstPositiveUnreservedOffset S n hS hSne) := by
  let hS' := isFinitePrimeBasis_insert_fresh hS hq hqS
  let hSne' : (insert q S).Nonempty := by simp
  let H := squareAnchorFirstPositiveUnreservedOffset S n hS hSne
  let H' := squareAnchorFirstPositiveUnreservedOffset (insert q S) n hS' hSne'
  have holdnot : ¬ ReservedByPrimeBasis S (n ^ 2 + H) :=
    squareAnchorFirstPositiveUnreservedOffset_not_reserved hS hSne n
  constructor
  · intro heq
    have hnewnot : ¬ ReservedByPrimeBasis (insert q S) (n ^ 2 + H) := by
      have h := squareAnchorFirstPositiveUnreservedOffset_not_reserved hS' hSne' n
      simpa [H, H', heq] using h
    exact (not_reserved_insert_fresh_iff_of_not_reserved_old hqS holdnot).mp hnewnot
  · intro hqnot
    have hnewnot : ¬ ReservedByPrimeBasis (insert q S) (n ^ 2 + H) :=
      (not_reserved_insert_fresh_iff_of_not_reserved_old hqS holdnot).mpr hqnot
    have hMle : finitePrimeBasisProduct S ≤
        finitePrimeBasisProduct (insert q S) := by
      rw [finitePrimeBasisProduct_insert hqS]
      exact Nat.le_mul_of_pos_left _ hq.pos
    have hHle := squareAnchorFirstPositiveUnreservedOffset_le_period hS hSne n
    have hnewle : H' ≤ H := by
      apply squareAnchorFirstPositiveUnreservedOffset_le_of_not_reserved
        hS' hSne' n H
      · exact squareAnchorFirstPositiveUnreservedOffset_pos hS hSne n
      · exact hHle.trans hMle
      · exact hnewnot
    have hmono := squareAnchorFirstPositiveUnreservedOffset_le_insert_fresh
      hS hSne hq hqS n
    exact le_antisymm hnewle hmono

/-- If the fresh prime deletes the old first-hit seat, the new first hit is
strictly later. -/
theorem squareAnchorFirstPositiveUnreservedOffset_insert_fresh_lt_of_dvd
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n : ℕ)
    (hqdiv : q ∣ n ^ 2 + squareAnchorFirstPositiveUnreservedOffset S n hS hSne) :
    squareAnchorFirstPositiveUnreservedOffset S n hS hSne <
      squareAnchorFirstPositiveUnreservedOffset (insert q S) n
        (isFinitePrimeBasis_insert_fresh hS hq hqS) (by simp) := by
  have hmono := squareAnchorFirstPositiveUnreservedOffset_le_insert_fresh
    hS hSne hq hqS n
  have hneq : ¬ squareAnchorFirstPositiveUnreservedOffset (insert q S) n
        (isFinitePrimeBasis_insert_fresh hS hq hqS) (by simp) =
      squareAnchorFirstPositiveUnreservedOffset S n hS hSne := by
    intro heq
    exact (squareAnchorFirstPositiveUnreservedOffset_insert_fresh_eq_iff
      hS hSne hq hqS n).mp heq hqdiv
  have hneq' : ¬ squareAnchorFirstPositiveUnreservedOffset S n hS hSne =
      squareAnchorFirstPositiveUnreservedOffset (insert q S) n
        (isFinitePrimeBasis_insert_fresh hS hq hqS) (by simp) := by
    intro heq
    exact hneq heq.symm
  exact lt_of_le_of_ne hmono hneq'

/-- The strict first-hit delay is equivalent to deletion by the fresh prime. -/
theorem squareAnchorFirstPositiveUnreservedOffset_insert_fresh_lt_iff
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n : ℕ) :
    squareAnchorFirstPositiveUnreservedOffset S n hS hSne <
      squareAnchorFirstPositiveUnreservedOffset (insert q S) n
        (isFinitePrimeBasis_insert_fresh hS hq hqS) (by simp) ↔
    q ∣ n ^ 2 + squareAnchorFirstPositiveUnreservedOffset S n hS hSne := by
  constructor
  · intro hlt
    by_contra hnot
    have heq := (squareAnchorFirstPositiveUnreservedOffset_insert_fresh_eq_iff
      hS hSne hq hqS n).mpr hnot
    omega
  · exact squareAnchorFirstPositiveUnreservedOffset_insert_fresh_lt_of_dvd
      hS hSne hq hqS n

/-! ## Successor-pair basis growth -/

/-- A fresh insertion cannot move an adjacent-pair first hit backwards. -/
theorem squareAnchorSuccessorPairPositiveFirstHit_le_insert_fresh
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n : ℕ) :
    squareAnchorSuccessorPairPositiveFirstHit S n hS hSne ≤
      squareAnchorSuccessorPairPositiveFirstHit (insert q S) n
        (isFinitePrimeBasis_insert_fresh hS hq hqS) (by simp) := by
  unfold squareAnchorSuccessorPairPositiveFirstHit
  exact min_le_min
    (squareAnchorFirstPositiveUnreservedOffset_le_insert_fresh
      hS hSne hq hqS n)
    (squareAnchorFirstPositiveUnreservedOffset_le_insert_fresh
      hS hSne hq hqS (n + 1))

/-- The finite successor-pair radius is monotone under a fresh basis
insertion, despite the enlarged period. -/
theorem squareSuccessorPairPositiveFirstHitRadius_le_insert_fresh
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) :
    squareSuccessorPairPositiveFirstHitRadius S hS hSne ≤
      squareSuccessorPairPositiveFirstHitRadius (insert q S)
        (isFinitePrimeBasis_insert_fresh hS hq hqS) (by simp) := by
  let hS' := isFinitePrimeBasis_insert_fresh hS hq hqS
  let hSne' : (insert q S).Nonempty := by simp
  unfold squareSuccessorPairPositiveFirstHitRadius
  apply Finset.sup_le
  intro n hn
  have hMle : finitePrimeBasisProduct S ≤
      finitePrimeBasisProduct (insert q S) := by
    rw [finitePrimeBasisProduct_insert hqS]
    exact Nat.le_mul_of_pos_left _ hq.pos
  have hnnew : n < finitePrimeBasisProduct (insert q S) :=
    (Finset.mem_range.mp hn).trans_le hMle
  exact (squareAnchorSuccessorPairPositiveFirstHit_le_insert_fresh
    hS hSne hq hqS n).trans
    (Finset.le_sup (s := Finset.range (finitePrimeBasisProduct (insert q S)))
      (f := fun m => squareAnchorSuccessorPairPositiveFirstHit
        (insert q S) m hS' hSne') (Finset.mem_range.mpr hnnew))

/-! ## Required `30 → 210` regressions -/

private theorem isFinitePrimeBasis_two_three_five_freshTransport :
    IsFinitePrimeBasis ({2, 3, 5} : Finset ℕ) := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl <;> norm_num

private theorem isFinitePrimeBasis_two_three_five_seven_freshTransport :
    IsFinitePrimeBasis (insert 7 ({2, 3, 5} : Finset ℕ)) := by
  have hS : IsFinitePrimeBasis ({2, 3, 5} : Finset ℕ) :=
    isFinitePrimeBasis_two_three_five_freshTransport
  exact isFinitePrimeBasis_insert_fresh hS Nat.prime_seven (by simp)

private theorem squareAnchorFirstPositiveUnreservedOffset_eq_of_profile_min_regression
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n k : ℕ)
    (hk : k ∈ genericPositiveUnreservedOffsetProfile S
      (squareAnchorWheelProjection S n))
    (hmin : ∀ t, t ∈ genericPositiveUnreservedOffsetProfile S
      (squareAnchorWheelProjection S n) → k ≤ t) :
    squareAnchorFirstPositiveUnreservedOffset S n hS hSne = k := by
  exact squareAnchorFirstPositiveUnreservedOffset_eq_of_profile_min
    hS hSne n k hk hmin

set_option maxHeartbeats 2000000 in
-- The 210-element finite regression is intentionally checked by the public
-- profile-membership API rather than by an opaque numerical shortcut.
/-- The `30 → 210` transport regression proves deletion at `n=1`, persistence
at `n=11`, and the pair-radius increase `5 → 7`. -/
theorem squareAnchorOffsetFreshPrimeFirstHit_two_three_five_seven_regression :
    squareAnchorFirstPositiveUnreservedOffset ({2, 3, 5} : Finset ℕ) 1
        isFinitePrimeBasis_two_three_five_freshTransport (by simp) = 6 ∧
      squareAnchorFirstPositiveUnreservedOffset (insert 7 ({2, 3, 5} : Finset ℕ)) 1
        isFinitePrimeBasis_two_three_five_seven_freshTransport (by simp) = 10 ∧
      squareAnchorFirstPositiveUnreservedOffset ({2, 3, 5} : Finset ℕ) 11
        isFinitePrimeBasis_two_three_five_freshTransport (by simp) = 6 ∧
      squareAnchorFirstPositiveUnreservedOffset (insert 7 ({2, 3, 5} : Finset ℕ)) 11
        isFinitePrimeBasis_two_three_five_seven_freshTransport (by simp) = 6 ∧
      squareSuccessorPairPositiveFirstHitRadius ({2, 3, 5} : Finset ℕ)
        isFinitePrimeBasis_two_three_five_freshTransport (by simp) = 5 ∧
      squareSuccessorPairPositiveFirstHitRadius
        (insert 7 ({2, 3, 5} : Finset ℕ))
        isFinitePrimeBasis_two_three_five_seven_freshTransport (by simp) = 7 ∧
      squareAnchorFirstPositiveUnreservedOffset (insert 7 ({2, 3, 5} : Finset ℕ)) 2
        isFinitePrimeBasis_two_three_five_seven_freshTransport (by simp) = 7 ∧
      squareAnchorWheelProjection ({2, 3, 5} : Finset ℕ) 11 = 1 ∧
      squareAnchorWheelProjection ({2, 3, 5} : Finset ℕ) 12 = 24 := by
  have hS : IsFinitePrimeBasis ({2, 3, 5} : Finset ℕ) :=
    isFinitePrimeBasis_two_three_five_freshTransport
  have hSne : ({2, 3, 5} : Finset ℕ).Nonempty := by simp
  have hS' : IsFinitePrimeBasis (insert 7 ({2, 3, 5} : Finset ℕ)) :=
    isFinitePrimeBasis_two_three_five_seven_freshTransport
  have hSne' : (insert 7 ({2, 3, 5} : Finset ℕ)).Nonempty := by simp
  have h30_1 : squareAnchorFirstPositiveUnreservedOffset
      ({2, 3, 5} : Finset ℕ) 1 hS hSne = 6 := by
    apply squareAnchorFirstPositiveUnreservedOffset_eq_of_profile_min_regression
      hS hSne 1 6
    · rw [mem_genericPositiveUnreservedOffsetProfile_iff]
      norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
        finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor, ReservedByPrimeBasis]
    · intro t ht
      by_contra hnot
      have hlt : t < 6 := Nat.lt_of_not_ge hnot
      interval_cases t <;>
        norm_num [mem_genericPositiveUnreservedOffsetProfile_iff,
          squareAnchorWheelProjection, primeBasisWheelProjection,
          finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
          ReservedByPrimeBasis] at ht
  have h210_1 : squareAnchorFirstPositiveUnreservedOffset
      (insert 7 ({2, 3, 5} : Finset ℕ)) 1 hS' hSne' = 10 := by
    apply squareAnchorFirstPositiveUnreservedOffset_eq_of_profile_min_regression
      hS' hSne' 1 10
    · rw [mem_genericPositiveUnreservedOffsetProfile_iff]
      norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
        finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor, ReservedByPrimeBasis]
    · intro t ht
      by_contra hnot
      have hlt : t < 10 := Nat.lt_of_not_ge hnot
      interval_cases t <;>
        norm_num [mem_genericPositiveUnreservedOffsetProfile_iff,
          squareAnchorWheelProjection, primeBasisWheelProjection,
          finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
          ReservedByPrimeBasis] at ht
  have h30_11 : squareAnchorFirstPositiveUnreservedOffset
      ({2, 3, 5} : Finset ℕ) 11 hS hSne = 6 := by
    have hphase : SameSquareAnchorPhase ({2, 3, 5} : Finset ℕ) 11 1 := by
      norm_num [SameSquareAnchorPhase, squareAnchorWheelProjection,
        primeBasisWheelProjection, finitePrimeBasisProduct]
    rw [squareAnchorFirstPositiveUnreservedOffset_eq_of_samePhase hS hphase hSne]
    exact h30_1
  have h210_11 : squareAnchorFirstPositiveUnreservedOffset
      (insert 7 ({2, 3, 5} : Finset ℕ)) 11 hS' hSne' = 6 := by
    have hpersist := squareAnchorFirstPositiveUnreservedOffset_insert_fresh_eq_iff
      hS hSne Nat.prime_seven (by simp) 11
    have heq := hpersist.mpr (by
      rw [h30_11]
      norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
        finitePrimeBasisProduct])
    simpa [h30_11] using heq
  have h210_2 : squareAnchorFirstPositiveUnreservedOffset
      (insert 7 ({2, 3, 5} : Finset ℕ)) 2 hS' hSne' = 7 := by
    apply squareAnchorFirstPositiveUnreservedOffset_eq_of_profile_min_regression
      hS' hSne' 2 7
    · rw [mem_genericPositiveUnreservedOffsetProfile_iff]
      norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
        finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor, ReservedByPrimeBasis]
    · intro t ht
      by_contra hnot
      have hlt : t < 7 := Nat.lt_of_not_ge hnot
      interval_cases t <;>
        norm_num [mem_genericPositiveUnreservedOffsetProfile_iff,
          squareAnchorWheelProjection, primeBasisWheelProjection,
          finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
          ReservedByPrimeBasis] at ht
  have hpair11 : squareAnchorSuccessorPairPositiveFirstHit
      (insert 7 ({2, 3, 5} : Finset ℕ)) 1 hS' hSne' = 7 := by
    norm_num [squareAnchorSuccessorPairPositiveFirstHit, h210_1, h210_2]
  have hpair_upper : squareSuccessorPairPositiveFirstHitRadius
      (insert 7 ({2, 3, 5} : Finset ℕ)) hS' hSne' ≤ 7 := by
    unfold squareSuccessorPairPositiveFirstHitRadius
    apply Finset.sup_le
    intro n hn
    have hn' : n < 210 := by simpa [finitePrimeBasisProduct] using hn
    have hwithin : ∃ t, t ≤ 7 ∧
        (t ∈ genericPositiveUnreservedOffsetProfile
            (insert 7 ({2, 3, 5} : Finset ℕ))
            (squareAnchorWheelProjection (insert 7 ({2, 3, 5} : Finset ℕ)) n) ∨
          t ∈ genericPositiveUnreservedOffsetProfile
            (insert 7 ({2, 3, 5} : Finset ℕ))
            (squareAnchorWheelProjection (insert 7 ({2, 3, 5} : Finset ℕ)) (n + 1))) := by
      interval_cases n <;>
        first
        | (refine ⟨1, by norm_num, Or.inl ?_⟩
           rw [mem_genericPositiveUnreservedOffsetProfile_iff]
           norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
             finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
             ReservedByPrimeBasis]
           done)
        | (refine ⟨2, by norm_num, Or.inl ?_⟩
           rw [mem_genericPositiveUnreservedOffsetProfile_iff]
           norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
             finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
             ReservedByPrimeBasis]
           done)
        | (refine ⟨3, by norm_num, Or.inl ?_⟩
           rw [mem_genericPositiveUnreservedOffsetProfile_iff]
           norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
             finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
             ReservedByPrimeBasis]
           done)
        | (refine ⟨4, by norm_num, Or.inl ?_⟩
           rw [mem_genericPositiveUnreservedOffsetProfile_iff]
           norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
             finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
             ReservedByPrimeBasis]
           done)
        | (refine ⟨5, by norm_num, Or.inl ?_⟩
           rw [mem_genericPositiveUnreservedOffsetProfile_iff]
           norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
             finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
             ReservedByPrimeBasis]
           done)
        | (refine ⟨6, by norm_num, Or.inl ?_⟩
           rw [mem_genericPositiveUnreservedOffsetProfile_iff]
           norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
             finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
             ReservedByPrimeBasis]
           done)
        | (refine ⟨7, by norm_num, Or.inl ?_⟩
           rw [mem_genericPositiveUnreservedOffsetProfile_iff]
           norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
             finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
             ReservedByPrimeBasis]
           done)
        | (refine ⟨1, by norm_num, Or.inr ?_⟩
           rw [mem_genericPositiveUnreservedOffsetProfile_iff]
           norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
             finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
             ReservedByPrimeBasis]
           done)
        | (refine ⟨2, by norm_num, Or.inr ?_⟩
           rw [mem_genericPositiveUnreservedOffsetProfile_iff]
           norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
             finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
             ReservedByPrimeBasis]
           done)
        | (refine ⟨3, by norm_num, Or.inr ?_⟩
           rw [mem_genericPositiveUnreservedOffsetProfile_iff]
           norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
             finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
             ReservedByPrimeBasis]
           done)
        | (refine ⟨4, by norm_num, Or.inr ?_⟩
           rw [mem_genericPositiveUnreservedOffsetProfile_iff]
           norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
             finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
             ReservedByPrimeBasis]
           done)
        | (refine ⟨5, by norm_num, Or.inr ?_⟩
           rw [mem_genericPositiveUnreservedOffsetProfile_iff]
           norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
             finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
             ReservedByPrimeBasis]
           done)
        | (refine ⟨6, by norm_num, Or.inr ?_⟩
           rw [mem_genericPositiveUnreservedOffsetProfile_iff]
           norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
             finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
             ReservedByPrimeBasis]
           done)
        | (refine ⟨7, by norm_num, Or.inr ?_⟩
           rw [mem_genericPositiveUnreservedOffsetProfile_iff]
           norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
             finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
             ReservedByPrimeBasis])
    obtain ⟨t, ht, hmem | hmem⟩ := hwithin
    · exact (squareAnchorSuccessorPairPositiveFirstHit_le_left hS' hSne' n).trans
        ((squareAnchorFirstPositiveUnreservedOffset_le_of_profile_mem
          hS' hSne' n t hmem).trans ht)
    · exact (squareAnchorSuccessorPairPositiveFirstHit_le_right hS' hSne' n).trans
        ((squareAnchorFirstPositiveUnreservedOffset_le_of_profile_mem
          hS' hSne' (n + 1) t hmem).trans ht)
  have hpair_lower : 7 ≤ squareSuccessorPairPositiveFirstHitRadius
      (insert 7 ({2, 3, 5} : Finset ℕ)) hS' hSne' := by
    rw [squareSuccessorPairPositiveFirstHitRadius]
    have hle := Finset.le_sup
      (s := Finset.range (finitePrimeBasisProduct (insert 7
        ({2, 3, 5} : Finset ℕ))))
      (b := 1)
      (f := fun n => squareAnchorSuccessorPairPositiveFirstHit
        (insert 7 ({2, 3, 5} : Finset ℕ)) n hS' hSne')
      (Finset.mem_range.mpr (by norm_num [finitePrimeBasisProduct]))
    simpa [hpair11] using hle
  have holdpair : squareSuccessorPairPositiveFirstHitRadius
      ({2, 3, 5} : Finset ℕ) hS hSne = 5 := by
    simpa using (squareSuccessorPairPositiveFirstHit_two_three_five_regression).2.1
  refine ⟨h30_1, h210_1, h30_11, h210_11, holdpair,
    le_antisymm hpair_upper hpair_lower, h210_2, ?_, ?_⟩
  · norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
      finitePrimeBasisProduct]
  · norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
      finitePrimeBasisProduct]

end DkMath.NumberTheory.PrimorialUniverse
