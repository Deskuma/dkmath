/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.Exchange

#print "file: DkMath.Tromino.ExchangeRescue"

namespace DkMath.Tromino

/-!
# Forbidden-state rescue

This module is deliberately state-only. A forbidden set contains target
states, while `availableExchanges` contains the deltas whose translated target
is not forbidden.
-/

/-- Exchange deltas whose target state avoids the forbidden set. -/
def availableExchanges
    (x : TrominoState) (B : Finset TrominoState) : Finset TrominoState :=
  Finset.univ.filter (fun delta => exchange delta x ∉ B)

/-- Membership in the available set is target-state avoidance. -/
@[simp] theorem mem_availableExchanges_iff
    {x delta : TrominoState} {B : Finset TrominoState} :
    delta ∈ availableExchanges x B ↔ exchange delta x ∉ B := by
  simp [availableExchanges]

/-- A non-full forbidden set has an exchange avoiding it. -/
theorem exists_availableExchange_of_ne_univ
    (x : TrominoState) (B : Finset TrominoState)
    (hB : B ≠ Finset.univ) :
    ∃ delta, delta ∈ availableExchanges x B := by
  have htarget : ∃ y, y ∉ B := by
    by_contra hnone
    apply hB
    apply Finset.eq_univ_iff_forall.mpr
    intro y
    by_contra hy
    exact hnone ⟨y, hy⟩
  rcases htarget with ⟨y, hy⟩
  rcases (existsUnique_exchange_to x y).exists with ⟨delta, hdelta⟩
  refine ⟨delta, ?_⟩
  rw [mem_availableExchanges_iff]
  simpa [hdelta] using hy

/-- If the current state is forbidden, a nonzero avoiding exchange exists. -/
theorem exists_nonzero_availableExchange_of_mem_of_ne_univ
    {x : TrominoState} {B : Finset TrominoState}
    (hx : x ∈ B) (hB : B ≠ Finset.univ) :
    ∃ delta, delta ≠ 0 ∧ delta ∈ availableExchanges x B := by
  rcases exists_availableExchange_of_ne_univ x B hB with ⟨delta, hdelta⟩
  refine ⟨delta, ?_, hdelta⟩
  intro hzero
  subst delta
  have havoid : exchange 0 x ∉ B :=
    mem_availableExchanges_iff.mp hdelta
  exact havoid (by simpa using hx)

/-- Exact legal-exchange cardinality in additive form. -/
theorem card_availableExchanges_add_card_forbidden
    (x : TrominoState) (B : Finset TrominoState) :
    (availableExchanges x B).card + B.card = 4 := by
  classical
  have hforbidden :
      (Finset.univ.filter
          (fun delta : TrominoState => exchange delta x ∈ B)).card = B.card := by
    apply Finset.card_equiv (exchangeEquiv x)
    intro delta
    simp
  have hpartition :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset TrominoState))
      (p := fun delta : TrominoState => exchange delta x ∉ B)
  calc
    (availableExchanges x B).card + B.card =
        (availableExchanges x B).card +
          (Finset.univ.filter
            (fun delta : TrominoState => exchange delta x ∈ B)).card := by
              rw [hforbidden]
    _ = (Finset.univ : Finset TrominoState).card := by
      simpa [availableExchanges] using hpartition
    _ = 4 := by simp

/-- Exact legal-exchange cardinality in subtraction form. -/
theorem card_availableExchanges
    (x : TrominoState) (B : Finset TrominoState) :
    (availableExchanges x B).card = 4 - B.card := by
  have h := card_availableExchanges_add_card_forbidden x B
  omega

/-- A forbidden set of cardinality three leaves exactly one exchange. -/
theorem card_availableExchanges_eq_one_of_card_eq_three
    {x : TrominoState} {B : Finset TrominoState}
    (hB : B.card = 3) :
    (availableExchanges x B).card = 1 := by
  rw [card_availableExchanges, hB]

/-- Every state being forbidden leaves no available exchange. -/
theorem availableExchanges_eq_empty_of_eq_univ
    (x : TrominoState) :
    availableExchanges x Finset.univ = ∅ := by
  ext delta
  simp [availableExchanges]

/-- The available set is empty exactly for the all-forbidden set. -/
theorem availableExchanges_eq_empty_iff
    (x : TrominoState) (B : Finset TrominoState) :
    availableExchanges x B = ∅ ↔ B = Finset.univ := by
  constructor
  · intro hempty
    by_contra hB
    rcases exists_availableExchange_of_ne_univ x B hB with ⟨delta, hdelta⟩
    rw [hempty] at hdelta
    simp at hdelta
  · intro hB
    subst B
    exact availableExchanges_eq_empty_of_eq_univ x

end DkMath.Tromino
