/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.ExchangeRescue

#print "file: DkMath.Tromino.PieceExchange"

namespace DkMath.Tromino

/-!
# Uniform piece exchange and boundary forbidden deltas

This module lifts the state-only exchange calculus to a finite list of
inside/outside contacts. It introduces no geometry: a contact is just two
states, and a uniform exchange acts on an arbitrary indexed coloring.
-/

/-- Apply one exchange delta uniformly to an indexed coloring. -/
def uniformExchange {I : Type*}
    (delta : TrominoState) (c : I → TrominoState) (i : I) : TrominoState :=
  exchange delta (c i)

/-- Uniform exchange preserves equality of indexed states. -/
theorem uniformExchange_eq_iff {I : Type*}
    (delta : TrominoState) (c : I → TrominoState) (i j : I) :
    uniformExchange delta c i = uniformExchange delta c j ↔ c i = c j := by
  constructor
  · intro h
    have h' : c i + delta = c j + delta := by
      simpa [uniformExchange, exchange] using h
    exact add_right_cancel h'
  · intro h
    simp [uniformExchange, h]

/-- Uniform exchange preserves inequality of indexed states. -/
theorem uniformExchange_ne_iff {I : Type*}
    (delta : TrominoState) (c : I → TrominoState) (i j : I) :
    uniformExchange delta c i ≠ uniformExchange delta c j ↔ c i ≠ c j := by
  exact not_congr (uniformExchange_eq_iff delta c i j)

/-- One inside/outside state contact, with no geometric position attached. -/
structure BoundaryContact where
  inside : TrominoState
  outside : TrominoState
deriving DecidableEq

/-- The unique exchange delta that makes a contact conflict. -/
def forbiddenDelta (contact : BoundaryContact) : TrominoState :=
  contact.inside + contact.outside

/-- A contact conflicts after exactly its forbidden delta. -/
theorem exchange_eq_contact_iff
    (contact : BoundaryContact) (delta : TrominoState) :
    exchange delta contact.inside = contact.outside ↔
      delta = forbiddenDelta contact := by
  constructor
  · intro h
    have h' : contact.inside + delta = contact.outside := by
      simpa [exchange] using h
    calc
      delta = 0 + delta := by simp
      _ = (contact.inside + contact.inside) + delta := by
        rw [state_add_self]
      _ = contact.inside + (contact.inside + delta) := by
        rw [add_assoc]
      _ = contact.inside + contact.outside := by rw [h']
      _ = forbiddenDelta contact := rfl
  · intro h
    rw [h]
    dsimp [forbiddenDelta, exchange]
    rw [← add_assoc, state_add_self, zero_add]

/-- The forbidden delta of a contact is unique. -/
theorem existsUnique_forbiddenDelta (contact : BoundaryContact) :
    ∃! delta, exchange delta contact.inside = contact.outside := by
  refine ⟨forbiddenDelta contact, ?_, ?_⟩
  · exact (exchange_eq_contact_iff contact _).2 rfl
  · intro delta hdelta
    exact (exchange_eq_contact_iff contact delta).1 hdelta

/-- The identity delta is forbidden exactly for an already-conflicting contact. -/
theorem forbiddenDelta_eq_zero_iff (contact : BoundaryContact) :
    forbiddenDelta contact = 0 ↔ contact.inside = contact.outside := by
  constructor
  · intro hzero
    have hconf : exchange 0 contact.inside = contact.outside :=
      (exchange_eq_contact_iff contact 0).2 hzero.symm
    simpa using hconf
  · intro hsame
    have hzero : 0 = forbiddenDelta contact :=
      (exchange_eq_contact_iff contact 0).1 (by
        simp [exchange, hsame])
    exact hzero.symm

/-- The finite set of exchange deltas forbidden by recorded contacts. -/
def forbiddenExchangeSet
    (contacts : Finset BoundaryContact) : Finset TrominoState :=
  contacts.image forbiddenDelta

/-- Membership in the forbidden set means arising from a recorded contact. -/
@[simp] theorem mem_forbiddenExchangeSet_iff
    {contacts : Finset BoundaryContact} {delta : TrominoState} :
    delta ∈ forbiddenExchangeSet contacts ↔
      ∃ contact ∈ contacts, forbiddenDelta contact = delta := by
  simp [forbiddenExchangeSet]

/-- All recorded contacts avoid equality after a uniform exchange. -/
def boundaryCompatible
    (delta : TrominoState) (contacts : Finset BoundaryContact) : Prop :=
  ∀ contact ∈ contacts,
    exchange delta contact.inside ≠ contact.outside

/-- Boundary compatibility is exactly avoidance of the forbidden delta set. -/
theorem boundaryCompatible_iff_not_mem
    {delta : TrominoState} {contacts : Finset BoundaryContact} :
    boundaryCompatible delta contacts ↔
      delta ∉ forbiddenExchangeSet contacts := by
  constructor
  · intro hcompatible hforbidden
    rcases (mem_forbiddenExchangeSet_iff.mp hforbidden) with
      ⟨contact, hcontact, hdelta⟩
    exact (hcompatible contact hcontact)
      ((exchange_eq_contact_iff contact delta).2 hdelta.symm)
  · intro hdelta contact hcontact hconflict
    apply hdelta
    apply mem_forbiddenExchangeSet_iff.mpr
    exact ⟨contact, hcontact,
      (exchange_eq_contact_iff contact delta).1 hconflict |>.symm⟩

/-- The finite set of deltas compatible with every recorded contact. -/
noncomputable def compatibleExchanges
    (contacts : Finset BoundaryContact) : Finset TrominoState := by
  classical
  exact Finset.univ.filter (fun delta => boundaryCompatible delta contacts)

@[simp] theorem mem_compatibleExchanges_iff
    {contacts : Finset BoundaryContact} {delta : TrominoState} :
    delta ∈ compatibleExchanges contacts ↔
      boundaryCompatible delta contacts := by
  simp [compatibleExchanges]

/-- Compatible deltas are the state-only available exchanges from zero. -/
theorem compatibleExchanges_eq_availableExchanges_zero
    (contacts : Finset BoundaryContact) :
    compatibleExchanges contacts =
      availableExchanges 0 (forbiddenExchangeSet contacts) := by
  ext delta
  rw [mem_compatibleExchanges_iff, mem_availableExchanges_iff,
    boundaryCompatible_iff_not_mem]
  simp [exchange]

/-- A non-full forbidden contact set admits a uniform piece rescue. -/
theorem exists_boundaryCompatible_of_forbiddenExchangeSet_ne_univ
    (contacts : Finset BoundaryContact)
    (hcontacts : forbiddenExchangeSet contacts ≠ Finset.univ) :
    ∃ delta, boundaryCompatible delta contacts := by
  rcases exists_availableExchange_of_ne_univ 0
      (forbiddenExchangeSet contacts) hcontacts with ⟨delta, hdelta⟩
  refine ⟨delta, (boundaryCompatible_iff_not_mem).2 ?_⟩
  have hdelta' : exchange delta 0 ∉ forbiddenExchangeSet contacts :=
    mem_availableExchanges_iff.mp hdelta
  simpa [exchange] using hdelta'

/-- A current contact conflict plus a non-full forbidden set has a nonzero rescue. -/
theorem exists_nonzero_boundaryCompatible_of_not_compatible_zero
    (contacts : Finset BoundaryContact)
    (hcurrent : ¬ boundaryCompatible 0 contacts)
    (hcontacts : forbiddenExchangeSet contacts ≠ Finset.univ) :
    ∃ delta, delta ≠ 0 ∧ boundaryCompatible delta contacts := by
  have hzero : 0 ∈ forbiddenExchangeSet contacts := by
    by_contra hzero
    apply hcurrent
    exact (boundaryCompatible_iff_not_mem).2 hzero
  rcases exists_nonzero_availableExchange_of_mem_of_ne_univ
      (x := 0) (B := forbiddenExchangeSet contacts) hzero hcontacts with
    ⟨delta, hdelta, havailable⟩
  refine ⟨delta, hdelta, (boundaryCompatible_iff_not_mem).2 ?_⟩
  have havailable' : exchange delta 0 ∉ forbiddenExchangeSet contacts :=
    mem_availableExchanges_iff.mp havailable
  simpa [exchange] using havailable'

/-- Exact compatible-delta cardinality in additive form. -/
theorem card_compatibleExchanges_add_card_forbidden
    (contacts : Finset BoundaryContact) :
    (compatibleExchanges contacts).card +
        (forbiddenExchangeSet contacts).card = 4 := by
  rw [compatibleExchanges_eq_availableExchanges_zero]
  exact card_availableExchanges_add_card_forbidden 0
    (forbiddenExchangeSet contacts)

/-- Exact compatible-delta cardinality in subtraction form. -/
theorem card_compatibleExchanges
    (contacts : Finset BoundaryContact) :
    (compatibleExchanges contacts).card =
      4 - (forbiddenExchangeSet contacts).card := by
  have h := card_compatibleExchanges_add_card_forbidden contacts
  omega

/-- Three distinct forbidden deltas leave exactly one compatible delta. -/
theorem card_compatibleExchanges_eq_one_of_forbidden_card_eq_three
    {contacts : Finset BoundaryContact}
    (hcontacts : (forbiddenExchangeSet contacts).card = 3) :
    (compatibleExchanges contacts).card = 1 := by
  rw [card_compatibleExchanges, hcontacts]

/-- No contacts impose no compatibility restrictions. -/
theorem card_compatibleExchanges_empty :
    (compatibleExchanges ∅).card = 4 := by
  simpa [forbiddenExchangeSet] using
    (card_compatibleExchanges (∅ : Finset BoundaryContact))

/-- One contact produces a singleton forbidden delta set. -/
theorem forbiddenExchangeSet_singleton (contact : BoundaryContact) :
    forbiddenExchangeSet {contact} = {forbiddenDelta contact} := by
  simp [forbiddenExchangeSet]

/-- All four forbidden deltas leave no compatible exchange. -/
theorem no_boundaryCompatible_of_forbiddenExchangeSet_eq_univ
    (contacts : Finset BoundaryContact)
    (hcontacts : forbiddenExchangeSet contacts = Finset.univ) :
    ¬ ∃ delta, boundaryCompatible delta contacts := by
  intro hex
  rcases hex with ⟨delta, hdelta⟩
  have hnot : delta ∉ forbiddenExchangeSet contacts :=
    (boundaryCompatible_iff_not_mem.mp hdelta)
  exact hnot (hcontacts ▸ Finset.mem_univ delta)

end DkMath.Tromino
