/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.ExchangeRescue

#print "file: DkMathTest.Tromino.ExchangeRescueAxiomAudit"

namespace DkMathTest.Tromino.ExchangeRescueAxiomAudit

open DkMath.Tromino

example (x y : TrominoState) :
    ∃! delta, exchange delta x = y :=
  existsUnique_exchange_to x y

example (x : TrominoState) :
    (availableExchanges x ∅).card = 4 := by
  simp [card_availableExchanges]

example (x : TrominoState) :
    (availableExchanges x {x}).card = 3 := by
  rw [card_availableExchanges]
  simp

example {x delta : TrominoState}
    (hdelta : delta ∈ availableExchanges x {x}) :
    delta ≠ 0 := by
  intro hzero
  subst delta
  have havoid : exchange 0 x ∉ ({x} : Finset TrominoState) :=
    mem_availableExchanges_iff.mp hdelta
  exact havoid (by simp)

example {x : TrominoState} {B : Finset TrominoState}
    (hB : B.card = 3) :
    (availableExchanges x B).card = 1 :=
  card_availableExchanges_eq_one_of_card_eq_three hB

example (x : TrominoState) :
    availableExchanges x Finset.univ = ∅ :=
  availableExchanges_eq_empty_of_eq_univ x

example (x : TrominoState) (B : Finset TrominoState)
    (hB : B ≠ Finset.univ) :
    ∃ delta, delta ∈ availableExchanges x B :=
  exists_availableExchange_of_ne_univ x B hB

example {x : TrominoState} {B : Finset TrominoState}
    (hx : x ∈ B) (hB : B ≠ Finset.univ) :
    ∃ delta, delta ≠ 0 ∧ delta ∈ availableExchanges x B :=
  exists_nonzero_availableExchange_of_mem_of_ne_univ hx hB

example (x : TrominoState) (B : Finset TrominoState) :
    availableExchanges x B = ∅ ↔ B = Finset.univ :=
  availableExchanges_eq_empty_iff x B

#print axioms DkMath.Tromino.existsUnique_exchange_to
#print axioms DkMath.Tromino.exchangeEquiv
#print axioms DkMath.Tromino.exists_availableExchange_of_ne_univ
#print axioms DkMath.Tromino.exists_nonzero_availableExchange_of_mem_of_ne_univ
#print axioms DkMath.Tromino.card_availableExchanges
#print axioms DkMath.Tromino.availableExchanges_eq_empty_iff

end DkMathTest.Tromino.ExchangeRescueAxiomAudit
